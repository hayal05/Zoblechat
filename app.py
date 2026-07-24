import eventlet
eventlet.monkey_patch()
# ^ MUST be the very first thing that happens in this module, before any other
# import (including stdlib ones like os/logging). gunicorn is configured to run
# this app with the eventlet worker (`gunicorn -k eventlet`, see Procfile), which
# means every request — HTTP and WebSocket alike — is served through eventlet's
# cooperative green threads. If the stdlib socket/ssl/threading/time modules
# aren't patched before anything else imports them, blocking calls (SQLite
# writes via SQLAlchemy, DNS lookups, etc.) can stall the single worker's event
# loop instead of yielding, which is what was causing registration/login to hang
# or reset in production and surface as a generic "Connection error" — this bug
# affects plain HTTP routes too, not just Socket.IO traffic, because they all
# run through the same eventlet-patched worker.

import os
import re
import uuid
import logging
from datetime import datetime

from dotenv import load_dotenv
from flask import Flask, request, jsonify, redirect, url_for, render_template
from flask_sqlalchemy import SQLAlchemy
from flask_login import (
    LoginManager, UserMixin, login_user, logout_user,
    login_required, current_user
)
from flask_socketio import SocketIO, join_room, emit
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from sqlalchemy import func
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename
from PIL import Image, UnidentifiedImageError

# -------------------------------------------------------------------
# Environment
# -------------------------------------------------------------------
load_dotenv()  # loads a local .env file if present; no-op in production if absent

BASE_DIR = os.path.abspath(os.path.dirname(__file__))
UPLOAD_FOLDER = os.path.join(BASE_DIR, "static", "uploads")

IS_PRODUCTION = os.environ.get("FLASK_ENV", "development") == "production"

logging.basicConfig(
    level=logging.INFO if IS_PRODUCTION else logging.DEBUG,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
)
logger = logging.getLogger("zoble_chat")

# -------------------------------------------------------------------
# Constraints (centralized so validation logic below stays consistent)
# -------------------------------------------------------------------
ALLOWED_EXTENSIONS = {"png", "jpg", "jpeg", "gif", "webp"}
MAX_CONTENT_LENGTH = 5 * 1024 * 1024      # 5 MB upload ceiling
MAX_IMAGE_DIMENSION = 4096                # reject absurdly large images (decompression-bomb guard)
USERNAME_PATTERN = re.compile(r"^[A-Za-z0-9_.]{3,30}$")
PASSWORD_MIN_LENGTH = 8
MESSAGE_MAX_LENGTH = 4000

# -------------------------------------------------------------------
# App Configuration
# -------------------------------------------------------------------
app = Flask(__name__)

_secret_key = os.environ.get("SECRET_KEY")
if not _secret_key:
    if IS_PRODUCTION:
        # Fail loudly rather than silently running a production deployment
        # with a guessable, hardcoded session-signing key.
        raise RuntimeError(
            "SECRET_KEY environment variable is required when FLASK_ENV=production."
        )
    logger.warning(
        "SECRET_KEY not set — using an insecure development default. "
        "Set SECRET_KEY in your environment before deploying."
    )
    _secret_key = "dev-secret-change-me"

app.config["SECRET_KEY"] = _secret_key
app.config["SQLALCHEMY_DATABASE_URI"] = os.environ.get(
    "DATABASE_URL", f"sqlite:///{os.path.join(BASE_DIR, 'chat.db')}"
)
app.config["SQLALCHEMY_TRACK_MODIFICATIONS"] = False
app.config["SQLALCHEMY_ENGINE_OPTIONS"] = {"pool_pre_ping": True}
app.config["UPLOAD_FOLDER"] = UPLOAD_FOLDER
app.config["MAX_CONTENT_LENGTH"] = MAX_CONTENT_LENGTH

# Session cookie hardening
app.config["SESSION_COOKIE_HTTPONLY"] = True
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"
app.config["SESSION_COOKIE_SECURE"] = IS_PRODUCTION  # requires HTTPS in prod (Render provides this)
app.config["REMEMBER_COOKIE_HTTPONLY"] = True
app.config["REMEMBER_COOKIE_SECURE"] = IS_PRODUCTION

os.makedirs(UPLOAD_FOLDER, exist_ok=True)

db = SQLAlchemy(app)

login_manager = LoginManager(app)
login_manager.login_view = "login_page"
login_manager.session_protection = "strong"  # ties session to IP/user-agent fingerprint

# Rate limiting — protects auth endpoints from brute-force / credential stuffing.
# Storage defaults to in-memory, which is fine for a single-worker deployment
# (this app intentionally runs with -w 1, see Procfile notes).
limiter = Limiter(
    key_func=get_remote_address,
    app=app,
    default_limits=["200 per day", "50 per hour"],
    storage_uri="memory://",
)

# SocketIO — async_mode="eventlet" pairs with the eventlet dependency and the
# `gunicorn -k eventlet` worker used in production.
socketio = SocketIO(app, async_mode="eventlet", cors_allowed_origins="*")


# -------------------------------------------------------------------
# Database Models
# -------------------------------------------------------------------
class User(db.Model, UserMixin):
    __tablename__ = "users"

    id = db.Column(db.Integer, primary_key=True)
    username = db.Column(db.String(30), unique=True, nullable=False, index=True)
    password_hash = db.Column(db.String(255), nullable=False)
    profile_pic = db.Column(db.String(255), nullable=False, default="default.png")
    created_at = db.Column(db.DateTime, default=datetime.utcnow)

    sent_messages = db.relationship(
        "Message", foreign_keys="Message.sender_id", backref="sender", lazy="dynamic"
    )
    received_messages = db.relationship(
        "Message", foreign_keys="Message.recipient_id", backref="recipient", lazy="dynamic"
    )

    def set_password(self, raw_password):
        self.password_hash = generate_password_hash(raw_password)

    def check_password(self, raw_password):
        return check_password_hash(self.password_hash, raw_password)

    def to_dict(self):
        return {"id": self.id, "username": self.username, "profile_pic": self.profile_pic}

    def __repr__(self):
        return f"<User {self.username}>"


class Message(db.Model):
    __tablename__ = "messages"

    id = db.Column(db.Integer, primary_key=True)
    sender_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    recipient_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    content = db.Column(db.String(MESSAGE_MAX_LENGTH), nullable=False)
    timestamp = db.Column(db.DateTime, default=datetime.utcnow, index=True)
    is_read = db.Column(db.Boolean, default=False, nullable=False)

    def to_dict(self):
        return {
            "id": self.id,
            "sender_id": self.sender_id,
            "recipient_id": self.recipient_id,
            "content": self.content,
            "timestamp": self.timestamp.isoformat(),
            "is_read": self.is_read,
        }

    def __repr__(self):
        return f"<Message {self.id} from {self.sender_id} to {self.recipient_id}>"


@login_manager.user_loader
def load_user(user_id):
    try:
        return User.query.get(int(user_id))
    except (TypeError, ValueError):
        return None


# -------------------------------------------------------------------
# Validation helpers
# -------------------------------------------------------------------
def allowed_file(filename):
    return "." in filename and filename.rsplit(".", 1)[1].lower() in ALLOWED_EXTENSIONS


def validate_username(username):
    if not username or not USERNAME_PATTERN.match(username):
        return "Username must be 3-30 characters: letters, numbers, underscores, or periods only."
    return None


def validate_password(password):
    if not password or len(password) < PASSWORD_MIN_LENGTH:
        return f"Password must be at least {PASSWORD_MIN_LENGTH} characters."
    if not re.search(r"[A-Za-z]", password) or not re.search(r"[0-9]", password):
        return "Password must contain at least one letter and one number."
    return None


def verify_is_real_image(filepath):
    """Confirms the uploaded file is actually a valid image (not just a
    file with a spoofed .png/.jpg extension), and that it isn't an
    absurdly large image designed to exhaust memory on decode."""
    try:
        with Image.open(filepath) as img:
            img.verify()
        # Re-open after verify() (which invalidates the file handle for further use)
        with Image.open(filepath) as img:
            width, height = img.size
            if width > MAX_IMAGE_DIMENSION or height > MAX_IMAGE_DIMENSION:
                return False
        return True
    except (UnidentifiedImageError, OSError, ValueError):
        return False


def get_room_name(user_id):
    """Each user gets a private room named after their user ID, so we can
    target them directly regardless of which browser tab/device they're on."""
    return f"user_{user_id}"


# -------------------------------------------------------------------
# Security headers (defense in depth on top of cookie flags above)
# -------------------------------------------------------------------
@app.after_request
def set_security_headers(response):
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["X-Frame-Options"] = "DENY"
    response.headers["Referrer-Policy"] = "strict-origin-when-cross-origin"
    response.headers["Permissions-Policy"] = "camera=(), microphone=(), geolocation=()"
    if IS_PRODUCTION:
        response.headers["Strict-Transport-Security"] = "max-age=31536000; includeSubDomains"
    return response


# -------------------------------------------------------------------
# Error handlers — consistent JSON errors instead of default HTML pages
# -------------------------------------------------------------------
@app.errorhandler(404)
def handle_404(e):
    return jsonify({"error": "Not found."}), 404


@app.errorhandler(413)
def handle_413(e):
    return jsonify({"error": "Upload too large. Maximum size is 5 MB."}), 413


@app.errorhandler(429)
def handle_429(e):
    return jsonify({"error": "Too many requests. Please slow down and try again shortly."}), 429


@app.errorhandler(500)
def handle_500(e):
    logger.exception("Unhandled server error")
    db.session.rollback()
    return jsonify({"error": "Something went wrong on our end. Please try again."}), 500


# -------------------------------------------------------------------
# Page Routes (HTML)
# -------------------------------------------------------------------
@app.route("/")
@login_required
def index():
    other_users = User.query.filter(User.id != current_user.id).order_by(User.username.asc()).all()

    unread_counts = dict(
        db.session.query(Message.sender_id, func.count(Message.id))
        .filter(Message.recipient_id == current_user.id, Message.is_read.is_(False))
        .group_by(Message.sender_id)
        .all()
    )

    users_payload = [
        {
            "id": u.id,
            "username": u.username,
            "profile_pic": u.profile_pic,
            "unread_count": unread_counts.get(u.id, 0),
        }
        for u in other_users
    ]

    return render_template(
        "chat.html",
        current_user_data=current_user.to_dict(),
        users=users_payload,
    )


@app.route("/login")
def login_page():
    if current_user.is_authenticated:
        return redirect(url_for("index"))
    return render_template("login.html")


@app.route("/register")
def register_page():
    if current_user.is_authenticated:
        return redirect(url_for("index"))
    return render_template("register.html")


# -------------------------------------------------------------------
# Authentication API Routes (JSON)
# -------------------------------------------------------------------
@app.route("/api/register", methods=["POST"])
@limiter.limit("10 per minute")
def register():
    data = request.get_json(silent=True) or request.form

    username = (data.get("username") or "").strip()
    password = data.get("password") or ""

    username_error = validate_username(username)
    if username_error:
        return jsonify({"error": username_error}), 400

    password_error = validate_password(password)
    if password_error:
        return jsonify({"error": password_error}), 400

    # Case-insensitive uniqueness check avoids "Alice" vs "alice" collisions
    if User.query.filter(func.lower(User.username) == username.lower()).first():
        return jsonify({"error": "Username already taken."}), 409

    try:
        user = User(username=username)
        user.set_password(password)
        db.session.add(user)
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to create user")
        return jsonify({"error": "Could not create account. Please try again."}), 500

    login_user(user)
    logger.info("New user registered: %s", user.username)
    return jsonify({"message": "Registered successfully.", "user": user.to_dict()}), 201


@app.route("/api/login", methods=["POST"])
@limiter.limit("10 per minute")
def login():
    data = request.get_json(silent=True) or request.form

    username = (data.get("username") or "").strip()
    password = data.get("password") or ""

    # Generic error message on both bad-username and bad-password paths,
    # so the response can't be used to enumerate valid usernames.
    user = User.query.filter(func.lower(User.username) == username.lower()).first()
    if not user or not user.check_password(password):
        return jsonify({"error": "Invalid username or password."}), 401

    login_user(user)
    return jsonify({"message": "Logged in successfully.", "user": user.to_dict()}), 200


@app.route("/api/logout", methods=["POST"])
@login_required
def logout():
    logout_user()
    return jsonify({"message": "Logged out successfully."}), 200


@app.route("/api/me", methods=["GET"])
@login_required
def me():
    return jsonify({"user": current_user.to_dict()}), 200


@app.route("/api/messages/<int:other_user_id>", methods=["GET"])
@login_required
def get_conversation(other_user_id):
    """Returns the full message history between the current user and
    other_user_id (ascending by time), and marks any unread messages
    from other_user_id -> current_user as read as a side effect of
    opening the conversation."""
    other_user = User.query.get(other_user_id)
    if not other_user:
        return jsonify({"error": "User not found."}), 404

    messages = (
        Message.query.filter(
            db.or_(
                db.and_(Message.sender_id == current_user.id, Message.recipient_id == other_user_id),
                db.and_(Message.sender_id == other_user_id, Message.recipient_id == current_user.id),
            )
        )
        .order_by(Message.timestamp.asc())
        .all()
    )

    updated_count = (
        Message.query.filter_by(
            sender_id=other_user_id,
            recipient_id=current_user.id,
            is_read=False,
        ).update({"is_read": True})
    )
    if updated_count:
        db.session.commit()
        # Let the sender's other open tabs know their messages were seen.
        socketio.emit(
            "messages_seen",
            {"reader_id": current_user.id, "count": updated_count},
            room=get_room_name(other_user_id),
        )

    return jsonify({"messages": [m.to_dict() for m in messages]}), 200


@app.route("/api/profile-picture", methods=["POST"])
@login_required
@limiter.limit("20 per hour")
def update_profile_picture():
    if "file" not in request.files:
        return jsonify({"error": "No file part in the request."}), 400

    file = request.files["file"]

    if file.filename == "":
        return jsonify({"error": "No file selected."}), 400

    if not allowed_file(file.filename):
        return jsonify({"error": "Unsupported file type."}), 400

    # secure_filename strips path traversal characters; we also prefix the
    # user's id + a uuid so filenames can never collide or be guessed.
    original_name = secure_filename(file.filename)
    ext = original_name.rsplit(".", 1)[1].lower()
    unique_name = f"{current_user.id}_{uuid.uuid4().hex}.{ext}"
    filepath = os.path.join(app.config["UPLOAD_FOLDER"], unique_name)

    try:
        file.save(filepath)
    except OSError:
        logger.exception("Failed to save uploaded file")
        return jsonify({"error": "Could not save the uploaded file."}), 500

    # Verify the saved file is genuinely an image before trusting it — a
    # extension check alone can be spoofed (e.g. a script renamed to .png).
    if not verify_is_real_image(filepath):
        try:
            os.remove(filepath)
        except OSError:
            pass
        return jsonify({"error": "The uploaded file is not a valid image."}), 400

    old_pic = current_user.profile_pic
    current_user.profile_pic = unique_name

    try:
        db.session.commit()
    except Exception:
        db.session.rollback()
        try:
            os.remove(filepath)
        except OSError:
            pass
        logger.exception("Failed to update profile picture in DB")
        return jsonify({"error": "Could not update profile picture. Please try again."}), 500

    # Clean up the old file, but never delete the shared default avatar.
    if old_pic and old_pic != "default.png":
        old_path = os.path.join(app.config["UPLOAD_FOLDER"], old_pic)
        if os.path.exists(old_path):
            try:
                os.remove(old_path)
            except OSError:
                logger.warning("Could not remove old profile picture: %s", old_pic)

    return jsonify({"message": "Profile picture updated.", "profile_pic": unique_name}), 200


# -------------------------------------------------------------------
# Socket.IO Event Handlers
# -------------------------------------------------------------------
@socketio.on("connect")
def handle_connect():
    if not current_user.is_authenticated:
        # Reject unauthenticated socket connections outright
        return False

    join_room(get_room_name(current_user.id))
    emit("connection_ack", {"message": f"Connected as {current_user.username}"})


@socketio.on("join")
def handle_join(data=None):
    """Explicit join event, useful if the client wants to (re)join
    its room manually after reconnecting."""
    if not current_user.is_authenticated:
        return

    join_room(get_room_name(current_user.id))
    emit("connection_ack", {"message": f"{current_user.username} joined their room"})


@socketio.on("send_message")
def handle_send_message(data):
    """
    Expected payload:
    {
        "recipient_id": <int>,
        "content": <str>
    }
    """
    if not current_user.is_authenticated:
        emit("error", {"error": "Not authenticated."})
        return

    if not isinstance(data, dict):
        emit("error", {"error": "Invalid payload."})
        return

    recipient_id = data.get("recipient_id")
    content = (data.get("content") or "").strip()

    if not isinstance(recipient_id, int):
        # Be tolerant of client-side numeric strings, but never trust non-numeric input
        try:
            recipient_id = int(recipient_id)
        except (TypeError, ValueError):
            emit("error", {"error": "recipient_id must be a valid user id."})
            return

    if not content:
        emit("error", {"error": "Message content cannot be empty."})
        return

    if len(content) > MESSAGE_MAX_LENGTH:
        emit("error", {"error": f"Message is too long (max {MESSAGE_MAX_LENGTH} characters)."})
        return

    if recipient_id == current_user.id:
        emit("error", {"error": "You cannot send a message to yourself."})
        return

    recipient = User.query.get(recipient_id)
    if not recipient:
        emit("error", {"error": "Recipient does not exist."})
        return

    try:
        message = Message(
            sender_id=current_user.id,
            recipient_id=recipient_id,
            content=content,
            is_read=False,
        )
        db.session.add(message)
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to save message")
        emit("error", {"error": "Could not send message. Please try again."})
        return

    payload = message.to_dict()
    payload["sender_username"] = current_user.username
    payload["sender_profile_pic"] = current_user.profile_pic

    # Broadcast to both parties' private rooms so every open tab/device
    # for sender AND recipient updates instantly.
    socketio.emit("receive_message", payload, room=get_room_name(recipient_id))
    socketio.emit("receive_message", payload, room=get_room_name(current_user.id))


@socketio.on("mark_read")
def handle_mark_read(data):
    """
    Expected payload:
    {
        "sender_id": <int>   # the user whose messages to you are being marked read
    }
    """
    if not current_user.is_authenticated:
        emit("error", {"error": "Not authenticated."})
        return

    if not isinstance(data, dict):
        emit("error", {"error": "Invalid payload."})
        return

    sender_id = data.get("sender_id")
    try:
        sender_id = int(sender_id)
    except (TypeError, ValueError):
        emit("error", {"error": "sender_id must be a valid user id."})
        return

    try:
        updated_count = (
            Message.query.filter_by(
                sender_id=sender_id,
                recipient_id=current_user.id,
                is_read=False,
            ).update({"is_read": True})
        )
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to mark messages as read")
        emit("error", {"error": "Could not update read status."})
        return

    emit("messages_marked_read", {
        "sender_id": sender_id,
        "count": updated_count,
    }, room=get_room_name(current_user.id))

    emit("messages_seen", {
        "reader_id": current_user.id,
        "count": updated_count,
    }, room=get_room_name(sender_id))


@socketio.on("disconnect")
def handle_disconnect():
    if current_user.is_authenticated:
        logger.info("%s disconnected", current_user.username)


# -------------------------------------------------------------------
# Entry Point
# -------------------------------------------------------------------
if __name__ == "__main__":
    socketio.run(app, debug=not IS_PRODUCTION, host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
