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
from collections import defaultdict
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
# Deliberately simple RFC-5322-ish check — good enough to catch typos without
# rejecting valid addresses the way an overly strict regex tends to.
EMAIL_PATTERN = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")
PASSWORD_MIN_LENGTH = 8
MESSAGE_MAX_LENGTH = 4000
FULL_NAME_MIN_LENGTH = 1
FULL_NAME_MAX_LENGTH = 60

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
login_manager.session_protection = "basic"  # "strong" ties the session to an IP/user-agent
# fingerprint, which sounds nice in theory but is a known source of trouble with
# Flask-SocketIO: the polling->websocket handshake (and any proxy/load balancer in
# front of the app, e.g. Render/Heroku) can make a legitimate reconnect look like a
# different client, causing Flask-Login to silently invalidate the session. That in
# turn makes current_user.is_authenticated false inside the Socket.IO "connect"
# handler below, so the server rejects the connection with no visible error — which
# looks exactly like "the send button doesn't do anything." "basic" still rotates
# the session id periodically but doesn't reject on fingerprint mismatch.

# Rate limiting — protects auth endpoints from brute-force / credential stuffing.
# Storage defaults to in-memory, which is fine for a single-worker deployment
# (this app intentionally runs with -w 1, see Procfile notes).
limiter = Limiter(
    key_func=get_remote_address,
    app=app,
    default_limits=["200 per day", "50 per hour"],
    storage_uri="memory://",
)


@limiter.request_filter
def exempt_socketio():
    # default_limits applies to every Flask route by default, and Flask-SocketIO's
    # handshake/polling requests go through Flask's normal request cycle at
    # /socket.io/... Each failed connection attempt triggers a fresh handshake, and
    # the Socket.IO client auto-retries every few seconds while disconnected — which
    # burns through "50 per hour" in well under a minute. Once that's exhausted every
    # further handshake gets a 429, and the client is stuck looping on "Reconnecting…"
    # for the rest of the hour no matter how many times the page is reloaded. The
    # actual chat message rate is separately bounded by Socket.IO's own event
    # handling, so exempting this path here is safe.
    return request.path.startswith("/socket.io")

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
    email = db.Column(db.String(255), unique=True, nullable=False, index=True)
    full_name = db.Column(db.String(FULL_NAME_MAX_LENGTH), nullable=False)
    password_hash = db.Column(db.String(255), nullable=False)
    profile_pic = db.Column(db.String(255), nullable=False, default="default.png")
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    # Updated whenever a user's last Socket.IO connection drops (see
    # handle_disconnect). NULL means "never seen online yet" (e.g. a brand
    # new account) rather than "was seen at time zero".
    last_seen = db.Column(db.DateTime, nullable=True)

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

    def to_dict(self, include_email=False, include_presence=False):
        data = {
            "id": self.id,
            "username": self.username,
            "full_name": self.full_name,
            "profile_pic": self.profile_pic,
        }
        # Email is only ever included for the account's own owner (e.g. the
        # /api/me response) — other users don't need to see each other's
        # email addresses just to render the chat list.
        if include_email:
            data["email"] = self.email
        if include_presence:
            online = is_user_online(self.id)
            data["online"] = online
            # Don't report a stale last_seen while the user is currently
            # online — the client should just show "Online" in that case.
            data["last_seen"] = None if online else (
                self.last_seen.isoformat() if self.last_seen else None
            )
        return data

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


def _ensure_schema():
    """db.create_all() only creates tables that don't exist yet — it never
    alters an existing table. Anyone upgrading from a previous version of
    this app (pre-email/full_name) would already have a users table without
    those columns, and every request would then crash with 'no such column'.
    This adds any missing columns in place so existing databases (and their
    existing accounts) keep working after the upgrade, instead of requiring
    everyone to delete their database.
    """
    from sqlalchemy import inspect, text

    inspector = inspect(db.engine)
    if "users" not in inspector.get_table_names():
        return  # fresh database — create_all() above already built it fully

    existing_columns = {col["name"] for col in inspector.get_columns("users")}

    if "email" not in existing_columns:
        logger.info("Migrating users table: adding 'email' column")
        with db.engine.begin() as conn:
            conn.execute(text("ALTER TABLE users ADD COLUMN email VARCHAR(255)"))
            # Backfill existing rows with a unique placeholder so the column
            # can be made functionally unique going forward without breaking
            # old accounts; they'll want to set a real email via their profile.
            conn.execute(text(
                "UPDATE users SET email = username || '@placeholder.local' "
                "WHERE email IS NULL"
            ))

    if "full_name" not in existing_columns:
        logger.info("Migrating users table: adding 'full_name' column")
        with db.engine.begin() as conn:
            conn.execute(text("ALTER TABLE users ADD COLUMN full_name VARCHAR(60)"))
            conn.execute(text("UPDATE users SET full_name = username WHERE full_name IS NULL"))

    if "last_seen" not in existing_columns:
        logger.info("Migrating users table: adding 'last_seen' column")
        with db.engine.begin() as conn:
            conn.execute(text("ALTER TABLE users ADD COLUMN last_seen DATETIME"))


with app.app_context():
    db.create_all()
    _ensure_schema()


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


def validate_email(email):
    if not email or len(email) > 255 or not EMAIL_PATTERN.match(email):
        return "Please enter a valid email address."
    return None


def validate_full_name(full_name):
    if not full_name or not (FULL_NAME_MIN_LENGTH <= len(full_name) <= FULL_NAME_MAX_LENGTH):
        return f"Name must be between {FULL_NAME_MIN_LENGTH} and {FULL_NAME_MAX_LENGTH} characters."
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
# Presence tracking ("online" / "last seen")
# -------------------------------------------------------------------
# Counts open Socket.IO connections per user id, so a user with multiple
# tabs/devices open only goes "offline" once every one of them disconnects.
# Kept in plain memory rather than the database — this app intentionally
# runs with a single gunicorn worker (`-w 1`, see Procfile), so there's only
# ever one process for this state to live in, and it doesn't need to survive
# a restart the way last_seen (persisted) does.
_online_counts = defaultdict(int)


def is_user_online(user_id):
    return _online_counts.get(user_id, 0) > 0


def mark_user_connected(user_id):
    """Returns True if this is the user's first open connection (i.e. they
    just transitioned from offline to online)."""
    was_offline = _online_counts[user_id] == 0
    _online_counts[user_id] += 1
    return was_offline


def mark_user_disconnected(user_id):
    """Returns True if this was the user's last open connection (i.e. they
    just transitioned from online to offline)."""
    if _online_counts.get(user_id, 0) <= 0:
        return False
    _online_counts[user_id] -= 1
    if _online_counts[user_id] <= 0:
        _online_counts.pop(user_id, None)
        return True
    return False


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
    # The sidebar only ever shows people the current user has actually
    # exchanged messages with — it is NOT a directory of every registered
    # account. Discovering anyone else happens through the search box
    # (/api/search-users), which starts a fresh conversation on demand.
    conversation_partner_ids = {
        row[0] for row in
        db.session.query(Message.recipient_id).filter(Message.sender_id == current_user.id)
        .union(
            db.session.query(Message.sender_id).filter(Message.recipient_id == current_user.id)
        ).all()
    }

    # Most recent message time with each partner, so the list can be sorted
    # like a normal messaging app (latest conversation first) rather than
    # alphabetically.
    last_message_at = {}
    if conversation_partner_ids:
        history = (
            Message.query.filter(
                db.or_(
                    db.and_(Message.sender_id == current_user.id, Message.recipient_id.in_(conversation_partner_ids)),
                    db.and_(Message.recipient_id == current_user.id, Message.sender_id.in_(conversation_partner_ids)),
                )
            )
            .order_by(Message.timestamp.asc())
            .all()
        )
        for m in history:
            other_id = m.recipient_id if m.sender_id == current_user.id else m.sender_id
            last_message_at[other_id] = m.timestamp  # last write wins since we walked ascending

    other_users = (
        User.query.filter(User.id.in_(conversation_partner_ids)).all()
        if conversation_partner_ids else []
    )
    other_users.sort(key=lambda u: last_message_at.get(u.id, datetime.min), reverse=True)

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
            "full_name": u.full_name,
            "profile_pic": u.profile_pic,
            "unread_count": unread_counts.get(u.id, 0),
            "online": is_user_online(u.id),
            "last_seen": (None if is_user_online(u.id) else (u.last_seen.isoformat() if u.last_seen else None)),
        }
        for u in other_users
    ]

    return render_template(
        "chat.html",
        current_user_data=current_user.to_dict(include_email=True),
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
    email = (data.get("email") or "").strip().lower()
    full_name = (data.get("full_name") or "").strip()
    password = data.get("password") or ""

    username_error = validate_username(username)
    if username_error:
        return jsonify({"error": username_error}), 400

    email_error = validate_email(email)
    if email_error:
        return jsonify({"error": email_error}), 400

    full_name_error = validate_full_name(full_name)
    if full_name_error:
        return jsonify({"error": full_name_error}), 400

    password_error = validate_password(password)
    if password_error:
        return jsonify({"error": password_error}), 400

    # Case-insensitive uniqueness checks avoid "Alice" vs "alice" (and
    # "A@x.com" vs "a@x.com") collisions.
    if User.query.filter(func.lower(User.username) == username.lower()).first():
        return jsonify({"error": "Username already taken."}), 409

    if User.query.filter(func.lower(User.email) == email).first():
        return jsonify({"error": "An account with that email already exists."}), 409

    try:
        user = User(username=username, email=email, full_name=full_name)
        user.set_password(password)
        db.session.add(user)
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to create user")
        return jsonify({"error": "Could not create account. Please try again."}), 500

    login_user(user)
    logger.info("New user registered: %s", user.username)
    return jsonify({"message": "Registered successfully.", "user": user.to_dict(include_email=True)}), 201


@app.route("/api/login", methods=["POST"])
@limiter.limit("10 per minute")
def login():
    data = request.get_json(silent=True) or request.form

    identifier = (data.get("username") or "").strip()
    password = data.get("password") or ""

    # Accept either a username or an email address in the same field, so
    # people who forget which one they registered with can still log in.
    # Generic error message on both bad-identifier and bad-password paths,
    # so the response can't be used to enumerate valid accounts.
    user = User.query.filter(
        db.or_(
            func.lower(User.username) == identifier.lower(),
            func.lower(User.email) == identifier.lower(),
        )
    ).first()
    if not user or not user.check_password(password):
        return jsonify({"error": "Invalid username/email or password."}), 401

    login_user(user)
    return jsonify({"message": "Logged in successfully.", "user": user.to_dict(include_email=True)}), 200


@app.route("/api/logout", methods=["POST"])
@login_required
def logout():
    logout_user()
    return jsonify({"message": "Logged out successfully."}), 200


@app.route("/api/me", methods=["GET"])
@login_required
def me():
    return jsonify({"user": current_user.to_dict(include_email=True)}), 200


@app.route("/api/profile", methods=["POST"])
@login_required
@limiter.limit("20 per hour")
def update_profile():
    """Updates the current user's display name (full_name). Username,
    email, and password are intentionally not editable here."""
    data = request.get_json(silent=True) or request.form

    full_name = (data.get("full_name") or "").strip()
    full_name_error = validate_full_name(full_name)
    if full_name_error:
        return jsonify({"error": full_name_error}), 400

    current_user.full_name = full_name

    try:
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to update profile")
        return jsonify({"error": "Could not update profile. Please try again."}), 500

    return jsonify({
        "message": "Profile updated.",
        "user": current_user.to_dict(include_email=True),
    }), 200


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


SEARCH_RESULTS_LIMIT = 20


@app.route("/api/search-users", methods=["GET"])
@login_required
@limiter.limit("60 per minute")
def search_users():
    """Looks up registered accounts by username or display name. This is the
    ONLY way to discover users you haven't already messaged — the sidebar
    itself only ever lists existing conversations (see index() above)."""
    query = (request.args.get("q") or "").strip()
    if not query:
        return jsonify({"users": []}), 200

    like_pattern = f"%{query.lower()}%"
    matches = (
        User.query.filter(
            User.id != current_user.id,
            db.or_(
                func.lower(User.username).like(like_pattern),
                func.lower(User.full_name).like(like_pattern),
            ),
        )
        .order_by(User.full_name.asc())
        .limit(SEARCH_RESULTS_LIMIT)
        .all()
    )

    return jsonify({
        "users": [u.to_dict(include_presence=True) for u in matches]
    }), 200


@app.route("/api/users/<int:user_id>", methods=["GET"])
@login_required
def get_user(user_id):
    """Fetches a single user's public profile + presence — used when opening
    a conversation with someone found via search, who isn't in the sidebar
    (and thus its embedded data) yet."""
    user = User.query.get(user_id)
    if not user:
        return jsonify({"error": "User not found."}), 404
    return jsonify({"user": user.to_dict(include_presence=True)}), 200


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
        # Reject unauthenticated socket connections, but with a reason string so
        # the client's connect_error handler can actually tell what happened
        # instead of just seeing a generic disconnect.
        logger.warning("Rejected unauthenticated Socket.IO connection attempt")
        raise ConnectionRefusedError("not_authenticated")

    join_room(get_room_name(current_user.id))
    emit("connection_ack", {"message": f"Connected as {current_user.username}"})

    if mark_user_connected(current_user.id):
        # First open connection for this user (not just another tab) — let
        # everyone currently connected know they're online now.
        socketio.emit("presence_update", {
            "user_id": current_user.id,
            "online": True,
            "last_seen": None,
        })


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
    if not current_user.is_authenticated:
        return

    logger.info("%s disconnected", current_user.username)

    if mark_user_disconnected(current_user.id):
        # That was this user's last open tab/device — they're actually
        # offline now, so stamp last_seen and tell everyone else.
        now = datetime.utcnow()
        try:
            User.query.filter_by(id=current_user.id).update({"last_seen": now})
            db.session.commit()
        except Exception:
            db.session.rollback()
            logger.exception("Failed to update last_seen on disconnect")

        socketio.emit("presence_update", {
            "user_id": current_user.id,
            "online": False,
            "last_seen": now.isoformat(),
        })


# -------------------------------------------------------------------
# Entry Point
# -------------------------------------------------------------------
if __name__ == "__main__":
    socketio.run(app, debug=not IS_PRODUCTION, host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
