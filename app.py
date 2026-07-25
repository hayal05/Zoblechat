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
from datetime import datetime, timedelta


def to_iso_utc(dt):
    """Serialize a naive UTC datetime (as produced by datetime.utcnow(), which
    is what every timestamp in this app is stored as) into an ISO string that
    explicitly marks itself as UTC.

    Without this, `dt.isoformat()` alone produces a string with no timezone
    designator (e.g. "2026-07-24T09:15:30"), and JavaScript's `new Date(...)`
    parses timezone-less date-time strings as *local* time, not UTC. That
    silently shifts every timestamp by the browser's UTC offset — e.g. a
    user in UTC+3 would see "last seen" times that are 3 hours further in
    the past than they really are, even for someone who just went offline
    a moment ago.
    """
    return dt.isoformat() + "Z" if dt else None

from dotenv import load_dotenv
from flask import Flask, request, jsonify, redirect, url_for, render_template, make_response
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
# Chat photo attachments live in their own subfolder so they never collide
# with profile-picture filenames and can be reasoned about (cleaned up,
# backed up, etc.) independently of avatars.
CHAT_PHOTOS_FOLDER = os.path.join(UPLOAD_FOLDER, "chat_photos")
# Stories live in their own subfolder for the same reason chat photos do —
# independent filename namespace, independent cleanup (expired stories get
# their files deleted; chat photos never do).
STORY_PHOTOS_FOLDER = os.path.join(UPLOAD_FOLDER, "story_photos")

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
# Accepts an optional leading "+" followed by 7-15 digits (E.164-ish range).
# Registration/login normalize phone input by stripping spaces, hyphens,
# and parentheses before this pattern is checked, so "(555) 123-4567" and
# "555-123-4567" both validate the same as "5551234567".
PHONE_PATTERN = re.compile(r"^\+?[0-9]{7,15}$")
PASSWORD_MIN_LENGTH = 8
MESSAGE_MAX_LENGTH = 4000
CHAT_PHOTO_MAX_BYTES = 5 * 1024 * 1024   # mirrors MAX_CONTENT_LENGTH (Flask enforces this globally too)
FULL_NAME_MIN_LENGTH = 1
FULL_NAME_MAX_LENGTH = 60
# Upper bound on how many phone numbers a single "find contacts" sync can
# submit. A real address book rarely exceeds a few hundred entries; this
# just keeps one request from being (ab)used to probe the whole phone
# number keyspace in bulk.
CONTACTS_MATCH_MAX = 1000
# Stories: photo-only posts that disappear after a fixed lifetime, with a
# single reaction (no comments, no video).
STORY_EXPIRY_HOURS = 72
# How often the background sweep removes expired stories (and their image
# files) from disk. Queries already filter out expired stories on every
# request regardless, so this is purely about not letting old files pile up.
STORY_CLEANUP_INTERVAL_SECONDS = 15 * 60
# Sane ceiling so one account can't spam an unbounded number of simultaneous
# active stories.
MAX_ACTIVE_STORIES_PER_USER = 20
# Verification badge: how many *consecutive* calendar days a user needs to
# have been online (at least once each day) before the account is
# auto-verified. See record_daily_activity() for the streak bookkeeping.
VERIFICATION_STREAK_DAYS = 3
# Message reaction stickers: a fixed set rather than free-form emoji input,
# so the reactions bar under a bubble stays a small, recognizable row
# instead of turning into an open-ended emoji picker. One reaction per user
# per message — see MessageReaction for the toggle/swap semantics.
ALLOWED_REACTION_EMOJIS = {"❤️", "😂", "😮", "😢", "👍", "🙏"}

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
os.makedirs(CHAT_PHOTOS_FOLDER, exist_ok=True)
os.makedirs(STORY_PHOTOS_FOLDER, exist_ok=True)

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
    # A user registers with EITHER an email OR a phone number (not necessarily
    # both), so both are nullable at the DB level — enforcing "at least one of
    # the two is present" is done in the /api/register validation instead of
    # a DB-level constraint, since SQLite's ALTER TABLE support makes adding a
    # CHECK constraint to an existing table impractical for the migration below.
    email = db.Column(db.String(255), unique=True, nullable=True, index=True)
    phone = db.Column(db.String(20), unique=True, nullable=True, index=True)
    full_name = db.Column(db.String(FULL_NAME_MAX_LENGTH), nullable=False)
    password_hash = db.Column(db.String(255), nullable=False)
    profile_pic = db.Column(db.String(255), nullable=False, default="default.png")
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    # Updated whenever a user's last Socket.IO connection drops (see
    # handle_disconnect). NULL means "never seen online yet" (e.g. a brand
    # new account) rather than "was seen at time zero".
    last_seen = db.Column(db.DateTime, nullable=True)

    # -- Verification badge / admin -----------------------------------
    # is_admin: only ever true for the very first account ever created
    # (see /api/register) — there's no promotion path beyond that today.
    is_admin = db.Column(db.Boolean, nullable=False, default=False)
    # is_verified: true once either (a) the account is the admin account,
    # auto-granted at registration, or (b) the account has been online at
    # least once on each of VERIFICATION_STREAK_DAYS consecutive calendar
    # days (see record_daily_activity()).
    is_verified = db.Column(db.Boolean, nullable=False, default=False)
    verified_at = db.Column(db.DateTime, nullable=True)
    # activity_streak / last_active_date: bookkeeping for the consecutive-day
    # check above. last_active_date is a DATE (not datetime) since the streak
    # is about calendar days, not a rolling 24h window.
    activity_streak = db.Column(db.Integer, nullable=False, default=0)
    last_active_date = db.Column(db.Date, nullable=True)

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
            # Badge flags are not sensitive — shown next to a user's name for
            # anyone who can see that name at all, same as WhatsApp/Twitter
            # verification checkmarks.
            "is_verified": bool(self.is_verified),
            "is_admin": bool(self.is_admin),
        }
        # Email/phone are only ever included for the account's own owner (e.g.
        # the /api/me response) — other users don't need to see each other's
        # contact details just to render the chat list.
        if include_email:
            data["email"] = self.email
            data["phone"] = self.phone
        if include_presence:
            online = is_user_online(self.id)
            data["online"] = online
            # Don't report a stale last_seen while the user is currently
            # online — the client should just show "Online" in that case.
            data["last_seen"] = None if online else to_iso_utc(self.last_seen)
        return data

    def __repr__(self):
        return f"<User {self.username}>"


class Message(db.Model):
    __tablename__ = "messages"

    id = db.Column(db.Integer, primary_key=True)
    sender_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    recipient_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    # For text messages this holds the message body. For photo messages it's
    # kept as a short human-readable label ("Photo") so old clients (or the
    # sidebar preview) still have *something* sensible to show, while the
    # actual attachment lives in image_path.
    content = db.Column(db.String(MESSAGE_MAX_LENGTH), nullable=False)
    # "text" or "image" — lets both the API and the client tell the two
    # kinds of messages apart without guessing from content.
    message_type = db.Column(db.String(10), nullable=False, default="text")
    # Filename only (relative to static/uploads/chat_photos/), mirroring how
    # User.profile_pic stores just a filename rather than a full path.
    image_path = db.Column(db.String(255), nullable=True)
    timestamp = db.Column(db.DateTime, default=datetime.utcnow, index=True)
    is_read = db.Column(db.Boolean, default=False, nullable=False)

    def to_dict(self):
        return {
            "id": self.id,
            "sender_id": self.sender_id,
            "recipient_id": self.recipient_id,
            "content": self.content,
            "message_type": self.message_type,
            "image_url": (
                url_for("static", filename=f"uploads/chat_photos/{self.image_path}")
                if self.image_path else None
            ),
            "timestamp": to_iso_utc(self.timestamp),
            "is_read": self.is_read,
            # Raw per-user reactions rather than pre-aggregated counts, so the
            # client can compute both "count per emoji" and "did *I* react
            # with this one" (for highlighting) from a single field, for
            # whichever of the two participants is viewing it.
            "reactions": [
                {"user_id": r.user_id, "emoji": r.emoji}
                for r in self.reactions.order_by(MessageReaction.created_at.asc())
            ],
        }

    def __repr__(self):
        return f"<Message {self.id} from {self.sender_id} to {self.recipient_id}>"


class Story(db.Model):
    """A single photo-only story post. Always has a hard expires_at set at
    creation time (created_at + STORY_EXPIRY_HOURS) — there is no separate
    "is_active" flag, expiry is purely time-based so it can never drift out
    of sync with reality."""
    __tablename__ = "stories"

    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    # Filename only (relative to static/uploads/story_photos/), same
    # storage convention as Message.image_path and User.profile_pic.
    image_path = db.Column(db.String(255), nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False, index=True)
    expires_at = db.Column(db.DateTime, nullable=False, index=True)

    user = db.relationship(
        "User", backref=db.backref("stories", lazy="dynamic", cascade="all, delete-orphan")
    )

    def is_expired(self):
        return datetime.utcnow() >= self.expires_at

    def to_dict(self, viewer_id=None):
        reacted_by_me = (
            viewer_id is not None
            and self.reactions.filter_by(user_id=viewer_id).first() is not None
        )
        return {
            "id": self.id,
            "user_id": self.user_id,
            "image_url": url_for("static", filename=f"uploads/story_photos/{self.image_path}"),
            "created_at": to_iso_utc(self.created_at),
            "expires_at": to_iso_utc(self.expires_at),
            "reaction_count": self.reactions.count(),
            "reacted_by_me": reacted_by_me,
        }

    def __repr__(self):
        return f"<Story {self.id} by {self.user_id}>"


class StoryReaction(db.Model):
    """The only reaction a story can get: one purple-heart "love" per user
    per story (toggleable — sending it again removes it). Stories have no
    comment feature at all, so there is nothing else to model here."""
    __tablename__ = "story_reactions"

    id = db.Column(db.Integer, primary_key=True)
    story_id = db.Column(db.Integer, db.ForeignKey("stories.id"), nullable=False, index=True)
    user_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)

    story = db.relationship(
        "Story", backref=db.backref("reactions", lazy="dynamic", cascade="all, delete-orphan")
    )
    reactor = db.relationship("User")

    __table_args__ = (
        db.UniqueConstraint("story_id", "user_id", name="uq_story_reaction_user"),
    )

    def __repr__(self):
        return f"<StoryReaction story={self.story_id} user={self.user_id}>"


class MessageReaction(db.Model):
    """A single reaction sticker from one user on one chat message, picked
    from ALLOWED_REACTION_EMOJIS. Each user may have at most one reaction
    per message: reacting again with the same emoji removes it, reacting
    with a different one swaps it in place. That keeps the reactions bar
    under a bubble a short, fixed row instead of growing unbounded as one
    person taps around — same one-per-user idea as StoryReaction, just not
    limited to a single emoji since messages support a small sticker set."""
    __tablename__ = "message_reactions"

    id = db.Column(db.Integer, primary_key=True)
    message_id = db.Column(db.Integer, db.ForeignKey("messages.id"), nullable=False, index=True)
    user_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    emoji = db.Column(db.String(8), nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)

    message = db.relationship(
        "Message", backref=db.backref("reactions", lazy="dynamic", cascade="all, delete-orphan")
    )
    reactor = db.relationship("User")

    __table_args__ = (
        db.UniqueConstraint("message_id", "user_id", name="uq_message_reaction_user"),
    )

    def __repr__(self):
        return f"<MessageReaction message={self.message_id} user={self.user_id} emoji={self.emoji}>"


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

    if "phone" not in existing_columns:
        logger.info("Migrating users table: adding 'phone' column")
        with db.engine.begin() as conn:
            conn.execute(text("ALTER TABLE users ADD COLUMN phone VARCHAR(20)"))
            # SQLite has no easy way to add a UNIQUE constraint to an existing
            # column via ALTER TABLE, but a plain index is enough to keep phone
            # lookups (login/registration uniqueness checks) fast; uniqueness
            # itself is already enforced in application code at registration.
            conn.execute(text(
                "CREATE UNIQUE INDEX IF NOT EXISTS ix_users_phone_unique "
                "ON users (phone) WHERE phone IS NOT NULL"
            ))

    if "is_admin" not in existing_columns:
        logger.info("Migrating users table: adding 'is_admin' column")
        with db.engine.begin() as conn:
            conn.execute(text("ALTER TABLE users ADD COLUMN is_admin BOOLEAN DEFAULT 0 NOT NULL"))
            # The very first account ever created (lowest id) becomes admin +
            # verified retroactively, same as a fresh registration would get
            # today — existing deployments shouldn't lose that guarantee just
            # because this column didn't exist when their admin signed up.
            conn.execute(text(
                "UPDATE users SET is_admin = 1 WHERE id = (SELECT MIN(id) FROM users)"
            ))

    if "is_verified" not in existing_columns:
        logger.info("Migrating users table: adding 'is_verified' column")
        with db.engine.begin() as conn:
            conn.execute(text("ALTER TABLE users ADD COLUMN is_verified BOOLEAN DEFAULT 0 NOT NULL"))
            conn.execute(text(
                "UPDATE users SET is_verified = 1 WHERE id = (SELECT MIN(id) FROM users)"
            ))

    if "verified_at" not in existing_columns:
        logger.info("Migrating users table: adding 'verified_at' column")
        with db.engine.begin() as conn:
            conn.execute(text("ALTER TABLE users ADD COLUMN verified_at DATETIME"))
            conn.execute(text(
                "UPDATE users SET verified_at = created_at WHERE id = (SELECT MIN(id) FROM users)"
            ))

    if "activity_streak" not in existing_columns:
        logger.info("Migrating users table: adding 'activity_streak' column")
        with db.engine.begin() as conn:
            conn.execute(text("ALTER TABLE users ADD COLUMN activity_streak INTEGER DEFAULT 0 NOT NULL"))

    if "last_active_date" not in existing_columns:
        logger.info("Migrating users table: adding 'last_active_date' column")
        with db.engine.begin() as conn:
            conn.execute(text("ALTER TABLE users ADD COLUMN last_active_date DATE"))

    if "messages" in inspector.get_table_names():
        existing_message_columns = {col["name"] for col in inspector.get_columns("messages")}

        if "message_type" not in existing_message_columns:
            logger.info("Migrating messages table: adding 'message_type' column")
            with db.engine.begin() as conn:
                conn.execute(text("ALTER TABLE messages ADD COLUMN message_type VARCHAR(10)"))
                conn.execute(text(
                    "UPDATE messages SET message_type = 'text' WHERE message_type IS NULL"
                ))

        if "image_path" not in existing_message_columns:
            logger.info("Migrating messages table: adding 'image_path' column")
            with db.engine.begin() as conn:
                conn.execute(text("ALTER TABLE messages ADD COLUMN image_path VARCHAR(255)"))


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


def normalize_phone(phone):
    """Strips spaces, hyphens, and parentheses so "(555) 123-4567" and
    "555-123-4567" are treated as the same number as "5551234567"."""
    return re.sub(r"[\s\-()]", "", phone or "")


def validate_phone(phone):
    if not phone or not PHONE_PATTERN.match(phone):
        return "Please enter a valid phone number."
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


def get_conversation_partner_ids(user_id):
    """Everyone this user has ever exchanged a message with, in either
    direction. Shared by the sidebar (index()) and the stories feature,
    since stories reuse the same "people you've actually talked to" audience
    as the chat list rather than being visible to every registered account."""
    return {
        row[0] for row in
        db.session.query(Message.recipient_id).filter(Message.sender_id == user_id)
        .union(
            db.session.query(Message.sender_id).filter(Message.recipient_id == user_id)
        ).all()
    }


def purge_expired_stories():
    """Deletes story rows (and their reactions, via cascade) plus the
    underlying image files once expires_at has passed. Story queries already
    filter on expires_at themselves, so nobody can ever *see* an expired
    story regardless of this — this function is only about not letting the
    image files and rows pile up on disk/in the DB after they're no longer
    reachable. Called both lazily (at the top of the story routes) and on a
    timer (_story_cleanup_loop) so cleanup happens even during quiet periods
    with no traffic."""
    expired = Story.query.filter(Story.expires_at <= datetime.utcnow()).all()
    if not expired:
        return

    for story in expired:
        path = os.path.join(STORY_PHOTOS_FOLDER, story.image_path)
        try:
            if os.path.exists(path):
                os.remove(path)
        except OSError:
            logger.warning("Could not remove expired story image: %s", story.image_path)
        db.session.delete(story)

    try:
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to purge expired stories")


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
# Auto-verification badge
# -------------------------------------------------------------------
# A user earns the verification badge by being online at least once on each
# of VERIFICATION_STREAK_DAYS *consecutive* calendar days. "Online" here
# means "opened a live Socket.IO connection" (i.e. actually had the app
# open), so this is called from handle_connect below — never from a plain
# page load/HTTP request, which wouldn't prove the tab was actually active.
def record_daily_activity(user):
    if user.is_verified:
        return  # already verified (or the admin account) — nothing to track

    today = datetime.utcnow().date()

    if user.last_active_date == today:
        return  # already counted today; connecting again (another tab,
        # a reconnect) shouldn't advance the streak twice in one day

    if user.last_active_date == today - timedelta(days=1):
        # Was active yesterday too — streak continues.
        user.activity_streak += 1
    else:
        # Either the very first time we've seen this user online, or there
        # was a gap of a day or more since they were last online — either
        # way the streak (re)starts at 1 today.
        user.activity_streak = 1

    user.last_active_date = today

    if user.activity_streak >= VERIFICATION_STREAK_DAYS:
        user.is_verified = True
        user.verified_at = datetime.utcnow()
        logger.info(
            "User %s auto-verified after %d consecutive active days",
            user.username, user.activity_streak,
        )

    try:
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to record daily activity for user %s", user.id)


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
    conversation_partner_ids = get_conversation_partner_ids(current_user.id)

    # Most recent message with each partner, so the list can be sorted like a
    # normal messaging app (latest conversation first) and can show a preview
    # snippet of that message before the conversation is opened.
    last_message_at = {}
    last_message_by_partner = {}
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
            last_message_by_partner[other_id] = m

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

    def preview_for(u):
        m = last_message_by_partner.get(u.id)
        if not m:
            return None
        return {
            # "Photo" already comes through in content for image messages
            # (see Message.content), so the snippet is sensible either way.
            "text": m.content,
            "message_type": m.message_type,
            "from_me": m.sender_id == current_user.id,
            "is_read": m.is_read,
            "timestamp": to_iso_utc(m.timestamp),
        }

    users_payload = [
        {
            "id": u.id,
            "username": u.username,
            "full_name": u.full_name,
            "profile_pic": u.profile_pic,
            "unread_count": unread_counts.get(u.id, 0),
            "online": is_user_online(u.id),
            "last_seen": (None if is_user_online(u.id) else to_iso_utc(u.last_seen)),
            "last_message": preview_for(u),
            "is_verified": bool(u.is_verified),
            "is_admin": bool(u.is_admin),
        }
        for u in other_users
    ]

    return _no_store(render_template(
        "chat.html",
        current_user_data=current_user.to_dict(include_email=True),
        users=users_payload,
    ))


def _no_store(response):
    """Stop the browser from serving this page out of its back/forward cache
    (bfcache) or disk cache. Without this, pressing the phone's hardware
    back button can show a *stale* snapshot of a previous page (e.g. the
    register/login screen exactly as it looked before the user logged in)
    instead of asking the server again — which makes it look like the app
    logged the user out and dumped them on the registration page, even
    though the session was never touched. Forcing revalidation means the
    login_page/register_page routes' `if current_user.is_authenticated`
    check always re-runs and bounces a logged-in user straight back to
    the chat, and index() always re-runs @login_required correctly too."""
    response = make_response(response)
    response.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    response.headers["Pragma"] = "no-cache"
    response.headers["Expires"] = "0"
    return response


@app.route("/login")
def login_page():
    if current_user.is_authenticated:
        return redirect(url_for("index"))
    return _no_store(render_template("login.html"))


@app.route("/register")
def register_page():
    if current_user.is_authenticated:
        return redirect(url_for("index"))
    return _no_store(render_template("register.html"))


# -------------------------------------------------------------------
# Authentication API Routes (JSON)
# -------------------------------------------------------------------
@app.route("/api/register", methods=["POST"])
@limiter.limit("10 per minute")
def register():
    data = request.get_json(silent=True) or request.form

    username = (data.get("username") or "").strip()
    full_name = (data.get("full_name") or "").strip()
    password = data.get("password") or ""

    # The client tells us which contact method it's collecting so we know
    # which single field to validate/store — but we don't actually trust
    # that label on its own; whichever of email/phone was actually filled
    # in wins, and it's an error if both or neither were provided.
    contact_method = (data.get("contact_method") or "").strip().lower()
    email_raw = (data.get("email") or "").strip().lower()
    phone_raw = normalize_phone(data.get("phone") or "")

    if contact_method not in ("email", "phone"):
        # Infer from whichever field is actually filled in, so older clients
        # that only ever sent "email" keep working unchanged.
        contact_method = "phone" if phone_raw and not email_raw else "email"

    if email_raw and phone_raw:
        return jsonify({"error": "Please register with either an email or a phone number, not both."}), 400

    email = None
    phone = None

    if contact_method == "phone":
        phone_error = validate_phone(phone_raw)
        if phone_error:
            return jsonify({"error": phone_error}), 400
        phone = phone_raw
    else:
        email_error = validate_email(email_raw)
        if email_error:
            return jsonify({"error": email_error}), 400
        email = email_raw

    username_error = validate_username(username)
    if username_error:
        return jsonify({"error": username_error}), 400

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

    if email and User.query.filter(func.lower(User.email) == email).first():
        return jsonify({"error": "An account with that email already exists."}), 409

    if phone and User.query.filter(User.phone == phone).first():
        return jsonify({"error": "An account with that phone number already exists."}), 409

    # The very first account ever created on this deployment is auto-verified
    # and promoted to admin immediately. In the extremely unlikely case of two
    # registration requests overlapping in the same instant (this app runs a
    # single worker, so that would take two concurrent requests racing before
    # either commits), both could observe an empty table and both could end
    # up admin — an acceptable edge case here given how rare a truly
    # simultaneous "first ever" signup is, but worth knowing about if this
    # app is ever scaled to multiple workers/processes.
    is_first_account_ever = User.query.count() == 0

    try:
        # No OTP/verification step — the account is created and usable
        # immediately from the email/phone number as entered.
        user = User(username=username, email=email, phone=phone, full_name=full_name)
        user.set_password(password)
        if is_first_account_ever:
            user.is_admin = True
            user.is_verified = True
            user.verified_at = datetime.utcnow()
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
    identifier_phone = normalize_phone(identifier)
    password = data.get("password") or ""

    # Accept a username, email address, or phone number in the same field, so
    # people who forget which one they registered with can still log in.
    # Generic error message on both bad-identifier and bad-password paths,
    # so the response can't be used to enumerate valid accounts.
    user = User.query.filter(
        db.or_(
            func.lower(User.username) == identifier.lower(),
            func.lower(User.email) == identifier.lower(),
            User.phone == identifier_phone,
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


@app.route("/api/contacts/match", methods=["POST"])
@login_required
@limiter.limit("15 per hour")
def match_contacts():
    """Given a batch of phone numbers pulled from the device's address book
    (via the browser's Contact Picker, on the client side), returns whichever
    of them belong to a registered Zoble account — this is what powers "find
    people from your phone contacts", the same way Telegram/WhatsApp cross-
    reference your address book against their user directory.

    Only numbers that already match a real account come back. Nothing about
    the other phone numbers is created, stored, or otherwise persisted
    server-side — each submitted number is only ever compared in-memory for
    the duration of this request, never logged, and the response never
    reveals *which* submitted number matched a given account (just the
    account itself), since the client already knows which of its own
    contacts it sent.
    """
    data = request.get_json(silent=True) or {}
    phones = data.get("phones")

    if not isinstance(phones, list):
        return jsonify({"error": "'phones' must be a list of phone number strings."}), 400

    if len(phones) > CONTACTS_MATCH_MAX:
        return jsonify({
            "error": f"Too many contacts in one request (max {CONTACTS_MATCH_MAX})."
        }), 400

    # Normalize the same way registration/login do, so "(555) 123-4567" in
    # someone's address book matches the "5551234567" they registered with.
    # Non-strings and anything that still fails the phone pattern after
    # normalizing are silently dropped rather than erroring the whole
    # request — a real address book is full of entries with no phone number,
    # extensions, or garbage formatting.
    normalized = set()
    for raw in phones:
        if not isinstance(raw, str):
            continue
        candidate = normalize_phone(raw)
        if PHONE_PATTERN.match(candidate):
            normalized.add(candidate)

    matches = []
    if normalized:
        matches = (
            User.query.filter(
                User.id != current_user.id,
                User.phone.in_(normalized),
            )
            .order_by(User.full_name.asc())
            .all()
        )

    return jsonify({
        "matches": [u.to_dict(include_presence=True) for u in matches],
        "checked": len(normalized),
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


@app.route("/api/messages/<int:recipient_id>/photo", methods=["POST"])
@login_required
@limiter.limit("30 per hour")
def send_photo_message(recipient_id):
    """Uploads an image and sends it as a chat message to recipient_id, the
    same way handle_send_message() does for text — it persists a Message
    row and broadcasts it over Socket.IO to both parties' rooms, so every
    open tab/device on both ends updates instantly without a page reload.
    """
    if recipient_id == current_user.id:
        return jsonify({"error": "You cannot send a photo to yourself."}), 400

    recipient = User.query.get(recipient_id)
    if not recipient:
        return jsonify({"error": "Recipient does not exist."}), 404

    if "file" not in request.files:
        return jsonify({"error": "No file part in the request."}), 400

    file = request.files["file"]
    if file.filename == "":
        return jsonify({"error": "No file selected."}), 400

    if not allowed_file(file.filename):
        return jsonify({"error": "Unsupported file type. Use PNG, JPG, GIF, or WEBP."}), 400

    original_name = secure_filename(file.filename)
    ext = original_name.rsplit(".", 1)[1].lower()
    # Prefixing with sender id + a uuid (same scheme as profile pictures)
    # means filenames can never collide or be guessed/enumerated.
    unique_name = f"{current_user.id}_{uuid.uuid4().hex}.{ext}"
    filepath = os.path.join(CHAT_PHOTOS_FOLDER, unique_name)

    try:
        file.save(filepath)
    except OSError:
        logger.exception("Failed to save uploaded chat photo")
        return jsonify({"error": "Could not save the uploaded file."}), 500

    # Same real-image + decompression-bomb guard used for profile pictures —
    # an extension check alone can be spoofed.
    if not verify_is_real_image(filepath):
        try:
            os.remove(filepath)
        except OSError:
            pass
        return jsonify({"error": "The uploaded file is not a valid image."}), 400

    try:
        message = Message(
            sender_id=current_user.id,
            recipient_id=recipient_id,
            content="Photo",
            message_type="image",
            image_path=unique_name,
            is_read=False,
        )
        db.session.add(message)
        db.session.commit()
    except Exception:
        db.session.rollback()
        try:
            os.remove(filepath)
        except OSError:
            pass
        logger.exception("Failed to save photo message")
        return jsonify({"error": "Could not send photo. Please try again."}), 500

    payload = message.to_dict()
    payload["sender_username"] = current_user.username
    payload["sender_profile_pic"] = current_user.profile_pic

    # Broadcast exactly like a text message so both sides' open tabs update
    # live — the client's existing "receive_message" handler already knows
    # how to render either kind, distinguishing on message_type.
    socketio.emit("receive_message", payload, room=get_room_name(recipient_id))
    socketio.emit("receive_message", payload, room=get_room_name(current_user.id))

    return jsonify({"message": "Photo sent.", "data": payload}), 201


@app.route("/api/messages/<int:message_id>/react", methods=["POST"])
@login_required
@limiter.limit("300 per hour")
def react_to_message(message_id):
    """
    Expected payload:
    {
        "emoji": <one of ALLOWED_REACTION_EMOJIS>
    }

    Add/swap/remove the current user's reaction sticker on a message.
    Sending the same emoji the user already reacted with removes it;
    sending a different one swaps it — one reaction per user per message,
    the same semantics MessageReaction's unique constraint enforces.

    Only the two people in the conversation (the message's sender or
    recipient) may react to it — this endpoint isn't a general-purpose
    "react to anyone's message" API.
    """
    data = request.get_json(silent=True) or {}
    emoji = (data.get("emoji") or "").strip()

    if emoji not in ALLOWED_REACTION_EMOJIS:
        return jsonify({"error": "Unsupported reaction."}), 400

    message = Message.query.get(message_id)
    if not message:
        return jsonify({"error": "Message not found."}), 404

    if current_user.id not in (message.sender_id, message.recipient_id):
        return jsonify({"error": "You can only react to messages in your own conversations."}), 403

    existing = MessageReaction.query.filter_by(message_id=message_id, user_id=current_user.id).first()

    try:
        if existing and existing.emoji == emoji:
            db.session.delete(existing)
            my_reaction = None
        elif existing:
            existing.emoji = emoji
            my_reaction = emoji
        else:
            db.session.add(MessageReaction(message_id=message_id, user_id=current_user.id, emoji=emoji))
            my_reaction = emoji
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to update message reaction")
        return jsonify({"error": "Could not update reaction. Please try again."}), 500

    reactions = [
        {"user_id": r.user_id, "emoji": r.emoji}
        for r in message.reactions.order_by(MessageReaction.created_at.asc())
    ]

    other_party_id = (
        message.recipient_id if current_user.id == message.sender_id else message.sender_id
    )

    # Broadcast to both participants' rooms (all open tabs/devices on both
    # ends), same pattern as handle_send_message — the reactor's own other
    # tabs need to see this too, not just the other party.
    socketio.emit("message_reacted", {
        "message_id": message_id,
        "reactions": reactions,
    }, room=get_room_name(other_party_id))
    socketio.emit("message_reacted", {
        "message_id": message_id,
        "reactions": reactions,
    }, room=get_room_name(current_user.id))

    return jsonify({"my_reaction": my_reaction, "reactions": reactions}), 200


# -------------------------------------------------------------------
# Stories API Routes (JSON)
#
# Photo-only posts (no video) that expire automatically after
# STORY_EXPIRY_HOURS (72h), visible to the same audience as the chat list —
# people the current user has actually messaged, plus themselves. The only
# reaction is a purple heart "love"; there is no comment feature at all.
# -------------------------------------------------------------------
@app.route("/api/stories", methods=["GET"])
@login_required
def list_stories():
    purge_expired_stories()

    visible_ids = get_conversation_partner_ids(current_user.id) | {current_user.id}

    active_stories = (
        Story.query.filter(Story.user_id.in_(visible_ids), Story.expires_at > datetime.utcnow())
        .order_by(Story.created_at.asc())
        .all()
    )

    grouped = defaultdict(list)
    for story in active_stories:
        grouped[story.user_id].append(story)

    # The current user's own entry always comes first and is always present
    # (even with zero active stories), so the client can render a "your
    # story" slot with an add button regardless of whether they've posted.
    own_stories = grouped.pop(current_user.id, [])
    users_payload = [{
        "user_id": current_user.id,
        "username": current_user.username,
        "full_name": current_user.full_name,
        "profile_pic": current_user.profile_pic,
        "stories": [s.to_dict(viewer_id=current_user.id) for s in own_stories],
    }]

    for user_id, user_stories in grouped.items():
        user = user_stories[0].user
        users_payload.append({
            "user_id": user.id,
            "username": user.username,
            "full_name": user.full_name,
            "profile_pic": user.profile_pic,
            "stories": [s.to_dict(viewer_id=current_user.id) for s in user_stories],
        })

    return jsonify({"users": users_payload}), 200


@app.route("/api/stories", methods=["POST"])
@login_required
@limiter.limit("20 per hour")
def post_story():
    purge_expired_stories()

    active_count = Story.query.filter(
        Story.user_id == current_user.id, Story.expires_at > datetime.utcnow()
    ).count()
    if active_count >= MAX_ACTIVE_STORIES_PER_USER:
        return jsonify({
            "error": f"You can only have {MAX_ACTIVE_STORIES_PER_USER} active stories at once."
        }), 400

    if "file" not in request.files:
        return jsonify({"error": "No file part in the request."}), 400

    file = request.files["file"]
    if file.filename == "":
        return jsonify({"error": "No file selected."}), 400

    if not allowed_file(file.filename):
        return jsonify({"error": "Unsupported file type. Use PNG, JPG, GIF, or WEBP."}), 400

    original_name = secure_filename(file.filename)
    ext = original_name.rsplit(".", 1)[1].lower()
    # Same collision-proof naming scheme used for profile pictures and chat
    # photos: sender id + a uuid.
    unique_name = f"{current_user.id}_{uuid.uuid4().hex}.{ext}"
    filepath = os.path.join(STORY_PHOTOS_FOLDER, unique_name)

    try:
        file.save(filepath)
    except OSError:
        logger.exception("Failed to save uploaded story photo")
        return jsonify({"error": "Could not save the uploaded file."}), 500

    # Same real-image + decompression-bomb guard used elsewhere — an
    # extension check alone can be spoofed.
    if not verify_is_real_image(filepath):
        try:
            os.remove(filepath)
        except OSError:
            pass
        return jsonify({"error": "The uploaded file is not a valid image."}), 400

    now = datetime.utcnow()
    story = Story(
        user_id=current_user.id,
        image_path=unique_name,
        created_at=now,
        expires_at=now + timedelta(hours=STORY_EXPIRY_HOURS),
    )

    try:
        db.session.add(story)
        db.session.commit()
    except Exception:
        db.session.rollback()
        try:
            os.remove(filepath)
        except OSError:
            pass
        logger.exception("Failed to save story")
        return jsonify({"error": "Could not post story. Please try again."}), 500

    payload = story.to_dict(viewer_id=current_user.id)
    payload["username"] = current_user.username
    payload["full_name"] = current_user.full_name
    payload["profile_pic"] = current_user.profile_pic

    # Let every conversation partner's open tab(s) know a new story landed,
    # the same private-room broadcast pattern used for messages.
    for partner_id in get_conversation_partner_ids(current_user.id):
        socketio.emit("new_story", payload, room=get_room_name(partner_id))
    socketio.emit("new_story", payload, room=get_room_name(current_user.id))

    return jsonify({"message": "Story posted.", "data": payload}), 201


@app.route("/api/stories/<int:story_id>", methods=["DELETE"])
@login_required
def delete_story(story_id):
    story = Story.query.get(story_id)
    if not story or story.is_expired():
        return jsonify({"error": "Story not found."}), 404
    if story.user_id != current_user.id:
        return jsonify({"error": "You can only delete your own stories."}), 403

    filepath = os.path.join(STORY_PHOTOS_FOLDER, story.image_path)

    try:
        db.session.delete(story)
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to delete story")
        return jsonify({"error": "Could not delete story. Please try again."}), 500

    try:
        if os.path.exists(filepath):
            os.remove(filepath)
    except OSError:
        logger.warning("Could not remove deleted story image: %s", story.image_path)

    for partner_id in get_conversation_partner_ids(current_user.id):
        socketio.emit(
            "story_deleted", {"story_id": story_id, "user_id": current_user.id},
            room=get_room_name(partner_id),
        )
    socketio.emit(
        "story_deleted", {"story_id": story_id, "user_id": current_user.id},
        room=get_room_name(current_user.id),
    )

    return jsonify({"message": "Story deleted."}), 200


@app.route("/api/stories/<int:story_id>/react", methods=["POST"])
@login_required
@limiter.limit("120 per hour")
def react_to_story(story_id):
    """Toggles the purple heart on this story for the current user — send
    it again to un-react. This is the only reaction stories support, and
    there is no comment endpoint at all."""
    story = Story.query.get(story_id)
    if not story or story.is_expired():
        return jsonify({"error": "Story not found."}), 404

    existing = StoryReaction.query.filter_by(story_id=story_id, user_id=current_user.id).first()

    try:
        if existing:
            db.session.delete(existing)
            reacted = False
        else:
            db.session.add(StoryReaction(story_id=story_id, user_id=current_user.id))
            reacted = True
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to toggle story reaction")
        return jsonify({"error": "Could not update reaction. Please try again."}), 500

    reaction_count = story.reactions.count()

    # Only the story owner's open tab(s) need a live update — everyone else
    # already has their own toggle state from this response.
    socketio.emit("story_reacted", {
        "story_id": story_id,
        "user_id": story.user_id,
        "reactor_id": current_user.id,
        "reactor_username": current_user.username,
        "reacted": reacted,
        "reaction_count": reaction_count,
    }, room=get_room_name(story.user_id))

    return jsonify({"reacted": reacted, "reaction_count": reaction_count}), 200


@app.route("/api/stories/<int:story_id>/reactors", methods=["GET"])
@login_required
def story_reactors(story_id):
    """Who's loved this story — visible only to the story's own owner, the
    same privacy model most stories features use."""
    story = Story.query.get(story_id)
    if not story or story.is_expired():
        return jsonify({"error": "Story not found."}), 404
    if story.user_id != current_user.id:
        return jsonify({"error": "You can only view reactions on your own stories."}), 403

    reactors = (
        User.query.join(StoryReaction, StoryReaction.user_id == User.id)
        .filter(StoryReaction.story_id == story_id)
        .order_by(StoryReaction.created_at.desc())
        .all()
    )
    return jsonify({
        "reactors": [
            {"id": u.id, "username": u.username, "full_name": u.full_name, "profile_pic": u.profile_pic}
            for u in reactors
        ]
    }), 200


def _story_cleanup_loop():
    """Runs for the lifetime of the process, sweeping expired stories off
    disk/DB on a fixed cadence. Uses socketio.sleep (eventlet-friendly,
    cooperative) rather than time.sleep so it never blocks the single
    worker's event loop — same reasoning as the eventlet.monkey_patch()
    note at the top of this file."""
    while True:
        socketio.sleep(STORY_CLEANUP_INTERVAL_SECONDS)
        with app.app_context():
            try:
                purge_expired_stories()
            except Exception:
                logger.exception("Story cleanup loop failed")


socketio.start_background_task(_story_cleanup_loop)


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

    record_daily_activity(current_user)

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
            "last_seen": to_iso_utc(now),
        })


# -------------------------------------------------------------------
# Entry Point
# -------------------------------------------------------------------
if __name__ == "__main__":
    socketio.run(app, debug=not IS_PRODUCTION, host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
