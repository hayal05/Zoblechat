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
import time
import uuid
import json
import base64
import hashlib
import secrets
import logging
import urllib.request
import urllib.error
import requests
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
from flask import Flask, request, jsonify, redirect, url_for, render_template, make_response, send_from_directory, abort
from flask_sqlalchemy import SQLAlchemy
from flask_login import (
    LoginManager, UserMixin, login_user, logout_user,
    login_required, current_user
)
from flask_socketio import SocketIO, join_room, leave_room, emit
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
# Feed post photos live in their own subfolder too — same reasoning as
# CHAT_PHOTOS_FOLDER/STORY_PHOTOS_FOLDER, independent filename namespace.
POST_PHOTOS_FOLDER = os.path.join(UPLOAD_FOLDER, "post_photos")

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


def format_call_duration(seconds):
    """Renders a call length as m:ss (e.g. 0 -> '0:00', 125 -> '2:05').
    Used both for the call-log Message preview text and for call_*
    notification text, so the wording matches everywhere it shows up."""
    try:
        seconds = max(0, int(seconds or 0))
    except (TypeError, ValueError):
        seconds = 0
    minutes, secs = divmod(seconds, 60)
    return f"{minutes}:{secs:02d}"
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
# Feed posts: text and/or photo, permanent (unlike stories), with likes,
# comments, a share counter, and reposts (a repost is itself a Post row
# with repost_of_id set, optionally carrying its own quote text).
POST_TEXT_MAX_LENGTH = 2000
POST_COMMENT_MAX_LENGTH = 500
POST_FEED_PAGE_SIZE = 10
# Verification badge: how many *consecutive* calendar days a user needs to
# have been online (at least once each day) before the account is
# auto-verified. See record_daily_activity() for the streak bookkeeping.
VERIFICATION_STREAK_DAYS = 3
# Message reaction stickers: a fixed set rather than free-form emoji input,
# so the reactions bar under a bubble stays a small, recognizable row
# instead of turning into an open-ended emoji picker. One reaction per user
# per message — see MessageReaction for the toggle/swap semantics.
ALLOWED_REACTION_EMOJIS = {"❤️", "😂", "😮", "😢", "👍", "🙏"}

# Email verification (OTP): registration no longer creates an account
# directly — it first emails a 6-digit code to the address entered, and
# the account is only created once that code is confirmed. See
# PendingRegistration below and /api/register/start, /api/register/verify.
OTP_LENGTH = 6
OTP_EXPIRY_MINUTES = 10
OTP_MAX_ATTEMPTS = 5
OTP_RESEND_COOLDOWN_SECONDS = 45

# -------------------------------------------------------------------
# Outbound email (verification codes only)
# -------------------------------------------------------------------
# Sent via the Brevo HTTP API (https://brevo.com) over HTTPS (port 443),
# which isn't affected by Render's free-tier block on outbound SMTP ports.
#
# Unlike Resend, Brevo doesn't require verifying a whole domain to send to
# arbitrary recipients — it only requires verifying one sender email
# address you already own (Brevo emails that address a 6-digit code to
# confirm you control it). That makes it a good fit when there's no
# domain to authenticate: set BREVO_FROM_EMAIL to the address you
# verified in the Brevo dashboard and you can send to anyone from it.
#
# All optional at the config level: if BREVO_API_KEY isn't set,
# send_otp_email() logs the code instead of emailing it, so local
# development never needs a real API key just to exercise the signup flow.
BREVO_API_KEY = os.environ.get("BREVO_API_KEY")
BREVO_FROM_EMAIL = os.environ.get("BREVO_FROM_EMAIL")
BREVO_FROM_NAME = os.environ.get("BREVO_FROM_NAME", "Zoble Chat")
BREVO_API_URL = "https://api.brevo.com/v3/smtp/email"

# -------------------------------------------------------------------
# Uploaded image resilience (profile pics, chat/story/post photos, group photos)
# -------------------------------------------------------------------
# Render's free-tier filesystem is wiped on every redeploy/restart, so any
# file saved to static/uploads/ can vanish while the database row that
# references it (which now lives in a persistent Postgres DB) survives.
# When all three of these are set, every upload is also mirrored to
# Cloudinary (https://cloudinary.com, permanent free tier — 25GB), and
# uploaded_file() below transparently redirects to the Cloudinary copy
# whenever the local file is missing. Local disk stays the primary,
# fast path; Cloudinary is purely a fallback, so leaving these unset just
# means uploads behave exactly as before (and don't survive a redeploy).
CLOUDINARY_CLOUD_NAME = os.environ.get("CLOUDINARY_CLOUD_NAME")
CLOUDINARY_API_KEY = os.environ.get("CLOUDINARY_API_KEY")
CLOUDINARY_API_SECRET = os.environ.get("CLOUDINARY_API_SECRET")
CLOUDINARY_CONFIGURED = bool(CLOUDINARY_CLOUD_NAME and CLOUDINARY_API_KEY and CLOUDINARY_API_SECRET)

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
# Neon, and several other Postgres providers, hand out connection strings
# starting with "postgres://" — a legacy scheme SQLAlchemy 2.x no longer
# accepts (it requires "postgresql://"). Normalize it so pasting a
# provider's URL straight into DATABASE_URL just works.
if app.config["SQLALCHEMY_DATABASE_URI"].startswith("postgres://"):
    app.config["SQLALCHEMY_DATABASE_URI"] = app.config["SQLALCHEMY_DATABASE_URI"].replace(
        "postgres://", "postgresql://", 1
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
os.makedirs(POST_PHOTOS_FOLDER, exist_ok=True)

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
    # Every new signup now goes through /api/register/start + verify, which
    # always collects (and OTP-verifies) an email — phone stays nullable
    # only because older accounts registered with a phone number instead,
    # back when that was still an option.
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
    # (see /api/register/verify) — there's no promotion path beyond that today.
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
    # Last time this user opened the news feed overlay. Posts created after
    # this timestamp (by someone else) count as "unread" for the little
    # badge on the feed nav button — same idea as Message.is_read, just
    # tracked as a single watermark instead of a per-row flag since the
    # feed is one shared stream rather than per-conversation threads.
    # NULL means "never opened the feed yet", so everything counts as
    # unread until their first visit.
    last_feed_view_at = db.Column(db.DateTime, nullable=True)

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


class PasswordReset(db.Model):
    """A password reset in progress. Same shape/lifecycle as
    PendingRegistration's OTP flow: /api/password-reset/start emails a
    6-digit code and stores it here (keyed by the account's email);
    /api/password-reset/verify checks the code and, only if it matches,
    updates the real User row's password_hash in the same request. Kept
    in the database (not an in-memory dict) so an in-progress reset
    survives a worker restart between the two requests.

    One row per email — starting a new reset for an email that already
    has a row in progress replaces it, so an abandoned attempt can never
    block a retry.
    """
    __tablename__ = "password_resets"

    id = db.Column(db.Integer, primary_key=True)
    email = db.Column(db.String(255), unique=True, nullable=False, index=True)
    user_id = db.Column(db.Integer, db.ForeignKey("users.id", ondelete="CASCADE"), nullable=False)
    otp_code = db.Column(db.String(OTP_LENGTH), nullable=False)
    otp_expires_at = db.Column(db.DateTime, nullable=False)
    # Wrong-code guesses against this row. Hitting OTP_MAX_ATTEMPTS forces a
    # fresh code (see /api/password-reset/verify) instead of allowing
    # unlimited brute-force attempts against a 6-digit space.
    attempts = db.Column(db.Integer, nullable=False, default=0)
    # Backs the resend cooldown — /api/password-reset/resend refuses to
    # fire off another email until OTP_RESEND_COOLDOWN_SECONDS after this.
    last_sent_at = db.Column(db.DateTime, nullable=False, default=datetime.utcnow)
    created_at = db.Column(db.DateTime, nullable=False, default=datetime.utcnow)

    user = db.relationship("User")

    def is_expired(self):
        return datetime.utcnow() > self.otp_expires_at

    def __repr__(self):
        return f"<PasswordReset {self.email}>"


class PendingRegistration(db.Model):
    """A signup that hasn't been confirmed yet. Registration is now two
    steps: /api/register/start collects name/email/password and emails a
    code, storing everything needed to finish the job here; /api/register/
    verify checks the code and only THEN creates the real User row. Kept
    in the database (not an in-memory dict) so a pending signup survives a
    worker restart between the two requests.

    One row per email — starting a new signup for an email that already
    has a pending row replaces it (see /api/register/start), so a stale
    or abandoned attempt can never block a retry.
    """
    __tablename__ = "pending_registrations"

    id = db.Column(db.Integer, primary_key=True)
    email = db.Column(db.String(255), unique=True, nullable=False, index=True)
    full_name = db.Column(db.String(FULL_NAME_MAX_LENGTH), nullable=False)
    # Hashed immediately on submit, same as a real User — a pending row is
    # never storing anyone's password in the clear.
    password_hash = db.Column(db.String(255), nullable=False)
    otp_code = db.Column(db.String(OTP_LENGTH), nullable=False)
    otp_expires_at = db.Column(db.DateTime, nullable=False)
    # Wrong-code guesses against this row. Hitting OTP_MAX_ATTEMPTS forces a
    # fresh code (see /api/register/verify) instead of allowing unlimited
    # brute-force attempts against a 6-digit space.
    attempts = db.Column(db.Integer, nullable=False, default=0)
    # Backs the resend cooldown — /api/register/resend refuses to fire off
    # another email until OTP_RESEND_COOLDOWN_SECONDS after this.
    last_sent_at = db.Column(db.DateTime, nullable=False, default=datetime.utcnow)
    created_at = db.Column(db.DateTime, nullable=False, default=datetime.utcnow)

    def is_expired(self):
        return datetime.utcnow() > self.otp_expires_at

    def __repr__(self):
        return f"<PendingRegistration {self.email}>"


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


class Post(db.Model):
    """A single feed post. Unlike Story, a post never expires and can be
    text-only, photo-only, or both (at least one of the two is required —
    enforced in the route, not here). Visible to every user, same as a
    normal social news feed."""
    __tablename__ = "posts"

    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    text = db.Column(db.Text, nullable=True)
    # Filename only (relative to static/uploads/post_photos/), same storage
    # convention as Story.image_path.
    image_path = db.Column(db.String(255), nullable=True)
    share_count = db.Column(db.Integer, default=0, nullable=False)
    # Set only on a repost: points at the original post being reposted.
    # `text` on a repost row is an optional quote/caption the reposter
    # added, not the original post's own text (that's read from
    # `original_post` instead). SET NULL on delete so a repost survives
    # its original being removed — it just renders without the original
    # attached rather than disappearing itself.
    repost_of_id = db.Column(
        db.Integer, db.ForeignKey("posts.id", ondelete="SET NULL"), nullable=True, index=True
    )
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False, index=True)

    user = db.relationship(
        "User", backref=db.backref("posts", lazy="dynamic", cascade="all, delete-orphan")
    )
    original_post = db.relationship(
        "Post", remote_side=[id],
        backref=db.backref("reposts", lazy="dynamic", passive_deletes=True),
    )

    def to_dict(self, viewer_id=None):
        liked_by_me = (
            viewer_id is not None
            and self.likes.filter_by(user_id=viewer_id).first() is not None
        )
        reposted_by_me = (
            viewer_id is not None
            and Post.query.filter_by(user_id=viewer_id, repost_of_id=self.id).first() is not None
        )
        return {
            "id": self.id,
            "user_id": self.user_id,
            "username": self.user.username,
            "full_name": self.user.full_name,
            "profile_pic": self.user.profile_pic,
            "is_verified": bool(self.user.is_verified),
            "is_admin": bool(self.user.is_admin),
            "text": self.text,
            "image_url": (
                url_for("static", filename=f"uploads/post_photos/{self.image_path}")
                if self.image_path else None
            ),
            "created_at": to_iso_utc(self.created_at),
            "like_count": self.likes.count(),
            "liked_by_me": liked_by_me,
            "comment_count": self.comments.count(),
            "share_count": self.share_count,
            "repost_of_id": self.repost_of_id,
            # Nested one level only — reposting a repost attaches to the
            # true original (see repost_post()), so this never recurses.
            "repost_of": self.original_post.to_dict(viewer_id=viewer_id) if self.original_post else None,
            "repost_count": self.reposts.count(),
            "reposted_by_me": reposted_by_me,
        }

    def __repr__(self):
        return f"<Post {self.id} by {self.user_id}>"


class PostLike(db.Model):
    """One like per user per post — sending it again removes it, same
    toggle behavior as StoryReaction."""
    __tablename__ = "post_likes"

    id = db.Column(db.Integer, primary_key=True)
    post_id = db.Column(db.Integer, db.ForeignKey("posts.id"), nullable=False, index=True)
    user_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)

    post = db.relationship(
        "Post", backref=db.backref("likes", lazy="dynamic", cascade="all, delete-orphan")
    )
    liker = db.relationship("User")

    __table_args__ = (
        db.UniqueConstraint("post_id", "user_id", name="uq_post_like_user"),
    )

    def __repr__(self):
        return f"<PostLike post={self.post_id} user={self.user_id}>"


class PostComment(db.Model):
    """A single comment on a post. Posts support unlimited comments,
    unlike stories which have no comment feature at all."""
    __tablename__ = "post_comments"

    id = db.Column(db.Integer, primary_key=True)
    post_id = db.Column(db.Integer, db.ForeignKey("posts.id"), nullable=False, index=True)
    user_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    text = db.Column(db.String(500), nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False, index=True)

    post = db.relationship(
        "Post", backref=db.backref("comments", lazy="dynamic", cascade="all, delete-orphan")
    )
    author = db.relationship("User")

    def to_dict(self):
        return {
            "id": self.id,
            "post_id": self.post_id,
            "user_id": self.user_id,
            "username": self.author.username,
            "full_name": self.author.full_name,
            "profile_pic": self.author.profile_pic,
            "is_verified": bool(self.author.is_verified),
            "is_admin": bool(self.author.is_admin),
            "text": self.text,
            "created_at": to_iso_utc(self.created_at),
        }

    def __repr__(self):
        return f"<PostComment {self.id} on post={self.post_id}>"


class Follow(db.Model):
    """One row per (follower -> followed) relationship. Powers the Follow
    button on the account page opened from a feed post's name/avatar —
    purely social bookkeeping, doesn't gate messaging or feed visibility
    (anyone can already chat with or see posts from anyone else)."""
    __tablename__ = "follows"

    id = db.Column(db.Integer, primary_key=True)
    follower_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    followed_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)

    follower = db.relationship(
        "User", foreign_keys=[follower_id],
        backref=db.backref("following", lazy="dynamic", cascade="all, delete-orphan"),
    )
    followed = db.relationship(
        "User", foreign_keys=[followed_id],
        backref=db.backref("followers", lazy="dynamic", cascade="all, delete-orphan"),
    )

    __table_args__ = (
        db.UniqueConstraint("follower_id", "followed_id", name="uq_follow_pair"),
    )

    def __repr__(self):
        return f"<Follow {self.follower_id} -> {self.followed_id}>"


class Group(db.Model):
    """A group chat. Membership/role lives in GroupMember; this row just
    holds the group's own identity."""
    __tablename__ = "groups"

    id = db.Column(db.Integer, primary_key=True)
    name = db.Column(db.String(60), nullable=False)
    # Filename only (same storage convention as User.profile_pic), living in
    # UPLOAD_FOLDER. Nullable/None means "no custom photo" — the client
    # falls back to the generic group icon (.avatar-group) rather than a
    # shared default image file, since unlike user avatars there's no
    # single sensible "default group photo".
    photo = db.Column(db.String(255), nullable=True)
    # ON DELETE SET NULL — a group outlives its creator's account being
    # deleted; who's an admin is tracked in GroupMember, not here.
    created_by = db.Column(db.Integer, db.ForeignKey("users.id", ondelete="SET NULL"), nullable=True)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)

    members = db.relationship(
        "GroupMember", backref="group", lazy="dynamic", cascade="all, delete-orphan"
    )
    messages = db.relationship(
        "GroupMessage", backref="group", lazy="dynamic", cascade="all, delete-orphan"
    )

    def to_dict(self, viewer_id=None):
        member_rows = self.members.order_by(GroupMember.joined_at.asc()).all()
        last_message = self.messages.order_by(GroupMessage.timestamp.desc()).first()

        # Mirrors the 1:1 sidebar's Message.is_read-based unread_count: how
        # many messages in this group the viewer hasn't seen yet, judged
        # against their own GroupMember.last_read_at watermark (the same
        # field GroupMessage.to_dict() uses for its per-message "is_read").
        # A viewer who has never opened the group (last_read_at is None)
        # has everyone else's messages unread; a non-member (or anonymous
        # caller) gets 0 rather than a query against a watermark that
        # doesn't exist for them.
        unread_count = 0
        if viewer_id is not None:
            viewer_member = next((m for m in member_rows if m.user_id == viewer_id), None)
            if viewer_member is not None:
                unread_query = self.messages.filter(GroupMessage.sender_id != viewer_id)
                if viewer_member.last_read_at is not None:
                    unread_query = unread_query.filter(
                        GroupMessage.timestamp > viewer_member.last_read_at
                    )
                unread_count = unread_query.count()

        return {
            "id": self.id,
            "name": self.name,
            "photo": self.photo,
            "created_by": self.created_by,
            "created_at": to_iso_utc(self.created_at),
            "member_count": len(member_rows),
            "members": [m.to_dict() for m in member_rows],
            "my_role": next(
                (m.role for m in member_rows if m.user_id == viewer_id), None
            ) if viewer_id is not None else None,
            "last_message": last_message.to_dict() if last_message else None,
            "unread_count": unread_count,
        }

    def __repr__(self):
        return f"<Group {self.id} {self.name!r}>"


class GroupMember(db.Model):
    __tablename__ = "group_members"

    id = db.Column(db.Integer, primary_key=True)
    group_id = db.Column(db.Integer, db.ForeignKey("groups.id", ondelete="CASCADE"), nullable=False, index=True)
    user_id = db.Column(db.Integer, db.ForeignKey("users.id", ondelete="CASCADE"), nullable=False, index=True)
    role = db.Column(db.String(10), nullable=False, default="member")  # 'admin' | 'member'
    joined_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    # Stamped forward every time this member has the group conversation open
    # (see the "mark_group_read" socket event) — lets GroupMessage.to_dict()
    # figure out whether *every other* member has seen a given message, the
    # same "read" concept 1:1 chat already has via Message.is_read, just
    # derived from a per-member watermark instead of a single boolean since
    # a group message has more than one possible reader.
    last_read_at = db.Column(db.DateTime, nullable=True)

    user = db.relationship("User")

    __table_args__ = (
        db.UniqueConstraint("group_id", "user_id", name="uq_group_member_user"),
    )

    def to_dict(self):
        return {
            "user_id": self.user_id,
            "username": self.user.username if self.user else None,
            "full_name": self.user.full_name if self.user else None,
            "profile_pic": self.user.profile_pic if self.user else None,
            "role": self.role,
            "joined_at": to_iso_utc(self.joined_at),
        }

    def __repr__(self):
        return f"<GroupMember group={self.group_id} user={self.user_id} role={self.role}>"


class GroupMessage(db.Model):
    __tablename__ = "group_messages"

    id = db.Column(db.Integer, primary_key=True)
    group_id = db.Column(db.Integer, db.ForeignKey("groups.id", ondelete="CASCADE"), nullable=False, index=True)
    sender_id = db.Column(db.Integer, db.ForeignKey("users.id", ondelete="CASCADE"), nullable=False, index=True)
    content = db.Column(db.String(MESSAGE_MAX_LENGTH), nullable=False)
    message_type = db.Column(db.String(10), nullable=False, default="text")  # 'text' | 'image'
    image_path = db.Column(db.String(255), nullable=True)
    timestamp = db.Column(db.DateTime, default=datetime.utcnow, index=True)

    sender = db.relationship("User")

    def to_dict(self):
        # "Read" for a group message means every *other* current member has
        # opened the conversation at least as recently as this message was
        # sent (their last_read_at watermark is past it) — mirrors the
        # single/double check semantics of Message.is_read, just evaluated
        # against every other member instead of a single recipient. A group
        # with no other members yet (just the sender) is never "read".
        other_members = GroupMember.query.filter(
            GroupMember.group_id == self.group_id,
            GroupMember.user_id != self.sender_id,
        ).all()
        is_read = bool(other_members) and all(
            m.last_read_at is not None and m.last_read_at >= self.timestamp
            for m in other_members
        )

        return {
            "id": self.id,
            "group_id": self.group_id,
            "sender_id": self.sender_id,
            "sender_username": self.sender.username if self.sender else None,
            "sender_full_name": self.sender.full_name if self.sender else None,
            "sender_profile_pic": self.sender.profile_pic if self.sender else None,
            "content": self.content,
            "message_type": self.message_type,
            "image_url": (
                url_for("static", filename=f"uploads/chat_photos/{self.image_path}")
                if self.image_path else None
            ),
            "timestamp": to_iso_utc(self.timestamp),
            "is_read": is_read,
            # Same raw per-user shape as Message.to_dict()'s reactions field —
            # lets the client reuse its existing reaction-rendering logic
            # unchanged for group messages.
            "reactions": [
                {"user_id": r.user_id, "emoji": r.emoji}
                for r in self.reactions.order_by(GroupMessageReaction.created_at.asc())
            ],
        }

    def __repr__(self):
        return f"<GroupMessage {self.id} group={self.group_id} from={self.sender_id}>"


class GroupMessageReaction(db.Model):
    """A single reaction sticker from one group member on one GroupMessage —
    the group-chat equivalent of MessageReaction, with identical one-per-user
    swap/remove semantics."""
    __tablename__ = "group_message_reactions"

    id = db.Column(db.Integer, primary_key=True)
    group_message_id = db.Column(
        db.Integer, db.ForeignKey("group_messages.id", ondelete="CASCADE"), nullable=False, index=True
    )
    user_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=False, index=True)
    emoji = db.Column(db.String(8), nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)

    message = db.relationship(
        "GroupMessage", backref=db.backref("reactions", lazy="dynamic", cascade="all, delete-orphan")
    )
    reactor = db.relationship("User")

    __table_args__ = (
        db.UniqueConstraint("group_message_id", "user_id", name="uq_group_message_reaction_user"),
    )

    def __repr__(self):
        return f"<GroupMessageReaction message={self.group_message_id} user={self.user_id}>"


class Notification(db.Model):
    """A single notification for `user_id`, e.g. someone followed them,
    liked/commented on/shared/reposted their post, reacted to their story or a
    message/group message they sent, or added them to a group. `actor_id`
    is whoever triggered it (nullable — SET NULL on delete, so a
    notification outlives the actor's account being removed, same
    reasoning as Group.created_by). Exactly one of post_id/story_id/
    group_id/message_id/group_message_id is populated depending on `type`;
    the rest stay None."""
    __tablename__ = "notifications"

    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey("users.id", ondelete="CASCADE"), nullable=False, index=True)
    actor_id = db.Column(db.Integer, db.ForeignKey("users.id", ondelete="SET NULL"), nullable=True, index=True)
    # 'follow' | 'post_like' | 'post_comment' | 'post_share' | 'post_repost' |
    # 'story_reaction' | 'message_reaction' | 'group_message_reaction' |
    # 'group_added' | 'call_missed' | 'call_received' | 'call_outgoing'
    #
    # The three call_* types all point at the same call-log Message row via
    # message_id (see _finalize_call): 'call_missed'/'call_received' go to
    # the callee (depending on whether they picked up), 'call_outgoing'
    # always goes to the caller, regardless of how the call ended.
    type = db.Column(db.String(30), nullable=False)
    post_id = db.Column(db.Integer, db.ForeignKey("posts.id", ondelete="SET NULL"), nullable=True)
    story_id = db.Column(db.Integer, db.ForeignKey("stories.id", ondelete="SET NULL"), nullable=True)
    group_id = db.Column(db.Integer, db.ForeignKey("groups.id", ondelete="SET NULL"), nullable=True)
    message_id = db.Column(db.Integer, db.ForeignKey("messages.id", ondelete="SET NULL"), nullable=True)
    group_message_id = db.Column(db.Integer, db.ForeignKey("group_messages.id", ondelete="SET NULL"), nullable=True)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False, index=True)
    is_read = db.Column(db.Boolean, default=False, nullable=False, index=True)

    actor = db.relationship("User", foreign_keys=[actor_id])

    # Human-readable text per type, filled in by to_dict(). {group} is
    # swapped for the group's current name at render time (not baked in at
    # creation) so a later rename shows up correctly on old notifications too.
    _TEXT_BY_TYPE = {
        "follow": "started following you",
        "post_like": "liked your post",
        "post_comment": "commented on your post",
        "post_share": "shared your post",
        "post_repost": "reposted your post",
        "story_reaction": "reacted to your story",
        "message_reaction": "reacted to your message",
        "group_message_reaction": "reacted to your message in {group}",
        "group_added": "added you to {group}",
    }

    def _call_text(self):
        """call_* notifications don't fit the static _TEXT_BY_TYPE lookup —
        the wording depends on how the call actually ended, which lives on
        the linked call-log Message (message_id), not on the notification
        row itself."""
        status, duration = None, None
        msg = Message.query.get(self.message_id) if self.message_id else None
        if msg:
            try:
                meta = json.loads(msg.content)
                status = meta.get("call_status")
                duration = meta.get("duration")
            except (TypeError, ValueError):
                pass

        if self.type == "call_missed":
            return "tried to call you"
        if self.type == "call_received":
            return f"had a voice call with you · {format_call_duration(duration)}"
        if self.type == "call_outgoing":
            if status == "completed":
                return f"answered your call · {format_call_duration(duration)}"
            if status == "declined":
                return "declined your call"
            return "didn't answer your call"
        return ""

    def to_dict(self):
        if self.type.startswith("call_"):
            text = self._call_text()
        else:
            text = self._TEXT_BY_TYPE.get(self.type, "")
            if "{group}" in text:
                group = Group.query.get(self.group_id) if self.group_id else None
                text = text.format(group=group.name if group else "a group")

        return {
            "id": self.id,
            "type": self.type,
            "actor_id": self.actor_id,
            "actor_username": self.actor.username if self.actor else None,
            "actor_full_name": self.actor.full_name if self.actor else None,
            "actor_profile_pic": self.actor.profile_pic if self.actor else None,
            "text": text,
            "post_id": self.post_id,
            "story_id": self.story_id,
            "group_id": self.group_id,
            "message_id": self.message_id,
            "group_message_id": self.group_message_id,
            "created_at": to_iso_utc(self.created_at),
            "is_read": self.is_read,
        }

    def __repr__(self):
        return f"<Notification {self.id} user={self.user_id} type={self.type}>"


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
            conn.execute(text("ALTER TABLE users ADD COLUMN last_seen TIMESTAMP"))

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
            conn.execute(text("ALTER TABLE users ADD COLUMN verified_at TIMESTAMP"))
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

    if "last_feed_view_at" not in existing_columns:
        logger.info("Migrating users table: adding 'last_feed_view_at' column")
        with db.engine.begin() as conn:
            conn.execute(text("ALTER TABLE users ADD COLUMN last_feed_view_at TIMESTAMP"))
            # Backfill existing accounts to "now" so upgrading doesn't dump a
            # huge unread count on everyone for posts they'd already seen
            # before this feature existed — only genuinely new posts from
            # here on out should show as unread.
            conn.execute(text(
                "UPDATE users SET last_feed_view_at = CURRENT_TIMESTAMP "
                "WHERE last_feed_view_at IS NULL"
            ))

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

    if "groups" in inspector.get_table_names():
        existing_group_columns = {col["name"] for col in inspector.get_columns("groups")}

        if "photo" not in existing_group_columns:
            logger.info("Migrating groups table: adding 'photo' column")
            with db.engine.begin() as conn:
                conn.execute(text("ALTER TABLE groups ADD COLUMN photo VARCHAR(255)"))

    if "group_members" in inspector.get_table_names():
        existing_group_member_columns = {col["name"] for col in inspector.get_columns("group_members")}

        if "last_read_at" not in existing_group_member_columns:
            logger.info("Migrating group_members table: adding 'last_read_at' column")
            with db.engine.begin() as conn:
                conn.execute(text("ALTER TABLE group_members ADD COLUMN last_read_at TIMESTAMP"))

    if "posts" in inspector.get_table_names():
        existing_post_columns = {col["name"] for col in inspector.get_columns("posts")}

        if "repost_of_id" not in existing_post_columns:
            logger.info("Migrating posts table: adding 'repost_of_id' column")
            with db.engine.begin() as conn:
                conn.execute(text(
                    "ALTER TABLE posts ADD COLUMN repost_of_id INTEGER "
                    "REFERENCES posts(id) ON DELETE SET NULL"
                ))
                conn.execute(text(
                    "CREATE INDEX IF NOT EXISTS ix_posts_repost_of_id ON posts (repost_of_id)"
                ))


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


def generate_otp_code():
    """A cryptographically random 6-digit code (zero-padded, so it's always
    OTP_LENGTH digits) — secrets.randbelow rather than random.randint since
    this gates account creation."""
    return f"{secrets.randbelow(10 ** OTP_LENGTH):0{OTP_LENGTH}d}"


def send_otp_email(to_email, code, full_name):
    """Emails a verification code for the signup flow via the Brevo HTTP
    API. Falls back to just logging the code when BREVO_API_KEY isn't
    configured, so local development and this project's own tests can
    exercise registration without a real API key — see the BREVO_*
    constants above.

    Raises on a genuine send failure so the caller can surface a real error
    to the person instead of silently leaving them stuck waiting on an
    email that never arrives.
    """
    subject = "Your Zoble verification code"
    text_body = (
        f"Hi {full_name},\n\n"
        f"Your Zoble verification code is: {code}\n\n"
        f"This code expires in {OTP_EXPIRY_MINUTES} minutes. If you didn't "
        f"try to sign up for Zoble, you can ignore this email.\n"
    )
    _send_brevo_email(to_email, subject, text_body, dev_log_label="Verification", dev_log_code=code)


def send_password_reset_email(to_email, code, full_name):
    """Emails a password-reset code via the same Brevo HTTP API as
    send_otp_email above — identical delivery mechanics, just a distinct
    subject/body so a reset code can never be mistaken for a signup
    verification code, and a reassurance line for the (common) case where
    someone else typed in this email address by mistake and the real
    owner never asked for a reset.

    Raises on a genuine send failure so the caller can surface a real
    error instead of leaving the person stuck waiting on an email that
    never arrives.
    """
    subject = "Your Zoble password reset code"
    text_body = (
        f"Hi {full_name},\n\n"
        f"Your Zoble password reset code is: {code}\n\n"
        f"This code expires in {OTP_EXPIRY_MINUTES} minutes. If you didn't "
        f"request a password reset, you can safely ignore this email — "
        f"your password won't be changed.\n"
    )
    _send_brevo_email(to_email, subject, text_body, dev_log_label="Password reset", dev_log_code=code)


def _send_brevo_email(to_email, subject, text_body, dev_log_label, dev_log_code):
    """Shared HTTP-sending mechanics behind send_otp_email and
    send_password_reset_email above — falls back to just logging the code
    when BREVO_API_KEY isn't configured, so local development and this
    project's own tests can exercise either flow without a real API key
    (see the BREVO_* constants above).
    """
    if not BREVO_API_KEY or not BREVO_FROM_EMAIL:
        logger.info(
            "[DEV] %s code for %s: %s (no BREVO_API_KEY/BREVO_FROM_EMAIL configured)",
            dev_log_label, to_email, dev_log_code,
        )
        return

    payload = json.dumps({
        "sender": {"name": BREVO_FROM_NAME, "email": BREVO_FROM_EMAIL},
        "to": [{"email": to_email}],
        "subject": subject,
        "textContent": text_body,
    }).encode("utf-8")

    req = urllib.request.Request(
        BREVO_API_URL,
        data=payload,
        method="POST",
        headers={
            "api-key": BREVO_API_KEY,
            "Content-Type": "application/json",
            "Accept": "application/json",
            # Some HTTP APIs behind bot-protection reject urllib's default
            # "Python-urllib/x.y" User-Agent — send a normal one to be safe.
            "User-Agent": "zoble-chat/1.0 (+https://zoble-chat.onrender.com)",
        },
    )

    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            resp.read()
    except urllib.error.HTTPError as e:
        # Brevo returns a JSON error body (e.g. unverified sender, invalid
        # API key) — log it so the real cause shows up server-side instead
        # of just a bare status code.
        detail = e.read().decode("utf-8", errors="replace")
        logger.error("Brevo API rejected the request (%s): %s", e.code, detail)
        raise
    except urllib.error.URLError:
        logger.exception("Failed to reach Brevo API")
        raise


def generate_unique_username(email, full_name):
    """Registration no longer asks for a username — one is derived
    automatically from the email's local part (falling back to the name)
    so the rest of the app, which identifies people by username in search,
    mentions, and chat rows, keeps working unchanged. Collisions just get a
    numeric suffix appended, same idea as how most social apps mint a
    default handle."""
    source = (email.split("@")[0] if email else "") or full_name or "user"
    base = re.sub(r"[^A-Za-z0-9_.]", "", source).lower()[:24]
    if len(base) < 3:
        base = (base + secrets.token_hex(3))[:24]

    candidate = base
    suffix = 0
    while User.query.filter(func.lower(User.username) == candidate.lower()).first():
        suffix += 1
        candidate = f"{base}{suffix}"[:30]
    return candidate


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


def _cloudinary_signature(params):
    """Cloudinary's signing scheme: sort params by key, join as
    'key=value&key=value...', append the API secret, then SHA-1 the whole
    string. https://cloudinary.com/documentation/authentication_signatures
    """
    to_sign = "&".join(f"{k}={v}" for k, v in sorted(params.items()))
    return hashlib.sha1((to_sign + CLOUDINARY_API_SECRET).encode("utf-8")).hexdigest()


def cloudinary_public_id_for(relative_path):
    """Maps a path under static/uploads/ (e.g. 'chat_photos/12_abcd.jpg',
    or just 'abcd.png' for profile pics) to the Cloudinary public_id used
    to mirror it. Cloudinary tracks the file extension separately as
    'format' rather than as part of the public_id, so it's stripped here
    — and re-appended when reconstructing the delivery URL in
    uploaded_file() below.

    Deliberately deterministic and reversible from nothing but the
    filename already stored in the database, so there's no need for a
    separate column to remember each file's Cloudinary URL — any code
    that already has the stored filename can find the mirror.
    """
    root, _ext = os.path.splitext(relative_path)
    return f"zoble/{root}"


def cloudinary_mirror_upload(local_filepath, relative_path):
    """Best-effort mirror of a just-saved local upload to Cloudinary, keyed
    so uploaded_file() can reconstruct its URL later purely from
    relative_path (the path under static/uploads/, e.g.
    'chat_photos/12_abcd.jpg').

    Failures are logged, not raised: Cloudinary is a resilience fallback
    for after a redeploy wipes local disk, not the primary write path, so
    a hiccup here should never block the user's upload from succeeding.
    """
    if not CLOUDINARY_CONFIGURED:
        logger.warning(
            "Skipping Cloudinary mirror upload for %s — CLOUDINARY_CLOUD_NAME/"
            "CLOUDINARY_API_KEY/CLOUDINARY_API_SECRET not all set.",
            relative_path,
        )
        return
    public_id = cloudinary_public_id_for(relative_path)
    timestamp = int(time.time())
    signature = _cloudinary_signature({"public_id": public_id, "timestamp": timestamp})
    try:
        with open(local_filepath, "rb") as f:
            resp = requests.post(
                f"https://api.cloudinary.com/v1_1/{CLOUDINARY_CLOUD_NAME}/image/upload",
                data={
                    "api_key": CLOUDINARY_API_KEY,
                    "timestamp": timestamp,
                    "public_id": public_id,
                    "signature": signature,
                },
                files={"file": f},
                timeout=15,
            )
        resp.raise_for_status()
        logger.info("Cloudinary mirror upload succeeded for %s -> public_id=%s", relative_path, public_id)
    except requests.RequestException as e:
        body = getattr(getattr(e, "response", None), "text", "<no response>")
        logger.exception("Cloudinary mirror upload failed for %s. Response body: %s", relative_path, body)


def cloudinary_mirror_delete(relative_path):
    """Best-effort cleanup of a mirrored file on Cloudinary, called
    alongside the app's existing local os.remove() calls when a photo is
    replaced or deleted (e.g. changing your profile picture). Never
    raises — an orphaned Cloudinary file just wastes a little of the free
    storage quota, which isn't worth failing the user's request over.
    """
    if not CLOUDINARY_CONFIGURED:
        logger.warning(
            "Skipping Cloudinary mirror delete for %s — CLOUDINARY_CLOUD_NAME/"
            "CLOUDINARY_API_KEY/CLOUDINARY_API_SECRET not all set.",
            relative_path,
        )
        return
    public_id = cloudinary_public_id_for(relative_path)
    timestamp = int(time.time())
    signature = _cloudinary_signature({"public_id": public_id, "timestamp": timestamp})
    try:
        requests.post(
            f"https://api.cloudinary.com/v1_1/{CLOUDINARY_CLOUD_NAME}/image/destroy",
            data={
                "api_key": CLOUDINARY_API_KEY,
                "timestamp": timestamp,
                "public_id": public_id,
                "signature": signature,
            },
            timeout=15,
        )
    except requests.RequestException:
        logger.exception("Cloudinary mirror delete failed for %s", relative_path)


@app.route("/api/debug/cloudinary-status", methods=["GET"])
@login_required
def cloudinary_status():
    """Admin-only live health check for the photo-persistence fallback.

    Reports which of the three CLOUDINARY_* env vars are actually set
    (without leaking their values), then — if all three are present —
    performs one real signed upload + delete round trip against
    Cloudinary's API using a tiny 1x1 pixel throwaway image, so a bad
    API key/secret or an unreachable account shows up here as a clear
    error message instead of only ever surfacing as "photos vanished
    after the next disk wipe" with no visible cause.
    """
    if not current_user.is_admin:
        return jsonify({"error": "Admin access required."}), 403

    status = {
        "cloud_name_set": bool(CLOUDINARY_CLOUD_NAME),
        "api_key_set": bool(CLOUDINARY_API_KEY),
        "api_secret_set": bool(CLOUDINARY_API_SECRET),
        "configured": CLOUDINARY_CONFIGURED,
        "test_upload": None,
    }

    if not CLOUDINARY_CONFIGURED:
        status["test_upload"] = "skipped — one or more env vars are unset, see above"
        return jsonify(status), 200

    # Smallest possible valid PNG (1x1 transparent pixel) — real bytes,
    # not a placeholder, so Cloudinary's upload validation has something
    # legitimate to accept rather than rejecting empty/garbage content.
    test_png = base64.b64decode(
        "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mNk+A8AAQUBAScY42YAAAAASUVORK5CYII="
    )
    test_public_id = f"zoble/debug/connectivity_check_{int(time.time())}"
    timestamp = int(time.time())
    signature = _cloudinary_signature({"public_id": test_public_id, "timestamp": timestamp})

    try:
        resp = requests.post(
            f"https://api.cloudinary.com/v1_1/{CLOUDINARY_CLOUD_NAME}/image/upload",
            data={
                "api_key": CLOUDINARY_API_KEY,
                "timestamp": timestamp,
                "public_id": test_public_id,
                "signature": signature,
            },
            files={"file": ("test.png", test_png, "image/png")},
            timeout=15,
        )
        if resp.ok:
            status["test_upload"] = "ok — Cloudinary accepted the test upload"
        else:
            status["test_upload"] = f"FAILED — HTTP {resp.status_code}: {resp.text[:500]}"
    except requests.RequestException as e:
        status["test_upload"] = f"FAILED — could not reach Cloudinary: {e}"
    else:
        # Clean up the test file either way we don't care about; best-effort.
        cloudinary_mirror_delete(f"debug/{os.path.basename(test_public_id)}.png")

    return jsonify(status), 200


@app.route("/api/debug/db-status", methods=["GET"])
@login_required
def db_status():
    """Admin-only live health check for where the database actually lives.

    This is the other half of the "photos revert to default" failure mode:
    Cloudinary being configured and working (see /api/debug/cloudinary-status)
    only saves the image *bytes*. The filename that points at them
    (User.profile_pic, Post/Message/Story.image_path, etc.) lives in this
    app's own database — and if DATABASE_URL isn't set, that database is a
    SQLite file sitting on the same ephemeral disk as the uploads folder.
    Render (and most free-tier hosts) wipe that disk on every redeploy and
    on every restart after the app has been idle, which deletes the rows
    referencing those images right along with it — even though the actual
    files are still sitting safely in Cloudinary, nothing in the (fresh,
    empty) database points at them anymore. From the user's side this
    looks exactly like "my photo turned back into the default avatar" or
    "my post's photo disappeared", with no error anywhere, because nothing
    actually failed — the row just isn't there to look at.

    Fix: set DATABASE_URL to a persistent Postgres connection string (see
    env.example) so accounts/posts/messages — and the photo filenames they
    reference — survive restarts the same way the Cloudinary-mirrored
    files already do.
    """
    if not current_user.is_admin:
        return jsonify({"error": "Admin access required."}), 403

    uri = app.config["SQLALCHEMY_DATABASE_URI"]
    is_sqlite = uri.startswith("sqlite:")

    status = {
        "database_url_env_var_set": bool(os.environ.get("DATABASE_URL")),
        "engine": db.engine.dialect.name,
        "using_ephemeral_sqlite": is_sqlite,
        "warning": (
            "Using local SQLite with no DATABASE_URL set — every account, post, "
            "message, and photo filename will be WIPED the next time this app "
            "restarts or redeploys (Render's free-tier disk is ephemeral). "
            "Cloudinary keeps the actual image files safe, but the database "
            "rows pointing at them will be gone, which is exactly what makes "
            "photos look like they've reverted to the default. Set DATABASE_URL "
            "to a persistent Postgres connection string (e.g. from Neon — see "
            "env.example) to fix this."
        ) if is_sqlite else None,
    }

    try:
        status["user_count"] = User.query.count()
        status["post_count"] = Post.query.count()
    except Exception as e:
        status["query_error"] = str(e)

    return jsonify(status), 200


@app.route("/static/uploads/<path:filename>")
def uploaded_file(filename):
    """Serves an uploaded file from local disk, falling back to its
    Cloudinary mirror when the local copy is missing.

    Render's free-tier filesystem is wiped on every redeploy/restart, so a
    file uploaded before the most recent deploy can vanish from disk even
    though the database row referencing it (User.profile_pic,
    Message/Story/Post/GroupMessage.image_path, Group.photo) survives in
    Postgres. Rather than 404ing in that case, redirect to the copy
    cloudinary_mirror_upload() saved at upload time. This intentionally
    shares its URL prefix with, and takes priority over, Flask's default
    static file route (see uploaded_file's more specific rule vs. the
    built-in '/static/<path:filename>') — every existing template and
    client-side script that builds an image URL as '/static/uploads/...'
    keeps working unchanged either way.
    """
    local_path = os.path.join(app.config["UPLOAD_FOLDER"], filename)
    if os.path.isfile(local_path):
        return send_from_directory(app.config["UPLOAD_FOLDER"], filename)

    if CLOUDINARY_CONFIGURED:
        public_id = cloudinary_public_id_for(filename)
        ext = (os.path.splitext(filename)[1].lstrip(".") or "jpg").lower()
        return redirect(f"https://res.cloudinary.com/{CLOUDINARY_CLOUD_NAME}/image/upload/{public_id}.{ext}")

    abort(404)


def get_room_name(user_id):
    """Each user gets a private room named after their user ID, so we can
    target them directly regardless of which browser tab/device they're on."""
    return f"user_{user_id}"


def get_group_room_name(group_id):
    """Each group gets its own Socket.IO room, separate from any user's
    private room, so a group broadcast can never leak into a 1:1 DM room
    or vice versa."""
    return f"group_{group_id}"


def is_group_member(group_id, user_id):
    return db.session.query(
        GroupMember.query.filter_by(group_id=group_id, user_id=user_id).exists()
    ).scalar()


def is_group_admin(group_id, user_id):
    return db.session.query(
        GroupMember.query.filter_by(group_id=group_id, user_id=user_id, role="admin").exists()
    ).scalar()


def get_group_admin_count(group_id):
    return GroupMember.query.filter_by(group_id=group_id, role="admin").count()


def get_user_group_ids(user_id):
    return [
        row[0] for row in
        db.session.query(GroupMember.group_id).filter(GroupMember.user_id == user_id).all()
    ]


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


def create_notification(user_id, actor_id=None, ntype=None, post_id=None,
                         story_id=None, group_id=None, message_id=None,
                         group_message_id=None):
    """Creates one Notification row for `user_id` and pushes it live over
    Socket.IO to their private room, so the bell badge counts up instantly
    without the client having to poll. Never notifies someone about their
    own action (liking your own post, reacting to your own message, etc.)
    since actor_id == user_id in that case just means you triggered it.
    Failures are logged and swallowed rather than raised — a notification
    is a nice-to-have side effect of the real action (the like/comment/
    follow/etc. itself already succeeded by the time this is called), so
    it should never turn an otherwise-successful request into a 500."""
    if actor_id is not None and actor_id == user_id:
        return None

    try:
        notif = Notification(
            user_id=user_id,
            actor_id=actor_id,
            type=ntype,
            post_id=post_id,
            story_id=story_id,
            group_id=group_id,
            message_id=message_id,
            group_message_id=group_message_id,
        )
        db.session.add(notif)
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to create notification (type=%s, user_id=%s)", ntype, user_id)
        return None

    socketio.emit("new_notification", notif.to_dict(), room=get_room_name(user_id))
    return notif


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
        cloudinary_mirror_delete(f"story_photos/{story.image_path}")
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
# Voice call tracking (in-memory, same reasoning as _online_counts above —
# single gunicorn worker, so there's only ever one process for this to
# live in) + the call-log Message / call_* Notification rows it produces.
# -------------------------------------------------------------------
# call_id -> {"caller_id", "callee_id", "invited_at", "answered_at"}
_active_calls = {}


def format_call_log_text(message, viewer_id):
    """Human-readable preview of a message_type == 'call' Message, from
    `viewer_id`'s point of view (caller sees 'No answer', the callee sees
    'Missed voice call' for that exact same row)."""
    try:
        meta = json.loads(message.content)
    except (TypeError, ValueError):
        meta = {}
    status = meta.get("call_status")
    is_caller = viewer_id == message.sender_id

    if status == "completed":
        return f"📞 Voice call · {format_call_duration(meta.get('duration'))}"
    if is_caller:
        return "📞 Call declined" if status == "declined" else "📞 No answer"
    return "📞 Missed voice call"


def _finalize_call(call_id, status):
    """Pops the in-progress call record for `call_id` (if any) and turns it
    into a permanent call-log Message row — visible inside the 1:1
    conversation exactly like any other message — plus one call_missed/
    call_received notification for the callee and one call_outgoing
    notification for the caller, so the outcome also surfaces in the
    notification bell for whichever side wasn't actively looking at this
    conversation. `status` is 'completed', 'declined', or 'no_answer'.
    No-ops if the call was already finalized (e.g. call_reject already
    logged it before call_end arrived) or never existed."""
    record = _active_calls.pop(call_id, None)
    if not record:
        return

    caller_id = record["caller_id"]
    callee_id = record["callee_id"]
    duration = None
    if status == "completed" and record.get("answered_at"):
        duration = int((datetime.utcnow() - record["answered_at"]).total_seconds())

    try:
        message = Message(
            sender_id=caller_id,
            recipient_id=callee_id,
            content=json.dumps({"call_status": status, "duration": duration}),
            message_type="call",
            is_read=True,
        )
        db.session.add(message)
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to save call-log message (call_id=%s)", call_id)
        return

    payload = message.to_dict()
    caller = User.query.get(caller_id)
    payload["sender_username"] = caller.username if caller else None
    payload["sender_profile_pic"] = caller.profile_pic if caller else None
    socketio.emit("receive_message", payload, room=get_room_name(callee_id))
    socketio.emit("receive_message", payload, room=get_room_name(caller_id))

    create_notification(
        user_id=callee_id,
        actor_id=caller_id,
        ntype="call_received" if status == "completed" else "call_missed",
        message_id=message.id,
    )
    create_notification(
        user_id=caller_id,
        actor_id=callee_id,
        ntype="call_outgoing",
        message_id=message.id,
    )


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
            # (see Message.content); call messages get a similar human
            # summary computed from their JSON content instead of the raw
            # {"call_status": ..., "duration": ...} string.
            "text": format_call_log_text(m, current_user.id) if m.message_type == "call" else m.content,
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
        feed_unread_count=get_feed_unread_count(current_user.id, current_user.last_feed_view_at),
        notifications_unread_count=Notification.query.filter_by(
            user_id=current_user.id, is_read=False
        ).count(),
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


@app.route("/forgot-password")
def forgot_password_page():
    if current_user.is_authenticated:
        return redirect(url_for("index"))
    return _no_store(render_template("forgot_password.html"))


# -------------------------------------------------------------------
# Authentication API Routes (JSON)
# -------------------------------------------------------------------
@app.route("/api/register/start", methods=["POST"])
@limiter.limit("6 per hour")
def register_start():
    """Step 1 of signup: validate name/email/password, email a 6-digit
    code, and stash everything needed to finish the job in
    PendingRegistration. No User row exists yet — that only happens once
    the code is confirmed in /api/register/verify. There's no username
    field here anymore; one is generated automatically once the account
    is actually created."""
    data = request.get_json(silent=True) or request.form

    full_name = (data.get("full_name") or "").strip()
    email = (data.get("email") or "").strip().lower()
    password = data.get("password") or ""

    full_name_error = validate_full_name(full_name)
    if full_name_error:
        return jsonify({"error": full_name_error}), 400

    email_error = validate_email(email)
    if email_error:
        return jsonify({"error": email_error}), 400

    password_error = validate_password(password)
    if password_error:
        return jsonify({"error": password_error}), 400

    if User.query.filter(func.lower(User.email) == email).first():
        return jsonify({"error": "An account with that email already exists."}), 409

    now = datetime.utcnow()
    code = generate_otp_code()

    try:
        send_otp_email(email, code, full_name)
    except Exception:
        logger.exception("Failed to send verification email to %s", email)
        return jsonify({"error": "Could not send verification email. Please try again."}), 502

    try:
        # Starting a new signup for this email replaces any previous
        # pending attempt (abandoned, expired, or otherwise) rather than
        # erroring on the unique constraint — a person retrying a typo'd
        # signup shouldn't get stuck.
        pending = PendingRegistration.query.filter_by(email=email).first()
        if pending is None:
            pending = PendingRegistration(email=email)
            db.session.add(pending)

        pending.full_name = full_name
        pending.password_hash = generate_password_hash(password)
        pending.otp_code = code
        pending.otp_expires_at = now + timedelta(minutes=OTP_EXPIRY_MINUTES)
        pending.attempts = 0
        pending.last_sent_at = now
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to store pending registration for %s", email)
        return jsonify({"error": "Something went wrong. Please try again."}), 500

    logger.info("Verification code sent for pending registration: %s", email)
    return jsonify({
        "message": "Verification code sent.",
        "email": email,
        "expires_in_minutes": OTP_EXPIRY_MINUTES,
    }), 200


@app.route("/api/register/resend", methods=["POST"])
@limiter.limit("6 per hour")
def register_resend():
    """Re-sends a fresh code for an in-progress signup, subject to a short
    cooldown so the resend link can't be used to spam someone's inbox."""
    data = request.get_json(silent=True) or request.form
    email = (data.get("email") or "").strip().lower()

    pending = PendingRegistration.query.filter_by(email=email).first()
    if not pending:
        return jsonify({"error": "No pending signup found for that email. Please start over."}), 404

    seconds_since_last_send = (datetime.utcnow() - pending.last_sent_at).total_seconds()
    if seconds_since_last_send < OTP_RESEND_COOLDOWN_SECONDS:
        wait = int(OTP_RESEND_COOLDOWN_SECONDS - seconds_since_last_send)
        return jsonify({"error": f"Please wait {wait}s before requesting another code.", "retry_after": wait}), 429

    code = generate_otp_code()
    try:
        send_otp_email(email, code, pending.full_name)
    except Exception:
        logger.exception("Failed to resend verification email to %s", email)
        return jsonify({"error": "Could not send verification email. Please try again."}), 502

    try:
        pending.otp_code = code
        pending.otp_expires_at = datetime.utcnow() + timedelta(minutes=OTP_EXPIRY_MINUTES)
        pending.attempts = 0
        pending.last_sent_at = datetime.utcnow()
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to update pending registration for %s", email)
        return jsonify({"error": "Something went wrong. Please try again."}), 500

    return jsonify({"message": "Verification code sent.", "expires_in_minutes": OTP_EXPIRY_MINUTES}), 200


@app.route("/api/register/verify", methods=["POST"])
@limiter.limit("20 per hour")
def register_verify():
    """Step 2 of signup: checks the emailed code and, only once it's
    correct, actually creates the User row (with an auto-generated
    username — see generate_unique_username)."""
    data = request.get_json(silent=True) or request.form
    email = (data.get("email") or "").strip().lower()
    code = (data.get("code") or "").strip()

    pending = PendingRegistration.query.filter_by(email=email).first()
    if not pending:
        return jsonify({"error": "No pending signup found for that email. Please start over."}), 404

    if pending.is_expired():
        db.session.delete(pending)
        db.session.commit()
        return jsonify({"error": "That code has expired. Please request a new one."}), 410

    if pending.attempts >= OTP_MAX_ATTEMPTS:
        db.session.delete(pending)
        db.session.commit()
        return jsonify({"error": "Too many incorrect attempts. Please request a new code."}), 429

    if not code or code != pending.otp_code:
        pending.attempts += 1
        db.session.commit()
        remaining = max(OTP_MAX_ATTEMPTS - pending.attempts, 0)
        return jsonify({"error": "Incorrect code.", "attempts_remaining": remaining}), 400

    # Code matches — this is now a real, uniqueness-safe email (nobody else
    # could have registered it while it sat pending, since /api/register/
    # start already checked and this whole route only runs after that).
    if User.query.filter(func.lower(User.email) == email).first():
        db.session.delete(pending)
        db.session.commit()
        return jsonify({"error": "An account with that email already exists."}), 409

    username = generate_unique_username(email, pending.full_name)

    # Same first-account-ever admin/verified bootstrap as before — see the
    # longer comment this used to have in the old single-step /api/register.
    is_first_account_ever = User.query.count() == 0

    try:
        user = User(username=username, email=email, full_name=pending.full_name)
        user.password_hash = pending.password_hash
        user.last_feed_view_at = datetime.utcnow()
        if is_first_account_ever:
            user.is_admin = True
            user.is_verified = True
            user.verified_at = datetime.utcnow()
        db.session.add(user)
        db.session.delete(pending)
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to create user after OTP verification")
        return jsonify({"error": "Could not create account. Please try again."}), 500

    login_user(user)
    logger.info("New user registered (email verified): %s", user.username)
    return jsonify({"message": "Registered successfully.", "user": user.to_dict(include_email=True)}), 201


@app.route("/api/password-reset/start", methods=["POST"])
@limiter.limit("6 per hour")
def password_reset_start():
    """Step 1 of password reset: emails a 6-digit code if — and only
    if — the address belongs to a real account. Always returns the same
    generic success message either way (unlike /api/register/start, which
    can safely reveal "that email is taken" because that's not a login
    credential) so this endpoint can't be used to check which emails have
    a Zoble account."""
    data = request.get_json(silent=True) or request.form
    email = (data.get("email") or "").strip().lower()

    email_error = validate_email(email)
    if email_error:
        return jsonify({"error": email_error}), 400

    generic_response = jsonify({
        "message": "If an account exists for that email, a reset code has been sent.",
        "email": email,
        "expires_in_minutes": OTP_EXPIRY_MINUTES,
    })

    user = User.query.filter(func.lower(User.email) == email).first()
    if not user:
        # No account — say nothing further, but still look and feel like
        # a success response so the timing/shape can't be used to probe.
        return generic_response, 200

    now = datetime.utcnow()
    code = generate_otp_code()

    try:
        send_password_reset_email(email, code, user.full_name)
    except Exception:
        logger.exception("Failed to send password reset email to %s", email)
        return jsonify({"error": "Could not send reset email. Please try again."}), 502

    try:
        reset = PasswordReset.query.filter_by(email=email).first()
        if reset is None:
            reset = PasswordReset(email=email, user_id=user.id)
            db.session.add(reset)

        reset.user_id = user.id
        reset.otp_code = code
        reset.otp_expires_at = now + timedelta(minutes=OTP_EXPIRY_MINUTES)
        reset.attempts = 0
        reset.last_sent_at = now
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to store password reset request for %s", email)
        return jsonify({"error": "Something went wrong. Please try again."}), 500

    logger.info("Password reset code sent for: %s", email)
    return generic_response, 200


@app.route("/api/password-reset/resend", methods=["POST"])
@limiter.limit("6 per hour")
def password_reset_resend():
    """Re-sends a fresh code for an in-progress reset, subject to the same
    short cooldown as /api/register/resend. Only ever called after the
    person already went through /start with this exact email, so — same
    as register_resend — confirming whether a row exists here doesn't
    leak anything new."""
    data = request.get_json(silent=True) or request.form
    email = (data.get("email") or "").strip().lower()

    reset = PasswordReset.query.filter_by(email=email).first()
    if not reset:
        return jsonify({"error": "No pending reset found for that email. Please start over."}), 404

    seconds_since_last_send = (datetime.utcnow() - reset.last_sent_at).total_seconds()
    if seconds_since_last_send < OTP_RESEND_COOLDOWN_SECONDS:
        wait = int(OTP_RESEND_COOLDOWN_SECONDS - seconds_since_last_send)
        return jsonify({"error": f"Please wait {wait}s before requesting another code.", "retry_after": wait}), 429

    code = generate_otp_code()
    try:
        send_password_reset_email(email, code, reset.user.full_name if reset.user else "")
    except Exception:
        logger.exception("Failed to resend password reset email to %s", email)
        return jsonify({"error": "Could not send reset email. Please try again."}), 502

    try:
        reset.otp_code = code
        reset.otp_expires_at = datetime.utcnow() + timedelta(minutes=OTP_EXPIRY_MINUTES)
        reset.attempts = 0
        reset.last_sent_at = datetime.utcnow()
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to update password reset request for %s", email)
        return jsonify({"error": "Something went wrong. Please try again."}), 500

    return jsonify({"message": "Reset code sent.", "expires_in_minutes": OTP_EXPIRY_MINUTES}), 200


@app.route("/api/password-reset/verify", methods=["POST"])
@limiter.limit("20 per hour")
def password_reset_verify():
    """Step 2 of password reset: checks the emailed code and, only once
    it's correct, sets the account's new password in this same request —
    a one-shot code rather than issuing a separate reset token, same
    trust model as /api/register/verify's code-completes-the-action
    design."""
    data = request.get_json(silent=True) or request.form
    email = (data.get("email") or "").strip().lower()
    code = (data.get("code") or "").strip()
    new_password = data.get("new_password") or ""

    reset = PasswordReset.query.filter_by(email=email).first()
    if not reset:
        return jsonify({"error": "No pending reset found for that email. Please start over."}), 404

    if reset.is_expired():
        db.session.delete(reset)
        db.session.commit()
        return jsonify({"error": "That code has expired. Please request a new one."}), 410

    if reset.attempts >= OTP_MAX_ATTEMPTS:
        db.session.delete(reset)
        db.session.commit()
        return jsonify({"error": "Too many incorrect attempts. Please request a new code."}), 429

    if not code or code != reset.otp_code:
        reset.attempts += 1
        db.session.commit()
        remaining = max(OTP_MAX_ATTEMPTS - reset.attempts, 0)
        return jsonify({"error": "Incorrect code.", "attempts_remaining": remaining}), 400

    password_error = validate_password(new_password)
    if password_error:
        return jsonify({"error": password_error}), 400

    user = User.query.get(reset.user_id)
    if not user:
        # The account was deleted mid-reset — vanishingly rare, but leave
        # nothing dangling.
        db.session.delete(reset)
        db.session.commit()
        return jsonify({"error": "That account no longer exists."}), 404

    try:
        user.set_password(new_password)
        db.session.delete(reset)
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to update password after OTP verification for %s", email)
        return jsonify({"error": "Could not reset password. Please try again."}), 500

    # Deliberately not logging the person in here (unlike register_verify) —
    # a password reset is exactly the moment to make sure the next session
    # starts with a fresh, explicit login using the new password.
    logger.info("Password reset completed for: %s", user.username)
    return jsonify({"message": "Password reset successfully."}), 200


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

    # Broadcast to every connected client (not just the current user's own
    # tabs) so this account's display name updates everywhere it appears —
    # the chat sidebar, conversation headers, group member lists, story
    # rings, and any already-loaded feed posts/comments — without those
    # other clients needing to refresh. Chat and the news feed both read
    # identity straight off the User row (see Post.to_dict()), so this is
    # what keeps them showing the same name for the same account instead of
    # a stale one lingering wherever it was cached client-side.
    socketio.emit("profile_updated", {
        "user_id": current_user.id,
        "full_name": current_user.full_name,
        "profile_pic": current_user.profile_pic,
        "is_verified": bool(current_user.is_verified),
        "is_admin": bool(current_user.is_admin),
    })

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


@app.route("/api/users/<int:user_id>/profile", methods=["GET"])
@login_required
def get_user_account_page(user_id):
    """Fetches the data behind the account page opened by tapping a name or
    avatar in the news feed — the base user fields plus follower/following
    counts and whether the current viewer already follows them."""
    user = User.query.get(user_id)
    if not user:
        return jsonify({"error": "User not found."}), 404

    data = user.to_dict()
    data["follower_count"] = user.followers.count()
    data["following_count"] = user.following.count()
    data["is_own"] = user.id == current_user.id
    data["is_following"] = (
        not data["is_own"]
        and Follow.query.filter_by(follower_id=current_user.id, followed_id=user.id).first() is not None
    )
    return jsonify({"user": data}), 200


@app.route("/api/users/<int:user_id>/posts", methods=["GET"])
@login_required
def list_user_posts(user_id):
    """Cursor-paginated, same shape/pagination as GET /api/posts, but scoped
    to a single account — this is what fills the post list on the account
    page opened by tapping a name/avatar in the news feed. Pass
    ?before_id=<id> for the next older page. Includes that user's reposts
    (each is its own Post row), same as the main feed, so the account page
    reflects everything they've shared, not just what they originally wrote."""
    user = User.query.get(user_id)
    if not user:
        return jsonify({"error": "User not found."}), 404

    before_id = request.args.get("before_id", type=int)

    query = Post.query.filter_by(user_id=user_id)
    if before_id:
        query = query.filter(Post.id < before_id)

    posts = query.order_by(Post.id.desc()).limit(POST_FEED_PAGE_SIZE).all()

    return jsonify({
        "posts": [p.to_dict(viewer_id=current_user.id) for p in posts],
        "has_more": len(posts) == POST_FEED_PAGE_SIZE,
    }), 200


@app.route("/api/users/<int:user_id>/follow", methods=["POST"])
@login_required
@limiter.limit("100 per hour")
def toggle_follow(user_id):
    """Toggles the current user following user_id — send it again to
    unfollow, same toggle pattern as like_post / react_to_story."""
    if user_id == current_user.id:
        return jsonify({"error": "You can't follow yourself."}), 400

    target = User.query.get(user_id)
    if not target:
        return jsonify({"error": "User not found."}), 404

    existing = Follow.query.filter_by(follower_id=current_user.id, followed_id=user_id).first()

    try:
        if existing:
            db.session.delete(existing)
            following = False
        else:
            db.session.add(Follow(follower_id=current_user.id, followed_id=user_id))
            following = True
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to toggle follow")
        return jsonify({"error": "Could not update follow status. Please try again."}), 500

    follower_count = target.followers.count()

    if following:
        create_notification(user_id=user_id, actor_id=current_user.id, ntype="follow")

    socketio.emit("follow_updated", {
        "follower_id": current_user.id,
        "followed_id": user_id,
        "following": following,
        "follower_count": follower_count,
    })

    return jsonify({"following": following, "follower_count": follower_count}), 200


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

    cloudinary_mirror_upload(filepath, unique_name)

    # Clean up the old file, but never delete the shared default avatar.
    if old_pic and old_pic != "default.png":
        old_path = os.path.join(app.config["UPLOAD_FOLDER"], old_pic)
        if os.path.exists(old_path):
            try:
                os.remove(old_path)
            except OSError:
                logger.warning("Could not remove old profile picture: %s", old_pic)
        cloudinary_mirror_delete(old_pic)

    # Same reasoning as the full_name broadcast in update_profile() above —
    # one account, one photo, shown consistently everywhere it's referenced
    # (chat sidebar, headers, group members, stories, feed posts/comments)
    # without waiting on a page reload.
    socketio.emit("profile_updated", {
        "user_id": current_user.id,
        "full_name": current_user.full_name,
        "profile_pic": current_user.profile_pic,
        "is_verified": bool(current_user.is_verified),
        "is_admin": bool(current_user.is_admin),
    })

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

    cloudinary_mirror_upload(filepath, f"chat_photos/{unique_name}")

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

    if my_reaction is not None and current_user.id != message.sender_id:
        create_notification(
            user_id=message.sender_id, actor_id=current_user.id,
            ntype="message_reaction", message_id=message_id,
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


@app.route("/api/groups/messages/<int:message_id>/react", methods=["POST"])
@login_required
@limiter.limit("300 per hour")
def react_to_group_message(message_id):
    """Group-chat equivalent of react_to_message — same payload shape,
    same add/swap/remove toggle semantics, just scoped to "any current
    member of the group" instead of "one of the two 1:1 participants".
    """
    data = request.get_json(silent=True) or {}
    emoji = (data.get("emoji") or "").strip()

    if emoji not in ALLOWED_REACTION_EMOJIS:
        return jsonify({"error": "Unsupported reaction."}), 400

    message = GroupMessage.query.get(message_id)
    if not message:
        return jsonify({"error": "Message not found."}), 404

    if not is_group_member(message.group_id, current_user.id):
        return jsonify({"error": "You can only react to messages in your own groups."}), 403

    existing = GroupMessageReaction.query.filter_by(
        group_message_id=message_id, user_id=current_user.id
    ).first()

    try:
        if existing and existing.emoji == emoji:
            db.session.delete(existing)
            my_reaction = None
        elif existing:
            existing.emoji = emoji
            my_reaction = emoji
        else:
            db.session.add(
                GroupMessageReaction(group_message_id=message_id, user_id=current_user.id, emoji=emoji)
            )
            my_reaction = emoji
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to update group message reaction")
        return jsonify({"error": "Could not update reaction. Please try again."}), 500

    reactions = [
        {"user_id": r.user_id, "emoji": r.emoji}
        for r in message.reactions.order_by(GroupMessageReaction.created_at.asc())
    ]

    if my_reaction is not None and current_user.id != message.sender_id:
        create_notification(
            user_id=message.sender_id, actor_id=current_user.id,
            ntype="group_message_reaction", group_id=message.group_id,
            group_message_id=message_id,
        )

    # Broadcast to the whole group room (every member's open tabs, including
    # our own other tabs) rather than two individual rooms like the 1:1
    # version — a group reaction is visible to everyone in the conversation.
    socketio.emit("group_message_reacted", {
        "message_id": message_id,
        "group_id": message.group_id,
        "reactions": reactions,
    }, room=get_group_room_name(message.group_id))

    return jsonify({"my_reaction": my_reaction, "reactions": reactions}), 200


# -------------------------------------------------------------------
# Groups API Routes (JSON)
#
# A group's messages live in Socket.IO (handle_send_group_message) the
# same way 1:1 text messages do — these REST routes cover creating a
# group, listing the current user's groups, and fetching one group's
# full detail + history when its conversation is opened. Photo messages
# go through send_group_photo_message below, mirroring send_photo_message.
# -------------------------------------------------------------------
@app.route("/api/groups", methods=["POST"])
@login_required
@limiter.limit("20 per hour")
def create_group():
    """
    Expected payload:
    {
        "name": <str>,
        "member_ids": [<int>, ...]   # NOT including the creator
    }
    The creator is always added as 'admin', regardless of what's in
    member_ids — you cannot demote yourself via the request body.
    """
    data = request.get_json(silent=True) or {}
    name = (data.get("name") or "").strip()
    raw_member_ids = data.get("member_ids") or []

    if not name:
        return jsonify({"error": "Group name is required."}), 400
    if len(name) > 60:
        return jsonify({"error": "Group name must be 60 characters or fewer."}), 400
    if not isinstance(raw_member_ids, list):
        return jsonify({"error": "member_ids must be an array."}), 400
    if len(raw_member_ids) > 250:
        return jsonify({"error": "Cannot add more than 250 members at once."}), 400

    try:
        member_ids = {int(uid) for uid in raw_member_ids}
    except (TypeError, ValueError):
        return jsonify({"error": "member_ids must contain valid user ids."}), 400

    member_ids.discard(current_user.id)  # creator is added separately, as admin

    if member_ids:
        found_count = User.query.filter(User.id.in_(member_ids)).count()
        if found_count != len(member_ids):
            return jsonify({"error": "One or more member_ids do not exist."}), 400

    try:
        group = Group(name=name, created_by=current_user.id)
        db.session.add(group)
        db.session.flush()  # assigns group.id before we insert members

        db.session.add(GroupMember(group_id=group.id, user_id=current_user.id, role="admin"))
        for uid in member_ids:
            db.session.add(GroupMember(group_id=group.id, user_id=uid, role="member"))

        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to create group")
        return jsonify({"error": "Could not create group. Please try again."}), 500

    payload = group.to_dict(viewer_id=current_user.id)

    for uid in member_ids:
        create_notification(
            user_id=uid, actor_id=current_user.id, ntype="group_added", group_id=group.id
        )

    # Every member's open tabs should see the new group appear instantly,
    # same live-update principle as receive_message — join each member's
    # private room (not the group room; they haven't joined that yet from
    # the client) and push the new group there.
    for uid in member_ids | {current_user.id}:
        socketio.emit("group_created", payload, room=get_room_name(uid))

    return jsonify({"group": payload}), 201


@app.route("/api/groups", methods=["GET"])
@login_required
def list_groups():
    """All groups the current user belongs to, most recently active first."""
    my_group_ids = get_user_group_ids(current_user.id)
    groups = Group.query.filter(Group.id.in_(my_group_ids)).all() if my_group_ids else []

    def sort_key(g):
        last = g.messages.order_by(GroupMessage.timestamp.desc()).first()
        return last.timestamp if last else g.created_at

    groups.sort(key=sort_key, reverse=True)

    return jsonify({
        "groups": [g.to_dict(viewer_id=current_user.id) for g in groups]
    }), 200


@app.route("/api/groups/<int:group_id>", methods=["GET"])
@login_required
def get_group(group_id):
    """Full group detail plus message history — used when a conversation
    is opened. Only members may view a group; everyone else gets a 403
    rather than a 404, since group IDs aren't secret, only their contents."""
    group = Group.query.get(group_id)
    if not group:
        return jsonify({"error": "Group not found."}), 404

    if not is_group_member(group_id, current_user.id):
        return jsonify({"error": "You are not a member of this group."}), 403

    messages = (
        GroupMessage.query.filter_by(group_id=group_id)
        .order_by(GroupMessage.timestamp.asc())
        .all()
    )

    payload = group.to_dict(viewer_id=current_user.id)
    payload["messages"] = [m.to_dict() for m in messages]
    return jsonify({"group": payload}), 200


@app.route("/api/groups/<int:group_id>/messages/photo", methods=["POST"])
@login_required
@limiter.limit("30 per hour")
def send_group_photo_message(group_id):
    """Uploads an image and sends it to a group, mirroring send_photo_message
    for 1:1 chat — persists a GroupMessage row and broadcasts it over
    Socket.IO to the group's room so every member's open tab updates live."""
    if not is_group_member(group_id, current_user.id):
        return jsonify({"error": "You are not a member of this group."}), 403

    if "file" not in request.files:
        return jsonify({"error": "No file part in the request."}), 400

    file = request.files["file"]
    if file.filename == "":
        return jsonify({"error": "No file selected."}), 400

    if not allowed_file(file.filename):
        return jsonify({"error": "Unsupported file type. Use PNG, JPG, GIF, or WEBP."}), 400

    original_name = secure_filename(file.filename)
    ext = original_name.rsplit(".", 1)[1].lower()
    unique_name = f"{current_user.id}_{uuid.uuid4().hex}.{ext}"
    filepath = os.path.join(CHAT_PHOTOS_FOLDER, unique_name)

    try:
        file.save(filepath)
    except OSError:
        logger.exception("Failed to save uploaded group chat photo")
        return jsonify({"error": "Could not save the uploaded file."}), 500

    if not verify_is_real_image(filepath):
        try:
            os.remove(filepath)
        except OSError:
            pass
        return jsonify({"error": "The uploaded file is not a valid image."}), 400

    try:
        message = GroupMessage(
            group_id=group_id,
            sender_id=current_user.id,
            content="Photo",
            message_type="image",
            image_path=unique_name,
        )
        db.session.add(message)
        db.session.commit()
    except Exception:
        db.session.rollback()
        try:
            os.remove(filepath)
        except OSError:
            pass
        logger.exception("Failed to save group photo message")
        return jsonify({"error": "Could not send photo. Please try again."}), 500

    cloudinary_mirror_upload(filepath, f"chat_photos/{unique_name}")

    payload = message.to_dict()
    socketio.emit("new_group_message", payload, room=get_group_room_name(group_id))

    return jsonify({"message": "Photo sent.", "data": payload}), 201


@app.route("/api/groups/<int:group_id>", methods=["PATCH"])
@login_required
@limiter.limit("30 per hour")
def update_group(group_id):
    """Renames a group. Admin-only, same as changing the group photo —
    letting any member rename the group out from under everyone else is
    the kind of griefing vector a chat app has to design against."""
    group = Group.query.get(group_id)
    if not group:
        return jsonify({"error": "Group not found."}), 404

    if not is_group_member(group_id, current_user.id):
        return jsonify({"error": "You are not a member of this group."}), 403
    if not is_group_admin(group_id, current_user.id):
        return jsonify({"error": "Only a group admin can rename this group."}), 403

    data = request.get_json(silent=True) or {}
    name = (data.get("name") or "").strip()
    if not name:
        return jsonify({"error": "Group name is required."}), 400
    if len(name) > 60:
        return jsonify({"error": "Group name must be 60 characters or fewer."}), 400

    group.name = name
    try:
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to rename group")
        return jsonify({"error": "Could not rename group. Please try again."}), 500

    payload = group.to_dict(viewer_id=current_user.id)
    # Every member's open tab should see the new name immediately, in the
    # sidebar list and in an open conversation header alike.
    socketio.emit("group_updated", payload, room=get_group_room_name(group_id))

    return jsonify({"group": payload}), 200


@app.route("/api/groups/<int:group_id>/photo", methods=["POST"])
@login_required
@limiter.limit("20 per hour")
def update_group_photo(group_id):
    """Uploads/replaces a group's photo. Admin-only. Mirrors
    update_profile_picture(), just scoped to a Group instead of the
    current user, and broadcasting the change to the group's room."""
    group = Group.query.get(group_id)
    if not group:
        return jsonify({"error": "Group not found."}), 404

    if not is_group_member(group_id, current_user.id):
        return jsonify({"error": "You are not a member of this group."}), 403
    if not is_group_admin(group_id, current_user.id):
        return jsonify({"error": "Only a group admin can change this group's photo."}), 403

    if "file" not in request.files:
        return jsonify({"error": "No file part in the request."}), 400

    file = request.files["file"]
    if file.filename == "":
        return jsonify({"error": "No file selected."}), 400

    if not allowed_file(file.filename):
        return jsonify({"error": "Unsupported file type. Use PNG, JPG, GIF, or WEBP."}), 400

    # secure_filename strips path traversal characters; we also prefix with
    # "group_<id>_" + a uuid so filenames can never collide or be guessed,
    # and so a group's photo history is trivially distinguishable from any
    # user's profile picture living in the same upload folder.
    original_name = secure_filename(file.filename)
    ext = original_name.rsplit(".", 1)[1].lower()
    unique_name = f"group_{group.id}_{uuid.uuid4().hex}.{ext}"
    filepath = os.path.join(app.config["UPLOAD_FOLDER"], unique_name)

    try:
        file.save(filepath)
    except OSError:
        logger.exception("Failed to save uploaded group photo")
        return jsonify({"error": "Could not save the uploaded file."}), 500

    if not verify_is_real_image(filepath):
        try:
            os.remove(filepath)
        except OSError:
            pass
        return jsonify({"error": "The uploaded file is not a valid image."}), 400

    old_photo = group.photo
    group.photo = unique_name

    try:
        db.session.commit()
    except Exception:
        db.session.rollback()
        try:
            os.remove(filepath)
        except OSError:
            pass
        logger.exception("Failed to update group photo in DB")
        return jsonify({"error": "Could not update group photo. Please try again."}), 500

    cloudinary_mirror_upload(filepath, unique_name)

    if old_photo:
        old_path = os.path.join(app.config["UPLOAD_FOLDER"], old_photo)
        if os.path.exists(old_path):
            try:
                os.remove(old_path)
            except OSError:
                logger.warning("Could not remove old group photo: %s", old_photo)
        cloudinary_mirror_delete(old_photo)

    payload = group.to_dict(viewer_id=current_user.id)
    socketio.emit("group_updated", payload, room=get_group_room_name(group_id))

    return jsonify({"message": "Group photo updated.", "group": payload}), 200


@app.route("/api/groups/<int:group_id>/photo", methods=["DELETE"])
@login_required
@limiter.limit("20 per hour")
def remove_group_photo(group_id):
    """Clears a group's custom photo, reverting the client to the generic
    group icon. Admin-only, same reasoning as setting one."""
    group = Group.query.get(group_id)
    if not group:
        return jsonify({"error": "Group not found."}), 404

    if not is_group_member(group_id, current_user.id):
        return jsonify({"error": "You are not a member of this group."}), 403
    if not is_group_admin(group_id, current_user.id):
        return jsonify({"error": "Only a group admin can change this group's photo."}), 403

    old_photo = group.photo
    if not old_photo:
        return jsonify({"group": group.to_dict(viewer_id=current_user.id)}), 200

    group.photo = None
    try:
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to remove group photo")
        return jsonify({"error": "Could not remove group photo. Please try again."}), 500

    old_path = os.path.join(app.config["UPLOAD_FOLDER"], old_photo)
    if os.path.exists(old_path):
        try:
            os.remove(old_path)
        except OSError:
            logger.warning("Could not remove old group photo: %s", old_photo)
    cloudinary_mirror_delete(old_photo)

    payload = group.to_dict(viewer_id=current_user.id)
    socketio.emit("group_updated", payload, room=get_group_room_name(group_id))

    return jsonify({"message": "Group photo removed.", "group": payload}), 200


@app.route("/api/groups/<int:group_id>/members", methods=["POST"])
@login_required
@limiter.limit("30 per hour")
def add_group_members(group_id):
    """Adds one or more existing users to a group. Admin-only. Newly added
    members haven't joined the group's Socket.IO room yet (they only do
    that from join_group, client-side, once they know the group exists),
    so — same as create_group — we push straight to each new member's
    private room rather than the group room for the "you're in a group
    now" notification, and to the group room for everyone already there.
    """
    group = Group.query.get(group_id)
    if not group:
        return jsonify({"error": "Group not found."}), 404

    if not is_group_member(group_id, current_user.id):
        return jsonify({"error": "You are not a member of this group."}), 403
    if not is_group_admin(group_id, current_user.id):
        return jsonify({"error": "Only a group admin can add members."}), 403

    data = request.get_json(silent=True) or {}
    raw_member_ids = data.get("member_ids") or []
    if not isinstance(raw_member_ids, list):
        return jsonify({"error": "member_ids must be an array."}), 400
    if len(raw_member_ids) > 250:
        return jsonify({"error": "Cannot add more than 250 members at once."}), 400

    try:
        member_ids = {int(uid) for uid in raw_member_ids}
    except (TypeError, ValueError):
        return jsonify({"error": "member_ids must contain valid user ids."}), 400

    if not member_ids:
        return jsonify({"error": "No members to add."}), 400

    found_count = User.query.filter(User.id.in_(member_ids)).count()
    if found_count != len(member_ids):
        return jsonify({"error": "One or more member_ids do not exist."}), 400

    existing_member_ids = {
        uid for (uid,) in db.session.query(GroupMember.user_id).filter_by(group_id=group_id).all()
    }
    new_ids = member_ids - existing_member_ids
    if not new_ids:
        return jsonify({"error": "Everyone selected is already in this group."}), 400

    try:
        for uid in new_ids:
            db.session.add(GroupMember(group_id=group_id, user_id=uid, role="member"))
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to add group members")
        return jsonify({"error": "Could not add members. Please try again."}), 500

    payload = group.to_dict(viewer_id=current_user.id)

    for uid in new_ids:
        create_notification(
            user_id=uid, actor_id=current_user.id, ntype="group_added", group_id=group_id
        )

    # Existing members' open tabs get a live-updated member list/count.
    socketio.emit("group_updated", payload, room=get_group_room_name(group_id))
    # Newly added members get the group appear in their sidebar, the same
    # event create_group() uses for the initial member set.
    for uid in new_ids:
        socketio.emit("group_created", group.to_dict(viewer_id=uid), room=get_room_name(uid))

    return jsonify({"group": payload}), 200


@app.route("/api/groups/<int:group_id>/members/<int:user_id>", methods=["DELETE"])
@login_required
@limiter.limit("30 per hour")
def remove_group_member(group_id, user_id):
    """Removes another member from the group. Admin-only, and not usable
    on yourself — that's what POST /api/groups/<id>/leave is for, which
    also handles the "I'm the last admin" succession logic that a forced
    removal never needs to."""
    group = Group.query.get(group_id)
    if not group:
        return jsonify({"error": "Group not found."}), 404

    if not is_group_member(group_id, current_user.id):
        return jsonify({"error": "You are not a member of this group."}), 403
    if not is_group_admin(group_id, current_user.id):
        return jsonify({"error": "Only a group admin can remove members."}), 403

    if user_id == current_user.id:
        return jsonify({"error": "Use 'Leave group' to remove yourself."}), 400

    member = GroupMember.query.filter_by(group_id=group_id, user_id=user_id).first()
    if not member:
        return jsonify({"error": "That user is not a member of this group."}), 404

    try:
        db.session.delete(member)
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to remove group member")
        return jsonify({"error": "Could not remove member. Please try again."}), 500

    payload = group.to_dict(viewer_id=current_user.id)
    socketio.emit("group_updated", payload, room=get_group_room_name(group_id))
    # Tell the removed member's own tabs directly — they're no longer a
    # member, so they won't get the group_updated broadcast above (it only
    # reaches the group's Socket.IO room, which client-side leave logic
    # only triggers on *this* event, not the other way around).
    socketio.emit(
        "group_member_removed",
        {"group_id": group_id, "user_id": user_id, "removed_by": current_user.id},
        room=get_room_name(user_id),
    )

    return jsonify({"group": payload}), 200


@app.route("/api/groups/<int:group_id>/members/<int:user_id>/role", methods=["PATCH"])
@login_required
@limiter.limit("30 per hour")
def change_group_member_role(group_id, user_id):
    """Promotes a member to admin or demotes an admin to member.
    Admin-only. Demoting the group's last remaining admin is blocked —
    that would leave the group with nobody able to manage it (rename,
    change photo, add/remove members) short of a database edit."""
    group = Group.query.get(group_id)
    if not group:
        return jsonify({"error": "Group not found."}), 404

    if not is_group_member(group_id, current_user.id):
        return jsonify({"error": "You are not a member of this group."}), 403
    if not is_group_admin(group_id, current_user.id):
        return jsonify({"error": "Only a group admin can change member roles."}), 403

    data = request.get_json(silent=True) or {}
    role = data.get("role")
    if role not in ("admin", "member"):
        return jsonify({"error": "role must be 'admin' or 'member'."}), 400

    member = GroupMember.query.filter_by(group_id=group_id, user_id=user_id).first()
    if not member:
        return jsonify({"error": "That user is not a member of this group."}), 404

    if member.role == role:
        return jsonify({"group": group.to_dict(viewer_id=current_user.id)}), 200

    if member.role == "admin" and role == "member" and get_group_admin_count(group_id) <= 1:
        return jsonify({
            "error": "This is the only admin left. Promote someone else to admin first."
        }), 400

    member.role = role
    try:
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to change group member role")
        return jsonify({"error": "Could not update that member's role. Please try again."}), 500

    payload = group.to_dict(viewer_id=current_user.id)
    socketio.emit("group_updated", payload, room=get_group_room_name(group_id))

    return jsonify({"group": payload}), 200


@app.route("/api/groups/<int:group_id>/leave", methods=["POST"])
@login_required
@limiter.limit("30 per hour")
def leave_group(group_id):
    """Removes the current user from a group. If they're the group's last
    remaining member, the group (and its messages/photo) is deleted
    outright. If they're the sole admin with other members still present,
    the longest-standing remaining member is auto-promoted to admin so
    the group is never left with zero admins — same reasoning as the
    block in change_group_member_role()."""
    group = Group.query.get(group_id)
    if not group:
        return jsonify({"error": "Group not found."}), 404

    member = GroupMember.query.filter_by(group_id=group_id, user_id=current_user.id).first()
    if not member:
        return jsonify({"error": "You are not a member of this group."}), 403

    remaining = (
        GroupMember.query.filter(GroupMember.group_id == group_id, GroupMember.user_id != current_user.id)
        .order_by(GroupMember.joined_at.asc())
        .all()
    )
    was_last_admin = member.role == "admin" and get_group_admin_count(group_id) <= 1
    promoted_user_id = None
    group_deleted = False

    try:
        if not remaining:
            # Last member out deletes the group entirely, including its
            # message history — nobody's left to read it, and there's no
            # "restore a group" flow to keep it around for.
            group_photo = group.photo
            db.session.delete(group)
            db.session.commit()
            group_deleted = True
            if group_photo:
                old_path = os.path.join(app.config["UPLOAD_FOLDER"], group_photo)
                if os.path.exists(old_path):
                    try:
                        os.remove(old_path)
                    except OSError:
                        logger.warning("Could not remove group photo for deleted group: %s", group_photo)
                cloudinary_mirror_delete(group_photo)
        else:
            if was_last_admin:
                successor = remaining[0]
                successor.role = "admin"
                promoted_user_id = successor.user_id
            db.session.delete(member)
            db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to process leave-group request")
        return jsonify({"error": "Could not leave group. Please try again."}), 500

    if group_deleted:
        # Nobody's left to notify over the group room (everyone already
        # left it), but the leaving user's own other open tabs still need
        # to drop the group from their sidebar.
        socketio.emit(
            "group_member_removed",
            {"group_id": group_id, "user_id": current_user.id, "removed_by": current_user.id},
            room=get_room_name(current_user.id),
        )
    else:
        payload = group.to_dict()
        socketio.emit("group_updated", payload, room=get_group_room_name(group_id))
        socketio.emit(
            "group_member_removed",
            {"group_id": group_id, "user_id": current_user.id, "removed_by": current_user.id},
            room=get_room_name(current_user.id),
        )
        if promoted_user_id:
            socketio.emit(
                "group_member_role_changed",
                {"group_id": group_id, "user_id": promoted_user_id, "role": "admin"},
                room=get_group_room_name(group_id),
            )

    return jsonify({"message": "Left group.", "group_deleted": group_deleted}), 200


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

    cloudinary_mirror_upload(filepath, f"story_photos/{unique_name}")

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
    cloudinary_mirror_delete(f"story_photos/{story.image_path}")

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

    if reacted:
        create_notification(
            user_id=story.user_id, actor_id=current_user.id, ntype="story_reaction", story_id=story_id
        )

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


# -------------------------------------------------------------------
# Feed posts — text and/or photo, permanent, with likes/comments/shares.
# Unlike stories these never expire and are visible to every user, the
# same audience as a normal public news feed.
# -------------------------------------------------------------------
def get_feed_unread_count(user_id, since):
    """Count of feed posts by other users created after `since` (a user's
    last_feed_view_at watermark, or None if they've never opened the feed
    yet, in which case every post by someone else counts)."""
    query = Post.query.filter(Post.user_id != user_id)
    if since is not None:
        query = query.filter(Post.created_at > since)
    return query.count()


@app.route("/api/posts/unread-count", methods=["GET"])
@login_required
def feed_unread_count():
    """Lightweight poll endpoint for the feed badge — lets the client
    resync (e.g. after reconnecting) instead of trusting only the running
    client-side tally built from Socket.IO events."""
    count = get_feed_unread_count(current_user.id, current_user.last_feed_view_at)
    return jsonify({"unread_count": count}), 200


@app.route("/api/posts/mark-seen", methods=["POST"])
@login_required
def mark_feed_seen():
    """Called when the user opens the feed overlay — resets their unread
    watermark to now, same moment as when the feed's contents are actually
    on screen in front of them."""
    current_user.last_feed_view_at = datetime.utcnow()
    try:
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to update last_feed_view_at")
        return jsonify({"error": "Could not update feed status."}), 500
    return jsonify({"message": "Feed marked as seen."}), 200


# -------------------------------------------------------------------
# Notifications — a bell icon next to the news feed icon, live-updated
# over Socket.IO ("new_notification") whenever create_notification() fires
# from a like/comment/share/follow/reaction/group-add elsewhere in this
# file. Unlike the feed's single watermark, each notification keeps its
# own is_read flag so the dropdown can tell individual items apart.
# -------------------------------------------------------------------
@app.route("/api/notifications", methods=["GET"])
@login_required
def list_notifications():
    """Cursor-paginated: pass ?before_id=<id> to fetch the page of
    notifications older than that one, same pattern as /api/posts."""
    before_id = request.args.get("before_id", type=int)

    query = Notification.query.filter_by(user_id=current_user.id)
    if before_id:
        query = query.filter(Notification.id < before_id)

    page_size = 30
    rows = query.order_by(Notification.id.desc()).limit(page_size + 1).all()
    has_more = len(rows) > page_size
    rows = rows[:page_size]

    return jsonify({
        "notifications": [n.to_dict() for n in rows],
        "has_more": has_more,
    }), 200


@app.route("/api/notifications/unread-count", methods=["GET"])
@login_required
def notifications_unread_count():
    """Lightweight poll endpoint for the bell badge — lets the client
    resync (e.g. after reconnecting) instead of trusting only the running
    client-side tally built from Socket.IO events, same role
    /api/posts/unread-count plays for the feed badge."""
    count = Notification.query.filter_by(user_id=current_user.id, is_read=False).count()
    return jsonify({"unread_count": count}), 200


@app.route("/api/notifications/mark-seen", methods=["POST"])
@login_required
def mark_notifications_seen():
    """Called when the notifications dropdown is opened — flips every
    currently-unread notification for this user to read, all at once
    (there's no per-item mark-read affordance in the UI, only "open the
    panel" the way opening a group/1:1 conversation marks its messages read)."""
    try:
        updated_count = (
            Notification.query.filter_by(user_id=current_user.id, is_read=False)
            .update({"is_read": True})
        )
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to mark notifications as seen")
        return jsonify({"error": "Could not update notification status."}), 500

    return jsonify({"message": "Notifications marked as seen.", "count": updated_count}), 200


@app.route("/api/posts", methods=["GET"])
@login_required
def list_posts():
    """Cursor-paginated: pass ?before_id=<id> to fetch the page of posts
    older than that id. Without it, returns the newest page. Ordered
    newest-first so the swipeable feed always opens on the latest post."""
    before_id = request.args.get("before_id", type=int)

    query = Post.query
    if before_id:
        query = query.filter(Post.id < before_id)

    posts = query.order_by(Post.id.desc()).limit(POST_FEED_PAGE_SIZE).all()

    return jsonify({
        "posts": [p.to_dict(viewer_id=current_user.id) for p in posts],
        "has_more": len(posts) == POST_FEED_PAGE_SIZE,
    }), 200


@app.route("/api/posts", methods=["POST"])
@login_required
@limiter.limit("30 per hour")
def create_post():
    """Accepts multipart/form-data with an optional 'text' field and an
    optional 'file' field — at least one of the two is required, so a
    post is never completely empty."""
    text = (request.form.get("text") or "").strip()
    file = request.files.get("file")
    has_file = file is not None and file.filename != ""

    if not text and not has_file:
        return jsonify({"error": "A post needs text, a photo, or both."}), 400

    if len(text) > POST_TEXT_MAX_LENGTH:
        return jsonify({"error": f"Post text can't exceed {POST_TEXT_MAX_LENGTH} characters."}), 400

    unique_name = None
    if has_file:
        if not allowed_file(file.filename):
            return jsonify({"error": "Unsupported file type. Use PNG, JPG, GIF, or WEBP."}), 400

        original_name = secure_filename(file.filename)
        ext = original_name.rsplit(".", 1)[1].lower()
        unique_name = f"{current_user.id}_{uuid.uuid4().hex}.{ext}"
        filepath = os.path.join(POST_PHOTOS_FOLDER, unique_name)

        try:
            file.save(filepath)
        except OSError:
            logger.exception("Failed to save uploaded post photo")
            return jsonify({"error": "Could not save the uploaded file."}), 500

        if not verify_is_real_image(filepath):
            try:
                os.remove(filepath)
            except OSError:
                pass
            return jsonify({"error": "The uploaded file is not a valid image."}), 400

    post = Post(user_id=current_user.id, text=text or None, image_path=unique_name)

    try:
        db.session.add(post)
        db.session.commit()
    except Exception:
        db.session.rollback()
        if unique_name:
            try:
                os.remove(os.path.join(POST_PHOTOS_FOLDER, unique_name))
            except OSError:
                pass
        logger.exception("Failed to save post")
        return jsonify({"error": "Could not create post. Please try again."}), 500

    if unique_name:
        cloudinary_mirror_upload(os.path.join(POST_PHOTOS_FOLDER, unique_name), f"post_photos/{unique_name}")

    payload = post.to_dict(viewer_id=current_user.id)
    # Broadcast to every connected client — the feed is public, unlike
    # stories which only fan out to conversation partners.
    socketio.emit("new_post", payload)

    return jsonify({"message": "Post created.", "data": payload}), 201


@app.route("/api/posts/<int:post_id>", methods=["DELETE"])
@login_required
def delete_post(post_id):
    post = Post.query.get(post_id)
    if not post:
        return jsonify({"error": "Post not found."}), 404
    if post.user_id != current_user.id:
        return jsonify({"error": "You can only delete your own posts."}), 403

    image_path = post.image_path

    try:
        db.session.delete(post)
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to delete post")
        return jsonify({"error": "Could not delete post. Please try again."}), 500

    if image_path:
        filepath = os.path.join(POST_PHOTOS_FOLDER, image_path)
        try:
            if os.path.exists(filepath):
                os.remove(filepath)
        except OSError:
            logger.warning("Could not remove deleted post image: %s", image_path)
        cloudinary_mirror_delete(f"post_photos/{image_path}")

    socketio.emit("post_deleted", {"post_id": post_id})

    return jsonify({"message": "Post deleted."}), 200


@app.route("/api/posts/<int:post_id>/like", methods=["POST"])
@login_required
@limiter.limit("300 per hour")
def like_post(post_id):
    """Toggles a like on this post for the current user — send it again
    to un-like, same toggle pattern as react_to_story."""
    post = Post.query.get(post_id)
    if not post:
        return jsonify({"error": "Post not found."}), 404

    existing = PostLike.query.filter_by(post_id=post_id, user_id=current_user.id).first()

    try:
        if existing:
            db.session.delete(existing)
            liked = False
        else:
            db.session.add(PostLike(post_id=post_id, user_id=current_user.id))
            liked = True
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to toggle post like")
        return jsonify({"error": "Could not update like. Please try again."}), 500

    like_count = post.likes.count()

    if liked:
        create_notification(
            user_id=post.user_id, actor_id=current_user.id, ntype="post_like", post_id=post_id
        )

    socketio.emit("post_liked", {
        "post_id": post_id,
        "liker_id": current_user.id,
        "liker_username": current_user.username,
        "liked": liked,
        "like_count": like_count,
    })

    return jsonify({"liked": liked, "like_count": like_count}), 200


@app.route("/api/posts/<int:post_id>/comments", methods=["GET"])
@login_required
def list_post_comments(post_id):
    post = Post.query.get(post_id)
    if not post:
        return jsonify({"error": "Post not found."}), 404

    comments = post.comments.order_by(PostComment.created_at.asc()).all()
    return jsonify({"comments": [c.to_dict() for c in comments]}), 200


@app.route("/api/posts/<int:post_id>/comments", methods=["POST"])
@login_required
@limiter.limit("120 per hour")
def add_post_comment(post_id):
    post = Post.query.get(post_id)
    if not post:
        return jsonify({"error": "Post not found."}), 404

    data = request.get_json(silent=True) or {}
    text = (data.get("text") or "").strip()
    if not text:
        return jsonify({"error": "Comment can't be empty."}), 400
    if len(text) > POST_COMMENT_MAX_LENGTH:
        return jsonify({"error": f"Comment can't exceed {POST_COMMENT_MAX_LENGTH} characters."}), 400

    comment = PostComment(post_id=post_id, user_id=current_user.id, text=text)

    try:
        db.session.add(comment)
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to save post comment")
        return jsonify({"error": "Could not post comment. Please try again."}), 500

    payload = comment.to_dict()
    payload["comment_count"] = post.comments.count()

    create_notification(
        user_id=post.user_id, actor_id=current_user.id, ntype="post_comment", post_id=post_id
    )

    socketio.emit("post_commented", payload)

    return jsonify({"message": "Comment posted.", "data": payload}), 201


@app.route("/api/posts/<int:post_id>/share", methods=["POST"])
@login_required
@limiter.limit("120 per hour")
def share_post(post_id):
    """Just increments a counter — the actual share action (native share
    sheet or copy-link) happens client-side; this is what makes the
    share count visible to everyone else."""
    post = Post.query.get(post_id)
    if not post:
        return jsonify({"error": "Post not found."}), 404

    post.share_count = (post.share_count or 0) + 1

    try:
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to record post share")
        return jsonify({"error": "Could not record share. Please try again."}), 500

    create_notification(
        user_id=post.user_id, actor_id=current_user.id, ntype="post_share", post_id=post_id
    )

    socketio.emit("post_shared", {"post_id": post_id, "share_count": post.share_count})

    return jsonify({"share_count": post.share_count}), 200


@app.route("/api/posts/<int:post_id>/repost", methods=["POST"])
@login_required
@limiter.limit("60 per hour")
def repost_post(post_id):
    """Reposts a feed post onto the current user's own feed as a new post
    row that references the original, with an optional quote/caption —
    the same "quote repost" idea as other social feeds. Reposting a post
    you've already reposted removes that repost instead (toggle, same
    pattern as like_post). Reposting a repost attaches to the original
    underneath it, so the chain never nests more than one level deep."""
    post = Post.query.get(post_id)
    if not post:
        return jsonify({"error": "Post not found."}), 404

    original = post.original_post if post.repost_of_id else post

    data = request.get_json(silent=True) or {}
    quote_text = (data.get("text") or "").strip()
    if len(quote_text) > POST_TEXT_MAX_LENGTH:
        return jsonify({"error": f"Post text can't exceed {POST_TEXT_MAX_LENGTH} characters."}), 400

    existing = Post.query.filter_by(user_id=current_user.id, repost_of_id=original.id).first()

    try:
        if existing:
            existing_id = existing.id
            db.session.delete(existing)
            db.session.commit()
            reposted = False
            repost_payload = None
        else:
            repost = Post(user_id=current_user.id, text=quote_text or None, repost_of_id=original.id)
            db.session.add(repost)
            db.session.commit()
            reposted = True
            repost_payload = repost.to_dict(viewer_id=current_user.id)
    except Exception:
        db.session.rollback()
        logger.exception("Failed to toggle repost")
        return jsonify({"error": "Could not update repost. Please try again."}), 500

    repost_count = original.reposts.count()

    if reposted:
        create_notification(
            user_id=original.user_id, actor_id=current_user.id,
            ntype="post_repost", post_id=original.id
        )
        # Broadcast the repost itself like any other new post, so it shows
        # up live in everyone's feed — same as create_post().
        socketio.emit("new_post", repost_payload)
    else:
        socketio.emit("post_deleted", {"post_id": existing_id})

    socketio.emit("post_reposted", {
        "original_post_id": original.id,
        "reposter_id": current_user.id,
        "reposted": reposted,
        "repost_count": repost_count,
    })

    return jsonify({
        "reposted": reposted,
        "repost_count": repost_count,
        "data": repost_payload,
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

    # Auto-join every group this user belongs to, same as their private
    # room — so new_group_message / group_created events reach every open
    # tab immediately without the client having to emit join_group for
    # each group it already knows about.
    for group_id in get_user_group_ids(current_user.id):
        join_room(get_group_room_name(group_id))

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


@socketio.on("join_group")
def handle_join_group(data=None):
    """
    Expected payload: {"group_id": <int>}
    Explicit per-group join, for reconnect scenarios or a group the user
    was just added to mid-session (auto-join on connect only covers
    groups they were already in at connection time).
    """
    if not current_user.is_authenticated:
        emit("error", {"error": "Not authenticated."})
        return

    if not isinstance(data, dict):
        emit("error", {"error": "Invalid payload."})
        return

    try:
        group_id = int(data.get("group_id"))
    except (TypeError, ValueError):
        emit("error", {"error": "group_id must be a valid group id."})
        return

    if not is_group_member(group_id, current_user.id):
        emit("error", {"error": "You are not a member of this group."})
        return

    join_room(get_group_room_name(group_id))
    emit("group_join_ack", {"group_id": group_id})


@socketio.on("leave_group")
def handle_leave_group(data=None):
    """Expected payload: {"group_id": <int>} — leaves the Socket.IO room
    only (e.g. navigating away from the conversation view); does not
    remove the user's GroupMember row."""
    if not current_user.is_authenticated or not isinstance(data, dict):
        return

    try:
        group_id = int(data.get("group_id"))
    except (TypeError, ValueError):
        return

    leave_room(get_group_room_name(group_id))


@socketio.on("send_group_message")
def handle_send_group_message(data):
    """
    Expected payload:
    {
        "group_id": <int>,
        "content": <str>
    }
    Same shape/flow as handle_send_message, but broadcasts to the
    group's shared room instead of two individual private rooms.
    """
    if not current_user.is_authenticated:
        emit("error", {"error": "Not authenticated."})
        return

    if not isinstance(data, dict):
        emit("error", {"error": "Invalid payload."})
        return

    try:
        group_id = int(data.get("group_id"))
    except (TypeError, ValueError):
        emit("error", {"error": "group_id must be a valid group id."})
        return

    content = (data.get("content") or "").strip()
    if not content:
        emit("error", {"error": "Message content cannot be empty."})
        return
    if len(content) > MESSAGE_MAX_LENGTH:
        emit("error", {"error": f"Message is too long (max {MESSAGE_MAX_LENGTH} characters)."})
        return

    # Re-check membership on every send, not just at join_group time — the
    # socket could still be sitting in the room after being removed from
    # the group, and room membership alone isn't authorization to post.
    if not is_group_member(group_id, current_user.id):
        emit("error", {"error": "You are not a member of this group."})
        return

    try:
        message = GroupMessage(
            group_id=group_id,
            sender_id=current_user.id,
            content=content,
        )
        db.session.add(message)
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to save group message")
        emit("error", {"error": "Could not send message. Please try again."})
        return

    payload = message.to_dict()

    # Broadcast to the whole room, sender included, so every open tab —
    # sender's other devices too — renders off this one server-confirmed
    # event instead of the sender optimistically rendering its own message.
    socketio.emit("new_group_message", payload, room=get_group_room_name(group_id))


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


@socketio.on("mark_group_read")
def handle_mark_group_read(data):
    """
    Expected payload:
    {
        "group_id": <int>
    }
    Group-chat equivalent of "mark_read" — stamps the current user's
    GroupMember.last_read_at watermark to now, then tells everyone else in
    the room so senders can flip their own outgoing ticks to "read" live
    without anyone re-fetching the conversation.
    """
    if not current_user.is_authenticated:
        emit("error", {"error": "Not authenticated."})
        return

    if not isinstance(data, dict):
        emit("error", {"error": "Invalid payload."})
        return

    try:
        group_id = int(data.get("group_id"))
    except (TypeError, ValueError):
        emit("error", {"error": "group_id must be a valid group id."})
        return

    if not is_group_member(group_id, current_user.id):
        emit("error", {"error": "You are not a member of this group."})
        return

    now = datetime.utcnow()
    try:
        GroupMember.query.filter_by(group_id=group_id, user_id=current_user.id).update(
            {"last_read_at": now}
        )
        db.session.commit()
    except Exception:
        db.session.rollback()
        logger.exception("Failed to update group read status")
        emit("error", {"error": "Could not update read status."})
        return

    socketio.emit("group_messages_seen", {
        "group_id": group_id,
        "reader_id": current_user.id,
        "at": to_iso_utc(now),
    }, room=get_group_room_name(group_id))



# -------------------------------------------------------------------
# Voice calls (1:1) — plain WebRTC signaling relay over Socket.IO.
#
# The server never touches audio itself; it just relays small JSON
# messages between the two participants' private rooms (get_room_name)
# so a "call_invite" reaches every open tab/device for the callee, an
# SDP offer/answer + ICE candidates ("call_signal") get passed straight
# through, and either side can end the call ("call_end") or decline it
# ("call_reject") at any point.
# -------------------------------------------------------------------

def _coerce_user_id(raw):
    """Returns (user_id, error_message). error_message is None on success."""
    try:
        user_id = int(raw)
    except (TypeError, ValueError):
        return None, "to_user_id must be a valid user id."
    return user_id, None


@socketio.on("call_invite")
def handle_call_invite(data):
    """
    Expected payload: {"to_user_id": <int>, "call_id": <str>}
    Caller -> callee: "Someone wants to call you."
    """
    if not current_user.is_authenticated:
        emit("error", {"error": "Not authenticated."})
        return

    if not isinstance(data, dict):
        emit("error", {"error": "Invalid payload."})
        return

    to_user_id, err = _coerce_user_id(data.get("to_user_id"))
    if err:
        emit("error", {"error": err})
        return

    call_id = str(data.get("call_id") or "")
    if not call_id:
        emit("error", {"error": "call_id is required."})
        return

    if to_user_id == current_user.id:
        emit("error", {"error": "You cannot call yourself."})
        return

    callee = User.query.get(to_user_id)
    if not callee:
        emit("error", {"error": "That user does not exist."})
        return

    _active_calls[call_id] = {
        "caller_id": current_user.id,
        "callee_id": to_user_id,
        "invited_at": datetime.utcnow(),
        "answered_at": None,
    }

    socketio.emit("call_incoming", {
        "call_id": call_id,
        "from_user_id": current_user.id,
        "from_username": current_user.username,
        "from_profile_pic": current_user.profile_pic,
    }, room=get_room_name(to_user_id))


@socketio.on("call_accept")
def handle_call_accept(data):
    """Expected payload: {"to_user_id": <int>, "call_id": <str>}
    Callee -> caller: "I picked up, send me your offer." """
    if not current_user.is_authenticated or not isinstance(data, dict):
        return

    to_user_id, err = _coerce_user_id(data.get("to_user_id"))
    if err:
        return
    call_id = str(data.get("call_id") or "")
    if not call_id:
        return

    record = _active_calls.get(call_id)
    if record is not None:
        record["answered_at"] = datetime.utcnow()

    socketio.emit("call_accepted", {
        "call_id": call_id,
        "from_user_id": current_user.id,
    }, room=get_room_name(to_user_id))


@socketio.on("call_reject")
def handle_call_reject(data):
    """Expected payload: {"to_user_id": <int>, "call_id": <str>, "reason": <str optional>}
    Callee -> caller: "Declined" (or auto-declined because already busy)."""
    if not current_user.is_authenticated or not isinstance(data, dict):
        return

    to_user_id, err = _coerce_user_id(data.get("to_user_id"))
    if err:
        return
    call_id = str(data.get("call_id") or "")
    if not call_id:
        return

    reason = data.get("reason") or "declined"
    # "busy" means the callee's client auto-declined because they were
    # already on another call — that's a missed call, not a deliberate
    # decline, so it gets logged the same way an unanswered call would.
    _finalize_call(call_id, "declined" if reason == "declined" else "no_answer")

    socketio.emit("call_rejected", {
        "call_id": call_id,
        "from_user_id": current_user.id,
        "reason": reason,
    }, room=get_room_name(to_user_id))


@socketio.on("call_signal")
def handle_call_signal(data):
    """Expected payload: {"to_user_id": <int>, "call_id": <str>, "signal": <dict>}
    Passthrough relay for SDP offers/answers and ICE candidates — the
    server doesn't inspect `signal`, it just forwards it untouched."""
    if not current_user.is_authenticated or not isinstance(data, dict):
        return

    to_user_id, err = _coerce_user_id(data.get("to_user_id"))
    if err:
        return
    call_id = str(data.get("call_id") or "")
    signal = data.get("signal")
    if not call_id or not isinstance(signal, dict):
        return

    socketio.emit("call_signal", {
        "call_id": call_id,
        "from_user_id": current_user.id,
        "signal": signal,
    }, room=get_room_name(to_user_id))


@socketio.on("call_end")
def handle_call_end(data):
    """Expected payload: {"to_user_id": <int>, "call_id": <str>, "reason": <str optional>}
    Either side hanging up, or the caller canceling before it's answered."""
    if not current_user.is_authenticated or not isinstance(data, dict):
        return

    to_user_id, err = _coerce_user_id(data.get("to_user_id"))
    if err:
        return
    call_id = str(data.get("call_id") or "")
    if not call_id:
        return

    record = _active_calls.get(call_id)
    if record is not None:
        _finalize_call(call_id, "completed" if record.get("answered_at") else "no_answer")

    socketio.emit("call_ended", {
        "call_id": call_id,
        "from_user_id": current_user.id,
        "reason": (data.get("reason") or "hangup"),
    }, room=get_room_name(to_user_id))


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

        # Going fully offline mid-call (closed tab, lost connection, etc.)
        # would otherwise leave the other party's call screen open forever
        # and the call never logged — finalize it here the same way a
        # normal hangup would.
        dangling_call_ids = [
            cid for cid, rec in _active_calls.items()
            if rec["caller_id"] == current_user.id or rec["callee_id"] == current_user.id
        ]
        for cid in dangling_call_ids:
            record = _active_calls.get(cid)
            other_id = record["callee_id"] if record["caller_id"] == current_user.id else record["caller_id"]
            _finalize_call(cid, "completed" if record.get("answered_at") else "no_answer")
            socketio.emit("call_ended", {
                "call_id": cid,
                "from_user_id": current_user.id,
                "reason": "disconnected",
            }, room=get_room_name(other_id))


# -------------------------------------------------------------------
# Entry Point
# -------------------------------------------------------------------
if __name__ == "__main__":
    socketio.run(app, debug=not IS_PRODUCTION, host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
