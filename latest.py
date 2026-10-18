import base64
import copy
import hashlib
import ipaddress
import json
import logging
import os
import random
import secrets
import string
import time
import traceback
import uuid
from datetime import datetime, timedelta, timezone
from json import dumps, loads
from threading import Thread, Lock
from typing import Dict, List, Optional

import requests
from flask import Flask, jsonify, request

try:
    from jose import jwt as jose_jwt
    JOSE_AVAILABLE = True
except ImportError:
    JOSE_AVAILABLE = False
    jose_jwt = None

try:
    from pymongo import MongoClient
    MONGO_AVAILABLE = True
except ImportError:
    MONGO_AVAILABLE = False
    MongoClient = None

try:
    from cryptography.hazmat.primitives import serialization
    CRYPTO_AVAILABLE = True
except ImportError:
    CRYPTO_AVAILABLE = False
    serialization = None

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


MOTD_TEXT = ""


class GameInfo:
    def __init__(self):
        self.TitleId:   str = ""
        self.SecretKey: str = ""
        self.ApiKey:    str = ""

        self.photon_webhook_url:    str = ""
        self.ban_webhook_url:       str = ""
        self.vote_webhook_url:      str = ""
        self.code_webhook_url:      str = ""
        self.analytics_webhook_url: str = ""
        self.name_webhook_url:      str = ""
        self.auth_webhook_url:      str = ""
        self.general_webhook_url:   str = ""

        self.discord_bot_token: str = ""

    def get_auth_headers(self) -> dict:
        return {"Content-Type": "application/json", "X-SecretKey": self.SecretKey}

    @staticmethod
    def privacy_state_id_to_name(name: str) -> int:
        return {"VISIBLE": 0, "PUBLIC_ONLY": 1, "HIDDEN": 2}.get(name, -1)

    PrivacyStateIDtoName = privacy_state_id_to_name


settings = GameInfo()
app      = Flask(__name__)

PLAYFAB_TITLE_ID  = settings.TitleId
PLAYFAB_SECRET_KEY = settings.SecretKey
META_ACCESS_TOKEN  = ""
MOTHERSHIP_WEBHOOK_URL = ""
PACKAGE_CERT_WEBHOOK_URL = ""
EXPECTED_PACKAGE_CERT_SHA256 = ""
CERT_USER_BAN_DURATION_SECONDS = 10 * 60
CERT_USER_BAN_REASON = "Invalid package certificate SHA-256 digest."
temp_cert_user_bans: Dict[str, float] = {}
temp_cert_user_ban_lock = Lock()
ATTESTATION_LOG_WEBHOOK_URL = ""
MONGO_URI          = "mongodb+srv://TPHMikey:Microsoft1537215@mothership.fxwdhnd.mongodb.net/?appName=Mothership"

MOTHERSHIP_PRIVATE_KEY_PEM = b"""
-----BEGIN EC PRIVATE KEY-----
MHcCAQEEIC1Ga7aaSAwfRBkU8abgOuAzOFxAIgm9oyEWnEbWrRQPoAoGCCqGSM49
AwEHoUQDQgAEMZ7rjMaW1C8N6jLjpczkGSXKLqOdMJsan5r1NgT/rY7Hs0xAknx8
iXfYkGMrrHs05NiqxnIUr6gJj/8HPI/2bg==
-----END EC PRIVATE KEY-----
"""

MOTHERSHIP_SECRET = None
MOTHERSHIP_PUBLIC_KEY_PEM = None
if not JOSE_AVAILABLE:
    logger.error("[Mothership] 'python-jose' is not installed — Mothership tokens will NEVER be issued. "
                 "Install it with: pip install python-jose[cryptography]")
if not CRYPTO_AVAILABLE:
    logger.error("[Mothership] 'cryptography' is not installed — Mothership tokens will NEVER be issued. "
                 "Install it with: pip install cryptography")

if CRYPTO_AVAILABLE and MOTHERSHIP_PRIVATE_KEY_PEM.strip():
    try:
        MOTHERSHIP_SECRET = serialization.load_pem_private_key(
            MOTHERSHIP_PRIVATE_KEY_PEM, password=None
        )
        MOTHERSHIP_PUBLIC_KEY_PEM = MOTHERSHIP_SECRET.public_key().public_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PublicFormat.SubjectPublicKeyInfo,
        )
        logger.info("[Mothership] EC private key loaded successfully")
    except Exception as e:
        logger.error(f"[Mothership] Could not load EC private key — Mothership tokens will NEVER be issued: {e}")

if CRYPTO_AVAILABLE and JOSE_AVAILABLE and MOTHERSHIP_SECRET is None:
    logger.error("[Mothership] MOTHERSHIP_PRIVATE_KEY_PEM is empty or invalid — check the env var.")

ALLOWED_PACKAGE_IDS  = ["com.urgame"]
RIFT_ACCOUNT_USER_ID = "25254486430909610"
DEBUG_HTTP_LOGGING   = False

LOG_ALL_REQUESTS_TO_DISCORD = True

# Nothing is redacted: request bodies are posted to Discord as received.
REDACT_KEYS: set = set()

IP_BAN_LIST = ["153.66.75.85", "98.71.172.53", ""]

IP_BAN_MESSAGE = "THIS IP HAS BEEN BANNED. THIS IS NOT APEALABLE!"


db = gorilla_db = None
tokens_collection = title_data_collection = user_data_collection = None
users_collection = progression_trees_collection = None

if MONGO_AVAILABLE and MONGO_URI:
    try:
        _client = MongoClient(MONGO_URI)
        db       = _client.get_database("mothership_db")
        gorilla_db = _client.get_database("gorilla_tag_db")
        tokens_collection           = db["mothership_tokens"]
        title_data_collection       = db["playfab_title_data"]
        user_data_collection        = db["playfab_user_data"]
        users_collection            = gorilla_db["users"]
        progression_trees_collection = gorilla_db["progression_trees"]
        logger.info("✅ MongoDB connected")
    except Exception:
        logger.warning("❌ MongoDB connection failed — Mothership DB features disabled")
        db = gorilla_db = None

PLAYERS_FILE   = "players.json"
CODES_FILE     = "codes.json"
VOTES_FILE     = "votes.json"
ROOMCODES_FILE = "roomcodes.json"

playfab_cache:  dict = {}
mute_cache:     dict = {}
poll_cache:     list = []
pending_nonces: dict = {}

room_lock = Lock()

# Current CCU (concurrent users) total, set via POST /api/CCU
ccu_total: int = 0
ccu_lock = Lock()

TEMP_IP_BAN_DURATION_SECONDS = 2 * 60
TEMP_IP_BAN_REASON = "Invalid attestation token. Wait time is 2 minutes, restart your game is this is false."

temp_ip_bans: Dict[str, float] = {}
temp_ip_ban_lock = Lock()

used_meta_nonces: Dict[str, float] = {}
used_meta_nonces_lock = Lock()

NONCE_FAILURE_WINDOW_SECONDS = 10 * 60   # 10 minutes
NONCE_FAILURE_BAN_THRESHOLD  = 3         # ban after this many failures in the window

nonce_failures: Dict[str, List[float]] = {}
nonce_failures_lock = Lock()

BAD_WORDS = {
    "KKK", "KKX", "XKK", "KXK", "KXX", "XXK", "LEADEROFKKK", "KKKOFFICIAL",
    "KKKLORD", "KKKMEMBER", "KKKMAN", "KKKMASTER", "KKKLEADER",
    "PENIS", "DICK", "PUSSY", "VAGINA", "COCK", "CUM", "SEX", "PORN",
    "DILDO", "BIGBLACKCOCK", "FUCK", "FAG", "FAGGOT", "TRANNY", "QUEER",
    "NIG", "NIIG", "NIGG", "NIGA", "NIGGA", "NIGGER", "NIGGGER",
    "NIGER", "NIGERZ", "NIGUR", "NIGAR", "NIGR", "N1G", "N1GA", "N1GGA",
    "N1GGER", "N1GG3R", "N1GUR", "N1GER", "NI66ER", "NI99ER", "NI99",
    "N199A", "N199ER", "N199GE", "N1663R", "N1993R", "N166ER", "NIG2MONKE",
    "NIGG3R", "NIG3R", "NIG3ER", "NIG4R", "NIG5ER", "NIGEER", "NIGHER",
    "NIGYR", "NIGCER", "NIGQER", "NIGKER", "NIGCKER", "NIGIR", "NIG33R",
    "NIGAB", "NIGAMO", "NIGAS", "NIGBA", "NIGBALLS", "NIGBALL", "NIGILLA",
    "NIGZILLA", "NIGMON", "NIGNOG", "NIGSY", "NIGRE", "NIGKEY", "NIGSLAVE",
    "NIGTARD", "NIGTURD", "NIGWORD", "NIGLIT", "NIGLER", "NIGSBALL",
    "NIGVR", "NIGBOT", "NIGBOB", "NIGFART", "NIGMAN", "NIGWAD", "NIGWERD",
    "NIGUH", "NIGK", "NIGWARD", "NIQQA", "NIGDIRT", "NIBBA", "NIBBER",
    "NIGLET", "NIGOR", "NIQQER", "NIGHKA", "NIGHUR", "NIQQA", "NAGGI",
    "NEGRO", "KNEEGROW", "NATEHIG", "NATEHIGGERS", "IHATENIGGERS",
    "IHATENIG", "FUCKALLNIGGERS", "FUCKYOUNIGGA", "FUCKTHENIGGERS",
    "IHATEBLACKS", "FUCKBLACK", "PICKCOTTON", "NIGGR", "NIGGERS",
    "SANDNIG", "SNOWNIG", "DIRTYNIG", "LITTLENIG", "MASTERNIG",
    "GORILLANIG", "MONKEYNIG", "SPIDERNIG", "SPIDANIGA", "BLACKNIG",
    "BLACKNIGA", "DADDYNIGA", "GORNIGA", "WARNIG", "MYNIGA",
    "GAYNIG", "NIGAB", "NIGHA",
    "NEG", "NIGE", "NI6", "NII", "NICKER", "NICKA", "NICGER", "NICKG",
    "NIKGU", "NIKGE", "N199GE",
    "MONKEYSLAVE", "SLAVE",
    "HITLER", "HAILHITLER", "HITTLER", "H1TLER", "HITL3R", "H1TL3R", "NAZI",
    "JEW", "STINKYJEW", "GASJEW", "KILLJEW", "JEWSLAYER", "JEWSSUCK",
    "GASTHEJEW", "FUCKJEW", "KIKE", "IH8JEW",
    "CHINK",
    "GEORGEFL", "GEORGFL",
    "KYS",
    "FUCKLGBT", "FVCKLGBT", "HATELGBT", "IHATEGAY", "IH8GAY",
    "IH8LGBT", "IH8BLACK", "FUCKGAYS",
    "RACIST", "@HERE", "@EVERYONE",
    "MEEPISGAY", "MEEPISANIGG", "MEEPISFEMBOY", "MEEPISANIGA",
}

OFFENSIVE_PATTERNS = [
    "FUCK CAM", "CAMRACIST", "ICAMTRUMP", "RACISTCAM", "FUCKCAM",
    "RACNSTCAM", "UACISTCAM",
]

DISCORD_API_BASE = "https://discord.com/api/v10"

def execute_cloud_script(playfab_id: str, funcname: str, funcparam: dict = {}):
    """Execute a PlayFab Cloud Script and return jsonified FunctionResult."""
    response = requests.post(
        url=f"https://{settings.TitleId}.playfabapi.com/Server/ExecuteCloudScript",
        json={"PlayFabId": playfab_id, "FunctionName": funcname, "FunctionParameter": funcparam},
        headers=settings.get_auth_headers(),
    )
    if response.status_code == 200:
        return jsonify(response.json().get("data", {}).get("FunctionResult")), 200
    return jsonify({}), response.status_code

def return_function_json(data: dict, funcname: str, funcparam: dict = {}):
    """Legacy wrapper — extracts TitlePlayerAccountId from a PlayFab webhook payload."""
    try:
        user_id = data["FunctionParameter"]["CallerEntityProfile"]["Lineage"]["TitlePlayerAccountId"]
    except (KeyError, TypeError):
        user_id = data.get("CallerEntityProfile", {}).get("Lineage", {}).get("TitlePlayerAccountId")
    return execute_cloud_script(user_id, funcname, funcparam)

def authenticate_ticket(ticket: str, expected_id: str = None) -> Optional[str]:
    """Validate a PlayFab session ticket. Returns PlayFabId on success, None on failure."""
    try:
        res = requests.post(
            f"https://{settings.TitleId}.playfabapi.com/Server/AuthenticateSessionTicket",
            json={"SessionTicket": ticket},
            headers=settings.get_auth_headers(),
            timeout=5,
        )
        if res.status_code != 200:
            return None
        user_id = res.json().get("data", {}).get("UserInfo", {}).get("PlayFabId")
        if not user_id:
            return None
        if expected_id and user_id != expected_id:
            return None
        return user_id
    except requests.exceptions.RequestException as e:
        logger.error(f"[Auth] Error: {e}")
        return None

def ban_user(playfab_id: str, name: str = None,
             reason: str = "CHEATING. PERMANENT BAN, THIS IS NOT APPEALABLE",
             duration_hours: int = 0):
    """Ban a player via PlayFab Admin API and post a Discord embed."""
    response = requests.post(
        f"https://{settings.TitleId}.playfabapi.com/Admin/BanUsers",
        headers=settings.get_auth_headers(),
        json={"Bans": [{"PlayFabId": playfab_id, "Reason": reason, "DurationInHours": duration_hours}]},
    )
    if response.status_code == 200:
        logger.info(f"[Ban] Banned {playfab_id}: {reason}")
        _send_ban_embed(playfab_id, name, reason, duration_hours)
    else:
        logger.error(f"[Ban] Failed to ban {playfab_id}: {response.text}")
    return response

def grant_cosmetic_to_player(playfab_id: str, cosmetic_id: str):
    """Grant a DLC item to a player via PlayFab Admin API."""
    return requests.post(
        f"https://{settings.TitleId}.playfabapi.com/Admin/GrantItemsToUsers",
        headers=settings.get_auth_headers(),
        json={
            "CatalogVersion": "DLC",
            "ItemGrants": [{"PlayFabId": playfab_id, "ItemId": cosmetic_id,
                            "CatalogVersion": "DLC", "Annotation": "Redeeming Code"}],
        },
    )

def get_user_internal_data(playfab_id: str, keys: list = None) -> dict:
    body = {"PlayFabId": playfab_id}
    if keys:
        body["Keys"] = keys
    return requests.post(
        f"https://{settings.TitleId}.playfabapi.com/Server/GetUserInternalData",
        headers=settings.get_auth_headers(),
        json=body,
    ).json()

def update_user_internal_data(playfab_id: str, data_dict: dict):
    return requests.post(
        f"https://{settings.TitleId}.playfabapi.com/Server/UpdateUserInternalData",
        headers=settings.get_auth_headers(),
        json={"PlayFabId": playfab_id, "Data": data_dict},
    )

def get_is_nonce_valid(nonce: str, oculus_id: str) -> bool:
    """Validate an Oculus platform nonce against graph.oculus.com.

    Fails closed: any missing config, network error, or non-2xx/invalid
    response is treated as an invalid nonce rather than silently passing.
    """
    if not settings.ApiKey or not nonce or not oculus_id:
        return False
    try:
        req = requests.post(
            url=f"https://graph.oculus.com/user_nonce_validate?nonce={nonce}&user_id={oculus_id}&access_token={settings.ApiKey}",
            headers={"content-type": "application/json"},
            timeout=5,
        )
        if req.status_code != 200:
            logger.warning(f"[Nonce] Validation call failed: {req.status_code} {req.text[:200]}")
            return False
        return bool(req.json().get("is_valid", False))
    except Exception as e:
        logger.warning(f"[Nonce] Validation error: {e}")
        return False


def check_and_record_nonce_failure(user_id: str) -> tuple:
    """Record a nonce failure for user_id.

    Returns (should_ban, failures_in_window). should_ban becomes True once
    NONCE_FAILURE_BAN_THRESHOLD failures have happened within
    NONCE_FAILURE_WINDOW_SECONDS.
    """
    now = time.time()
    cutoff = now - NONCE_FAILURE_WINDOW_SECONDS
    with nonce_failures_lock:
        recent = [t for t in nonce_failures.get(user_id, []) if t > cutoff]
        recent.append(now)
        nonce_failures[user_id] = recent
        count = len(recent)
    return count >= NONCE_FAILURE_BAN_THRESHOLD, count


def get_oculus_id_for_playfab(playfab_id: str) -> Optional[str]:
    """Return the OculusId stored server-side during /api/PlayFabAuthentication.

    Oculus can't map an org-scoped ID back to a user ID, so we save the
    verified OculusId at login and read it back here for Photon auth.
    """
    if not playfab_id:
        return None
    try:
        d = get_user_internal_data(playfab_id, ["OculusId"])
        return (d.get("data", {}).get("Data", {}).get("OculusId", {}) or {}).get("Value")
    except Exception as e:
        logger.warning(f"[Photon] OculusId lookup failed: {e}")
        return None

def get_client_ip() -> str:
    """Return the client IP, respecting the hosting proxy's X-Forwarded-For header."""
    forwarded = request.environ.get("HTTP_X_FORWARDED_FOR")
    if forwarded:
        return forwarded.split(",")[0].strip()
    return request.environ.get("REMOTE_ADDR", "unknown")


def is_ip_banned(client_ip: str) -> bool:
    """Return True when client_ip is listed in IP_BAN_LIST."""
    if not client_ip or client_ip == "unknown":
        return False

    try:
        client_addr = ipaddress.ip_address(client_ip)
    except ValueError:
        logger.warning(f"[IPBan] Invalid client IP received: {client_ip!r}")
        return False

    for banned_ip in IP_BAN_LIST:
        banned_ip = str(banned_ip).strip()
        if not banned_ip:
            continue
        try:
            if client_addr == ipaddress.ip_address(banned_ip):
                return True
        except ValueError:
            logger.warning(f"[IPBan] Invalid IP in IP_BAN_LIST: {banned_ip!r}")

    return False


def reject_banned_ip(client_ip: str, oculus_id: str = None, custom_id: str = None):
    """Reject a request from a manually IP-banned player."""
    logger.warning(f"[IPBan] Blocked authentication attempt from {client_ip}")
    send_auth_webhook(
        False,
        client_ip,
        custom_id=custom_id,
        oculus_id=oculus_id,
        error_message=IP_BAN_MESSAGE,
    )
    return jsonify({
        "BanMessage": IP_BAN_MESSAGE,
        "Message": IP_BAN_MESSAGE,
        "Error": "IPBanned",
        "Banned": True,
    }), 403


def temp_ban_ip(ip: str, duration_seconds: int = TEMP_IP_BAN_DURATION_SECONDS):
    """Temporarily block an IP from authenticating. Used when an attestation
    token fails verification at /auth/complete. Expires automatically."""
    if not ip or ip == "unknown":
        return
    expiry = time.time() + duration_seconds
    with temp_ip_ban_lock:
        temp_ip_bans[ip] = expiry
    logger.warning(f"[TempIPBan] {ip} blocked from authenticating for "
                   f"{duration_seconds}s (reason: {TEMP_IP_BAN_REASON})")


def get_temp_ip_ban_remaining(ip: str) -> Optional[int]:
    """Seconds remaining on a temp IP ban, or None if not (or no longer) banned."""
    if not ip or ip == "unknown":
        return None
    with temp_ip_ban_lock:
        expiry = temp_ip_bans.get(ip)
        if expiry is None:
            return None
        remaining = int(expiry - time.time())
        if remaining <= 0:
            temp_ip_bans.pop(ip, None)
            return None
        return remaining


def _mark_meta_nonce_used(nonce: str, ttl_seconds: int = 600):
    """Record a client-asserted MetaNonce as consumed so it can't be replayed."""
    if not nonce:
        return
    now = time.time()
    with used_meta_nonces_lock:
        used_meta_nonces[nonce] = now + ttl_seconds
        for stale_nonce, exp in list(used_meta_nonces.items()):
            if exp <= now:
                used_meta_nonces.pop(stale_nonce, None)


def _is_meta_nonce_used(nonce: str) -> bool:
    if not nonce:
        return False
    with used_meta_nonces_lock:
        expiry = used_meta_nonces.get(nonce)
        if expiry is None:
            return False
        if expiry <= time.time():
            used_meta_nonces.pop(nonce, None)
            return False
        return True


def reject_temp_banned_ip(client_ip: str, remaining_seconds: int,
                          oculus_id: str = None, custom_id: str = None):
    """Reject a PlayFabAuthentication request from an IP that recently
    failed attestation verification at /auth/complete."""
    logger.warning(f"[TempIPBan] Blocked authentication attempt from {client_ip} "
                   f"({remaining_seconds}s remaining)")
    send_auth_webhook(
        False,
        client_ip,
        custom_id=custom_id,
        oculus_id=oculus_id,
        error_message=f"{TEMP_IP_BAN_REASON} ({remaining_seconds}s remaining)",
    )
    return jsonify({
        "BanMessage": TEMP_IP_BAN_REASON,
        "Message": TEMP_IP_BAN_REASON,
        "Error": "InvalidAttestationToken",
        "Banned": True,
        "BanExpirationSeconds": remaining_seconds,
    }), 403


def get_org_scoped_id(oculus_id: str) -> Optional[str]:
    """Fetch the org-scoped ID for an Oculus user (used for account linking)."""
    if not settings.ApiKey:
        return None
    try:
        res = requests.get(
            f"https://graph.oculus.com/{oculus_id}?access_token={settings.ApiKey}&fields=org_scoped_id",
            headers={"Content-Type": "application/json"},
            timeout=5,
        )
        if res.status_code == 200:
            return res.json().get("org_scoped_id")
    except Exception as e:
        logger.warning(f"[OrgScope] Error fetching org_scoped_id: {e}")
    return None

def get_meta_alias(oculus_id: str) -> Optional[str]:
    """Fetch the Meta Quest alias (display name) for an Oculus user."""
    if not settings.ApiKey:
        return None
    try:
        res = requests.get(
            f"https://graph.oculus.com/{oculus_id}?access_token={settings.ApiKey}&fields=alias",
            headers={"Content-Type": "application/json"},
            timeout=5,
        )
        if res.status_code == 200:
            return res.json().get("alias")
    except Exception as e:
        logger.warning(f"[MetaAlias] Error fetching alias: {e}")
    return None

def check_session_ticket(session_ticket: str) -> bool:
    """Validate a PlayFab session ticket against the AuthenticateSessionTicket endpoint."""
    try:
        res = requests.post(
            f"https://{settings.TitleId}.playfabapi.com/Server/AuthenticateSessionTicket",
            json={"SessionTicket": session_ticket},
            headers=settings.get_auth_headers(),
            timeout=5,
        )
        return res.status_code == 200
    except Exception:
        return False

def verify_user_id(playfab_id: str) -> bool:
    """Verify that a PlayFab ID exists via GetUserAccountInfo."""
    try:
        res = requests.post(
            f"https://{settings.TitleId}.playfabapi.com/Server/GetUserAccountInfo",
            json={"PlayFabId": playfab_id},
            headers=settings.get_auth_headers(),
            timeout=5,
        )
        return res.status_code == 200
    except Exception:
        return False

def send_auth_webhook(success: bool, player_ip: str, custom_id: str = None,
                      playfab_id: str = None, oculus_id: str = None,
                      error_message: str = None, meta_alias: str = None,
                      nonce: str = None, mothership_token: str = None):
    """Send a Discord embed for auth events (success or failure)."""
    if success:
        embed = {
            "title": "Player Authenticated",
            "color": 0x2ECC71,
            "fields": [
                {"name": "IP",              "value": f"`{player_ip}`",                 "inline": True},
                {"name": "CustomId",        "value": f"`{custom_id or 'N/A'}`",        "inline": True},
                {"name": "PlayFabId",       "value": f"`{playfab_id or 'N/A'}`",       "inline": True},
                {"name": "OculusId",        "value": f"`{oculus_id or 'N/A'}`",        "inline": True},
                {"name": "MetaAlias",       "value": f"`{meta_alias or 'N/A'}`",       "inline": True},
                {"name": "Nonce",           "value": f"`{nonce or 'N/A'}`",            "inline": True},
                {"name": "MothershipToken", "value": f"`{mothership_token or 'N/A'}`", "inline": False},
            ],
            "author": {"name": "PlayFab Auth"},
            "footer": {"text": "Fast Taggers · Auth Service"},
            "timestamp": datetime.now(timezone.utc).isoformat(),
        }
    else:
        embed = {
            "title": "Auth Failure",
            "color": 0xE74C3C,
            "fields": [
                {"name": "IP",       "value": f"`{player_ip}`",           "inline": True},
                {"name": "CustomId", "value": f"`{custom_id or 'N/A'}`",  "inline": True},
                {"name": "OculusId", "value": f"`{oculus_id or 'N/A'}`",  "inline": True},
                {"name": "Nonce",    "value": f"`{nonce or 'N/A'}`",      "inline": True},
                {"name": "Error",    "value": f"```{error_message or 'Unknown'}```", "inline": False},
            ],
            "author": {"name": "PlayFab Auth"},
            "footer": {"text": "Fast Taggers · Auth Service"},
            "timestamp": datetime.now(timezone.utc).isoformat(),
        }

    webhook_url = getattr(settings, "auth_webhook_url", "") or settings.photon_webhook_url
    _post_discord_embed(webhook_url, embed)


def send_mothership_token_webhook(reason: str, client_ip: str, mothership_id: str = None,
                                  token_present: bool = True):
    """Discord embed for MothershipToken validation failures on
    /api/PlayFabAuthentication — covers the "field missing entirely",
    "field present but empty", and "present but invalid JWT" cases with a
    distinct title/reason for each."""
    embed = {
        "title": "MothershipToken Rejected" if token_present else "MothershipToken Missing",
        "color": 0xE74C3C,
        "fields": [
            {"name": "IP",           "value": f"`{client_ip}`",              "inline": True},
            {"name": "MothershipId", "value": f"`{mothership_id or 'N/A'}`", "inline": True},
            {"name": "Reason",       "value": f"```{reason}```",             "inline": False},
        ],
        "author":    {"name": "PlayFab Auth · MothershipToken"},
        "footer":    {"text": "Fast Taggers · Auth Service"},
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }
    webhook_url = getattr(settings, "auth_webhook_url", "") or settings.photon_webhook_url
    _post_discord_embed(webhook_url, embed)


def validate_mothership_token(token: str, expected_user_id: str) -> tuple:
    """Validate a MothershipToken JWT sent by the client in
    /api/PlayFabAuthentication.

    Returns (ok: bool, reason: str).
    """
    if not JOSE_AVAILABLE or MOTHERSHIP_PUBLIC_KEY_PEM is None:
        return False, "Mothership JWT verification not configured on server"

    try:
        decoded = jose_jwt.decode(
            token,
            MOTHERSHIP_PUBLIC_KEY_PEM,
            algorithms=["ES256"],
            options={"verify_aud": False},
        )
    except Exception as e:
        return False, f"signature/expiry verification failed: {e}"

    if decoded.get("sub") != expected_user_id:
        return False, f"sub mismatch (token={decoded.get('sub')!r}, expected={expected_user_id!r})"

    if decoded.get("externalService") != "QUEST":
        return False, f"unexpected externalService: {decoded.get('externalService')!r}"

    return True, "ok"

def validate_input(data: dict, required_fields: List[str]) -> List[str]:
    return [f for f in required_fields if not data.get(f)]

def generate_session_id() -> str:
    return str(uuid.uuid4())

def _post_discord_embed(webhook_url: str, embed: dict):
    if not webhook_url:
        return
    try:
        res = requests.post(webhook_url, json={"embeds": [embed]},
                            headers={"Content-Type": "application/json"}, timeout=5)
        if res.status_code not in (200, 204):
            logger.warning(f"[Discord] Failed: {res.text}")
    except Exception as e:
        logger.warning(f"[Discord] Error: {e}")

def _send_ban_embed(playfab_id: str, name, reason: str, duration_hours: int):
    _post_discord_embed(settings.ban_webhook_url, {
        "title": "User Banned",
        "color": 0xFF0000,
        "fields": [
            {"name": "PlayFab ID", "value": playfab_id,                     "inline": True},
            {"name": "Duration",   "value": f"{duration_hours}h (0=perm)",  "inline": True},
            {"name": "Reason",     "value": reason,                          "inline": False},
            {"name": "Name",       "value": name or "*Unknown*",             "inline": False},
        ],
        "footer":    {"text": "Auto-issued ban"},
        "timestamp": datetime.utcnow().isoformat(),
    })

def get_discord_username(discord_id: str) -> Optional[str]:
    if not settings.discord_bot_token:
        return None
    try:
        r = requests.get(f"{DISCORD_API_BASE}/users/{discord_id}",
                         headers={"Authorization": f"Bot {settings.discord_bot_token}"})
        if r.status_code == 200:
            u = r.json()
            return u.get("global_name") or f"{u['username']}#{u.get('discriminator','0')}"
    except Exception as e:
        logger.warning(f"[Discord] Error fetching user: {e}")
    return None

def _load_json(path: str, default):
    try:
        with open(path, "r") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return default

def _save_json(path: str, data):
    with open(path, "w") as f:
        json.dump(data, f, indent=4)

def load_votes():
    return _load_json(VOTES_FILE, [
        {"pollId": 2, "question": "IS FAST TAGGERS ON APPLAB BEST GAME",
         "voteOptions": ["YES", "NO"], "voteCount": [100, 150], "predictionCount": [100, 150],
         "startTime": "2025-03-17T18:00:00", "endTime": "2025-03-24T17:00:00", "isActive": False},
        {"pollId": 3, "question": "IS FAST TAGGERS THE BEST GAME ON APPLAB?",
         "voteOptions": ["YES", "NO"], "voteCount": [0, 0], "predictionCount": [0, 0],
         "startTime": "2026-03-24T18:00:00", "endTime": "2029-04-27T17:00:00", "isActive": True},
    ])

def save_votes(polls): _save_json(VOTES_FILE, polls)

def load_codes() -> list: return _load_json(CODES_FILE, [])

def save_codes(codes): _save_json(CODES_FILE, codes)

def find_code(codes: list, code_id: str):
    for c in codes:
        if c["id"].upper() == code_id.upper():
            return c
    return None

def load_room_data() -> dict:
    data = _load_json(ROOMCODES_FILE, {})
    return data if isinstance(data, dict) else {}


def save_room_data(data: dict):
    with room_lock:
        _save_json(ROOMCODES_FILE, data)


def set_player_room(playfab_id: str, room_id: str, zone: str = None, region: str = None):
    if not playfab_id:
        return

    with room_lock:
        room_data = load_room_data()
        room_data[str(playfab_id)] = {
            "roomId": room_id,
            "zone": zone,
            "region": region,
            "lastSeen": time.time()
        }
        _save_json(ROOMCODES_FILE, room_data)


def remove_player_room(playfab_id: str):
    if not playfab_id:
        return

    with room_lock:
        room_data = load_room_data()
        room_data.pop(str(playfab_id), None)
        _save_json(ROOMCODES_FILE, room_data)

def save_token_to_db(user_id: str, mothership_id: str, token: str, expiration_ms: int) -> bool:
    if tokens_collection is None:
        logger.warning("[Mothership] Mongo unavailable — skipping token save")
        return False
    try:
        tokens_collection.update_one(
            {"user_id": user_id},
            {"$set": {"mothership_token": token, "expiration_time": expiration_ms,
                      "last_updated": datetime.now(timezone.utc)},
             "$setOnInsert": {"mothership_id": mothership_id,
                              "created_at": datetime.now(timezone.utc)}},
            upsert=True,
        )
        return True
    except Exception:
        logger.warning("[Mothership] MongoDB write failed:\n" + traceback.format_exc())
        return False

def get_title_data_from_mongo(keys: list = None):
    if title_data_collection is None:
        return None
    try:
        doc = title_data_collection.find_one({}, sort=[("last_updated", -1)])
        if not doc:
            return None
        results = doc.get("Results", [])
        if keys:
            results = [r for r in results if r.get("key") in keys]
        return results
    except Exception:
        logger.warning("[Mothership] Mongo title data fetch failed:\n" + traceback.format_exc())
        return None

def get_user_data_from_mongo(user_id: str, key_name: str):
    if user_data_collection is None:
        return None
    try:
        return user_data_collection.find_one({"user_id": user_id, "key_name": key_name})
    except Exception:
        logger.warning("[Mothership] Mongo user data fetch failed:\n" + traceback.format_exc())
        return None

def save_user_data_to_mongo(user_id: str, key_name: str, value) -> bool:
    if user_data_collection is None:
        return False
    try:
        metadata_id = str(uuid.uuid4())
        user_data_collection.update_one(
            {"user_id": user_id, "key_name": key_name},
            {"$set": {"value": value, "last_written_by": user_id,
                      "last_updated": datetime.now(timezone.utc)},
             "$inc": {"generation": 1},
             "$setOnInsert": {"id": "", "metadata_id": metadata_id,
                              "created_by": user_id, "created_at": datetime.now(timezone.utc)}},
            upsert=True,
        )
        return True
    except Exception:
        logger.warning("[Mothership] Mongo user data save failed:\n" + traceback.format_exc())
        return False

def send_mothership_webhook(title: str, claims: dict, user_id: str,
                            error: str = None, color: int = 3447003):
    if not MOTHERSHIP_WEBHOOK_URL:
        return
    result = "FAILED" if error else "PASSED"
    fields = [
        {"name": "Attestation", "value": result,      "inline": True},
        {"name": "User ID",     "value": str(user_id), "inline": True},
    ]
    if error:
        fields.append({"name": "Reason", "value": str(error), "inline": False})
    fields.append({"name": "Claims",
                   "value": "```json\n" + json.dumps(claims, indent=2)[:1000] + "\n```",
                   "inline": False})
    try:
        requests.post(MOTHERSHIP_WEBHOOK_URL, json={"embeds": [{
            "title":  title,
            "color":  color,
            "fields": fields,
        }]}, timeout=5)
    except Exception as e:
        logger.warning(f"[Mothership] Webhook failed: {e}")

def temp_ban_cert_user(user_key: str, duration_seconds: int = CERT_USER_BAN_DURATION_SECONDS):
    if not user_key:
        return
    with temp_cert_user_ban_lock:
        temp_cert_user_bans[str(user_key)] = time.time() + duration_seconds
    logger.warning(f"[CertBan] User {user_key} blocked for {duration_seconds}s")

def get_temp_cert_user_ban_remaining(user_key: str) -> Optional[int]:
    if not user_key:
        return None
    key = str(user_key)
    with temp_cert_user_ban_lock:
        expiry = temp_cert_user_bans.get(key)
        if expiry is None:
            return None
        remaining = int(expiry - time.time())
        if remaining <= 0:
            temp_cert_user_bans.pop(key, None)
            return None
        return remaining

def send_package_cert_webhook(client_ip, user_id, claims, digest, valid, banned=False):
    if not PACKAGE_CERT_WEBHOOK_URL:
        return
    app_state = claims.get("app_state", {}) if isinstance(claims, dict) else {}
    device_state = claims.get("device_state", {}) if isinstance(claims, dict) else {}
    status = "VALID · AUTHENTICATION PASSED" if valid else "INVALID · AUTHENTICATION FAILED"
    embed = {
        "title": "🛡️ Package Certificate · " + status,
        "color": 0x2ECC71 if valid else 0xE74C3C,
        "description": "The Oculus attestation contained `package_cert_sha256_digest` and it was checked by the server.",
        "fields": [
            {"name":"User ID","value":f"`{user_id or 'N/A'}`","inline":True},
            {"name":"Client IP","value":f"`{client_ip or 'unknown'}`","inline":True},
            {"name":"Package ID","value":f"`{app_state.get('package_id','N/A')}`","inline":True},
            {"name":"Version","value":f"`{app_state.get('version','N/A')}`","inline":True},
            {"name":"App Integrity","value":f"`{app_state.get('app_integrity_state','N/A')}`","inline":True},
            {"name":"Device Integrity","value":f"`{device_state.get('device_integrity_state','N/A')}`","inline":True},
            {"name":"SHA-256 Received","value":f"```json\n{json.dumps(digest, indent=2)}\n```","inline":False},
            {"name":"SHA-256 Expected","value":f"`{EXPECTED_PACKAGE_CERT_SHA256}`","inline":False},
            {"name":"Action","value":("✅ **ACCEPTED** — digest matched exactly." if valid else "⛔ **REJECTED** — user blocked for 10 minutes."),"inline":False},
        ],
        "footer":{"text":"Fast Taggers · Package Certificate Authentication"},
        "timestamp":datetime.now(timezone.utc).isoformat(),
    }
    try:
        res=requests.post(PACKAGE_CERT_WEBHOOK_URL,json={"embeds":[embed]},headers={"Content-Type":"application/json"},timeout=5)
        if res.status_code not in (200,204):
            logger.warning(f"[CertWebhook] Failed: {res.status_code} {res.text[:300]}")
    except Exception as e:
        logger.warning(f"[CertWebhook] Error: {e}")

def build_mothership_token(user_id: str, claims: dict) -> Optional[dict]:
    """Mint a Mothership JWT for user_id and persist it.

    Returns the token payload dict on success, or None if the JWT/EC key
    isn't configured (caller decides how to surface that).
    """
    if not JOSE_AVAILABLE or MOTHERSHIP_SECRET is None:
        return None

    expiration = datetime.now(timezone.utc) + timedelta(hours=1)
    payload = {
        "sub":             user_id,
        "externalService": "QUEST",
        "nbf":             int(datetime.now(timezone.utc).timestamp()),
        "iat":             int(datetime.now(timezone.utc).timestamp()),
        "exp":             int(expiration.timestamp()),
    }
    token = jose_jwt.encode(payload, MOTHERSHIP_SECRET, algorithm="ES256")
    save_token_to_db(user_id, user_id, token, int(expiration.timestamp() * 1000))
    send_mothership_webhook("Attestation Check Passed", claims, user_id)

    return {
        "MothershipToken": token,
        "MothershipId": user_id,
        "ExpirationTime": int(expiration.timestamp() * 1000),
        "ExternalProviderId": user_id,
        "ExternalProviderUsername": "",
        "IsPrimaryId": True,
        "PlayerId": user_id,
        "Tags": None,
        "Token": token,
        "ServerTime": int(time.time() * 1000),
        "statusCode": 200
    }

def issue_mothership_token(user_id: str, claims: dict):
    """HTTP wrapper around build_mothership_token for standalone routes
    (/v2/.../auth/complete/QUEST and /v1/.../auth/RIFT)."""
    token_data = build_mothership_token(user_id, claims)
    if token_data is None:
        return jsonify({"error": "Mothership JWT not configured"}), 500
    return jsonify(token_data), 200

def _decode_mothership_token(token: str) -> Optional[str]:
    """Decode JWT and return sub (user_id), or None on failure."""
    if not JOSE_AVAILABLE:
        return None
    try:
        decoded = jose_jwt.decode(token, None, options={"verify_signature": False})
        return decoded.get("sub")
    except Exception:
        return None

ENTITLEMENTS = {
    "SI_TechPoints":     {"entitlement_id": "d4a0fad9-4602-435d-b379-cd5f69fb4321", "name": "SI_TechPoints",     "in_game_id": "SI_TECH_POINTS",       "title_id": "f3e9fb19", "env_id": "7f3a99dd-5598-4725-98cf-6538d28feb9f", "type": "CURRENCY",              "tags": None},
    "SI_StrangeWood":    {"entitlement_id": "078b85fb-c0d9-44d5-a3ca-e325819b13cd", "name": "SI_StrangeWood",    "in_game_id": "SI_STRANGE_WOOD",      "title_id": "f3e9fb19", "env_id": "7f3a99dd-5598-4725-98cf-6538d28feb9f", "type": "CURRENCY_LOW_SCRUTINY", "tags": None},
    "SI_VibratingSpring":{"entitlement_id": "5150d276-db1a-4263-bff4-edbe7b55f841", "name": "SI_VibratingSpring","in_game_id": "SI_VIBRATING_SPRING", "title_id": "f3e9fb19", "env_id": "7f3a99dd-5598-4725-98cf-6538d28feb9f", "type": "CURRENCY_LOW_SCRUTINY", "tags": None},
    "SI_WeirdGear":      {"entitlement_id": "427839b6-58a4-4e8b-9cb4-3d48cb1fb513", "name": "SI_WeirdGear",      "in_game_id": "SI_WEIRD_GEAR",        "title_id": "f3e9fb19", "env_id": "7f3a99dd-5598-4725-98cf-6538d28feb9f", "type": "CURRENCY_LOW_SCRUTINY", "tags": None},
    "SI_FloppyMetal":    {"entitlement_id": "11844689-b2d0-4f02-923f-3bf49ba3aac6", "name": "SI_FloppyMetal",    "in_game_id": "SI_FLOPPY_METAL",      "title_id": "f3e9fb19", "env_id": "7f3a99dd-5598-4725-98cf-6538d28feb9f", "type": "CURRENCY_LOW_SCRUTINY", "tags": None},
    "SI_BouncySand":     {"entitlement_id": "8040ba58-afaa-44d3-bc0a-4d7864abf45d", "name": "SI_BouncySand",     "in_game_id": "SI_BOUNCY_SAND",       "title_id": "f3e9fb19", "env_id": "7f3a99dd-5598-4725-98cf-6538d28feb9f", "type": "CURRENCY_LOW_SCRUTINY", "tags": None},
    "GR_ResearchPoints": {"entitlement_id": "88342aff-549c-42dc-9998-ccc8160ba254", "name": "GR_ResearchPoints", "in_game_id": "GR_RESEARCH_POINTS",   "title_id": "f3e9fb19", "env_id": "7f3a99dd-5598-4725-98cf-6538d28feb9f", "type": "CURRENCY",              "tags": None},
}

DEFAULT_PROGRESSION_TREE_DATA = {
    "data": {"trees": [
        {"id": "f1e898ab-9c13-47f5-a044-cd7be3f51246", "name": "SI_Gadgets", "track_id": None,
         "created_at": "2025-10-02T15:53:15.278Z",
         "NodeDefinitions": [
             {"id": "408cc525-5013-4fe3-849a-ae90cca3294b", "name": "Initialize",
              "tree_id": "f1e898ab-9c13-47f5-a044-cd7be3f51246",
              "prerequisite_entitlements": None, "prerequisite_levels": None, "prerequisite_nodes": None,
              "transaction": {"transaction_id": "dee9bc37-5d7b-425f-8fed-4abb09a47ad8", "name": "T_SI_Initialize",
                              "inventory_changes": {"SI_TechPoints": {"Delta": 8}, "SI_StrangeWood": {"Delta": 8}, "SI_VibratingSpring": {"Delta": 8}}},
              "cost": None, "unlocked": True},
             {"id": "1001f2a8-1555-4356-bac0-ad5dc85038d2", "name": "Stilt_Unlock",
              "tree_id": "f1e898ab-9c13-47f5-a044-cd7be3f51246",
              "prerequisite_entitlements": None, "prerequisite_levels": None, "prerequisite_nodes": None,
              "transaction": None, "cost": {"SI_TechPoints": {"Delta": 8}, "SI_StrangeWood": {"Delta": 8}}, "unlocked": False},
             {"id": "1fb647a1-dcb5-48ea-ac60-59e59f49e89b", "name": "Thruster_Unlock",
              "tree_id": "f1e898ab-9c13-47f5-a044-cd7be3f51246",
              "prerequisite_entitlements": None, "prerequisite_levels": None, "prerequisite_nodes": None,
              "transaction": None, "cost": {"SI_TechPoints": {"Delta": 8}, "SI_VibratingSpring": {"Delta": 8}}, "unlocked": False},
             {"id": "81e9c384-9b08-4349-8039-ab2eda3e7c20", "name": "Platform_Unlock",
              "tree_id": "f1e898ab-9c13-47f5-a044-cd7be3f51246",
              "prerequisite_entitlements": None, "prerequisite_levels": None, "prerequisite_nodes": None,
              "transaction": None, "cost": {"SI_TechPoints": {"Delta": 8}, "SI_StrangeWood": {"Delta": 8}}, "unlocked": False},
             {"id": "90d1fddd-9a7c-4799-9f5f-75615a9820ec", "name": "Blaster_Standard_Unlock",
              "tree_id": "f1e898ab-9c13-47f5-a044-cd7be3f51246",
              "prerequisite_entitlements": None, "prerequisite_levels": None, "prerequisite_nodes": None,
              "transaction": None, "cost": {"SI_WeirdGear": {"Delta": 12}, "SI_TechPoints": {"Delta": 16}}, "unlocked": False},
         ]},
        {"id": "fcf4207d-399d-4678-a2a5-f204dbe3df6a", "name": "GRTools", "track_id": None,
         "created_at": "2025-07-22T18:07:38.310Z",
         "NodeDefinitions": [
             {"id": "9acd1c2c-c122-40c1-8a5c-4e10610711b1", "name": "EnergyEfficiency",
              "tree_id": "fcf4207d-399d-4678-a2a5-f204dbe3df6a",
              "prerequisite_entitlements": None, "prerequisite_levels": None, "prerequisite_nodes": None,
              "transaction": None, "cost": None, "unlocked": True},
             {"id": "d4f88967-e507-44a8-9ef3-cd2f598ed1de", "name": "ChargeBaton",
              "tree_id": "fcf4207d-399d-4678-a2a5-f204dbe3df6a",
              "prerequisite_entitlements": None, "prerequisite_levels": None, "prerequisite_nodes": None,
              "transaction": None, "cost": None, "unlocked": True},
             {"id": "40c36a94-de4f-4298-bc08-e4e0128499ee", "name": "FlashTool",
              "tree_id": "fcf4207d-399d-4678-a2a5-f204dbe3df6a",
              "prerequisite_entitlements": None, "prerequisite_levels": None, "prerequisite_nodes": None,
              "transaction": None, "cost": {"GR_ResearchPoints": {"Delta": 4}}, "unlocked": False},
         ]},
    ]}
}

def transform_cost_format(cost_dict: dict):
    if cost_dict is None:
        return None
    result = {}
    for currency, data in cost_dict.items():
        delta = data.get("Delta", 0) if isinstance(data, dict) else data
        ent = ENTITLEMENTS.get(currency)
        result[currency] = {"Entitlement": ent.copy(), "Delta": delta} if ent else {"Delta": delta}
    return result

def transform_transaction_format(txn: dict, title_id: str, env_id: str):
    if txn is None:
        return None
    t = txn.copy()
    t.setdefault("title_id", title_id)
    t.setdefault("env_id", env_id)
    for k in ("external_service_name", "external_service_entitlement_id",
              "revokable", "requires_external_fulfillment", "repeatable", "real_money_price"):
        t.setdefault(k, None)
    t.setdefault("sunset", False)
    if t.get("inventory_changes"):
        t["inventory_changes"] = transform_cost_format(t["inventory_changes"])
    return t

def get_progression_tree_data() -> dict:
    if progression_trees_collection is None:
        return DEFAULT_PROGRESSION_TREE_DATA
    try:
        doc = progression_trees_collection.find_one({"_id": "progression_trees"})
        if doc:
            doc.pop("_id", None)
            return doc
    except Exception:
        pass
    return DEFAULT_PROGRESSION_TREE_DATA


def sanitize_str(value, max_len: int = 256) -> str:
    """Coerce to a trimmed string, capped at max_len."""
    if value is None:
        return ""
    return str(value).strip()[:max_len]


def get_play_fab_id(mothership_id: str) -> Optional[str]:
    """Best-effort lookup of a PlayFabId for a given MothershipId.

    Mothership IDs are minted as PlayFabId values in this backend
    (see build_mothership_token/playfab_authentication), so today this is
    an identity mapping. Kept as a function so the lookup can be swapped
    for a real DB-backed mapping later without touching callers.
    """
    if not mothership_id:
        return None
    return mothership_id


def get_pf_headers() -> dict:
    return settings.get_auth_headers()


def _redact(obj):
    """Recursively replace values of sensitive keys (tickets, nonces, tokens)."""
    if isinstance(obj, dict):
        return {k: ("[redacted]" if str(k).lower() in REDACT_KEYS else _redact(v))
                for k, v in obj.items()}
    if isinstance(obj, list):
        return [_redact(v) for v in obj]
    return obj


def _send_request_hit_embed(endpoint: str, matched: bool):
    """Post a Discord embed describing an incoming HTTP request.

    Used by the global before_request hook so that EVERY request gets
    logged — not just ones that fall through to the catch-all 404 route.
    `matched` tells you whether this path corresponds to a real registered
    route or not, since that context is lost once you're inside a
    generic before_request hook.

    Sensitive fields (tickets, nonces, tokens) are redacted before posting.
    """
    client_ip = get_client_ip()

    body = request.get_json(silent=True)
    if body is not None:
        try:
            body_str = json.dumps(_redact(body), indent=2)
        except Exception:
            body_str = str(body)
    else:
        raw = request.get_data(as_text=True)
        body_str = raw if raw else "None"

    if len(body_str) > 950:
        body_str = body_str[:950] + "\n... (truncated)"

    title = "endpoint got boi" if matched else "unknown endpoint???"
    color = 0x4CAF50 if matched else 0xFFA500

    _post_discord_embed(settings.general_webhook_url, {
        "title": title,
        "color": color,
        "fields": [
            {"name": "Endpoint", "value": f"/{endpoint}", "inline": True},
            {"name": "Method",   "value": request.method, "inline": True},
            {"name": "IP",       "value": client_ip,      "inline": True},
            {"name": "Body",     "value": f"```json\n{body_str}\n```", "inline": False},
        ],
        "author": {"name": "endpoint logger boi"},
    })


@app.before_request
def log_every_request_to_discord():
    """Runs before EVERY request, whether or not it matches a real route."""
    if not LOG_ALL_REQUESTS_TO_DISCORD:
        return

    endpoint_path = request.path.lstrip("/")
    logger.info(f"[RequestLog] HIT: /{endpoint_path} method={request.method}")

    matched = request.url_rule is not None
    try:
        _send_request_hit_embed(endpoint_path, matched)
    except Exception as e:
        logger.error(f"[RequestLog] Failed to send webhook: {e}")


@app.before_request
def log_request_in():
    if not DEBUG_HTTP_LOGGING:
        return
    logger.info(f"\n{request.method} {request.path}")
    for k, v in request.headers.items():
        if k.lower() in REDACT_KEYS:
            v = "[redacted]"
        logger.info(f"  {k}: {v}")
    body = request.get_data(as_text=True)
    if body:
        logger.info(f"Body: {body[:500]}")

@app.after_request
def log_response_out(response):
    if DEBUG_HTTP_LOGGING:
        logger.info(f"📤 {response.status}")
    return response

@app.route("/", methods=["POST", "GET"])
def main():
    return jsonify({
        "MOTD": MOTD_TEXT
    })
@app.route("/api/PlayFabAuthentication",    methods=["POST", "GET"])
@app.route("/re/api/PlayFabAuthentication", methods=["POST"])
@app.route("/pf/api/PlayFabAuthentication", methods=["POST"])
@app.route("/reals/api/PlayFabAuthentication", methods=["POST"])
@app.route("/rea/api/PlayFabAuthentication",  methods=["POST"])
@app.route("/real/api/PlayFabAuthentication", methods=["POST"])
def playfab_authentication():
    rjson     = request.get_json(silent=True) or {}
    client_ip = get_client_ip()

    if is_ip_banned(client_ip):
        return reject_banned_ip(
            client_ip,
            oculus_id=rjson.get("OculusId"),
            custom_id=rjson.get("CustomId"),
        )

    temp_ban_remaining = get_temp_ip_ban_remaining(client_ip)
    if temp_ban_remaining is not None:
        return reject_temp_banned_ip(
            client_ip,
            temp_ban_remaining,
            oculus_id=rjson.get("OculusId"),
            custom_id=rjson.get("CustomId"),
        )

    required_fields = ["Nonce", "AppId", "Platform", "OculusId"]
    missing = [f for f in required_fields if not rjson.get(f)]
    if missing:
        send_auth_webhook(False, client_ip, oculus_id=rjson.get("OculusId"),
                          error_message=f"Missing parameter(s): {', '.join(missing)}",
                          nonce=rjson.get("Nonce"))
        return jsonify({"Message": f"Missing parameter(s): {', '.join(missing)}",
                        "Error": f"BadRequest-No{missing[0]}"}), 401

    if "MothershipToken" not in rjson or "MothershipId" not in rjson:
        send_mothership_token_webhook(
            "MothershipToken or MothershipId key missing from request body",
            client_ip, mothership_id=rjson.get("MothershipId"), token_present=False,
        )
        return jsonify({"Message": "Missing MothershipToken or MothershipId",
                        "Error": "BadRequest-NoMothershipToken"}), 400

    mothership_token = rjson["MothershipToken"]
    mothership_id    = rjson["MothershipId"]

    if not mothership_token:
        send_mothership_token_webhook(
            "MothershipToken is present but empty",
            client_ip, mothership_id=mothership_id, token_present=False,
        )
        return jsonify({"Message": "MothershipToken is empty",
                        "Error": "BadRequest-EmptyMothershipToken"}), 400

    token_ok, token_reason = validate_mothership_token(mothership_token, mothership_id)
    if not token_ok:
        send_mothership_token_webhook(
            token_reason, client_ip, mothership_id=mothership_id, token_present=True,
        )
        return jsonify({"Message": "Invalid MothershipToken",
                        "Error": "BadRequest-InvalidMothershipToken",
                        "Detail": token_reason}), 401

    if rjson.get("AppId") != settings.TitleId:
        send_auth_webhook(False, client_ip, oculus_id=rjson.get("OculusId"),
                          error_message="App ID mismatch", nonce=rjson.get("Nonce"))
        return jsonify({"Message": "Request sent for the wrong App ID",
                        "Error": "BadRequest-AppIdMismatch"}), 400

    platform = rjson.get("Platform", "")
    if platform == "Windows":
        send_auth_webhook(False, client_ip, oculus_id=rjson.get("OculusId"),
                          error_message="Windows platform blocked", nonce=rjson.get("Nonce"))
        return jsonify({"Message": "Forbidden platform", "Error": "Forbidden-Platform"}), 403

    custom_id = rjson.get("CustomId", "")
    if custom_id and not custom_id.startswith(("OC", "PI")):
        send_auth_webhook(False, client_ip, custom_id=custom_id,
                          error_message="Invalid CustomId prefix", nonce=rjson.get("Nonce"))
        return jsonify({"Message": "Bad request", "Error": "BadRequest-IncorrectPrefix"}), 400

    oculus_id = rjson["OculusId"]
    nonce     = rjson["Nonce"]

    if not get_is_nonce_valid(nonce, oculus_id):
        send_auth_webhook(False, client_ip, custom_id=custom_id, oculus_id=oculus_id,
                          error_message="Invalid or expired nonce", nonce=nonce)
        return jsonify({"Message": "Invalid nonce",
                        "Error": "BadRequest-InvalidNonce"}), 401

    org_scoped_id = get_org_scoped_id(oculus_id)
    if not org_scoped_id:
        send_auth_webhook(False, client_ip, custom_id=custom_id, oculus_id=oculus_id,
                          error_message="Invalid Oculus ID or org-scoped ID lookup failed",
                          nonce=nonce)
        return jsonify({"Message": "Invalid Oculus ID",
                        "Error": "BadRequest-InvalidOculusId"}), 400

    if custom_id.startswith("OCULUS"):
        claimed_org_id = custom_id[len("OCULUS"):]
        if not claimed_org_id.isdigit() or claimed_org_id != str(org_scoped_id):
            send_auth_webhook(False, client_ip, custom_id=custom_id, oculus_id=oculus_id,
                              error_message=f"CustomId org-scoped id mismatch "
                                            f"(claimed={claimed_org_id}, actual={org_scoped_id})",
                              nonce=nonce)
            return jsonify({"Message": "CustomId does not match authenticated Oculus account",
                            "Error": "BadRequest-CustomIdMismatch"}), 400

    server_custom_id = f"OCULUS{org_scoped_id}"
    if server_custom_id == "OCULUS0":
        ban_req = requests.post(
            f"https://{settings.TitleId}.playfabapi.com/Admin/BanUsers",
            json={"Bans": [{"PlayFabId": rjson.get("currentPlayerId", ""),
                            "DurationInHours": None, "Reason": "CHEATING - FAKE ORG SCOPED ID"}]},
            headers=settings.get_auth_headers(),
        )
        send_auth_webhook(False, client_ip, custom_id=custom_id, oculus_id=oculus_id,
                          error_message="OCULUS0 anti-cheat triggered", nonce=nonce)
        return jsonify({"Message": "Banned for cheating", "Error": "Banned"}), 403

    meta_alias = get_meta_alias(oculus_id)

    login_req = requests.post(
        url=f"https://{settings.TitleId}.playfabapi.com/Server/LoginWithServerCustomId",
        json={"ServerCustomId": server_custom_id, "CreateAccount": True},
        headers=settings.get_auth_headers(),
    )

    if login_req.status_code == 200:
        data         = login_req.json().get("data", {})
        playfab_id   = data.get("PlayFabId")
        session      = data.get("SessionTicket")
        entity       = data.get("EntityToken", {})
        entity_token = entity.get("EntityToken")
        entity_id    = entity.get("Entity", {}).get("Id")
        entity_type  = entity.get("Entity", {}).get("Type")

        # Persist the verified OculusId server-side. /api/photon reads it back
        # to validate the Photon nonce (Oculus can't resolve org-scoped ID -> user ID).
        try:
            update_user_internal_data(playfab_id, {"OculusId": str(oculus_id)})
        except Exception as e:
            logger.warning(f"[Auth] Failed to store OculusId for {playfab_id}: {e}")

        if custom_id:
            try:
                requests.post(
                    f"https://{settings.TitleId}.playfabapi.com/Server/LinkServerCustomId",
                    json={"ForceLink": True, "PlayFabId": playfab_id, "ServerCustomId": custom_id},
                    headers=settings.get_auth_headers(),
                )
            except Exception as e:
                logger.warning(f"[Auth] LinkServerCustomId failed: {e}")

        try:
            requests.post(
                f"https://{settings.TitleId}.playfabapi.com/Client/LinkCustomID",
                json={"CustomId": server_custom_id, "ForceLink": True},
                headers={"Content-Type": "application/json", "X-Authorization": session},
            )
        except Exception as e:
            logger.warning(f"[Auth] LinkCustomID failed: {e}")

        mothership_claims = {
            "request_details": {"nonce": nonce},
            "app_state":       {"app_integrity_state": "StoreRecognized",
                                "package_id": rjson.get("AppId")},
            "device_state":    {"device_integrity_state": "Advanced"},
        }
        mothership_data = build_mothership_token(playfab_id, mothership_claims)
        mothership_token_value = mothership_data.get("MothershipToken") if mothership_data else None

        send_auth_webhook(True, client_ip, custom_id=custom_id, playfab_id=playfab_id,
                          oculus_id=oculus_id, meta_alias=meta_alias, nonce=nonce,
                          mothership_token=mothership_token_value)

        session_id = generate_session_id()
        response_payload = {
            "PlayFabId":     playfab_id,
            "SessionTicket": session,
            "EntityToken":   entity_token,
            "EntityId":      entity_id,
            "EntityType":    entity_type,
            "SessionId":     session_id,
        }

        if mothership_data:
            response_payload.update(mothership_data)
        else:
            reason = "unknown"
            if not JOSE_AVAILABLE:
                reason = "python-jose not installed"
            elif not CRYPTO_AVAILABLE:
                reason = "cryptography not installed"
            elif MOTHERSHIP_SECRET is None:
                reason = "EC private key failed to load"
            logger.error(f"[Auth] Mothership token NOT issued for {playfab_id}: {reason}")
            response_payload["MothershipError"] = reason

        return jsonify(response_payload), 200

    else:
        if login_req.status_code == 403:
            ban_info = login_req.json()
            if ban_info.get("errorCode") == 1002:
                details = ban_info.get("errorDetails", {})
                key     = next(iter(details.keys()), None)
                exp     = (details.get(key, []) or ["Indefinite"])[0]
                send_auth_webhook(False, client_ip, custom_id=custom_id, oculus_id=oculus_id,
                                  error_message=f"Banned: {key}", nonce=nonce)
                return jsonify({"BanMessage": key, "BanExpirationTime": exp}), 403
            err_msg = ban_info.get("errorMessage", "Forbidden")
            send_auth_webhook(False, client_ip, custom_id=custom_id, oculus_id=oculus_id,
                              error_message=err_msg, nonce=nonce)
            return jsonify({"Error": "PlayFab Error", "Message": err_msg}), 403

        err = login_req.json()
        err_msg = err.get("errorMessage", "An error occurred.")
        send_auth_webhook(False, client_ip, custom_id=custom_id, oculus_id=oculus_id,
                          error_message=err_msg, nonce=nonce)
        return jsonify({"Error": "PlayFab Error", "Message": err_msg}), login_req.status_code

@app.route("/api/CachePlayFabId", methods=["POST", "GET"])
def cache_playfab_id():
    rjson = request.get_json(silent=True) or {}

    if "SessionTicket" in rjson and "PlayFabId" not in rjson:
        rjson["PlayFabId"] = rjson["SessionTicket"].split("-")[0]
    pid = rjson.get("PlayFabId")
    if not pid:
        return jsonify({"Message": "Try Again Later."}), 404
    playfab_cache[pid] = rjson
    logger.info(f"[Cache] Cached PlayFabId: {pid}")
    return jsonify({"Message": "Authed", "PlayFabId": pid}), 200

@app.route("/api/CCU", methods=["POST"])
def ccu():
    """Concurrent-user counter.

    If the request body contains a numeric "PlayersOnline", store it as the
    new total. Every call (whether or not it updated the value) returns the
    currently stored total, so all clients see the same number until a
    request arrives with a different PlayersOnline value.
    """
    global ccu_total
    rjson = request.get_json(silent=True)
    if not isinstance(rjson, dict):
        rjson = {}

    players = rjson.get("PlayersOnline")
    if isinstance(players, (int, float)) and not isinstance(players, bool):
        with ccu_lock:
            ccu_total = int(players)

    with ccu_lock:
        current = ccu_total

    return jsonify({"CCUTotal": current}), 200

@app.route("/nonce", methods=["GET"])
def nonce_endpoint():
    try:
        value = "".join(secrets.choice(string.ascii_letters + string.digits) for _ in range(32))
        return jsonify({"Nonce": value}), 200
    except Exception as e:
        return jsonify({"Error": str(e)}), 500

@app.route("/api/TitleData", methods=["POST", "GET"])
def title_data():
    response = requests.post(
        url=f"https://{settings.TitleId}.playfabapi.com/Server/GetTitleData",
        headers=settings.get_auth_headers(),
    )
    if response.status_code == 200:
        raw  = response.json().get("data", {}).get("Data", {})
        data = json.loads(json.dumps(raw).replace("\\\\", "\\"))
        return jsonify(data)
    return jsonify({}), response.status_code

@app.route("/api/CheckForBadName", methods=["POST", "GET"])
def check_for_bad_name():
    body      = request.get_json(silent=True) or {}
    func_arg  = body.get("FunctionArgument") or body.get("FunctionResult") or {}
    name      = (func_arg.get("name") or "").upper().strip()
    playfab_id = body.get("CallerEntityProfile", {}).get("Lineage", {}).get("MasterPlayerAccountId")

    logger.info(f"[NameCheck] name={name!r} playfab_id={playfab_id}")

    banned     = False
    ban_reason = "No ban"

    for pattern in OFFENSIVE_PATTERNS:
        if pattern in name:
            ban_reason = "DEFAMATION DETECTED. CONTINUED USE WILL RESULT IN LEGAL ACTION"
            if playfab_id:
                ban_user(playfab_id, name=name, reason=ban_reason)
            banned = True
            break

    if not banned:
        for word in BAD_WORDS:
            if word in name:
                ban_reason = f"BAD NAME DETECTED: {name}"
                if playfab_id:
                    ban_user(playfab_id, name=name, reason=ban_reason, duration_hours=1)
                banned = True
                break

    _post_discord_embed(settings.name_webhook_url, {
        "title": "Name Entry",
        "color": 0xFF5733 if banned else 0x4CAF50,
        "fields": [
            {"name": "Entry",      "value": name or "N/A",           "inline": True},
            {"name": "PlayFab ID", "value": playfab_id or "Unknown", "inline": True},
            {"name": "Action",     "value": ban_reason,              "inline": False},
        ],
    })

    return jsonify({"result": 2 if banned else 0, "banLength": -1})

@app.route("/api/GetRandomName", methods=["POST", "GET"])
@app.route("/api/GetName",       methods=["POST", "GET"])
@app.route("/api/v2/GetName",    methods=["POST", "GET"])
def get_random_name():
    return jsonify({"result": f"GORILLA{random.randint(1000, 9999)}"})

@app.route("/api/GetAcceptedAgreements", methods=["POST", "GET"])
def get_accepted_agreements():
    body = request.get_json(silent=True) or {}
    func_result = body.get("FunctionResult", {})
    if func_result:
        return jsonify(func_result)
    return jsonify({"PrivacyPolicy": "2024.09.20", "TOS": "2024.09.20", "EULA": "2024.09.20"}), 200

@app.route("/api/SubmitAcceptedAgreements", methods=["POST", "GET"])
def submit_accepted_agreements():
    rjson      = request.get_json(silent=True) or {}
    ticket     = rjson.get("PlayFabTicket")
    agreements = rjson.get("Agreements", {})

    if ticket:
        auth = requests.post(
            f"https://{settings.TitleId}.playfabapi.com/Server/AuthenticateSessionTicket",
            json={"SessionTicket": ticket},
            headers=settings.get_auth_headers(),
        )
        if auth.status_code != 200:
            return "", 400

        playfab_id = auth.json().get("data", {}).get("UserInfo", {}).get("PlayFabId")
        for key, val in agreements.items():
            requests.post(
                f"https://{settings.TitleId}.playfabapi.com/Server/UpdateUserData",
                headers=settings.get_auth_headers(),
                json={"PlayFabId": playfab_id, "Data": {f"accepted_agreement:{key}": val}},
            )

    func_result = rjson.get("FunctionResult", {})
    if func_result:
        return jsonify(func_result)
    return jsonify({"status": "ok", "PrivacyPolicy": "2024.09.20", "TOS": "2024.09.20"}), 200

@app.route("/api/ConsumeOculusIAP", methods=["POST", "GET"])
def consume_oculus_iap():
    rjson   = request.get_json(silent=True) or {}
    missing = validate_input(rjson, ["userID", "nonce", "sku"])
    if missing:
        return jsonify({"error": f"Missing required fields: {', '.join(missing)}"}), 400

    user_id = rjson.get("userID")
    nonce   = rjson.get("nonce")
    sku     = rjson.get("sku")

    response = requests.post(
        url=f"https://graph.oculus.com/consume_entitlement?nonce={nonce}&user_id={user_id}&sku={sku}&access_token={settings.ApiKey}",
        headers={"content-type": "application/json"},
    )
    if response.json().get("success"):
        return jsonify({"result": True})
    return jsonify({"error": True, "message": response.json().get("message", "Consume failed")})

@app.route("/api/ConsumeCodeItem",       methods=["POST"])
@app.route("/re/api/ConsumeCodeItem",    methods=["POST"])
@app.route("/pf/api/ConsumeCodeItem",    methods=["POST"])
@app.route("/reals/api/ConsumeCodeItem", methods=["POST"])
@app.route("/rea/api/ConsumeCodeItem",   methods=["POST"])
@app.route("/real/api/ConsumeCodeItem",  methods=["POST"])
def consume_code_item():
    try:
        data       = request.get_json()
        code_id    = (data.get("itemGUID") or "").upper()
        playfab_id = data.get("playFabID")

        codes      = load_codes()
        code_entry = find_code(codes, code_id)

        if not code_entry:
            return jsonify({"result": "CodeNotFound"}), 404

        if code_entry.get("redeemed"):
            return jsonify({"result": "AlreadyRedeemed",
                            "playFabItemName": code_entry.get("cosmetic")}), 200

        grant_resp = grant_cosmetic_to_player(playfab_id, code_entry["cosmetic"])
        if grant_resp.status_code != 200:
            return jsonify({"result": "GrantFailed", "error": grant_resp.text}), 500

        code_entry["redeemed"] = True
        save_codes(codes)

        _post_discord_embed(settings.code_webhook_url, {
            "title": "Code Redeemed",
            "description": (f"**PlayFab ID**: {playfab_id}\n"
                            f"**Code**: `{code_id}`\n"
                            f"**Cosmetic**: `{code_entry['cosmetic']}`"),
            "color": 0x00FF00,
        })

        return jsonify({"result": "Success", "itemID": code_id,
                        "playFabItemName": code_entry["cosmetic"]}), 200

    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/SetPrivacyState",    methods=["POST"])
@app.route("/re/api/SetPrivacyState", methods=["POST"])
def set_privacy_state():
    rjson      = request.get_json()
    playfab_id = rjson.get("PlayFabId", "")
    privacy    = rjson.get("PrivacyState", "VISIBLE")
    ticket     = rjson.get("PlayFabTicket", "")

    if not playfab_id or not ticket or settings.privacy_state_id_to_name(privacy) == -1:
        return "", 400

    auth = requests.post(
        f"https://{settings.TitleId}.playfabapi.com/Server/AuthenticateSessionTicket",
        json={"SessionTicket": ticket},
        headers=settings.get_auth_headers(),
    )
    if (auth.status_code != 200
            or auth.json()["data"]["UserInfo"]["PlayFabId"] != playfab_id):
        return "", 400

    requests.post(
        f"https://{settings.TitleId}.playfabapi.com/Server/UpdateUserInternalData",
        headers=settings.get_auth_headers(),
        json={"PlayFabId": playfab_id, "Data": {"PrivacyState": privacy}},
    )
    return jsonify({"statusCode": 200, "error": None}), 200

@app.route("/api/GetFriendsV2", methods=["POST"])
def get_friends_v2():
    rjson = request.get_json(silent=True) or {}

    playfab_id = rjson.get("PlayFabId", "")
    ticket = rjson.get("PlayFabTicket", "")

    if not playfab_id or not ticket:
        return "Missing fields", 400

    auth = requests.post(
        f"https://{settings.TitleId}.playfabapi.com/Server/AuthenticateSessionTicket",
        json={"SessionTicket": ticket},
        headers=settings.get_auth_headers(),
        timeout=5,
    )

    if (
        auth.status_code != 200
        or auth.json().get("data", {}).get("UserInfo", {}).get("PlayFabId") != playfab_id
    ):
        return "", 400

    internal = get_user_internal_data(playfab_id).get("data", {}).get("Data", {})

    friend_str = internal.get("Friends", {}).get("Value", "")
    privacy_state_str = internal.get("PrivacyState", {}).get("Value", "VISIBLE")

    room_data = load_room_data()
    friends = []

    for fid in friend_str.split(","):
        fid = fid.strip()

        if not fid:
            continue

        fd_resp = get_user_internal_data(fid)

        if fd_resp.get("code") not in (None, 200) and "data" not in fd_resp:
            continue

        d = fd_resp.get("data", {}).get("Data", {})

        def clean(x):
            return None if x in ("null", "") else x

        nickname = clean(d.get("Nickname", {}).get("Value", ""))
        zone = clean(d.get("Zone", {}).get("Value", ""))
        region = clean(d.get("Region", {}).get("Value", ""))
        is_public = d.get("IsPublic", {}).get("Value", "false")
        friend_priv = d.get("PrivacyState", {}).get("Value", "VISIBLE")

        stored_room = room_data.get(str(fid))

        room_id = None
        stored_zone = None
        stored_region = None

        if isinstance(stored_room, dict):
            last_seen = stored_room.get("lastSeen", 0)

            if time.time() - last_seen <= 60:
                room_id = stored_room.get("roomId")
                stored_zone = stored_room.get("zone")
                stored_region = stored_room.get("region")

        elif stored_room:
            room_id = stored_room

        if stored_zone:
            zone = stored_zone

        if stored_region:
            region = stored_region

        presence = {
            "friendLinkId": fid,
            "userName": nickname,
            "roomId": None,
            "zone": None,
            "region": None,
            "isPublic": is_public
        }

        if friend_priv == "VISIBLE":
            presence.update({
                "roomId": room_id,
                "zone": zone,
                "region": region,
                "isPublic": is_public
            })

        elif friend_priv == "PUBLIC_ONLY" and is_public == "true":
            presence.update({
                "roomId": room_id,
                "zone": zone,
                "region": region,
                "isPublic": is_public
            })

        friends.append({
            "presence": presence,
            "created": datetime.now(timezone.utc).isoformat()
        })

    return jsonify({
        "result": {
            "friends": friends,
            "myPrivacyState": settings.privacy_state_id_to_name(privacy_state_str)
        },
        "statusCode": 200,
        "error": None,
    })

@app.route("/api/RequestFriend",    methods=["POST"])
@app.route("/re/api/RequestFriend", methods=["POST"])
def request_friend():
    rjson          = request.get_json()
    playfab_id     = rjson.get("PlayFabId", "")
    friend_link_id = rjson.get("FriendFriendLinkId", "")
    ticket         = rjson.get("PlayFabTicket", "")

    if not playfab_id:     return "Must supply a valid PlayFab ID", 400
    if not friend_link_id: return "Must supply a valid FriendFriendLinkId", 400
    if authenticate_ticket(ticket, playfab_id) is None:
        return "", 500

    data = get_user_internal_data(playfab_id)
    friends_str = data.get("data", {}).get("Data", {}).get("Friends", {}).get("Value", "")
    friends = set(friends_str.split(",")) if friends_str else set()
    friends.add(friend_link_id)
    update_user_internal_data(playfab_id, {"Friends": ",".join(friends)})
    return jsonify({"statusCode": 200, "error": None}), 200

@app.route("/api/RemoveFriend",    methods=["POST"])
@app.route("/re/api/RemoveFriend", methods=["POST"])
def remove_friend():
    rjson          = request.get_json()
    playfab_id     = rjson.get("PlayFabId", "")
    friend_link_id = rjson.get("FriendFriendLinkId", "")
    my_link_id     = rjson.get("MyFriendLinkId", "")
    ticket         = rjson.get("PlayFabTicket", "")

    if not playfab_id:     return "Must supply a valid PlayFab ID", 400
    if not friend_link_id: return "Must supply a valid FriendFriendLinkId", 400
    if authenticate_ticket(ticket, playfab_id) is None:
        return "Unauthorized", 403

    for a, b in [(playfab_id, friend_link_id), (friend_link_id, my_link_id)]:
        d = get_user_internal_data(a)
        fs = d.get("data", {}).get("Data", {}).get("Friends", {}).get("Value", "")
        friends = set(fs.split(",")) if fs else set()
        friends.discard(b)
        update_user_internal_data(a, {"Friends": ",".join(friends)})

    return jsonify({"statusCode": 200, "error": None}), 200

@app.route("/api/GetQuestStatus",    methods=["POST"])
@app.route("/re/api/GetQuestStatus", methods=["POST"])
def get_quest_status():
    rjson      = request.get_json()
    playfab_id = rjson.get("PlayFabId")
    ticket     = rjson.get("PlayFabTicket")

    if authenticate_ticket(ticket, playfab_id) is None:
        return "", 400

    try:
        val_str = requests.post(
            f"https://{settings.TitleId}.playfabapi.com/Server/GetUserData",
            headers=settings.get_auth_headers(),
            json={"PlayFabId": playfab_id, "Keys": ["progression_v1"]},
        ).json()["data"]["Data"]["progression_v1"]["Value"]
        result = loads(val_str)
    except Exception:
        result = {"dailyPoints": {}, "weeklyPoints": {}, "userPointsTotal": 0}

    return jsonify({"result": result, "statusCode": 200, "error": None})

@app.route("/api/SetQuestComplete", methods=["POST"])
def set_quest_complete():
    rjson      = request.get_json()
    playfab_id = rjson.get("PlayFabId")
    ticket     = rjson.get("PlayFabTicket")

    if authenticate_ticket(ticket, playfab_id) is None:
        return "", 400

    try:
        val_str = requests.post(
            f"https://{settings.TitleId}.playfabapi.com/Admin/GetUserData",
            headers=settings.get_auth_headers(),
            json={"PlayFabId": playfab_id, "Keys": ["progression_v1"]},
        ).json()["data"]["Data"]["progression_v1"]["Value"]
        current = loads(val_str)
    except Exception:
        current = {"dailyPoints": {}, "weeklyPoints": {}, "userPointsTotal": 0}

    today   = datetime.utcnow().strftime("%m/%d/%Y")
    week    = str(datetime.utcnow().isocalendar()[1])
    current["dailyPoints"][today]  = current["dailyPoints"].get(today, 0) + 1
    current["weeklyPoints"][week]  = current["weeklyPoints"].get(week, 0)
    current["userPointsTotal"]    += 1

    requests.post(
        f"https://{settings.TitleId}.playfabapi.com/Admin/UpdateUserData",
        headers=settings.get_auth_headers(),
        json={"PlayFabId": playfab_id,
              "Data": {"progression_v1": dumps(current)}, "Permission": "Private"},
    )
    return jsonify({"result": current, "statusCode": 200, "error": None})

@app.route("/api/FetchPoll",       methods=["GET", "POST"])
@app.route("/re/api/FetchPoll",    methods=["GET", "POST"])
@app.route("/pf/api/FetchPoll",    methods=["GET", "POST"])
@app.route("/reals/api/FetchPoll", methods=["GET", "POST"])
@app.route("/rea/api/FetchPoll",   methods=["GET", "POST"])
@app.route("/real/api/FetchPoll",  methods=["GET", "POST"])
def fetch_poll():
    global poll_cache
    polls = load_votes()
    poll_cache = polls
    return jsonify(polls), 200

@app.route("/api/Vote", methods=["POST"])
def vote():
    data          = request.get_json()
    playfab_id    = data.get("PlayFabId")
    poll_id       = int(data.get("PollId", data.get("pollId", -1)))
    option_index  = data.get("OptionIndex", data.get("optionIndex"))
    is_prediction = data.get("IsPrediction", data.get("isPrediction", False))

    polls = load_votes()
    poll  = next((p for p in polls if p.get("pollId", p.get("PollId")) == poll_id), None)
    if not poll or not poll.get("isActive"):
        return "", 404

    options = poll.get("voteOptions", [])
    if not isinstance(option_index, int) or not (0 <= option_index < len(options)):
        return "", 400

    if len(poll.get("voteCount", [])) != len(options):
        poll["voteCount"] = [0] * len(options)
    if len(poll.get("predictionCount", [])) != len(options):
        poll["predictionCount"] = [0] * len(options)

    if is_prediction:
        poll["predictionCount"][option_index] += 1
    else:
        poll["voteCount"][option_index] += 1

    save_votes(polls)

    _post_discord_embed(settings.vote_webhook_url, {
        "title": "Vote Recorded",
        "description": (f"**PlayFab ID**: {playfab_id}\n"
                        f"**Poll**: {poll.get('question', '')}\n"
                        f"**Voted**: {options[option_index]}\n"
                        f"**Prediction**: {is_prediction}"),
        "color": 3447003,
    })
    return jsonify(poll), 200

@app.route("/api/64", methods=["POST"])
def upload_gorillanalytics():
    data = request.get_json()
    if not data:
        return jsonify({"error": "Invalid data"}), 400

    func_result = data.get("FunctionResult", {})

    _post_discord_embed(settings.analytics_webhook_url, {
        "title": "Analytics Upload",
        "color": 5814783,
        "fields": [
            {"name": "Version",       "value": str(func_result.get("version",       "N/A")), "inline": True},
            {"name": "Upload Chance", "value": str(func_result.get("upload_chance", "N/A")), "inline": True},
            {"name": "Map",           "value": str(func_result.get("map",           "N/A")), "inline": True},
            {"name": "Mode",          "value": str(func_result.get("mode",          "N/A")), "inline": True},
            {"name": "Queue",         "value": str(func_result.get("queue",         "N/A")), "inline": True},
            {"name": "Player Count",  "value": str(func_result.get("player_count",  "N/A")), "inline": True},
            {"name": "Position",
             "value": f"({func_result.get('pos_x','?')}, {func_result.get('pos_y','?')}, {func_result.get('pos_z','?')})",
             "inline": False},
            {"name": "Cosmetics Worn",  "value": str(func_result.get("cosmetics_worn",  "None")), "inline": False},
            {"name": "Cosmetics Owned", "value": str(func_result.get("cosmetics_owned", "None")), "inline": False},
        ],
    })
    return jsonify({"status": "Success"}), 200

@app.route("/api/ReturnMyOculusHashV2", methods=["POST", "GET"])
def return_my_oculus_hash_v2():
    rjson = request.get_json()

    try:
        master_id = rjson["CallerEntityProfile"]["Lineage"]["MasterPlayerAccountId"]
        resp = requests.post(
            f"https://{settings.TitleId}.playfabapi.com/Server/GetUserAccountInfo",
            headers=settings.get_auth_headers(),
            json={"PlayFabId": master_id},
        )
        if resp.status_code == 200:
            custom_id = (resp.json()["data"]["UserInfo"]["ServerCustomIdInfo"]["CustomId"]
                         .replace("OCULUS", ""))
            h = hashlib.sha256(custom_id.encode("utf-8")).hexdigest()
            return jsonify({"oculusHash": h, "error": False}), 200
    except Exception:
        pass

    return return_function_json(rjson, "ReturnMyOculusHash")

@app.route("/api/ReturnCurrentVersionV2", methods=["POST", "GET"])
def return_current_version_v2():
    rjson = request.get_json()
    try:
        caller_id = rjson["CallerEntityProfile"]["Lineage"]["MasterPlayerAccountId"]
        if rjson.get("FunctionArgument", {}).get("UpdatedSynchTest") != 12379015:
            ban_user(caller_id)
            return jsonify({"Fail": True, "ResultCode": None})
    except (KeyError, TypeError):
        pass
    return return_function_json(rjson, "ReturnCurrentVersion")

@app.route("/api/TryDistributeCurrencyV2", methods=["POST", "GET"])
def try_distribute_currency_v2():
    """Daily login currency reward — gives SR once per UTC day, then proxies cloud script."""
    rjson = request.get_json(silent=True) or {}

    SR_PER_DAY = 100

    current_player_id = (rjson.get("CallerEntityProfile", {})
                              .get("Lineage", {})
                              .get("MasterPlayerAccountId"))

    if current_player_id and settings.TitleId and settings.SecretKey:
        try:
            get_data_resp = requests.post(
                f"https://{settings.TitleId}.playfabapi.com/Server/GetUserReadOnlyData",
                headers=settings.get_auth_headers(),
                json={"PlayFabId": current_player_id, "Keys": ["DailyLogin"]},
            )
            daily_login_value = (get_data_resp.json()
                                              .get("data", {})
                                              .get("Data", {})
                                              .get("DailyLogin", {})
                                              .get("Value"))

            last_login_date = None
            if daily_login_value:
                last_login_date = (
                    datetime.fromisoformat(daily_login_value.replace("Z", "+00:00"))
                    .astimezone(timezone.utc)
                    .replace(hour=0, minute=0, second=0, microsecond=0)
                )

            today_utc = datetime.utcnow().replace(hour=0, minute=0, second=0,
                                                  microsecond=0, tzinfo=timezone.utc)
            if not last_login_date or last_login_date < today_utc:
                requests.post(
                    f"https://{settings.TitleId}.playfabapi.com/Server/AddUserVirtualCurrency",
                    headers=settings.get_auth_headers(),
                    json={"PlayFabId": current_player_id,
                          "VirtualCurrency": "SR", "Amount": SR_PER_DAY},
                )
                requests.post(
                    f"https://{settings.TitleId}.playfabapi.com/Server/UpdateUserReadOnlyData",
                    headers=settings.get_auth_headers(),
                    json={"PlayFabId": current_player_id,
                          "Data": {"DailyLogin": today_utc.isoformat()}},
                )
                logger.info(f"[Currency] Gave {SR_PER_DAY} SR to {current_player_id}")
        except Exception as e:
            logger.warning(f"[Currency] Daily login error: {e}")

    return return_function_json(rjson, "TryDistributeCurrency")

@app.route("/api/BroadCastMyRoomV2", methods=["POST", "GET"])
def broadcast_my_room_v2():
    rjson = request.get_json(silent=True) or {}
    function_param = rjson.get("FunctionParameter", {}) or {}

    user_id = (
        rjson.get("UserId")
        or function_param.get("UserId")
        or function_param.get("PlayFabId")
        or function_param.get("CreatorId")
    )

    room_id = (
        function_param.get("GameId")
        or function_param.get("RoomId")
        or function_param.get("RoomCode")
        or function_param.get("roomId")
    )

    zone = function_param.get("Zone") or function_param.get("zone")

    region = (
        function_param.get("Region")
        or function_param.get("region")
    )

    if user_id and room_id:
        set_player_room(
            user_id,
            room_id,
            zone,
            region
        )

    _post_discord_embed(
        settings.general_webhook_url or settings.photon_webhook_url,
        {
            "color": 0x00BFFF,
            "fields": [{
                "name": "Room Broadcast",
                "value": (
                    f"```ini\n"
                    f"[Room ID]: {room_id or 'Unknown'}\n"
                    f"[Region]:  {str(region or 'Unknown').upper()}\n"
                    f"[Creator]: {function_param.get('CreatorName', 'Unknown')}\n"
                    f"[IP]:      {get_client_ip()}```"
                ),
            }],
            "author": {"name": "Room Broadcast"},
        },
    )

    return return_function_json(
        rjson,
        "BroadCastMyRoom",
        function_param
    )

@app.route("/api/ShouldUserAutomutePlayer", methods=["POST", "GET"])
def should_user_automute_player():
    return jsonify(mute_cache)

@app.route("/api/GrantCurrency", methods=["POST"])
def grant_currency():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["PlayFabId", "Currency", "Amount"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    response = requests.post(
        f"https://{settings.TitleId}.playfabapi.com/Admin/AddUserVirtualCurrency",
        json={"PlayFabId": rjson["PlayFabId"],
              "VirtualCurrency": rjson["Currency"],
              "Amount": rjson["Amount"]},
        headers=settings.get_auth_headers(),
    )
    return jsonify(response.json().get("data", {})), response.status_code

@app.route("/api/GetInventory", methods=["POST"])
def get_inventory():
    rjson = request.get_json()
    pid   = rjson.get("PlayFabId")
    if not pid:
        return jsonify({"error": "Missing PlayFabId"}), 400
    return execute_cloud_script(pid, "GetUserInventory")

@app.route("/api/GetLeaderboard", methods=["POST"])
def get_leaderboard():
    rjson = request.get_json()
    return execute_cloud_script(rjson.get("PlayFabId"), "GetLeaderboard",
                                {"StatisticName": rjson.get("StatisticName", "GlobalScore")})

@app.route("/api/UpdateStats", methods=["POST"])
def update_stats():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["PlayFabId", "Statistics"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    return execute_cloud_script(rjson["PlayFabId"], "UpdatePlayerStatistics", rjson["Statistics"])

@app.route("/api/UpdateProfile", methods=["POST"])
def update_profile():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["PlayFabId", "DisplayName"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    return execute_cloud_script(rjson["PlayFabId"], "UpdateUserTitleDisplayName",
                                {"DisplayName": rjson["DisplayName"]})

@app.route("/api/GetAchievements", methods=["POST"])
def get_achievements():
    rjson = request.get_json()
    pid   = rjson.get("PlayFabId")
    if not pid:
        return jsonify({"error": "Missing PlayFabId"}), 400
    return execute_cloud_script(pid, "GetPlayerAchievements")

@app.route("/api/UnlockAchievement", methods=["POST"])
def unlock_achievement():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["PlayFabId", "AchievementId"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    return execute_cloud_script(rjson["PlayFabId"], "UnlockAchievement",
                                {"AchievementId": rjson["AchievementId"]})

@app.route("/api/ReportPlayer", methods=["POST"])
def report_player():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["ReporterId", "ReportedId", "Reason"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    logger.info(f"[Report] {rjson['ReporterId']} reported {rjson['ReportedId']} for {rjson['Reason']}")
    return jsonify({"success": True, "message": "Report submitted"}), 200

@app.route("/api/CreateParty", methods=["POST"])
def create_party():
    rjson = request.get_json()
    if not rjson.get("PlayFabId"):
        return jsonify({"error": "Missing PlayFabId"}), 400
    return jsonify({"success": True, "PartyId": generate_session_id()}), 200

@app.route("/api/JoinParty", methods=["POST"])
def join_party():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["PlayFabId", "PartyId"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    return jsonify({"success": True}), 200

@app.route("/api/LeaveParty", methods=["POST"])
def leave_party():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["PlayFabId", "PartyId"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    return jsonify({"success": True}), 200

@app.route("/api/InviteToParty", methods=["POST"])
def invite_to_party():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["PlayFabId", "FriendId", "PartyId"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    return jsonify({"success": True}), 200

@app.route("/api/CreateGuild", methods=["POST"])
def create_guild():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["PlayFabId", "GuildName"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    return jsonify({"success": True, "GuildId": generate_session_id()}), 200

@app.route("/api/JoinGuild", methods=["POST"])
def join_guild():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["PlayFabId", "GuildId"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    return jsonify({"success": True}), 200

@app.route("/api/GetGuildInfo", methods=["POST"])
def get_guild_info():
    rjson = request.get_json()
    gid   = rjson.get("GuildId")
    if not gid:
        return jsonify({"error": "Missing GuildId"}), 400
    return jsonify({"guild": {"id": gid, "name": "SampleGuild", "members": 10}}), 200

@app.route("/api/StartMatchmaking", methods=["POST"])
def start_matchmaking():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["PlayFabId", "GameMode"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    return jsonify({"success": True, "MatchId": generate_session_id()}), 200

@app.route("/api/CancelMatchmaking", methods=["POST"])
def cancel_matchmaking():
    rjson = request.get_json()
    if not rjson.get("PlayFabId"):
        return jsonify({"error": "Missing PlayFabId"}), 400
    return jsonify({"success": True}), 200

@app.route("/api/GetMatchHistory", methods=["POST"])
def get_match_history():
    rjson = request.get_json()
    if not rjson.get("PlayFabId"):
        return jsonify({"error": "Missing PlayFabId"}), 400
    return jsonify({"matches": [{"id": "match1", "result": "win", "date": "2025-09-11"}]}), 200

@app.route("/api/GetDailyQuests", methods=["POST"])
def get_daily_quests():
    rjson = request.get_json()
    if not rjson.get("PlayFabId"):
        return jsonify({"error": "Missing PlayFabId"}), 400
    return jsonify({"quests": [{"id": "quest1", "name": "Tag 5 Players", "reward": 100}]}), 200

@app.route("/api/CompleteQuest", methods=["POST"])
def complete_quest():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["PlayFabId", "QuestId"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    return execute_cloud_script(rjson["PlayFabId"], "CompleteQuest",
                                {"QuestId": rjson["QuestId"]})

@app.route("/api/GetServerStatus", methods=["GET"])
def get_server_status():
    uptime = str(timedelta(seconds=int(time.time() - app.start_time))) \
             if hasattr(app, "start_time") else "unknown"
    return jsonify({
        "status":        "online",
        "uptime":        uptime,
        "activePlayers": random.randint(100, 1000),
    }), 200

@app.route("/api/GetServerConfig", methods=["GET"])
def get_server_config():
    return jsonify({
        "version":    "1.2.3",
        "maintenance": False,
        "regions":    ["US", "EU", "AS"],
        "maxPlayers": 1000,
    }), 200

@app.route("/api/SubmitFeedback", methods=["POST"])
def submit_feedback():
    rjson   = request.get_json()
    missing = validate_input(rjson, ["PlayFabId", "Feedback"])
    if missing:
        return jsonify({"error": f"Missing fields: {', '.join(missing)}"}), 400
    logger.info(f"[Feedback] {rjson['PlayFabId']}: {rjson['Feedback']}")
    return jsonify({"success": True}), 200

@app.route("/api/GetSeasonalEvent", methods=["POST"])
def get_seasonal_event():
    return jsonify({
        "EventName":  "WinterFest2025",
        "StartDate":  "2025-12-01",
        "EndDate":    "2026-01-15",
        "Rewards":    ["snow_hat", "ice_gloves"],
    }), 200

# ─────────────────────────────────────────────────────────────────────────────
# Photon custom authentication
# ─────────────────────────────────────────────────────────────────────────────

def _photon_error(code: int, message: str, status: int):
    # Photon reads "ResultCode"/"Message"; the lowercase keys are kept for
    # anything that already depends on them.
    return jsonify({"resultCode": code, "ResultCode": code,
                    "message": message, "Message": message,
                    "userId": None, "nickname": None}), status


@app.route("/api/photon", methods=["POST", "GET"])
@app.route("/api/photon/authenticate", methods=["POST", "GET"])
@app.route("/pf/api/photon", methods=["POST", "GET"])
def photon():
    if request.method == "GET":
        return _photon_error(0, "GET auth is deprecated", 400)

    try:
        rjson = request.get_json(silent=True)
        if not isinstance(rjson, dict):
            rjson = {}
        client_ip = get_client_ip()

        app_id   = rjson.get("AppId")
        platform = rjson.get("Platform")
        ticket   = rjson.get("Ticket")
        nonce    = rjson.get("Nonce")

        if app_id != settings.TitleId:
            return _photon_error(2, "Invalid AppId", 403)
        if platform != "Quest":
            return _photon_error(3, "Platform must be Quest", 403)
        if not ticket or not nonce:
            return _photon_error(3, "Missing Ticket or Nonce", 400)

        # 1. Authenticate the PlayFab session ticket.
        user_id = authenticate_ticket(ticket)
        if not user_id:
            _post_discord_embed(settings.photon_webhook_url, {
                "title": "❌ Photon Auth Failed", "color": 0xE74C3C,
                "fields": [{"name": "Reason", "value": "Invalid/expired SessionTicket", "inline": False},
                           {"name": "IP", "value": client_ip, "inline": True}],
            })
            return _photon_error(2, "Invalid SessionTicket", 403)

        # 2. Recover the linked Oculus identity.
        try:
            acct = requests.post(
                f"https://{settings.TitleId}.playfabapi.com/Server/GetUserAccountInfo",
                json={"PlayFabId": user_id},
                headers=settings.get_auth_headers(),
                timeout=10,
            )
        except requests.exceptions.RequestException as e:
            logger.error(f"[Photon] GetUserAccountInfo request failed: {e}")
            return _photon_error(3, "Account lookup unavailable", 503)

        if acct.status_code != 200:
            return _photon_error(3, "Failed to retrieve account info", 403)

        user_info        = (acct.json().get("data") or {}).get("UserInfo") or {}
        server_custom_id = (user_info.get("ServerCustomIdInfo") or {}).get("CustomId") or ""
        nickname         = (user_info.get("TitleInfo") or {}).get("DisplayName")

        if "OCULUS" not in server_custom_id:
            return _photon_error(3, "Account not linked to Oculus", 403)

        # The real OculusId was stored server-side during /api/PlayFabAuthentication.
        oculus_id = get_oculus_id_for_playfab(user_id)
        if not oculus_id:
            return _photon_error(3, "No OculusId on file, re-authenticate first", 403)

        # 3. Validate the nonce against Oculus.
        if not get_is_nonce_valid(nonce, oculus_id):
            should_ban, failure_count = check_and_record_nonce_failure(user_id)
            if should_ban:
                ban_user(user_id, name=nickname, reason=f"invalid credentials. if you think this is false, report this to the discord with this token: {request.remote_addr}.")
            temp_ban_ip(client_ip)
            _post_discord_embed(settings.photon_webhook_url, {
                "title": "❌ Photon Auth Failed", "color": 0xE74C3C,
                "fields": [
                    {"name": "Reason",   "value": "Nonce validation failed", "inline": False},
                    {"name": "UserId",   "value": user_id, "inline": True},
                    {"name": "OculusId", "value": str(oculus_id), "inline": True},
                    {"name": "Failures", "value": str(failure_count), "inline": True},
                    {"name": "Banned",   "value": str(should_ban), "inline": True},
                    {"name": "IP",       "value": client_ip, "inline": True},
                ],
            })
            return _photon_error(3, "Failed Nonce Verification", 403)

        with nonce_failures_lock:
            nonce_failures.pop(user_id, None)

        _post_discord_embed(settings.photon_webhook_url, {
            "title": "✅ Photon Auth", "color": 0x2ECC71,
            "fields": [
                {"name": "UserId",   "value": user_id, "inline": True},
                {"name": "OculusId", "value": str(oculus_id), "inline": True},
                {"name": "Nickname", "value": nickname or "None", "inline": True},
                {"name": "IP",       "value": client_ip, "inline": True},
            ],
        })

        return jsonify({
            "resultCode": 1,
            "message":    f"Authenticated user {user_id.lower()} title {settings.TitleId.lower()}",
            "userId":     user_id.upper(),
            "nickname":   nickname,
            "ResultCode": 1,
            "UserId":     user_id,
        }), 200

    except Exception:
        logger.error("[Photon] unhandled exception:\n" + traceback.format_exc())
        return _photon_error(0, "Internal auth error", 500)

@app.route("/PathCreate", methods=["POST"])
def path_create():
    rjson = request.get_json(silent=True) or {}

    user_id = rjson.get("UserId")
    room_id = (
        rjson.get("GameId")
        or rjson.get("RoomId")
        or rjson.get("RoomCode")
        or rjson.get("roomId")
    )

    zone = rjson.get("Zone") or rjson.get("zone")
    region = rjson.get("Region") or rjson.get("region")

    if user_id and room_id:
        set_player_room(user_id, room_id, zone, region)

    return execute_cloud_script(user_id, "RoomCreated", rjson)

@app.route("/PathJoin", methods=["POST"])
def path_join():
    rjson = request.get_json(silent=True) or {}

    user_id = rjson.get("UserId")
    room_id = (
        rjson.get("GameId")
        or rjson.get("RoomId")
        or rjson.get("RoomCode")
        or rjson.get("roomId")
    )

    zone = rjson.get("Zone") or rjson.get("zone")
    region = rjson.get("Region") or rjson.get("region")

    if user_id and room_id:
        set_player_room(user_id, room_id, zone, region)

    return execute_cloud_script(user_id, "RoomJoined", rjson)

@app.route("/PathLeave", methods=["POST"])
def path_leave():
    rjson = request.get_json(silent=True) or {}

    user_id = rjson.get("UserId")

    if user_id:
        remove_player_room(user_id)

    rjson["Type"] = "ClientDisconnect"

    return execute_cloud_script(user_id, "RoomLeft", rjson)

@app.route("/PathClose", methods=["POST"])
def path_close():
    rjson = request.get_json(silent=True) or {}

    user_id = rjson.get("UserId")

    if user_id:
        remove_player_room(user_id)

    rjson["Type"] = "Close"

    return execute_cloud_script(user_id, "RoomClosed", rjson)

@app.route("/PathRaiseEvent",    methods=["POST"])
def path_raise_event():
    rjson = request.get_json()
    return execute_cloud_script(rjson.get("UserId"), "RoomEventRaised", rjson)

@app.route("/PathSetProperties", methods=["POST"])
def path_set_properties():
    rjson = request.get_json()
    return execute_cloud_script(rjson.get("UserId"), "RoomPropertyUpdated", rjson)

@app.route("/v2/player/client/auth/begin/QUEST", methods=["POST"])
def auth_begin():
    data    = request.get_json(silent=True) or {}
    user_id = data.get("UserId")
    if not user_id:
        return jsonify({"error": "no UserId"}), 400
    nonce = base64.urlsafe_b64encode(secrets.token_bytes(64)).decode().rstrip("=")
    pending_nonces[user_id] = nonce
    logger.info(f"[Mothership] /auth/begin user_id={user_id}")
    return jsonify({"AttestationNonce": nonce}), 201

DISCORD_FIELD_VALUE_LIMIT = 1024


def _discord_safe_field(value: str, reserved_wrapper_chars: int = 0, max_len: int = 500) -> str:
    """Truncate `value` so it (plus any wrapper text the caller adds, e.g.
    triple-backtick code fences) stays comfortably under Discord's 1024
    character field-value limit.

    `max_len` defaults to 500, which is intentionally well below the 1024
    hard cap — attestation tokens and raw JSON bodies are the biggest
    offenders, and giving them a smaller budget leaves headroom for the
    other fields in the same embed so the *whole* embed also stays under
    Discord's 6000-char total-size limit.
    """
    if value is None:
        return "none"
    value = str(value)
    budget = max(0, DISCORD_FIELD_VALUE_LIMIT - reserved_wrapper_chars - len("\n... (truncated)"))
    budget = min(budget, max_len)
    if len(value) > budget:
        return value[:budget] + "\n... (truncated)"
    return value


def _log_attestation_request(user_id, attestation_token, meta_nonce, client_ip, rjson):
    """Post a plain debug embed for every /auth/complete call, showing the
    request fields as received (attestation token / nonce are truncated, and
    the raw body has sensitive keys redacted).
    """
    try:
        raw_body = json.dumps(rjson, indent=2)
    except Exception:
        raw_body = str(rjson)

    raw_body_safe = _discord_safe_field(raw_body, reserved_wrapper_chars=len("```json\n\n```"))
    token_safe    = _discord_safe_field(attestation_token or "none", reserved_wrapper_chars=len("```\n```"))
    meta_nonce_safe = _discord_safe_field(meta_nonce or "none", max_len=256)

    embed = {
        "title": "attestation request",
        "color": 0x2b2d31,
        "fields": [
            {"name": "user id",    "value": str(user_id or "none"),   "inline": True},
            {"name": "ip",         "value": str(client_ip or "none"), "inline": True},
            {"name": "meta nonce", "value": meta_nonce_safe, "inline": False},
            {"name": "attestation token", "value": f"```{token_safe}```", "inline": False},
            {"name": "raw body",   "value": f"```json\n{raw_body_safe}\n```", "inline": False},
        ],
    }
    _post_discord_embed(ATTESTATION_LOG_WEBHOOK_URL, embed)


@app.route("/v2/player/client/auth/complete/QUEST", methods=["POST"])
def auth_complete():
    rjson             = request.get_json(silent=True) or {}
    client_ip         = get_client_ip()
    user_id           = rjson.get("UserId")
    attestation_token = rjson.get("AttestationToken")
    meta_nonce        = rjson.get("MetaNonce")

    _log_attestation_request(user_id, attestation_token, meta_nonce, client_ip, rjson)

    def _invalid(reason: str, status: int = 401):
        """Single exit point for every failure path below. Any failure here
        means the attestation token didn't check out, so per spec we lock
        the caller's IP out of /api/PlayFabAuthentication for
        TEMP_IP_BAN_DURATION_SECONDS with reason TEMP_IP_BAN_REASON."""
        temp_ban_ip(client_ip)
        logger.warning(f"[Mothership] /auth/complete rejected ({reason}) "
                       f"ip={client_ip} user_id={user_id}")
        send_mothership_webhook("Attestation Check Failed", {}, user_id or "unknown",
                                error=reason, color=15105570)
        return jsonify({"error": TEMP_IP_BAN_REASON, "detail": reason}), status

    if not user_id:
        return _invalid("missing UserId")
    if attestation_token is None:
        return _invalid("missing AttestationToken")

    try:
        expected_nonce  = pending_nonces.pop(user_id, None)
        used_begin_flow = expected_nonce is not None

        if expected_nonce is None:
            if not meta_nonce:
                return _invalid("no nonce available (no /auth/begin call and no MetaNonce provided)")
            if _is_meta_nonce_used(meta_nonce):
                return _invalid("MetaNonce already used (replay)")
            expected_nonce = meta_nonce

        verify_url = (f"https://graph.oculus.com/platform_integrity/verify"
                      f"?token={attestation_token}&access_token={META_ACCESS_TOKEN}")
        r = requests.get(verify_url, timeout=5)
        if r.status_code != 200:
            return _invalid(f"oculus verification failed (status {r.status_code})")

        result = r.json()
        if "data" not in result or not result["data"]:
            return _invalid("invalid oculus response")

        claims_b64 = result["data"][0].get("claims")
        if not claims_b64:
            return _invalid("missing claims in oculus response")

        claims = json.loads(base64.urlsafe_b64decode(
            claims_b64 + "=" * (-len(claims_b64) % 4)))

        # The certificate digest is part of the decoded Oculus attestation claims,
        # not the /api/PlayFabAuthentication request body. Log it here.
        app_state = claims.get("app_state", {}) or {}
        if "package_cert_sha256_digest" in app_state:
            digest = app_state.get("package_cert_sha256_digest")
            valid_digest = (
                isinstance(digest, list)
                and digest == [EXPECTED_PACKAGE_CERT_SHA256]
            )
            send_package_cert_webhook(
                client_ip, user_id, claims, digest, valid_digest,
                banned=not valid_digest,
            )
            if not valid_digest:
                temp_ban_cert_user(user_id)
                return _invalid(
                    "invalid package certificate SHA-256 digest; "
                    "user placed on a 10-minute certificate ban"
                )

        if claims.get("request_details", {}).get("nonce") != expected_nonce:
            return _invalid("nonce mismatch")

        app_state    = claims.get("app_state", {})
        device_state = claims.get("device_state", {})

        if app_state.get("app_integrity_state") != "StoreRecognized":
            return _invalid("app integrity check failed")
        if device_state.get("device_integrity_state") != "Advanced":
            return _invalid("device integrity check failed")
        if app_state.get("package_id") not in ALLOWED_PACKAGE_IDS:
            return _invalid(f"package id not allowed: {app_state.get('package_id')!r}")

        if not used_begin_flow:
            _mark_meta_nonce_used(meta_nonce)

        return issue_mothership_token(user_id, claims)

    except Exception as e:
        logger.error("[Mothership] /auth/complete exception:\n" + traceback.format_exc())
        return _invalid(f"internal exception: {e}", status=500)

@app.route("/v1/client/player/auth/RIFT", methods=["POST"])
def auth_rift():
    """Single-step RIFT auth — always logs into the hardcoded Rift account.

    NOTE: this bypasses all device/app attestation. If this route shouldn't
    be publicly reachable, gate it behind your own network/allowlist rules.
    """
    data = request.get_json(silent=True) or {}
    logger.info(f"[Mothership] /auth/RIFT incoming_user={data.get('UserId','?')}")
    fake_claims = {
        "request_details": {"nonce": "rift-bypass"},
        "app_state":       {"app_integrity_state": "StoreRecognized",
                            "package_id": "com.rift.gorillatag"},
        "device_state":    {"device_integrity_state": "Advanced"},
    }
    return issue_mothership_token(RIFT_ACCOUNT_USER_ID, fake_claims)

@app.route("/v1/client/analytics/event/batch", methods=["POST"])
@app.route("/v1/client/analytics/event",       methods=["POST"])
def analytics_event():
    logger.info("[Mothership] Analytics event received")
    return jsonify({"success": True}), 200

@app.route("/v1/inventory/client", methods=["GET"])
def get_inventory_client():
    token = (request.headers.get("X-Mothership-Token") or
             request.headers.get("x-mothership-token"))
    if not token:
        return jsonify({"statusCode": 401, "message": "missing x-mothership-token", "data": None}), 401

    user_id = _decode_mothership_token(token)
    if not user_id:
        return jsonify({"statusCode": 401, "message": "invalid token", "data": None}), 401

    entitlements = []
    if users_collection is not None:
        user = users_collection.find_one({"mothership_id": user_id})
        if user:
            entitlements = user.get("entitlements", [])

    return jsonify({"statusCode": 200, "message": "Success",
                    "data": {"items": entitlements}}), 200

@app.route("/v1/title-data/client", methods=["GET"])
def get_title_data_client():
    return jsonify({"Results": [{"key": "MOTD", "data": MOTD_TEXT}]}), 200

@app.route("/v1/userdata/client", methods=["GET", "POST"])
def userdata_client():
    token = (request.headers.get("X-Mothership-Token") or
             request.headers.get("x-mothership-token"))
    if not token:
        return jsonify({"error": "missing x-mothership-token header"}), 401

    token_user_id = _decode_mothership_token(token)
    if not token_user_id:
        return jsonify({"error": "invalid token"}), 401

    if request.method == "GET":
        key_name = request.args.get("key_name")
        if not key_name:
            return jsonify({"error": "missing key_name parameter"}), 400

        user_data = get_user_data_from_mongo(token_user_id, key_name)
        if user_data:
            return jsonify({
                "id":             user_data.get("id", ""),
                "metadata_id":    user_data.get("metadata_id", ""),
                "key_name":       user_data.get("key_name", ""),
                "user_id":        user_data.get("user_id", ""),
                "value":          user_data.get("value", ""),
                "generation":     user_data.get("generation", 0),
                "created_by":     user_data.get("created_by", ""),
                "last_written_by": user_data.get("last_written_by", ""),
            }), 200
        return jsonify({
            "id": "", "metadata_id": str(uuid.uuid4()),
            "key_name": key_name, "user_id": token_user_id,
            "value": "", "generation": 0,
            "created_by": "", "last_written_by": "",
        }), 200

    data     = request.get_json(silent=True) or {}
    key_name = data.get("key_name")
    value    = data.get("value", "")
    user_id  = data.get("user_id") or token_user_id

    if not key_name:
        return jsonify({"error": "missing key_name in request body"}), 400

    success = save_user_data_to_mongo(user_id, key_name, value)
    if success:
        saved = get_user_data_from_mongo(user_id, key_name)
        if saved:
            return jsonify({
                "id":             saved.get("id", ""),
                "metadata_id":    saved.get("metadata_id", ""),
                "key_name":       saved.get("key_name", ""),
                "user_id":        saved.get("user_id", ""),
                "value":          saved.get("value", ""),
                "generation":     saved.get("generation", 0),
                "created_by":     saved.get("created_by", ""),
                "last_written_by": saved.get("last_written_by", ""),
            }), 200
    return jsonify({"error": "failed to save user data"}), 500

@app.route("/v1/progression-tree/client", methods=["GET"])
def get_progression_tree_client():
    token = (request.headers.get("X-Mothership-Token") or
             request.headers.get("x-mothership-token"))
    if not token:
        return jsonify({"error": "missing x-mothership-token header"}), 401

    user_id = _decode_mothership_token(token)
    if not user_id:
        return jsonify({"error": "invalid token"}), 401

    title_id = request.headers.get("x-mothership-title-id", "f3e9fb19")
    env_id   = request.headers.get("x-mothership-env-id",   "7f3a99dd-5598-4725-98cf-6538d28feb9f")

    user_trees = {}
    if users_collection is not None:
        user = users_collection.find_one({"mothership_id": user_id})
        if user:
            user_trees = user.get("progression", {}).get("trees", {})

    tree_data     = get_progression_tree_data()
    response_data = copy.deepcopy(tree_data)
    results       = []

    for tree in response_data.get("data", {}).get("trees", []):
        tree_id        = tree["id"]
        unlocked_nodes = user_trees.get(tree_id, {}).get("unlocked_nodes", [])

        for node in tree.get("NodeDefinitions", []):
            is_free       = node.get("cost") is None
            node["unlocked"] = node["id"] in unlocked_nodes or is_free
            if node.get("cost"):
                node["cost"] = transform_cost_format(node["cost"])
            if node.get("transaction"):
                node["transaction"] = transform_transaction_format(
                    node["transaction"], title_id, env_id)

        results.append({
            "Tree": {
                "id":         tree["id"],
                "title_id":   title_id,
                "env_id":     env_id,
                "name":       tree.get("name", ""),
                "track_id":   tree.get("track_id"),
                "created_at": tree.get("created_at",
                                       datetime.now(timezone.utc).isoformat() + "Z"),
            },
            "NodeDefinitions":         tree.get("NodeDefinitions", []),
            "PlayerId":                user_id,
            "InventoryRefreshRequired": False,
            "Track":                   None,
        })

    return jsonify({"Results": results}), 200

@app.route('/api/GetMySubscriptionsAndTheirBenefits', methods=['POST'])
def get_my_subscriptions_and_their_benefits():
    """
    Grants and caches user subscription plans.
    """
    try:
        body = request.get_json(silent=True) or {}
        mothership_id = sanitize_str(body.get("MothershipId"), 256)

        now_utc = datetime.now(timezone.utc)
        now_str = now_utc.isoformat().replace("+00:00", "Z")
        month_later_str = (now_utc + timedelta(days=30)).isoformat().replace("+00:00", "Z")

        shared_group_ok = False
        playfab_id = get_play_fab_id(mothership_id)

        random_sub_id = f"sub_{secrets.token_hex(4)}"

        if playfab_id:
            try:
                shared_group_id = f"{playfab_id}Inventory"
                sub_data = json.dumps({
                    "Sku": "fan_club",
                    "ExpirationTime": month_later_str,
                    "TotalLifetimeSeconds": 0
                })

                create_url = f"https://{settings.TitleId}.playfabapi.com/Server/CreateSharedGroup"
                requests.post(create_url, json={"SharedGroupId": shared_group_id}, headers=get_pf_headers(), timeout=5)

                update_url = f"https://{settings.TitleId}.playfabapi.com/Server/UpdateSharedGroupData"
                update_payload = {
                    "SharedGroupId": shared_group_id,
                    "Data": {
                        "subscriptions.fan_club": sub_data
                    },
                    "Permission": "Public"
                }
                resp = requests.post(update_url, json=update_payload, headers=get_pf_headers(), timeout=5)
                shared_group_ok = (resp.status_code == 200)
            except Exception as e:
                logger.error(f"[iap/subs] Error caching shared group parameters: {e}")

        mock_benefits = {
            "fan_club": [
                {
                    "BenefitId": "golden_name_benefit",
                    "SubscriptionId": random_sub_id,
                    "Active": True,
                    "ExpirationTime": month_later_str
                },
                {
                    "BenefitId": "hand_tracking_benefit",
                    "SubscriptionId": random_sub_id,
                    "Active": True,
                    "ExpirationTime": month_later_str
                },
                {
                    "BenefitId": "iobt_benefit",
                    "SubscriptionId": random_sub_id,
                    "Active": True,
                    "ExpirationTime": month_later_str
                },
                {
                    "BenefitId": "vim_benefit",
                    "SubscriptionId": random_sub_id,
                    "Active": True,
                    "ExpirationTime": month_later_str
                }
            ]
        }

        return jsonify({
            "Subscriptions": [{
                "SubscriptionId": random_sub_id,
                "EarliestStartDate": now_str,
                "CurrentStartDate": now_str,
                "MostRecentBillingCycleStartDate": now_str,
                "MostRecentBillingCycleEndDate": month_later_str,
                "TotalLifetimeSeconds": 0,
                "IsActive": True,
                "IsCancelling": False,
                "Sku": "fan_club",
                "PlayerId": mothership_id or "unknown",
                "TrialType": "none",
                "ExternalServiceName": "oculus",
                "ExternalSubscriptionId": "",
                "SubscriptionCatalogItemId": ""
            }],
            "PreviouslyGrantedBenefitsBySubscriptionSku": mock_benefits,
            "NewlyGrantedBenefitsBySubscriptionSku": {},
            "SharedGroupDataUpdateSucceeded": shared_group_ok,
            "CacheForOtherFunctionsSucceeded": True
        }), 200
    except Exception as err:
        logger.error(f"[iap/subs] Get Subscription layout error: {err}")
        return jsonify({"Subscriptions": []}), 500

@app.route('/api/TD', methods=['POST'])
def titled_data():
    return jsonify({"MOTD":"<color=red>WELCOME TO FAST TAGGERS!</color>"})

@app.route("/api/GetRoomPlayers", methods=["POST"])
def get_room_players():
    try:
        data = request.get_json(silent=True) or {}

        room_name = str(
            data.get("roomName", "")
        ).strip()

        if not room_name:
            return jsonify({
                "error": "roomName is required",
                "players": []
            }), 400

        room_data = load_room_data()

        if not isinstance(room_data, dict):
            return jsonify({
                "error": "Room data is invalid",
                "players": []
            }), 500

        # Try several common room-data layouts.
        room = (
            room_data.get(room_name)
            or room_data.get("rooms", {}).get(room_name)
        )

        if not room:
            return jsonify({
                "roomName": room_name,
                "players": []
            }), 200

        # Allow either:
        # {"players": [...]}
        # or directly a player list.
        if isinstance(room, dict):
            players = (
                room.get("players")
                or room.get("Players")
                or room.get("members")
                or room.get("Members")
                or []
            )
        elif isinstance(room, list):
            players = room
        else:
            players = []

        output = []

        for player in players:
            if isinstance(player, str):
                output.append({
                    "username": player,
                    "playfabId": "",
                    "region": "",
                    "zone": "",
                    "room": room_name
                })
                continue

            if not isinstance(player, dict):
                continue

            output.append({
                "username": (
                    player.get("username")
                    or player.get("userName")
                    or player.get("Username")
                    or player.get("Nickname")
                    or ""
                ),

                "playfabId": (
                    player.get("playfabId")
                    or player.get("PlayFabId")
                    or player.get("PlayFabID")
                    or player.get("playerId")
                    or ""
                ),

                "region": (
                    player.get("region")
                    or player.get("Region")
                    or ""
                ),

                "zone": (
                    player.get("zone")
                    or player.get("Zone")
                    or ""
                ),

                "room": room_name
            })

        return jsonify({
            "roomName": room_name,
            "players": output,
            "count": len(output)
        }), 200

    except Exception as e:
        return jsonify({
            "error": str(e),
            "players": []
        }), 500


# Catch-all 404. Kept LAST; Flask always prefers more specific routes over
# the <path:> converter, but keeping it at the end avoids any confusion.
@app.route("/<path:endpoint>", methods=["GET", "POST", "PUT", "DELETE", "PATCH", "HEAD", "OPTIONS"])
def catch_all_logger(endpoint):
    logger.info(f"[CatchAll] No route matched: /{endpoint} method={request.method}")
    return jsonify({"error": "Not Found"}), 404


if __name__ == "__main__":
    app.start_time = time.time()
    logger.info("🦍 Ultimate Backend starting on port 8080")
    app.run(host="0.0.0.0", port=8080, debug=False)
