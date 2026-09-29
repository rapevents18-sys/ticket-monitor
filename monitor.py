"""
Ticket monitor (cloud version, runs on GitHub Actions every ~15 minutes)
-----------------------------------------------------------------------
Each run:
  1. Reads NEW emails since the last run (Gmail API, read-only permission).
  2. Has Claude pick out NEW announcements (new tours, extra dates, presales/on-sales).
  3. Big names (rating >= ALERT_SCALE, or on your watchlist) -> instant Telegram alert.
  4. Every presale/on-sale time found is remembered -> a heads-up ping shortly before it opens.
  5. Everything else waits for the daily digest (DIGEST_HOUR, your timezone) or for you typing
     "go now digest" in Telegram.

Google logs a "testing" app out every 7 days, so the bot warns you a day before and you renew
the login with one command (see RELOGIN_STEPS).

State (what was already seen/sent) is stored encrypted in state.enc, so nothing personal is
readable in the repository. Logs only contain counts, never email content.
"""

import base64
import hashlib
import html
import json
import os
import re
import sys
import time
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

import requests
from cryptography.fernet import Fernet, InvalidToken


def env(name, default=""):
    return (os.getenv(name) or default).strip()


MODEL = env("CLAUDE_MODEL", "claude-haiku-4-5-20251001")
TZ = ZoneInfo(env("TIMEZONE", "Asia/Jerusalem"))
DIGEST_HOUR = int(env("DIGEST_HOUR", "10"))
WATCHLIST_RAW = env("WATCHLIST")
WATCHLIST = [w.strip().lower() for w in WATCHLIST_RAW.split(",") if w.strip()]
MY_CITIES = env("MY_CITIES", "London,Amsterdam")
ALERT_SCALE = int(env("ALERT_SCALE", "4"))            # 4-5 = "big name"
HEADSUP_MAX_MIN = int(env("HEADSUP_MAX_MIN", "45"))   # heads-up when a sale opens within this many minutes
MAX_EMAILS = int(env("MAX_EMAILS", "150"))
TOKEN_WARN_DAYS = 6                                    # Google logins last 7 days
MAX_GAP_DAYS = 5                                       # after an outage, look back at most this far
CHUNK_SIZE = 20
BODY_CHARS = 1500
STATE_FILE = Path(__file__).parent / "state.enc"
SCOPES = ["https://www.googleapis.com/auth/gmail.readonly"]
MAIL_FILTER = "-in:sent -in:spam -in:trash"

CATEGORY_LABELS = {
    "presale": "🔑 Presale",
    "registration": "📝 Registration",
    "on_sale": "🎟️ On-sale",
    "tour": "📣 New tour",
    "extra_dates": "➕ Extra dates",
}
TRIGGER_WORDS = {"digest", "digust", "go", "now", "run", "scan", "new", "news", "list"}
WINDOW_WORDS = {"24h": 1, "3d": 3, "7d": 7}
HELP_TEXT = (
    "🎫 Ticket monitor\n\n"
    "Type  go now digest  (or: digest / go / now) – everything new since the last digest\n"
    "24h / 3d / 7d – rescan the last 24 hours / 3 days / 7 days\n\n"
    "Big names are sent instantly, and you get a heads-up shortly before presales/on-sales open.\n"
    "Replies to your messages can take up to ~15 minutes."
)
RELOGIN_STEPS = (
    "1) On your Mac open Terminal and run:\n"
    "cd ~/ticket-digest && source venv/bin/activate && python digest.py relogin\n"
    "2) Sign in to Google when the browser opens (your new login is copied automatically).\n"
    "3) On GitHub: your repository > Settings > Secrets and variables > Actions > "
    "GMAIL_TOKEN_JSON > Update > paste (Cmd+V) > Update secret."
)


def norm(s):
    return re.sub(r"\W+", " ", (s or "").lower()).strip()


def scrub(text):
    """Never let a secret end up in a log or message."""
    for name in ("TELEGRAM_BOT_TOKEN", "ANTHROPIC_API_KEY", "GMAIL_TOKEN_JSON", "STATE_PASSPHRASE"):
        val = env(name)
        if val:
            text = text.replace(val, "***")
    return text


# ---------------------------------------------------------------- State ----
def _fernet():
    passphrase = env("STATE_PASSPHRASE")
    if not passphrase:
        raise RuntimeError("The STATE_PASSPHRASE secret is missing")
    key = base64.urlsafe_b64encode(hashlib.sha256(passphrase.encode()).digest())
    return Fernet(key)


def fresh_state():
    return {
        "last_check": 0,
        "seen_ids": [],
        "tg_offset": None,
        "pending": [],
        "alerted": [],
        "countdowns": [],
        "last_digest_date": "",
        "last_error_ts": 0,
        "token_id": "",
        "token_since": 0,
        "last_warn_ts": 0,
    }


def load_state():
    if not STATE_FILE.exists():
        return fresh_state()
    try:
        state = json.loads(_fernet().decrypt(STATE_FILE.read_bytes()))
    except InvalidToken:
        raise RuntimeError("state.enc can't be decrypted - did the STATE_PASSPHRASE secret change?")
    base = fresh_state()
    base.update(state)
    return base


def save_state(state):
    STATE_FILE.write_bytes(_fernet().encrypt(json.dumps(state).encode()))


# ---------------------------------------------------------------- Gmail ----
def gmail_service():
    """Returns (service, refresh_token). Raises if the weekly Google login has expired."""
    from google.auth.transport.requests import Request
    from google.oauth2.credentials import Credentials
    from googleapiclient.discovery import build

    raw = env("GMAIL_TOKEN_JSON")
    if not raw:
        raise RuntimeError("The GMAIL_TOKEN_JSON secret is missing")
    info = json.loads(raw)
    creds = Credentials.from_authorized_user_info(info, SCOPES)
    creds.refresh(Request())  # fails with invalid_grant once the 7-day login has expired
    return build("gmail", "v1", credentials=creds, cache_discovery=False), info.get("refresh_token", "")


def _decode(data):
    return base64.urlsafe_b64decode(data + "=" * (-len(data) % 4)).decode("utf-8", errors="replace")


def _collect_parts(part, plain, htmls):
    mime = part.get("mimeType", "")
    data = part.get("body", {}).get("data")
    if data and mime == "text/plain":
        plain.append(_decode(data))
    elif data and mime == "text/html":
        htmls.append(_decode(data))
    for sub in part.get("parts", []) or []:
        _collect_parts(sub, plain, htmls)


def _clean(text):
    text = re.sub(r"(?is)<(script|style).*?>.*?</\1>", " ", text)
    text = re.sub(r"(?s)<[^>]+>", " ", text)
    return re.sub(r"\s+", " ", html.unescape(text)).strip()


def to_email(msg):
    headers = {h["name"].lower(): h["value"] for h in msg["payload"].get("headers", [])}
    plain, htmls = [], []
    _collect_parts(msg["payload"], plain, htmls)
    body = _clean(" ".join(plain)) if plain else _clean(" ".join(htmls))
    return {
        "id": msg["id"],
        "tid": msg["threadId"],  # Gmail thread ids double as link ids
        "from": headers.get("from", ""),
        "subject": headers.get("subject", ""),
        "date": headers.get("date", ""),
        "body": body[:BODY_CHARS],
    }


def _get_message(service, msg_id):
    """Fetch one email; if Gmail says 'too fast', wait and try again."""
    for attempt in range(7):
        try:
            return service.users().messages().get(userId="me", id=msg_id, format="full").execute()
        except Exception as e:
            status = getattr(getattr(e, "resp", None), "status", None)
            if status in (403, 429, 500, 503) and attempt < 6:
                time.sleep(min(2 ** attempt, 30))
                continue
            raise


def list_ids(service, query, limit):
    ids, token = [], None
    while len(ids) < limit:
        kwargs = {"userId": "me", "q": query, "maxResults": min(100, limit - len(ids))}
        if token:
            kwargs["pageToken"] = token
        resp = service.users().messages().list(**kwargs).execute()
        ids += [m["id"] for m in resp.get("messages", [])]
        token = resp.get("nextPageToken")
        if not token:
            break
    return ids


def fetch_many(service, ids):
    out = []
    for mid in ids:
        try:
            out.append(to_email(_get_message(service, mid)))
        except Exception:
            continue
        time.sleep(0.1)  # gentle pacing so Gmail's per-minute limit isn't hit
    return out


# --------------------------------------------------------------- Claude ----
def system_prompt():
    now = datetime.now(TZ)
    return f"""You help a ticket reseller in Europe triage their inbox. Their main markets: {MY_CITIES}.
Now it is {now.strftime("%A %d %B %Y, %H:%M")} ({TZ.key}). When an email says things like "tomorrow" or "this Friday",
work out the real calendar date from the email's own date header and write key_time as an absolute date and time.
Artists they especially care about: {WATCHLIST_RAW or "(none listed)"}.

You receive a JSON list of emails. Pick out ONLY emails about live-event ticketing news:
presales, presale registrations/sign-ups, general on-sales, new tour or show announcements,
added dates. Ignore everything else (receipts, unrelated newsletters, ads, account notices).

Return ONLY a JSON array (no other text, no markdown fences). One object per relevant email:
{{
  "id": "<the email id exactly as given>",
  "category": "presale" | "registration" | "on_sale" | "tour" | "extra_dates",
  "is_new": <true if this email announces a NEW tour or show, ADDED/extra dates on an existing tour, or opens a presale/registration/on-sale for a newly announced or newly added show; false for reminders, "still available", "last chance", price drops, generic venue listings or newsletters about shows announced long ago>,
  "artist": "<artist or festival name; never null>",
  "shows": [{{"city": "<city>", "venue": "<venue or null>", "date": "<date, e.g. 12 Oct 2026>"}}, ...],
  "scale": <integer 1-5: how big the act/event is. 5 = global superstar or stadium tour, 4 = arena-level headliner or major festival, 3 = mid-size touring act, 2 = small venue, 1 = niche or local>,
  "key_time": "<the most important upcoming deadline or sale opening, with date, time and timezone, or null>",
  "key_time_iso": "<the SAME moment as key_time in ISO 8601 with UTC offset, e.g. 2026-10-01T10:00:00+01:00, or null if not exactly known. If the email gives no timezone, use the local timezone of the show's country>",
  "code": "<presale code if the email gives one, else null>",
  "summary": "<one short sentence>",
  "priority": "high" | "normal"
}}
Use "high" for major artists, big venues/stadiums, anything in the reseller's main markets,
or anything matching their watchlist. Use ONLY facts stated in the email. Use null when
something is not stated. Never invent dates, times or codes. If nothing is relevant, return [].
Ignore reminders or confirmations for shows happening today or in the next 2 days, and any order or
ticket-delivery emails, unless the email itself announces a presale or on-sale.
Focus on NEW announcements: new tours, brand-new shows, and extra/added dates for tours that are
already running (use category "extra_dates" for added dates). Presale, registration and on-sale
details count only when they belong to a newly announced tour or newly added date. Mark
everything else (reminders, "still available", "last chance", generic listings) with is_new false.
Include EVERY show/city/venue mentioned in the email under "shows". For a festival or multi-artist
event with no single headliner, put the event name in "artist"."""


def classify(emails):
    import anthropic  # imported here so the rest of the file can be tested without it

    client = anthropic.Anthropic()
    prompt = system_prompt()
    results = []
    for i in range(0, len(emails), CHUNK_SIZE):
        chunk = emails[i : i + CHUNK_SIZE]
        payload = [{k: e[k] for k in ("id", "from", "subject", "date", "body")} for e in chunk]
        resp = client.messages.create(
            model=MODEL,
            max_tokens=4000,
            system=prompt,
            messages=[{"role": "user", "content": json.dumps(payload, ensure_ascii=False)}],
        )
        text = "".join(b.text for b in resp.content if b.type == "text").strip()
        text = re.sub(r"^```(?:json)?|```$", "", text, flags=re.MULTILINE).strip()
        try:
            results.extend(json.loads(text))
        except json.JSONDecodeError:
            print(f"Warning: could not read Claude's answer for batch {i // CHUNK_SIZE + 1}")
    return results


def analyse(emails):
    """Classify emails and return slim, storable items for NEW announcements."""
    by_id = {e["id"]: e for e in emails}
    items = []
    for it in classify(emails) if emails else []:
        if it.get("is_new") is False:
            continue
        src = by_id.get(str(it.get("id")), {})
        items.append(
            {
                "artist": it.get("artist"),
                "category": it.get("category"),
                "shows": [s for s in (it.get("shows") or []) if isinstance(s, dict)],
                "scale": it.get("scale"),
                "key_time": it.get("key_time"),
                "key_time_iso": it.get("key_time_iso"),
                "code": it.get("code"),
                "summary": it.get("summary"),
                "priority": it.get("priority"),
                "tid": src.get("tid"),
                "subject": (src.get("subject") or "")[:80],
                "alerted": False,
            }
        )
    return items


# ---------------------------------------------------------- Formatting ----
def is_big(it):
    name = (it.get("artist") or "").lower()
    if any(w in name for w in WATCHLIST):
        return True
    try:
        return int(it.get("scale") or 0) >= ALERT_SCALE
    except (TypeError, ValueError):
        return False


def event_key(it):
    shows = sorted(
        f"{s.get('city')}|{s.get('venue')}|{s.get('date')}".lower()
        for s in (it.get("shows") or [])
        if isinstance(s, dict)
    )
    raw = "|".join([norm(it.get("artist")), str(it.get("category")), str(it.get("key_time_iso") or it.get("key_time")), *shows])
    return hashlib.md5(raw.encode()).hexdigest()[:12]


def merge_items(items):
    """One entry per artist, biggest first."""
    artists = {}
    for it in items:
        name = (it.get("artist") or "").strip() or (it.get("subject") or "Unknown")[:60]
        a = artists.setdefault(
            norm(name),
            {"name": name, "scale": 0, "high": False, "shows": {}, "notes": {}, "summary": "", "links": []},
        )
        try:
            a["scale"] = max(a["scale"], int(it.get("scale") or 0))
        except (TypeError, ValueError):
            pass
        a["high"] = a["high"] or it.get("priority") == "high"
        for s in it.get("shows") or []:
            if any(s.values()):
                k = tuple(str(s.get(f) or "").lower() for f in ("city", "venue", "date"))
                a["shows"].setdefault(k, s)
        label = CATEGORY_LABELS.get(it.get("category"), "ℹ️ Info")
        a["notes"].setdefault((it.get("category"), it.get("key_time")), (label, it.get("key_time"), it.get("code")))
        if not a["summary"] and it.get("summary"):
            a["summary"] = it["summary"]
        if it.get("tid") and it["tid"] not in a["links"]:
            a["links"].append(it["tid"])
    return sorted(artists.values(), key=lambda a: (-a["scale"], not a["high"], a["name"].lower()))


def render(a):
    out = [("⭐ " if a["high"] else "") + a["name"]]
    for label, key_time, code in a["notes"].values():
        line = f"  {label}" + (f": {key_time}" if key_time else "")
        if code:
            line += f"   🔐 {code}"
        out.append(line)
    shows = list(a["shows"].values())
    for s in shows[:12]:
        out.append("  📍 " + " · ".join(str(s[f]) for f in ("city", "venue", "date") if s.get(f)))
    if len(shows) > 12:
        out.append(f"  …and {len(shows) - 12} more shows")
    if a["summary"]:
        out.append("  " + a["summary"])
    for tid in a["links"][:3]:
        out.append(f"  ✉️ https://mail.google.com/mail/u/0/#all/{tid}")
    return "\n".join(out)


def build_digest(items, note=""):
    today = datetime.now(TZ).strftime("%a %d %b %Y, %H:%M")
    if not items:
        return f"📭 Ticket digest – {today}\nNothing new since the last digest.{note}"
    ordered = merge_items(items)
    big = [a for a in ordered if a["scale"] >= 4]
    rest = [a for a in ordered if a["scale"] < 4]
    blocks = [f"🎫 Ticket digest – {today}\n{len(ordered)} artists/events{note}"]
    if big:
        blocks.append("🔥 BIG NAMES")
        blocks.extend(render(a) for a in big)
    if rest:
        blocks.append("🎟️ EVERYTHING ELSE" if big else "🎟️ NEW ANNOUNCEMENTS")
        blocks.extend(render(a) for a in rest)
    return "\n\n".join(blocks)


# ------------------------------------------------------------- Telegram ----
def tg_send(text):
    token, chat = env("TELEGRAM_BOT_TOKEN"), env("TELEGRAM_CHAT_ID")
    chunks, current = [], ""
    for block in text.split("\n\n"):  # keep each artist's block together
        if current and len(current) + len(block) + 2 > 3800:
            chunks.append(current)
            current = ""
        current += block + "\n\n"
    chunks.append(current)
    for chunk in chunks:
        r = requests.post(
            f"https://api.telegram.org/bot{token}/sendMessage",
            json={"chat_id": chat, "text": chunk, "disable_web_page_preview": True},
            timeout=30,
        )
        r.raise_for_status()


def parse_command(text):
    words = set(re.findall(r"[a-z0-9]+", (text or "").lower()))
    for w, days in WINDOW_WORDS.items():
        if w in words:
            return ("window", days)
    if words & TRIGGER_WORDS:
        return ("digest", None)
    return ("help", None)


def poll_commands(state):
    token, allowed = env("TELEGRAM_BOT_TOKEN"), env("TELEGRAM_CHAT_ID")
    params = {"timeout": 0}
    if state.get("tg_offset"):
        params["offset"] = state["tg_offset"]
    r = requests.get(f"https://api.telegram.org/bot{token}/getUpdates", params=params, timeout=30).json()
    cmds = []
    for upd in r.get("result", []):
        state["tg_offset"] = upd["update_id"] + 1
        msg = upd.get("message") or {}
        if str(msg.get("chat", {}).get("id")) != allowed:
            continue  # ignore anyone who isn't you
        cmds.append(parse_command(msg.get("text")))
    return cmds


# ----------------------------------------------------------- Countdowns ----
def add_countdown(state, it):
    iso = it.get("key_time_iso")
    if not iso:
        return
    try:
        when = datetime.fromisoformat(str(iso).replace("Z", "+00:00"))
    except ValueError:
        return
    if when.tzinfo is None or when <= datetime.now(TZ):
        return
    cid = hashlib.md5(f"{norm(it.get('artist'))}|{it.get('category')}|{when.isoformat()}".encode()).hexdigest()[:12]
    if any(c["id"] == cid for c in state["countdowns"]):
        return
    state["countdowns"].append(
        {
            "id": cid,
            "artist": it.get("artist") or it.get("subject") or "Unknown",
            "label": CATEGORY_LABELS.get(it.get("category"), "Sale"),
            "key_time": it.get("key_time"),
            "when": when.isoformat(),
            "sent": False,
            "opened_sent": False,
        }
    )


def send_countdowns(state):
    now = datetime.now(TZ)
    keep = []
    for c in state["countdowns"]:
        try:
            when = datetime.fromisoformat(c["when"])
            mins = (when - now).total_seconds() / 60
        except Exception:
            continue
        if not c["sent"] and 0 < mins <= HEADSUP_MAX_MIN:
            tg_send(
                f"⏰ Opening soon – in about {int(mins)} min\n"
                f"{c['artist']} · {c['label']}\n"
                f"🕒 {when.astimezone(TZ):%a %d %b, %H:%M} (your time)"
                + (f"\n{c['key_time']}" if c.get("key_time") else "")
            )
            c["sent"] = True
        # A separate ping right as it opens, so a missed 45-min heads-up (e.g. the check didn't
        # run in time) still gets you a "go now" alert instead of silence.
        if not c.get("opened_sent") and -30 <= mins <= 0:
            tg_send(f"🟢 OPEN NOW\n{c['artist']} · {c['label']}\nGo get it — this just opened.")
            c["sent"] = True
            c["opened_sent"] = True
        elif not c["sent"] and mins < -30:
            c["sent"] = True  # missed by more than 30 min - too late to alert
        if mins > -2880:
            keep.append(c)
    state["countdowns"] = keep


# ------------------------------------------------------------------ Run ----
def check_token_age(state, refresh_token):
    """Warn a day before Google's 7-day login runs out, so alerts never pause."""
    tid = hashlib.md5(refresh_token.encode()).hexdigest()[:8]
    if state.get("token_id") != tid:  # a new login was pasted in -> restart the clock
        state["token_id"], state["token_since"], state["last_warn_ts"] = tid, time.time(), 0
    age_days = (time.time() - state["token_since"]) / 86400
    if age_days >= TOKEN_WARN_DAYS and time.time() - state.get("last_warn_ts", 0) > 12 * 3600:
        tg_send("⏳ Your Google login expires within about a day. Renew it now so alerts don't pause:\n" + RELOGIN_STEPS)
        state["last_warn_ts"] = time.time()


def process_new_mail(service, state):
    started = time.time()
    fresh = not state.get("last_check")
    if fresh:
        query = f"newer_than:1d {MAIL_FILTER}"  # first run: last 24 hours only
    else:
        since = max(state["last_check"] - 300, time.time() - MAX_GAP_DAYS * 86400)  # 5 min overlap for safety
        query = f"after:{int(since)} {MAIL_FILTER}"
    seen = set(state["seen_ids"])
    ids = [i for i in list_ids(service, query, MAX_EMAILS) if i not in seen]
    emails = fetch_many(service, ids)
    items = analyse(emails)
    print(f"New emails: {len(emails)}; new announcements: {len(items)}")

    for it in items:
        ck = event_key(it)
        if is_big(it) and ck not in state["alerted"]:
            state["alerted"].append(ck)
            if not fresh:  # on the very first run, don't spam alerts for old emails
                tg_send("🚨 BIG ANNOUNCEMENT\n" + render(merge_items([it])[0]))
                it["alerted"] = True
        add_countdown(state, it)
        state["pending"].append(it)

    state["seen_ids"] = (state["seen_ids"] + [e["id"] for e in emails])[-1000:]
    state["alerted"] = state["alerted"][-500:]
    state["pending"] = state["pending"][-300:]
    state["last_check"] = started


def rescan(service, days):
    ids = list_ids(service, f"newer_than:{days}d {MAIL_FILTER}", MAX_EMAILS)
    items = analyse(fetch_many(service, ids))
    tg_send(build_digest(items, f"\n(last {days} day(s), {len(ids)} emails)"))


def send_digest_if_due(state, now, force):
    today = now.strftime("%Y-%m-%d")
    scheduled = now.hour >= DIGEST_HOUR and state.get("last_digest_date") != today
    if not (force or scheduled):
        return
    pending = state["pending"]
    items = pending if force else [i for i in pending if not i.get("alerted")]
    skipped = len(pending) - len(items)
    note = f"\n({skipped} big-name alert(s) were already sent earlier)" if skipped else ""
    tg_send(build_digest(items, note))
    state["pending"] = []
    if scheduled:
        state["last_digest_date"] = today


def run(state):
    now = datetime.now(TZ)
    cmds = poll_commands(state)
    force = env("FORCE_DIGEST").lower() == "true" or any(c[0] == "digest" for c in cmds)
    service, refresh_token = gmail_service()
    check_token_age(state, refresh_token)
    process_new_mail(service, state)
    for kind, arg in cmds:
        if kind == "help":
            tg_send(HELP_TEXT)
        elif kind == "window":
            rescan(service, arg)
    send_countdowns(state)
    send_digest_if_due(state, now, force)


def notify_error(state, e):
    msg = scrub(str(e))
    print("ERROR:", type(e).__name__, msg[:200])
    low = msg.lower()
    if "invalid_grant" in low or type(e).__name__ == "RefreshError" or "expired or revoked" in low:
        hint = "Your Google login expired (this happens every 7 days).\n" + RELOGIN_STEPS
    else:
        hint = f"Error: {msg[:300]}"
    if time.time() - state.get("last_error_ts", 0) > 6 * 3600:  # at most one warning per 6 hours
        try:
            tg_send("⚠️ Ticket monitor problem.\n" + hint)
            state["last_error_ts"] = time.time()
        except Exception:
            pass


def main():
    state = load_state()
    original = json.dumps(state, sort_keys=True)
    try:
        run(state)
    except Exception as e:
        notify_error(state, e)
    finally:
        if json.dumps(state, sort_keys=True) != original:
            save_state(state)


if __name__ == "__main__":
    main()
