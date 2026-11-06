#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Gaus  (gaus.pyw)  -  Gaming - Automated - Updating - Service
==============================================================
A small Windows tray app for a home PC. It keeps your games up to date while you are out.

  * Accounts (no passwords): every person gets their own account, and each account has its
    own launchers (Steam, Epic, GOG Galaxy, EA app, Ubisoft Connect, Battle.net, Riot, Xbox, or
    any custom launcher) and, inside each launcher, its own games.
  * For every game it knows when the game usually patches (weekly rules + one-off dates, SAST).
  * In those windows it opens the launcher so the launcher downloads the update, waits until the
    download is finished, then shuts the PC down / hibernates / sleeps (idle check + cancel
    countdown). A sleeping or hibernating PC is woken by a wake timer beforehand.
  * Steam is checked precisely (installed build vs latest public build). Other launchers cannot be
    checked ahead of time, so Gaus opens them and watches their disk/network activity instead.
  * While it downloads it shows a loading screen: a slideshow of openly licensed photos per game.
  * It can update itself from a feed you control (see build_release.py), even silently.

Requirements : Windows 10/11 (Edge WebView2, already on most PCs), Python 3.11+
                 ->  pip install pywebview pystray pillow psutil
                 The window is HTML + CSS (the web folder next to this file).
Run          : double-click the .pyw (or:  pythonw gaus.pyw)
Data folder  : %APPDATA%\\Gaus  (config.json, state.json, photos, log)
All schedule times are SAST (UTC+2, no daylight saving).
"""
from __future__ import annotations

import base64
import functools
import io
import copy
import ctypes
import getpass
import hashlib
import html
import itertools
import json
import os
import queue
import random
import re
import shlex
import shutil
import socket
import subprocess
import sys
import threading
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
import uuid
import webbrowser
import zlib
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Optional


try:
    import winreg  # type: ignore
except ImportError:  # only happens off Windows (useful for testing)
    winreg = None
try:
    import psutil  # type: ignore
except ImportError:  # optional: only the non-Steam activity watching needs it
    psutil = None

# --------------------------------------------------------------------------- constants
IS_WINDOWS = sys.platform.startswith("win")
APP_TITLE = "Gaus"
APP_TAGLINE = "Gaming \u00b7 Automated \u00b7 Updating \u00b7 Service"
APP_VERSION = "1.21"
USER_AGENT = f"Gaus/{APP_VERSION} (personal home app; Python urllib)"
SAST = timezone(timedelta(hours=2), "SAST")

APP_DIR = Path(os.environ.get("GAUS_HOME") or (Path(os.environ.get("APPDATA") or Path.home()) / "Gaus"))
OLD_APP_DIR = Path(os.environ.get("APPDATA") or Path.home()) / "SteamUpdateScheduler"   # earlier name, migrated once
PHOTO_DIR = APP_DIR / "photos"
CONFIG_PATH = APP_DIR / "config.json"
STATE_PATH = APP_DIR / "state.json"
LOG_PATH = APP_DIR / "scheduler.log"
LOCK_PATH = APP_DIR / "app.lock"
FAVOURITES_PATH = APP_DIR / "favourites.json"
GENERIC_KEY = "_generic"
SAVER_KEY = "_saver"            # the pictures the user chose for their own screen saver
ART_SEARCHES = {"google": "https://www.google.com/search?tbm=isch&q=", "pinterest": "https://www.pinterest.com/search/pins/?q=",
                "deviantart": "https://www.deviantart.com/search?q=", "artstation": "https://www.artstation.com/search?sort_by=relevance&query="}
MAX_PICTURE_BYTES = 30 * 1024 * 1024
NEWS_PAGES = {2767030: "https://www.marvelrivals.com/news/"}    # a game's own news site, opened in the browser
# The publisher's own pages, shown as they are in a window. Their terms rule out scraping them or copying their art.
OFFICIAL_PAGES = {"stats": ("Marvel Rivals: hero stats", "https://www.marvelrivals.com/heroes_data/"),
                  "teamups": ("Marvel Rivals: team-ups", "https://www.marvelrivals.com/heroes/teamup.html")}
_STORE_ITEM = re.compile(r"\bbundle\b|costume|\bskin\b|emote|\bspray\b|nameplate|\bmvp\b|\bvfx\b", re.I)
_TEAM_UP_WITH = re.compile(r"team-up with ([A-Z][\w'&.\- ]*?)(?=,|\.|:|;| and |$)", re.I)
_TEAM_UP_TITLE = re.compile(r"^(.{3,50}?)\s*\(\s*([^()/\-]+?)\s*-\s*[^()]+\)$")
_PATCH_NOTES = re.compile(r"patch notes|balance post|balance adjust|extra balance|hotfix", re.I)
_PATCH_WORDS = re.compile(r"patch|update|hotfix|balance|version|bug fix|maintenance|season", re.I)
# Names to pick from in the favourite character list. Anyone can also type a name, so new heroes work too.
ROSTERS: dict[int, list[str]] = {2767030: [
    "Adam Warlock", "Angela", "Black Cat", "Black Panther", "Black Widow", "Blade", "Captain America", "Cloak & Dagger",
    "Cyclops", "Daredevil", "Deadpool", "Devil Dinosaur", "Doctor Strange", "Elsa Bloodstone", "Emma Frost", "Gambit",
    "Gorr the God Butcher", "Groot", "Hawkeye", "Hela", "Hulk", "Human Torch", "Invisible Woman", "Iron Fist", "Iron Man",
    "Jeff the Land Shark", "Jubilee", "Loki", "Luna Snow", "Magik", "Magneto", "Mantis", "Mister Fantastic", "Moon Knight",
    "Namor", "Peni Parker", "Phoenix", "Psylocke", "Rocket Raccoon", "Rogue", "Scarlet Witch", "Spider-Man", "Squirrel Girl",
    "Star-Lord", "Storm", "The Hood", "The Punisher", "The Thing", "Thor", "Ultron", "Venom", "White Fox", "Winter Soldier", "Wolverine"]}

# Where the app looks for new versions of itself: an https:// link to update.json.
# Set it ONCE before building (so your gf's copy is pre-configured) or paste it into
# Settings > "Update feed URL". Leave empty to disable self-update.
DEFAULT_UPDATE_FEED = "https://github.com/morganjones1308-design/gaus/releases/latest/download/update.json"
UPDATE_CHECK_SECONDS = 4 * 3600

CREATE_NO_WINDOW = 0x08000000
DETACHED_PROCESS = 0x00000008
RUN_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"
RUN_VALUE = "Gaus"
OLD_RUN_VALUE = "SteamUpdateScheduler"


# Steam appmanifest StateFlags (EAppState)
FLAG_INSTALLED = 4
FLAG_RUNNING = 64
BUSY_MASK = (2 | 32 | 128 | 256 | 512 | 1024 | 2048 | 4096 | 65536 | 131072 | 262144 |
             524288 | 1048576 | 2097152 | 4194304 | 8388608)
PENDING_MASK = 2 | 256 | 1024 | 1048576 | 2097152

MIN_GAME_PHOTOS = 8
MIN_SLIDES = 3                  # fewer own photos than this and generic scenery is mixed in
STEAM_SRC = "Steam"
OWN_SRC = "Your PC"
GENERIC_TARGET = 16
GENERIC_QUERIES = [
    "city skyline at night", "neon lights city street", "sunset over the ocean",
    "mountain landscape sunrise", "highway at night long exposure", "aerial view of a city",
    "palm trees sunset", "rooftop view skyline",
]
BAD_TITLE_WORDS = ("logo", "icon", "flag", "map of", "diagram", "coat of arms", "chart",
                   "signature", "seal of", "locator", "poster", "cover")

DEFAULT_SETTINGS: dict[str, Any] = {
    "paused": False,
    "auto_track": True,                # follow Steam downloads the user starts themselves
    "saver_ask": True,                 # offer the screen saver when a tracked download starts
    "saver_dim": 60,                   # how much the screen saver darkens the main monitor, in percent
    "saver_others": "dim",             # the other monitors during the screen saver: keep | dim | black
    "saver_source": "gaus",            # the pictures it shows: gaus (the game's art) | mine (the user's own)
    "tour_done": False,                # the welcome tour has been finished or skipped
    "remote_check": True,
    "remote_poll_seconds": 180,
    "start_early_minutes": 5,
    "watch_minutes": 180,
    "stall_minutes": 20,
    "max_download_hours": 8,
    "shutdown_enabled": True,
    "shutdown_after_manual": False,    # also power down after downloads the user started themselves
    "shutdown_idle_minutes": 10,
    "shutdown_wait_minutes": 30,
    "countdown_seconds": 120,
    "close_steam_before_shutdown": True,
    "dry_run_shutdown": False,
    "after_action": "shutdown",        # shutdown | sleep | hibernate (what to do when updates finish)
    "wake_from_sleep": True,           # wake the PC from sleep/hibernate before each window
    "wake_lead_minutes": 3,            # ...this long before "start watching"
    "loading_screen": "auto",          # auto | fullscreen | windowed | off
    "slide_seconds": 7,
    "photos_per_game": 24,
    "start_with_windows": False,
    "auto_update_check": True,
    "auto_install_updates": True,       # install a new app version by itself
    "generic_quiet_minutes": 4,        # non-Steam launchers: finished after this long without activity
    "update_feed_url": "",
}

# Researched patch rhythm for Marvel Rivals (Steam AppID 2767030):
#   minor patches on Thursdays 09:00 UTC (= 11:00 SAST), season launches on Fridays at the
#   same time. Dates beyond the weekly rule are listed here. Edit them in the app any time.
MARVEL_RIVALS_APPID = 2767030
PRESETS: dict[int, dict[str, Any]] = {
    MARVEL_RIVALS_APPID: {
        "weekly": [{"weekday": 3, "time": "11:00"}],
        "dates": ["2026-11-13 11:00"],
        "photo_keywords": ["Marvel Rivals", "Marvel Comics", "superhero cosplay",
                           "Comic Con cosplay", "New York City skyline", "Tokyo night neon"],
    },
}

_GENERIC_TIP = "Turn on automatic updates for the game in the launcher's own settings."
LAUNCHER_TYPES: dict[str, dict[str, Any]] = {
    "steam": {"name": "Steam", "precise": True, "args": ["-silent"], "exes": [],
              "procs": ["steam.exe", "steamwebhelper.exe"],
              "tip": "In Steam: right-click the game > Properties > Updates > 'Always keep this game up to date'."},
    "epic": {"name": "Epic Games Launcher", "precise": False, "args": [],
             "exes": [r"%ProgramFiles(x86)%\Epic Games\Launcher\Portal\Binaries\Win64\EpicGamesLauncher.exe",
                      r"%ProgramFiles(x86)%\Epic Games\Launcher\Portal\Binaries\Win32\EpicGamesLauncher.exe",
                      r"%ProgramFiles%\Epic Games\Launcher\Portal\Binaries\Win64\EpicGamesLauncher.exe"],
             "procs": ["EpicGamesLauncher.exe", "EpicWebHelper.exe"], "tip": _GENERIC_TIP},
    "gog": {"name": "GOG Galaxy", "precise": False, "args": [],
            "exes": [r"%ProgramFiles(x86)%\GOG Galaxy\GalaxyClient.exe", r"%ProgramFiles%\GOG Galaxy\GalaxyClient.exe"],
            "procs": ["GalaxyClient.exe", "GalaxyClientService.exe", "GalaxyCommunication.exe"], "tip": _GENERIC_TIP},
    "ea": {"name": "EA app", "precise": False, "args": [],
           "exes": [r"%ProgramFiles%\Electronic Arts\EA Desktop\EA Desktop\EADesktop.exe"],
           "procs": ["EADesktop.exe", "EABackgroundService.exe", "EACefSubprocess.exe"], "tip": _GENERIC_TIP},
    "ubisoft": {"name": "Ubisoft Connect", "precise": False, "args": [],
                "exes": [r"%ProgramFiles(x86)%\Ubisoft\Ubisoft Game Launcher\UbisoftConnect.exe",
                         r"%ProgramFiles(x86)%\Ubisoft\Ubisoft Game Launcher\upc.exe"],
                "procs": ["UbisoftConnect.exe", "upc.exe", "UplayWebCore.exe", "UbisoftGameLauncher.exe"],
                "tip": _GENERIC_TIP},
    "battlenet": {"name": "Battle.net", "precise": False, "args": [],
                  "exes": [r"%ProgramFiles(x86)%\Battle.net\Battle.net.exe", r"%ProgramFiles%\Battle.net\Battle.net.exe"],
                  "procs": ["Battle.net.exe", "Agent.exe"], "tip": _GENERIC_TIP},
    "riot": {"name": "Riot Client", "precise": False, "args": [],
             "exes": [r"C:\Riot Games\Riot Client\RiotClientServices.exe",
                      r"%ProgramFiles%\Riot Games\Riot Client\RiotClientServices.exe"],
             "procs": ["RiotClientServices.exe", "RiotClientUx.exe", "RiotClientUxRender.exe"],
             "tip": "Riot games patch themselves when the client opens."},
    "xbox": {"name": "Xbox app", "precise": False, "args": [],
             "exes": ["shell:AppsFolder\\Microsoft.GamingApp_8wekyb3d8bbwe!Microsoft.Xbox.App"],
             "procs": ["XboxPcApp.exe", "GamingServices.exe"], "tip": _GENERIC_TIP},
    "custom": {"name": "Custom launcher", "precise": False, "args": [], "exes": [], "procs": [],
               "tip": "Choose the launcher's .exe. Gaus opens it and watches its disk activity."},
}
GENERIC_ACTIVE_BPS = 300 * 1024          # launcher disk/network activity above this = it is downloading
GENERIC_RX_BPS = 2 * 1024 * 1024         # fallback when per-process counters cannot be read
GENERIC_BLIND_WAIT = 900                 # seconds to wait for a non-Steam launcher to start something
GENERIC_MIN_BYTES = 50 * 1024 * 1024     # activity must add up to this before it counts as a download

# --------------------------------------------------------------------------- events / logging
class Bus:
    """Tiny pub/sub. Worker threads emit; the controller subscribes and forwards to the window."""

    def __init__(self) -> None:
        self.subs: dict[str, list[Any]] = {}

    def on(self, name: str, fn: Any) -> None:
        self.subs.setdefault(name, []).append(fn)

    def emit(self, name: str, *args: Any) -> None:
        for fn in list(self.subs.get(name, [])):
            try:
                fn(*args)
            except Exception:
                traceback.print_exc()


BUS = Bus()
_log_lock = threading.Lock()


def emit(name: str, *args: Any) -> None:
    BUS.emit(name, *args)


def log(msg: str) -> None:
    line = f"[{datetime.now(SAST):%Y-%m-%d %H:%M:%S}] {msg}"
    try:
        APP_DIR.mkdir(parents=True, exist_ok=True)
        with _log_lock, open(LOG_PATH, "a", encoding="utf-8") as fh:
            fh.write(line + "\n")
    except OSError:
        pass
    emit("log", line)


def trim_log(max_bytes: int = 1_500_000, keep_bytes: int = 500_000) -> None:
    try:
        if LOG_PATH.exists() and LOG_PATH.stat().st_size > max_bytes:
            data = LOG_PATH.read_bytes()[-keep_bytes:]
            nl = data.find(b"\n")
            LOG_PATH.write_bytes(data[nl + 1:] if nl >= 0 else data)
    except OSError:
        pass


def migrate_old_data() -> None:
    """The app used to be called Steam Update Scheduler: carry its settings, games and photos over once."""
    try:
        if os.environ.get("GAUS_HOME") or (APP_DIR / "config.json").exists() or not OLD_APP_DIR.exists():
            return
        for item in OLD_APP_DIR.iterdir():
            if item.name == "app.lock" or item.name.endswith((".new", ".old")):
                continue
            dest = APP_DIR / item.name
            if item.is_dir():
                shutil.copytree(item, dest, dirs_exist_ok=True)
            else:
                shutil.copy2(item, dest)
        log("Carried over settings and photos from the earlier version")
    except OSError as exc:
        log(f"Could not carry over the earlier version's data: {exc}")


def read_json(path: Path, default: Any) -> Any:
    try:
        with open(path, "r", encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return default


def write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(data, fh, indent=2, ensure_ascii=False)
    os.replace(tmp, path)


def now_sast() -> datetime:
    return datetime.now(SAST)


def fmt_mbps(bytes_per_second: float) -> str:
    return f"{bytes_per_second * 8 / 1_000_000:.1f} Mbps"


def fmt_bytes(n: float) -> str:
    n = float(n)
    units = ["B", "KB", "MB", "GB", "TB"]
    i = 0
    while n >= 1024 and i < len(units) - 1:
        n /= 1024
        i += 1
    return f"{n:.1f} {units[i]}" if i >= 2 else f"{n:.0f} {units[i]}"


def to_int(value: Any, default: int = 0) -> int:
    try:
        return int(str(value).strip())
    except (ValueError, TypeError):
        return default


# --------------------------------------------------------------------------- schedule model
_DAY_WORDS = {"mon": 0, "tue": 1, "wed": 2, "thu": 3, "fri": 4, "sat": 5, "sun": 6}
_DAY_NAMES = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]


def parse_hhmm(text: str) -> tuple[int, int]:
    m = re.fullmatch(r"\s*(\d{1,2}):(\d{2})\s*", str(text))
    if not m:
        raise ValueError(f"Can't read the time '{text}'. Use HH:MM, for example 11:00.")
    hh, mm = int(m.group(1)), int(m.group(2))
    if hh > 23 or mm > 59:
        raise ValueError(f"'{text}' is not a valid time.")
    return hh, mm


def parse_dt(text: str) -> datetime:
    t = str(text).strip().replace("T", " ")
    try:
        return datetime.strptime(t, "%Y-%m-%d %H:%M").replace(tzinfo=SAST)
    except ValueError:
        raise ValueError(f"Can't read the date '{text}'. Use YYYY-MM-DD HH:MM, for example 2026-11-13 11:00.")


def parse_weekly_text(text: str) -> list[dict[str, Any]]:
    rules: list[dict[str, Any]] = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        m = re.fullmatch(r"([A-Za-z]+)\s+(\d{1,2}:\d{2})", line)
        if not m:
            raise ValueError(f"Can't read '{line}'. Use for example 'Thu 11:00' or 'Daily 11:00'.")
        word = m.group(1).lower()
        if word in ("daily", "everyday"):
            weekday = -1
        elif word[:3] in _DAY_WORDS:
            weekday = _DAY_WORDS[word[:3]]
        else:
            raise ValueError(f"'{m.group(1)}' is not a day of the week (use Mon..Sun or Daily).")
        hh, mm = parse_hhmm(m.group(2))
        rule = {"weekday": weekday, "time": f"{hh:02d}:{mm:02d}"}
        if rule not in rules:
            rules.append(rule)
    return rules


def format_weekly_text(rules: list[dict[str, Any]]) -> str:
    out = []
    for r in rules:
        day = "Daily" if r["weekday"] == -1 else _DAY_NAMES[r["weekday"]]
        out.append(f"{day} {r['time']}")
    return "\n".join(out)


def parse_dates_text(text: str) -> list[str]:
    out: list[str] = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        s = parse_dt(line).strftime("%Y-%m-%d %H:%M")
        if s not in out:
            out.append(s)
    return sorted(out)


def normalize_game(g: Any) -> Optional[dict[str, Any]]:
    if not isinstance(g, dict):
        return None
    appid = to_int(g.get("appid"), 0)
    if appid <= 0:
        return None
    weekly: list[dict[str, Any]] = []
    for r in g.get("weekly") or []:
        try:
            wd = int(r["weekday"])
            hh, mm = parse_hhmm(str(r["time"]))
            if -1 <= wd <= 6:
                rule = {"weekday": wd, "time": f"{hh:02d}:{mm:02d}"}
                if rule not in weekly:
                    weekly.append(rule)
        except (KeyError, ValueError, TypeError):
            continue
    dates: list[str] = []
    for s in g.get("dates") or []:
        try:
            dates.append(parse_dt(str(s)).strftime("%Y-%m-%d %H:%M"))
        except ValueError:
            continue
    keywords = [str(k).strip() for k in (g.get("photo_keywords") or []) if str(k).strip()]
    name = str(g.get("name") or f"App {appid}").strip()
    return {"appid": appid, "name": name, "enabled": bool(g.get("enabled", True)),
            "weekly": weekly, "dates": sorted(set(dates)),
            "photo_keywords": keywords or [name]}


def new_id() -> str:
    return uuid.uuid4().hex[:8]


def synthetic_appid(ltype: str, name: str) -> int:
    """Games from launchers without numeric ids get a stable id that can never clash with a Steam AppID."""
    return 10_000_000_000 + zlib.crc32(f"{ltype}|{name.strip().lower()}".encode("utf-8"))


def default_account_name() -> str:
    try:
        name = getpass.getuser().strip()
    except Exception:
        name = ""
    return name[:1].upper() + name[1:] if name else "Me"


def normalize_launcher(l: Any) -> Optional[dict[str, Any]]:
    if not isinstance(l, dict):
        return None
    ltype = str(l.get("type") or "")
    if ltype not in LAUNCHER_TYPES:
        return None
    games: list[dict[str, Any]] = []
    for g in l.get("games") or []:
        ng = normalize_game(g)
        if ng and all(ng["appid"] != x["appid"] for x in games):
            games.append(ng)
    return {"id": str(l.get("id") or new_id()), "type": ltype,
            "name": str(l.get("name") or LAUNCHER_TYPES[ltype]["name"]).strip() or LAUNCHER_TYPES[ltype]["name"],
            "path": str(l.get("path") or "").strip(), "args": str(l.get("args") or "").strip(),
            "enabled": bool(l.get("enabled", True)), "games": games}


def normalize_account(a: Any) -> Optional[dict[str, Any]]:
    if not isinstance(a, dict):
        return None
    launchers: list[dict[str, Any]] = []
    for l in a.get("launchers") or []:
        nl = normalize_launcher(l)
        if nl and all(nl["id"] != x["id"] for x in launchers):
            launchers.append(nl)
    return {"id": str(a.get("id") or new_id()), "name": str(a.get("name") or "Account").strip() or "Account",
            "enabled": bool(a.get("enabled", True)), "launchers": launchers}


def new_game(appid: int, name: str) -> dict[str, Any]:
    preset = PRESETS.get(appid)
    if preset:
        return normalize_game({"appid": appid, "name": name, "enabled": True, **copy.deepcopy(preset)})  # type: ignore
    return normalize_game({"appid": appid, "name": name, "enabled": True,
                           "weekly": [{"weekday": -1, "time": "11:00"}], "dates": [],
                           "photo_keywords": [name, f"{name} game"]})  # type: ignore


def trigger_key(appid: int, t: datetime) -> str:
    return f"{appid}|{t.strftime('%Y-%m-%d %H:%M')}"


def candidate_triggers(game: dict[str, Any], now: datetime, days_back: int = 1,
                       days_ahead: int = 14) -> list[datetime]:
    out: set[datetime] = set()
    today = now.astimezone(SAST).date()
    for offset in range(-days_back, days_ahead + 1):
        d = today + timedelta(days=offset)
        for rule in game.get("weekly", []):
            if rule["weekday"] in (-1, d.weekday()):
                hh, mm = parse_hhmm(rule["time"])
                out.add(datetime(d.year, d.month, d.day, hh, mm, tzinfo=SAST))
    for s in game.get("dates", []):
        try:
            out.add(parse_dt(s))
        except ValueError:
            pass
    return sorted(out)


def active_trigger(game: dict[str, Any], now: datetime, settings: dict[str, Any],
                   handled: dict[str, Any]) -> Optional[datetime]:
    early = timedelta(minutes=int(settings["start_early_minutes"]))
    span = timedelta(minutes=int(settings["watch_minutes"]))
    hit = None
    for t in candidate_triggers(game, now, days_back=1, days_ahead=1):
        if t - early <= now <= t + span and trigger_key(game["appid"], t) not in handled:
            hit = t
    return hit


def next_trigger(game: dict[str, Any], now: datetime) -> Optional[datetime]:
    for t in candidate_triggers(game, now, days_back=0, days_ahead=14):
        if t > now:
            return t
    return None


# --------------------------------------------------------------------------- Steam helpers
_VDF_TOKEN = re.compile(r'"((?:[^"\\]|\\.)*)"|([{}])')


def parse_vdf(text: str) -> dict[str, Any]:
    stack: list[dict[str, Any]] = [{}]
    key: Optional[str] = None
    for m in _VDF_TOKEN.finditer(text):
        s, brace = m.group(1), m.group(2)
        if brace == "{":
            if key is None:
                continue
            node: dict[str, Any] = {}
            stack[-1][key] = node
            stack.append(node)
            key = None
        elif brace == "}":
            if len(stack) > 1:
                stack.pop()
            key = None
        else:
            s = s.replace("\\\\", "\\").replace('\\"', '"')
            if key is None:
                key = s
            else:
                stack[-1][key] = s
                key = None
    return stack[0]


def vget(node: Any, key: str, default: Any = None) -> Any:
    if not isinstance(node, dict):
        return default
    for k, v in node.items():
        if k.lower() == key.lower():
            return v
    return default


def find_steam_path(settings: dict[str, Any]) -> Optional[Path]:
    custom = str(settings.get("steam_path") or "").strip()
    if custom and (Path(custom) / "steam.exe").exists():
        return Path(custom)
    candidates: list[str] = []
    if winreg is not None:
        for hive, sub, val in ((winreg.HKEY_CURRENT_USER, r"Software\Valve\Steam", "SteamPath"),
                               (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\Valve\Steam", "InstallPath"),
                               (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Valve\Steam", "InstallPath")):
            try:
                with winreg.OpenKey(hive, sub) as k:
                    candidates.append(str(winreg.QueryValueEx(k, val)[0]))
            except OSError:
                continue
    candidates += [r"C:\Program Files (x86)\Steam", r"C:\Program Files\Steam"]
    for c in candidates:
        if c and (Path(c) / "steam.exe").exists():
            return Path(c)
    return None


def library_dirs(steam: Path) -> list[Path]:
    dirs = [steam / "steamapps"]
    data = vget(parse_vdf(_read_text(steam / "steamapps" / "libraryfolders.vdf")), "libraryfolders", {})
    for _k, v in (data.items() if isinstance(data, dict) else []):
        path = vget(v, "path") if isinstance(v, dict) else (v if isinstance(v, str) else None)
        if path:
            p = Path(path) / "steamapps"
            if p not in dirs:
                dirs.append(p)
    return dirs


def _read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def read_manifest(appid: int, steam: Optional[Path]) -> Optional[dict[str, Any]]:
    if steam is None:
        return None
    for d in library_dirs(steam):
        f = d / f"appmanifest_{appid}.acf"
        if f.exists():
            state = vget(parse_vdf(_read_text(f)), "AppState")
            if not isinstance(state, dict):
                continue
            return {
                "path": f, "name": vget(state, "name", ""), "installdir": str(vget(state, "installdir", "") or ""),
                "state": to_int(vget(state, "StateFlags")),
                "buildid": to_int(vget(state, "buildid")),
                "target": to_int(vget(state, "TargetBuildID")),
                "to_dl": to_int(vget(state, "BytesToDownload")),
                "dl": to_int(vget(state, "BytesDownloaded")),
                "to_stage": to_int(vget(state, "BytesToStage")),
                "staged": to_int(vget(state, "BytesStaged")),
            }
    return None


def list_installed(steam: Optional[Path]) -> dict[int, str]:
    out: dict[int, str] = {}
    if steam is None:
        return out
    for d in library_dirs(steam):
        try:
            files = sorted(d.glob("appmanifest_*.acf"))
        except OSError:
            continue
        for f in files:
            state = vget(parse_vdf(_read_text(f)), "AppState")
            if isinstance(state, dict):
                appid = to_int(vget(state, "appid"))
                if appid:
                    out[appid] = str(vget(state, "name", f"App {appid}"))
    return out


def manifest_idle(m: dict[str, Any]) -> bool:
    return bool(m["state"] & FLAG_INSTALLED) and not (m["state"] & BUSY_MASK) \
        and m["target"] in (0, m["buildid"])


def manifest_busy(m: dict[str, Any]) -> bool:
    return bool(m["state"] & BUSY_MASK) or m["target"] not in (0, m["buildid"])


_STEAM_LOG_LINE = re.compile(r"^\[(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d)\] (?:AppID (\d+) (?:update started : download "
                             r"(\d+)/(\d+)|App update changed : (.*))|Current download rate: ([\d.]+) Mbps"
                             r"|stats: \(Invalid, 0\) : (\d+) Bytes, (\d+) sec)", re.M)


def steam_live(steam: Optional[Path]) -> dict[int, dict[str, Any]]:
    """What Steam is doing right now, from the end of its content log. The appmanifest is only rewritten when a
    download starts or stops, so it cannot show progress. The log has the speed Steam itself reports about once a
    minute, and its exact byte count every 5 minutes or so; the speed only fills the gap since the last count."""
    global _steam_log_cache
    if steam is None:
        return {}
    try:
        path = steam / "logs" / "content_log.txt"
        st = path.stat()
        sig = (st.st_mtime_ns, st.st_size)
        if _steam_log_cache[0] != sig:      # most ticks nothing changed, so don't read it again
            with open(path, "rb") as fh:
                fh.seek(max(0, st.st_size - 1_000_000))
                _steam_log_cache = (sig, *_parse_steam_log(fh.read().decode("utf-8", "replace")))
    except OSError:
        return {}
    _sig, parsed, rate, rate_t = _steam_log_cache
    apps = {k: dict(v) for k, v in parsed.items()}
    now = time.time()
    fresh = now - rate_t < 180
    for a in apps.values():
        downloading = "Downloading" in a["state"] and fresh
        a["active"] = "Running Update" in a["state"]
        a["speed"] = rate if downloading else 0.0
        if downloading and a["t"]:
            a["dl"] += rate * (now - a["t"])
        a["dl"] = min(a["dl"], a["total"])
    return apps


_steam_log_cache: tuple[Any, dict[int, dict[str, Any]], float, float] = (None, {}, 0.0, 0.0)


def _parse_steam_log(text: str) -> tuple[dict[int, dict[str, Any]], float, float]:
    apps: dict[int, dict[str, Any]] = {}
    rate, rate_t = 0.0, 0.0
    for line in _STEAM_LOG_LINE.finditer(text):
        when, appid, dl, total, changed, mbps, counted, secs = line.groups()
        if appid and changed is not None:
            apps.setdefault(int(appid), {"state": "", "dl": 0.0, "exact": 0.0, "total": 0, "t": 0.0, "t0": 0.0})["state"] = changed.strip()
            continue
        t = datetime.fromisoformat(when).timestamp()
        if appid:
            apps[int(appid)] = {"state": "Running Update", "dl": float(dl), "exact": float(dl), "total": int(total), "t": t, "t0": t}
        elif counted:
            for a in apps.values():
                if "Downloading" in a["state"] and a["t0"]:
                    # the first count can reach back past this download's start, so only take its share
                    a["exact"] += int(counted) * min(1.0, (t - a["t0"]) / max(1, int(secs)))
                    a["dl"], a["t"] = a["exact"], t
        else:
            rate = float(mbps) * 125_000    # Mbps to bytes per second
            rate_t = t
            for a in apps.values():
                if "Downloading" in a["state"] and a["t"]:
                    a["dl"] += rate * (t - a["t"])
                a["t"] = t
    return apps, rate, rate_t


def _run_hidden(cmd: list[str], timeout: int = 15) -> subprocess.CompletedProcess:
    flags = CREATE_NO_WINDOW if IS_WINDOWS else 0
    return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, creationflags=flags)


def steam_running() -> bool:
    if not IS_WINDOWS:
        return False
    try:
        out = _run_hidden(["tasklist", "/FI", "IMAGENAME eq steam.exe", "/NH"]).stdout.lower()
        return "steam.exe" in out
    except (OSError, subprocess.SubprocessError):
        return False


def running_app_id() -> int:
    if winreg is None:
        return 0
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Valve\Steam") as k:
            return int(winreg.QueryValueEx(k, "RunningAppID")[0])
    except (OSError, ValueError):
        return 0


def launch_steam(steam: Path) -> None:
    flags = (DETACHED_PROCESS | 0x00000200) if IS_WINDOWS else 0
    subprocess.Popen([str(steam / "steam.exe"), "-silent"], creationflags=flags, close_fds=True)


def close_steam(steam: Path) -> None:
    try:
        subprocess.Popen([str(steam / "steam.exe"), "-shutdown"],
                         creationflags=CREATE_NO_WINDOW if IS_WINDOWS else 0)
    except OSError:
        return
    for _ in range(45):
        if not steam_running():
            return
        time.sleep(1)


def run_shutdown() -> None:
    """Shut down for real. /f closes any program that would otherwise block the shutdown (a blocked shutdown
    leaves the PC awake until Windows' idle timer puts it to sleep). If we are still running 2 minutes later,
    Windows did not shut down, so try once more immediately."""
    try:
        r = _run_hidden(["shutdown", "/s", "/f", "/t", "10", "/c", "Gaus: game updates finished"])
        log(f"shutdown command finished with code {r.returncode} {(r.stderr or r.stdout or '').strip()[:200]}")
    except (OSError, subprocess.SubprocessError) as exc:
        log(f"shutdown command failed: {exc!r}")

    def verify() -> None:
        time.sleep(120)
        log("Windows has not shut down 2 minutes after the command - trying again right now")
        try:
            r2 = _run_hidden(["shutdown", "/s", "/f", "/t", "0"])
            log(f"second shutdown command finished with code {r2.returncode} {(r2.stderr or r2.stdout or '').strip()[:200]}")
        except (OSError, subprocess.SubprocessError) as exc:
            log(f"second shutdown command failed: {exc!r}")

    threading.Thread(target=verify, daemon=True, name="shutdown-verify").start()


# ---- sleep / wake
POWER_ACTIONS = {"sleep": "go to sleep", "hibernate": "hibernate", "shutdown": "shut down"}


def power_note(settings: dict[str, Any]) -> str:
    if not settings["shutdown_enabled"]:
        return ""
    return f"PC will {POWER_ACTIONS.get(str(settings['after_action']), 'shut down')} when updates finish"

ES_CONTINUOUS = 0x80000000
ES_SYSTEM_REQUIRED = 0x00000001
SUB_SLEEP_GUID = "238c9fa8-0aad-41ed-83f4-97be242c8f20"
RTCWAKE_GUID = "bd3b718a-0680-4d9d-8ab2-e1d2b4ac806d"      # "Allow wake timers"
_k32: Any = None


def _kernel32() -> Any:
    global _k32
    if _k32 is None:
        from ctypes import wintypes
        k = ctypes.WinDLL("kernel32", use_last_error=True)  # type: ignore[attr-defined]
        k.CreateWaitableTimerW.restype = wintypes.HANDLE
        k.CreateWaitableTimerW.argtypes = [ctypes.c_void_p, wintypes.BOOL, wintypes.LPCWSTR]
        k.SetWaitableTimer.restype = wintypes.BOOL
        k.SetWaitableTimer.argtypes = [wintypes.HANDLE, ctypes.POINTER(ctypes.c_longlong), wintypes.LONG,
                                       ctypes.c_void_p, ctypes.c_void_p, wintypes.BOOL]
        k.CancelWaitableTimer.restype = wintypes.BOOL
        k.CancelWaitableTimer.argtypes = [wintypes.HANDLE]
        k.WaitForSingleObject.restype = wintypes.DWORD
        k.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
        k.SetThreadExecutionState.restype = wintypes.DWORD
        k.SetThreadExecutionState.argtypes = [wintypes.DWORD]
        _k32 = k
    return _k32


def set_keep_awake(on: bool) -> None:
    """Stops Windows sleeping on its own (idle timeout). Call from the same thread every time."""
    if not IS_WINDOWS:
        return
    try:
        _kernel32().SetThreadExecutionState(ES_CONTINUOUS | (ES_SYSTEM_REQUIRED if on else 0))
    except (OSError, AttributeError):
        pass


class MonitorDimmer:
    """Darkens every monitor except the main one with black, click-through windows. Windows cannot safely power
    off one monitor on its own, and because these are plain windows they vanish with the app if it ever dies."""

    def __init__(self) -> None:
        self.thread_id = 0

    def show(self, alpha: int) -> None:
        if IS_WINDOWS and not self.thread_id:
            threading.Thread(target=self._run, args=(alpha,), daemon=True, name="dimmer").start()

    def hide(self) -> None:
        if self.thread_id:
            ctypes.windll.user32.PostThreadMessageW(self.thread_id, 0x0012, 0, 0)    # type: ignore[attr-defined]  # WM_QUIT
            self.thread_id = 0

    def _run(self, alpha: int) -> None:
        from ctypes import wintypes
        u = ctypes.WinDLL("user32", use_last_error=True)  # type: ignore[attr-defined]
        g = ctypes.WinDLL("gdi32")  # type: ignore[attr-defined]
        k = ctypes.WinDLL("kernel32")  # type: ignore[attr-defined]
        wndproc = ctypes.WINFUNCTYPE(ctypes.c_ssize_t, wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM)  # type: ignore[attr-defined]
        monitorproc = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HMONITOR, wintypes.HDC, ctypes.POINTER(wintypes.RECT), wintypes.LPARAM)  # type: ignore[attr-defined]

        class WndClass(ctypes.Structure):
            _fields_ = [("style", wintypes.UINT), ("proc", wndproc), ("extra", ctypes.c_int), ("wextra", ctypes.c_int),
                        ("inst", wintypes.HINSTANCE), ("icon", wintypes.HICON), ("cursor", wintypes.HANDLE),
                        ("brush", wintypes.HBRUSH), ("menu", wintypes.LPCWSTR), ("name", wintypes.LPCWSTR)]

        class MonitorInfo(ctypes.Structure):
            _fields_ = [("size", wintypes.DWORD), ("rect", wintypes.RECT), ("work", wintypes.RECT), ("flags", wintypes.DWORD)]

        u.DefWindowProcW.restype = ctypes.c_ssize_t
        u.DefWindowProcW.argtypes = [wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM]
        u.CreateWindowExW.restype = wintypes.HWND
        u.CreateWindowExW.argtypes = [wintypes.DWORD, wintypes.LPCWSTR, wintypes.LPCWSTR, wintypes.DWORD, ctypes.c_int, ctypes.c_int,
                                      ctypes.c_int, ctypes.c_int, wintypes.HWND, wintypes.HMENU, wintypes.HINSTANCE, wintypes.LPVOID]
        u.GetMonitorInfoW.argtypes = [wintypes.HMONITOR, ctypes.POINTER(MonitorInfo)]
        u.SetLayeredWindowAttributes.argtypes = [wintypes.HWND, wintypes.COLORREF, wintypes.BYTE, wintypes.DWORD]
        u.ShowWindow.argtypes = [wintypes.HWND, ctypes.c_int]
        u.EnumDisplayMonitors.argtypes = [wintypes.HDC, ctypes.c_void_p, monitorproc, wintypes.LPARAM]
        u.DestroyWindow.argtypes = [wintypes.HWND]
        u.UnregisterClassW.argtypes = [wintypes.LPCWSTR, wintypes.HINSTANCE]
        g.GetStockObject.restype = wintypes.HGDIOBJ
        k.GetModuleHandleW.restype = wintypes.HMODULE
        k.GetModuleHandleW.argtypes = [wintypes.LPCWSTR]

        proc = wndproc(lambda h, m, w, l: u.DefWindowProcW(h, m, w, l))
        inst = k.GetModuleHandleW(None)
        wc = WndClass(proc=proc, inst=inst, brush=g.GetStockObject(4), name="GausDimmer")    # 4 = BLACK_BRUSH
        u.RegisterClassW(ctypes.byref(wc))
        rects: list[tuple[int, int, int, int]] = []

        def add(mon: Any, _dc: Any, _r: Any, _l: Any) -> bool:
            info = MonitorInfo(size=ctypes.sizeof(MonitorInfo))
            if u.GetMonitorInfoW(mon, ctypes.byref(info)) and not info.flags & 1:    # 1 = the main monitor
                r = info.rect
                rects.append((r.left, r.top, r.right - r.left, r.bottom - r.top))
            return True

        callback = monitorproc(add)
        u.EnumDisplayMonitors(None, None, callback, 0)
        self.thread_id = k.GetCurrentThreadId()
        # layered | topmost | click-through | no taskbar button | never takes focus
        windows = [u.CreateWindowExW(0x80000 | 0x8 | 0x20 | 0x80 | 0x8000000, "GausDimmer", "Gaus", 0x80000000,
                                     x, y, w, h, None, None, inst, None) for x, y, w, h in rects]
        for hwnd in windows:
            u.SetLayeredWindowAttributes(hwnd, 0, alpha, 2)    # 2 = LWA_ALPHA
            u.ShowWindow(hwnd, 4)    # 4 = SW_SHOWNOACTIVATE
        msg = wintypes.MSG()
        while u.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
            u.TranslateMessage(ctypes.byref(msg))
            u.DispatchMessageW(ctypes.byref(msg))
        for hwnd in windows:
            u.DestroyWindow(hwnd)
        u.UnregisterClassW("GausDimmer", inst)


class WakeTimer:
    """A waitable timer that can wake the PC from sleep or hibernate (never from a full shutdown)."""

    def __init__(self, label: str) -> None:
        self.label = label
        self.handle: Any = None
        self.when: Optional[float] = None

    def arm(self, when_ts: Optional[float]) -> str:
        """Returns 'ok', 'cleared', 'unsupported' or 'error: ...'. None cancels the timer."""
        if not IS_WINDOWS:
            return "error: wake timers need Windows"
        try:
            k = _kernel32()
            if self.handle is None:
                self.handle = k.CreateWaitableTimerW(None, True, None)
                if not self.handle:
                    self.handle = None
                    return f"error: CreateWaitableTimer failed (code {ctypes.get_last_error()})"
            if when_ts is None:
                k.CancelWaitableTimer(self.handle)
                self.when = None
                return "cleared"
            due = ctypes.c_longlong(int((when_ts + 11644473600) * 10_000_000))   # absolute UTC FILETIME
            ctypes.set_last_error(0)
            if not k.SetWaitableTimer(self.handle, ctypes.byref(due), 0, None, None, True):
                return f"error: SetWaitableTimer failed (code {ctypes.get_last_error()})"
            unsupported = ctypes.get_last_error() == 50      # ERROR_NOT_SUPPORTED: no resume timers
            self.when = when_ts
            threading.Thread(target=self._watch, args=(self.handle, when_ts), daemon=True,
                             name=f"wake-{self.label}").start()
            return "unsupported" if unsupported else "ok"
        except (OSError, AttributeError, ValueError) as exc:
            return f"error: {exc}"

    def _watch(self, handle: Any, when_ts: float) -> None:
        try:
            k = _kernel32()
            while True:
                r = k.WaitForSingleObject(handle, 5000)
                if self.handle != handle or self.when != when_ts:
                    return                                   # re-armed or cancelled
                if r == 0:
                    log(f"Wake timer '{self.label}' fired (it was set for "
                        f"{datetime.fromtimestamp(when_ts, SAST):%a %H:%M:%S} SAST)")
                    return
                if r != 258:                                 # not WAIT_TIMEOUT
                    return
        except (OSError, AttributeError):
            pass


def wake_timers_ac_setting() -> Optional[int]:
    """Windows 'Allow wake timers' while plugged in: 0 disabled, 1 enabled, 2 important only."""
    if not IS_WINDOWS:
        return None
    try:
        out = _run_hidden(["powercfg", "/query", "SCHEME_CURRENT", SUB_SLEEP_GUID, RTCWAKE_GUID]).stdout
        vals = re.findall(r"0x([0-9a-fA-F]{8})", out)
        return int(vals[-2], 16) if len(vals) >= 2 else None      # last two = current AC, current DC
    except (OSError, subprocess.SubprocessError, ValueError):
        return None


def enable_wake_timers() -> bool:
    try:
        a = _run_hidden(["powercfg", "/setacvalueindex", "SCHEME_CURRENT", SUB_SLEEP_GUID, RTCWAKE_GUID, "1"])
        b = _run_hidden(["powercfg", "/setactive", "SCHEME_CURRENT"])
        return a.returncode == 0 and b.returncode == 0
    except (OSError, subprocess.SubprocessError):
        return False


def _suspend_now() -> None:
    try:
        ctypes.WinDLL("powrprof").SetSuspendState(0, 0, 0)    # type: ignore[attr-defined]
    except (OSError, AttributeError) as exc:
        log(f"Sleep command failed: {exc}")


def run_power_action(action: str) -> None:
    if action == "shutdown":
        run_shutdown()
        return
    if action == "hibernate":
        r = _run_hidden(["shutdown", "/h"])
        if r.returncode == 0:
            return
        log("Hibernate is not available (enable it once with 'powercfg /hibernate on' in an admin "
            "prompt) - going to sleep instead")
    if IS_WINDOWS:
        threading.Thread(target=_suspend_now, daemon=True, name="suspend").start()


class _LastInputInfo(ctypes.Structure):
    _fields_ = [("cbSize", ctypes.c_uint), ("dwTime", ctypes.c_uint)]


def user_idle_seconds() -> float:
    if not IS_WINDOWS:
        return 10 ** 9
    try:
        info = _LastInputInfo()
        info.cbSize = ctypes.sizeof(info)
        if not ctypes.windll.user32.GetLastInputInfo(ctypes.byref(info)):  # type: ignore[attr-defined]
            return 0.0
        kernel = ctypes.windll.kernel32  # type: ignore[attr-defined]
        kernel.GetTickCount.restype = ctypes.c_uint
        return max(0.0, ((kernel.GetTickCount() - info.dwTime) & 0xFFFFFFFF) / 1000.0)
    except (OSError, AttributeError):
        return 0.0


def minimize_windows_of(names: list[str]) -> int:
    """Minimizes the visible windows of these programs (it never closes them, so a download carries on)."""
    if not IS_WINDOWS or psutil is None:
        return 0
    from ctypes import wintypes
    u = ctypes.WinDLL("user32")  # type: ignore[attr-defined]
    wanted = {n.lower() for n in names}
    found: list[Any] = []
    enum_proc = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)  # type: ignore[attr-defined]
    u.EnumWindows.argtypes = [enum_proc, wintypes.LPARAM]
    u.IsWindowVisible.argtypes = [wintypes.HWND]
    u.GetWindowTextLengthW.argtypes = [wintypes.HWND]
    u.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
    u.ShowWindowAsync.argtypes = [wintypes.HWND, ctypes.c_int]

    def check(hwnd: Any, _l: Any) -> bool:
        if u.IsWindowVisible(hwnd) and u.GetWindowTextLengthW(hwnd):
            pid = wintypes.DWORD()
            u.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
            try:
                if psutil.Process(pid.value).name().lower() in wanted:
                    found.append(hwnd)
            except psutil.Error:
                pass
        return True

    u.EnumWindows(enum_proc(check), 0)
    for hwnd in found:
        u.ShowWindowAsync(hwnd, 6)    # 6 = SW_MINIMIZE
    return len(found)


def trim_memory(pids: list[int]) -> None:
    """Hands memory these processes aren't using back to Windows. Anything needed again just comes back."""
    if not IS_WINDOWS:
        return
    k = ctypes.WinDLL("kernel32")  # type: ignore[attr-defined]
    k.OpenProcess.restype = ctypes.c_void_p
    k.SetProcessWorkingSetSize.argtypes = [ctypes.c_void_p, ctypes.c_ssize_t, ctypes.c_ssize_t]
    k.CloseHandle.argtypes = [ctypes.c_void_p]
    for pid in pids:
        h = k.OpenProcess(0x0100 | 0x0400, False, pid)    # PROCESS_SET_QUOTA | PROCESS_QUERY_INFORMATION
        if h:
            k.SetProcessWorkingSetSize(h, -1, -1)
            k.CloseHandle(h)


def set_autostart(enabled: bool) -> None:
    if winreg is None or os.environ.get("GAUS_HOME"):    # a separate data folder is a test copy: leave the real entry alone
        return
    exe = Path(sys.executable)
    if is_frozen():
        cmd = f'"{exe}" --minimized'
    else:
        pyw = exe.with_name("pythonw.exe") if exe.name.lower() == "python.exe" else exe
        cmd = f'"{pyw}" "{Path(__file__).resolve()}" --minimized'
    try:
        if enabled:
            with winreg.CreateKey(winreg.HKEY_CURRENT_USER, RUN_KEY) as k:
                winreg.SetValueEx(k, RUN_VALUE, 0, winreg.REG_SZ, cmd)
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_SET_VALUE) as k:
            for name in ((OLD_RUN_VALUE,) if enabled else (RUN_VALUE, OLD_RUN_VALUE)):
                try:
                    winreg.DeleteValue(k, name)
                except FileNotFoundError:
                    pass
    except FileNotFoundError:
        pass
    except OSError as exc:
        log(f"Could not change 'Start with Windows': {exc}")


# --------------------------------------------------------------------------- launchers
def running_process_names() -> set[str]:
    """Lower-case names of every running process."""
    if psutil is not None:
        try:
            return {(p.info["name"] or "").lower() for p in psutil.process_iter(["name"])}
        except Exception:
            pass
    if IS_WINDOWS:
        try:
            out = _run_hidden(["tasklist", "/FO", "CSV", "/NH"], timeout=20).stdout
            return {line.split('","')[0].strip('"').lower() for line in out.splitlines() if line.strip()}
        except (OSError, subprocess.SubprocessError):
            pass
    return set()


class Launcher:
    """One game launcher as configured for a game: how to find it, start it and see if it runs."""

    def __init__(self, g: dict[str, Any]) -> None:
        self.type = str(g.get("launcher") or "steam")
        self.spec = LAUNCHER_TYPES.get(self.type, LAUNCHER_TYPES["custom"])
        self.name = str(g.get("launcher_name") or self.spec["name"])
        self.path = str(g.get("launcher_path") or "").strip()
        try:
            self.extra = shlex.split(str(g.get("launcher_args") or ""), posix=False)
        except ValueError:
            self.extra = []

    @property
    def precise(self) -> bool:
        return bool(self.spec["precise"])

    @property
    def ident(self) -> str:
        return f"{self.type}|{self.path.lower()}"

    def steam_dir(self) -> Optional[Path]:
        return find_steam_path({"steam_path": self.path}) if self.type == "steam" else None

    def exe(self) -> Optional[str]:
        if self.type == "steam":
            d = self.steam_dir()
            return str(d / "steam.exe") if d else None
        candidates = [self.path] if self.path else list(self.spec["exes"])
        for c in candidates:
            c = os.path.expandvars(c)
            if c.lower().startswith("shell:") or Path(c).exists():
                return c
        return None

    def procs(self) -> list[str]:
        if self.spec["procs"]:
            return list(self.spec["procs"])
        return [Path(self.path).name] if self.path else []

    def running(self, names: set[str]) -> bool:
        procs = self.procs()
        return bool(procs) and procs[0].lower() in names

    def start(self) -> None:
        exe = self.exe()
        if not exe:
            raise OSError(f"{self.name} was not found - set its location under Launchers")
        if exe.lower().startswith("shell:"):
            os.startfile(exe)  # type: ignore[attr-defined]
            return
        flags = (DETACHED_PROCESS | 0x00000200) if IS_WINDOWS else 0
        subprocess.Popen([exe] + list(self.spec["args"]) + self.extra, creationflags=flags,
                         close_fds=True, cwd=str(Path(exe).parent))


class ActivityMonitor:
    """Measures how busy a launcher is (disk + network I/O of its processes) so that launchers
    that cannot be queried can still be watched until their download has finished."""

    def __init__(self) -> None:
        self.prev: dict[str, tuple[float, int, int]] = {}

    def sample(self, key: str, procs: list[str]) -> Optional[tuple[float, float, bool]]:
        """(launcher_io_bytes_per_s, system_rx_bytes_per_s, io_readable) or None without psutil."""
        if psutil is None:
            return None
        names = {p.lower() for p in procs}
        io, readable = 0, False
        try:
            for proc in psutil.process_iter(["name"]):
                if (proc.info["name"] or "").lower() not in names:
                    continue
                try:
                    c = proc.io_counters()
                    io += c.read_bytes + c.write_bytes
                    readable = True
                except Exception:
                    continue
            rx = psutil.net_io_counters().bytes_recv
        except Exception:
            return None
        now = time.time()
        prev = self.prev.get(key)
        self.prev[key] = (now, io, rx)
        if prev is None or now - prev[0] < 1.0:
            return 0.0, 0.0, readable
        dt = now - prev[0]
        return max(0.0, (io - prev[1]) / dt), max(0.0, (rx - prev[2]) / dt), readable


def list_launcher_games(ltype: str) -> list[str]:
    """Titles of installed games, for launchers where that can be read reliably (Epic, GOG)."""
    names: list[str] = []
    try:
        if ltype == "epic":
            base = Path(os.path.expandvars(r"%ProgramData%\Epic\EpicGamesLauncher\Data\Manifests"))
            for f in sorted(base.glob("*.item")) if base.exists() else []:
                try:
                    data = json.loads(f.read_text(encoding="utf-8", errors="replace"))
                except (OSError, ValueError):
                    continue
                title = str(data.get("DisplayName") or "").strip()
                if title and title not in names:
                    names.append(title)
        elif ltype == "gog" and winreg is not None:
            with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\GOG.com\Games") as root:
                i = 0
                while True:
                    try:
                        sub = winreg.EnumKey(root, i)
                    except OSError:
                        break
                    i += 1
                    try:
                        with winreg.OpenKey(root, sub) as k:
                            title = str(winreg.QueryValueEx(k, "gameName")[0]).strip()
                    except OSError:
                        continue
                    if title and title not in names:
                        names.append(title)
    except Exception:
        pass
    return sorted(names, key=str.lower)


# --------------------------------------------------------------------------- web helpers
def http_get(url: str, timeout: int = 25, max_bytes: Optional[int] = None) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "*/*"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        if max_bytes is None:
            return resp.read()
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = resp.read(65536)
            if not chunk:
                break
            total += len(chunk)
            if total > max_bytes:
                raise ValueError("file too large")
            chunks.append(chunk)
        return b"".join(chunks)


_LINE_TAGS = re.compile(r"\[/?(?:\*|(?:p|list|olist|li)\b[^\]]*)\]")
_LOWER_IS_BETTER = re.compile(r"cooldown|\bcost\b|recovery|wind-?up|charge time|cast(?:ing)? time|delay|spread|recoil|damage taken|damage received|threshold|fall-?off|interval|self-damage")
_HIGHER_IS_BETTER = re.compile(r"damage|health|heal|speed|duration|range|radius|shield|armor|bonus|boost|charge|ammo|capacity|size|energy|lifesteal|width|distance")


def classify_change(point: str) -> str:
    """Reads a patch-note line the way the notes are worded: 'fix', 'buff', 'nerf', or '' when it can't be sure.
    'Reduce health' is a nerf but 'Reduce cooldown' is a buff, so it looks at what changes as well as which way."""
    low = point.lower()
    if re.search(r"\b(fixed|resolved|addressed|to fix)\b", low):
        return "fix"
    if re.match(r"(?:\d+\.\s*)?buff\b", low):
        return "buff"
    if re.match(r"(?:\d+\.\s*)?nerf\b", low):
        return "nerf"
    if re.search(r"\benem|\bopponent", low):      # making things worse for enemies reads backwards, so don't guess
        return ""
    verdicts = set()
    for sentence in re.split(r"(?<=[.;])\s+|\s+and\s+(?=(?:slightly\s+)?(?:increase|raise|enhance|boost|extend|reduce|decrease|lower|shorten)\b)", low):
        sentence = sentence.replace("cooldown reduction", "boost")
        numbers = re.search(r"from\s+([\d.]*\d)\D*?\bto\s+([\d.]*\d)", sentence)
        verb = re.match(r"(?:[^:]{0,40}:\s*|when [^,]+,\s*|in [^,]+,\s*)?(?:slightly\s+)?(increase|raise|enhance|boost|extend|reduce|decrease|lower|shorten)\b", sentence)
        if numbers and float(numbers[1]) != float(numbers[2]):
            up = float(numbers[2]) > float(numbers[1])
        elif verb:
            up = verb[1] in ("increase", "raise", "enhance", "boost", "extend")
        else:
            continue
        if _LOWER_IS_BETTER.search(sentence):
            verdicts.add("nerf" if up else "buff")
        elif _HIGHER_IS_BETTER.search(sentence):
            verdicts.add("buff" if up else "nerf")
    return verdicts.pop() if len(verdicts) == 1 else ""


def _plain_text(text: str) -> str:
    text = re.sub(r"\{STEAM_CLAN_IMAGE\}\S*|https?://\S+|\[[^\]]*\]|<[^>]+>", " ", text)
    return re.sub(r"\s+", " ", html.unescape(text)).strip()


def digest_post(contents: str, max_sections: int = 4, per_section: int = 3, line_chars: int = 90) -> list[dict[str, Any]]:
    """Boils a post down to its own headings and first few points, each kept short. The full post stays a link away."""
    marked = re.sub(r"\[h[1-3]\](.*?)\[/h[1-3]\]", lambda m: "\n#" + _plain_text(m[1]) + "\n", contents, flags=re.S)
    marked = _LINE_TAGS.sub("\n", marked)
    sections = [{"heading": "", "items": []}]
    for line in marked.splitlines():
        if line.startswith("#"):
            sections.append({"heading": line[1:].strip()[:70], "items": []})
        else:
            point = _plain_text(line).lstrip("-•* ")
            if point:
                sections[-1]["items"].append(point if len(point) <= line_chars else point[:line_chars].rsplit(" ", 1)[0] + "…")
    named = [s for s in sections if s["heading"] and s["items"]]
    chosen = named or [{"heading": "", "items": sections[0]["items"]}]     # no headings: just its first points
    return [{"heading": s["heading"], "items": s["items"][:per_section], "more": max(0, len(s["items"]) - per_section)}
            for s in chosen[:max_sections] if s["items"]]


def heroes_in_post(contents: str, roster: list[str], max_heroes: int = 30, per_hero: int = 3, line_chars: int = 120) -> list[dict[str, Any]]:
    """Each character's changes in a post. Balance posts list them under a heading with the character's name, and
    patch notes name the character in the line ("Gorr's Glitch: Fixed a bug where..."). Flavour text is left out."""
    if not roster:
        return []
    other_names = {"The Punisher": "Punisher", "Gorr the God Butcher": "Gorr"}
    patterns = {n: re.compile(r"\b(?:" + re.escape(n) + (("|" + other_names[n]) if n in other_names else "") + r")\b") for n in roster}
    headings = {n.lower(): n for n in roster} | {a.lower(): n for n, a in other_names.items()}
    marked = re.sub(r"\[h[1-3]\](.*?)\[/h[1-3]\]", lambda m: "\n#" + _plain_text(m[1]) + "\n", contents, flags=re.S)
    found: dict[str, list[dict[str, str]]] = {}
    current = team = ""
    for line in _LINE_TAGS.sub("\n", marked).splitlines():
        is_heading = line.startswith("#")
        point = _plain_text(line[1:] if is_heading else line).lstrip("-•* ")
        if not point:
            continue
        if point.lower() in headings:
            current, team = headings[point.lower()], ""
            continue
        title = _TEAM_UP_TITLE.match(point)      # "Team Name (Hero - Partner/Partner)" starts a team-up's changes
        if title and title[2].lower() in headings:
            current, team = headings[title[2].lower()], title[1]
            continue
        if is_heading:
            current = team = ""
            continue
        kind = classify_change(point)
        owner = current
        if not owner:
            hits = [(m.start(), n) for n, p in patterns.items() if (m := p.search(point))]
            owner = min(hits)[1] if hits else ""
            # a line it can't read only counts if it's about that character: "Gorr's Setting: Added..."
            if not kind and not (owner and hits and min(hits)[0] == 0 and ": " in point):
                continue
        elif not kind:
            continue        # flavour text under a character's heading
        if not owner:
            continue
        text = point.split(": ", 1)[1] if kind == "fix" and ": " in point else point
        partner = _TEAM_UP_WITH.search(point)
        if not kind and _STORE_ITEM.search(point):
            kind = "store"      # a cosmetic, not a change to how the character plays
        found.setdefault(owner, []).append({"text": text if len(text) <= line_chars else text[:line_chars].rsplit(" ", 1)[0] + "…", "kind": kind,
                                            "team": partner[1].strip() if partner else team})
    heroes = []
    for name, changes in list(found.items())[:max_heroes]:
        kinds = {c["kind"] for c in changes}
        verdict = "mixed" if {"buff", "nerf"} <= kinds else "buff" if "buff" in kinds else "nerf" if "nerf" in kinds else ""
        changes.sort(key=lambda c: not c["kind"])       # the ones it could read come first
        heroes.append({"name": name, "verdict": verdict, "fixed": "fix" in kinds, "changes": changes[:per_hero], "more": max(0, len(changes) - per_hero)})
    return heroes


def _without_heroes(sections: list[dict[str, Any]], roster: list[str]) -> list[dict[str, Any]]:
    """The sections left once characters have their own cards, so nothing is shown twice."""
    if not roster:
        return sections
    names = [n.replace("The ", "") for n in roster]
    out = []
    for s in sections:
        if s["heading"].upper() in ("VANGUARD", "DUELIST", "STRATEGIST", "HEROES", "ADJUSTMENTS", "BALANCE ADJUSTMENTS") or s["heading"] in roster:
            continue
        items = [i for i in s["items"] if not any(n in i for n in names)]
        if items:
            out.append({**s, "items": items})
    return out


def _patch_posts(appid: int, maxlength: int) -> list[dict[str, Any]]:
    """Steam's public news feed for a game, newest first, with update posts picked out when there are any."""
    params = urllib.parse.urlencode({"appid": appid, "count": 25, "maxlength": maxlength, "format": "json", "feeds": "steam_community_announcements"})
    data = json.loads(http_get(f"https://api.steampowered.com/ISteamNews/GetNewsForApp/v2/?{params}", timeout=20, max_bytes=5_000_000))
    posts = (data.get("appnews") or {}).get("newsitems") or []
    # a game that posts real patch notes gets just those, without its other announcements
    notes = [p for p in posts if "patchnotes" in (p.get("tags") or []) or _PATCH_NOTES.search(str(p.get("title", "")))]
    if notes and notes[0] in posts[:5]:
        return notes
    return [p for p in posts if _PATCH_WORDS.search(str(p.get("title", "")))] or posts


def fetch_latest_patch(appid: int) -> dict[str, str]:
    """Just the newest post's date and title for the pill on the game page. The post bodies aren't downloaded."""
    posts = _patch_posts(appid, 1)
    if not posts:
        return {}
    return {"date": f"{datetime.fromtimestamp(to_int(posts[0].get('date')), SAST):%a %d %b %Y}", "title": str(posts[0].get("title", ""))[:160]}


def fetch_patch_notes(appid: int, limit: int = 10) -> list[dict[str, Any]]:
    """The game's latest update posts, newest first, as short digests with a link."""
    posts = _patch_posts(appid, 0)
    return [{"title": str(p.get("title", ""))[:160], "date": f"{datetime.fromtimestamp(to_int(p.get('date')), SAST):%a %d %b %Y}",
             "sections": _without_heroes(digest_post(str(p.get("contents", ""))), ROSTERS.get(appid, [])), "url": str(p.get("url", "")),
             "heroes": heroes_in_post(str(p.get("contents", "")), ROSTERS.get(appid, []))} for p in posts[:limit]]


def fetch_remote_build(appid: int) -> Optional[dict[str, int]]:
    """Latest public build via the community API api.steamcmd.net (None if unavailable)."""
    try:
        data = json.loads(http_get(f"https://api.steamcmd.net/v1/info/{appid}", timeout=25))
        if data.get("status") != "success":
            return None
        pub = data["data"][str(appid)]["depots"]["branches"]["public"]
        return {"build": int(pub["buildid"]), "updated": to_int(pub.get("timeupdated"), 0)}
    except Exception as exc:  # network, JSON shape, anything
        log(f"Remote build check failed for {appid}: {exc!r}")
        return None


def steam_search(term: str) -> list[dict[str, Any]]:
    url = ("https://store.steampowered.com/api/storesearch/?" +
           urllib.parse.urlencode({"term": term, "l": "english", "cc": "ZA"}))
    data = json.loads(http_get(url, timeout=20))
    out = []
    for item in data.get("items", []):
        if item.get("type") == "app" and item.get("id"):
            out.append({"appid": int(item["id"]), "name": str(item.get("name", ""))})
    return out


def search_games(term: str, steam: Optional[Path]) -> list[dict[str, Any]]:
    installed = list_installed(steam)
    results: list[dict[str, Any]] = []
    seen: set[int] = set()
    error: Optional[Exception] = None
    try:
        for item in steam_search(term):
            seen.add(item["appid"])
            results.append({**item, "installed": item["appid"] in installed})
    except Exception as exc:
        error = exc
    low = term.lower()
    for appid, name in installed.items():
        if low in name.lower() and appid not in seen:
            results.append({"appid": appid, "name": name, "installed": True})
    if not results and error is not None:
        raise error
    return results


# --------------------------------------------------------------------------- self-update
def is_frozen() -> bool:
    return bool(getattr(sys, "frozen", False))


def version_tuple(v: str) -> tuple[int, ...]:
    nums = tuple(int(x) for x in re.findall(r"\d+", str(v)))
    return nums or (0,)


def effective_feed(settings: dict[str, Any]) -> str:
    return str(settings.get("update_feed_url") or "").strip() or DEFAULT_UPDATE_FEED.strip()


def fetch_update_manifest(url: str) -> dict[str, str]:
    """Read update.json: {"version": "1.1", "url": "https://.../Gaus.exe",
    "sha256": "<64 hex chars>", "notes": "what changed"}."""
    if not url:
        raise ValueError("No update feed is set. Paste the update.json link in Settings.")
    if not url.lower().startswith("https://"):
        raise ValueError("The update feed must be an https:// link.")
    data = json.loads(http_get(url, timeout=25, max_bytes=200_000))
    version = str(data["version"]).strip()
    download = str(data["url"]).strip()
    sha = str(data.get("sha256", "")).strip().lower()
    if not download.lower().startswith("https://"):
        raise ValueError("update.json: the download link must be https://")
    if not re.fullmatch(r"[0-9a-f]{64}", sha):
        raise ValueError("update.json: the sha256 checksum is missing or invalid")
    return {"version": version, "url": download, "sha256": sha, "notes": str(data.get("notes", ""))[:600]}


def cleanup_old_update_files() -> None:
    if not is_frozen():
        return
    exe = Path(sys.executable)
    for suffix in (".old", ".new"):
        try:
            p = exe.with_name(exe.name + suffix)
            if p.exists():
                p.unlink()
        except OSError:
            pass


def download_and_swap(manifest: dict[str, str], progress: Any = None) -> None:
    """Download the new .exe next to the running one, verify its SHA-256, then swap the files.
    Windows allows renaming a running .exe, so: running.exe -> running.exe.old, new -> running.exe."""
    exe = Path(sys.executable)
    new = exe.with_name(exe.name + ".new")
    old = exe.with_name(exe.name + ".old")
    req = urllib.request.Request(manifest["url"], headers={"User-Agent": USER_AGENT})
    digest = hashlib.sha256()
    done = 0
    try:
        with urllib.request.urlopen(req, timeout=60) as resp, open(new, "wb") as fh:
            total = to_int(resp.headers.get("Content-Length"), 0)
            while True:
                chunk = resp.read(262144)
                if not chunk:
                    break
                fh.write(chunk)
                digest.update(chunk)
                done += len(chunk)
                if done > 600_000_000:
                    raise ValueError("The download is unexpectedly large - update cancelled.")
                if progress and total:
                    progress(min(99, int(done * 100 / total)))
        if digest.hexdigest() != manifest["sha256"]:
            raise ValueError("The downloaded file did not match its checksum - update cancelled.")
        if old.exists():
            old.unlink()
        os.replace(exe, old)
        try:
            os.replace(new, exe)
        except OSError:
            os.replace(old, exe)
            raise
        if progress:
            progress(100)
    except Exception:
        try:
            if new.exists():
                new.unlink()
        except OSError:
            pass
        raise


def relaunch_self(show_window: bool) -> None:
    env = dict(os.environ)
    env["PYINSTALLER_RESET_ENVIRONMENT"] = "1"   # lets a one-file build start a fresh, independent copy
    flags = (DETACHED_PROCESS | 0x00000200) if IS_WINDOWS else 0
    args = [sys.executable, "--after-update"] + (["--show"] if show_window else [])
    subprocess.Popen(args, env=env, creationflags=flags, close_fds=True)


# --------------------------------------------------------------------------- photos
def strip_html(text: str) -> str:
    text = re.sub(r"<[^>]+>", "", text or "")
    text = html.unescape(text)
    text = re.sub(r"\s+", " ", text).strip()
    return text[:90]


def format_license(lic: str, version: str) -> str:
    lic = (lic or "").lower()
    if lic == "cc0":
        return "CC0 1.0"
    if lic == "pdm":
        return "Public Domain Mark"
    label = lic.upper() if lic else "CC"
    return f"CC {label} {version}".strip()


def parse_commons(data: dict[str, Any]) -> list[dict[str, Any]]:
    pages = (data.get("query") or {}).get("pages") or {}
    out: list[dict[str, Any]] = []
    for page in sorted(pages.values(), key=lambda p: p.get("index", 0)):
        infos = page.get("imageinfo") or []
        if not infos:
            continue
        ii = infos[0]
        if ii.get("mime") not in ("image/jpeg", "image/png"):
            continue
        w, h = to_int(ii.get("width")), to_int(ii.get("height"))
        if w < 1200 or h < 600 or w / max(h, 1) < 1.2:
            continue
        title = str(page.get("title", "")).replace("File:", "", 1)
        if any(b in title.lower() for b in BAD_TITLE_WORDS):
            continue
        meta = ii.get("extmetadata") or {}

        def mv(key: str) -> str:
            return strip_html((meta.get(key) or {}).get("value", ""))

        out.append({
            "download": ii.get("thumburl") or ii.get("url"),
            "title": re.sub(r"\.(jpe?g|png)$", "", title, flags=re.I).replace("_", " ")[:80],
            "author": mv("Artist") or "Unknown author",
            "license": mv("LicenseShortName") or "Free license",
            "license_url": mv("LicenseUrl"),
            "page": ii.get("descriptionurl") or "",
            "source": "Wikimedia Commons",
        })
    return [c for c in out if c["download"]]


def commons_search(query: str, limit: int = 20) -> list[dict[str, Any]]:
    params = {
        "action": "query", "format": "json", "generator": "search", "gsrnamespace": "6",
        "gsrsearch": f"{query} filetype:bitmap", "gsrlimit": str(limit),
        "prop": "imageinfo", "iiprop": "url|size|mime|extmetadata", "iiurlwidth": "1920",
        "iiextmetadatafilter": "Artist|LicenseShortName|LicenseUrl",
    }
    url = "https://commons.wikimedia.org/w/api.php?" + urllib.parse.urlencode(params)
    return parse_commons(json.loads(http_get(url, timeout=30)))


def parse_openverse(data: dict[str, Any]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for r in data.get("results") or []:
        url = r.get("url")
        if not url:
            continue
        w, h = to_int(r.get("width")), to_int(r.get("height"))
        if w and h and (w < 1200 or h < 600 or w / h < 1.2):
            continue
        lic = str(r.get("license") or "").lower()
        parts = lic.split("-")
        if "nc" in parts or "nd" in parts:
            continue
        title = str(r.get("title") or "Untitled")
        if any(b in title.lower() for b in BAD_TITLE_WORDS):
            continue
        out.append({
            "download": url, "title": title[:80],
            "author": str(r.get("creator") or "Unknown author")[:80],
            "license": format_license(lic, str(r.get("license_version") or "")),
            "license_url": str(r.get("license_url") or ""),
            "page": str(r.get("foreign_landing_url") or url),
            "source": "Openverse" + (f" / {r.get('source') or r.get('provider')}"
                                     if (r.get("source") or r.get("provider")) else ""),
        })
    return out


def openverse_search(query: str, limit: int = 20) -> list[dict[str, Any]]:
    params = {"q": query, "page_size": str(limit), "license_type": "commercial,modification",
              "aspect_ratio": "wide", "mature": "false"}
    url = "https://api.openverse.org/v1/images/?" + urllib.parse.urlencode(params)
    return parse_openverse(json.loads(http_get(url, timeout=30)))


def photo_dir(key: Any) -> Path:
    return PHOTO_DIR / str(key)


def load_index(key: Any) -> list[dict[str, Any]]:
    data = read_json(photo_dir(key) / "index.json", [])
    return data if isinstance(data, list) else []


def photo_entries(key: Any) -> list[dict[str, Any]]:
    out = []
    for e in load_index(key):
        p = photo_dir(key) / str(e.get("file", ""))
        if p.exists():
            e2 = dict(e)
            e2["path"] = str(p)
            out.append(e2)
    return out


def favourite_of(appid: int) -> str:
    data = read_json(FAVOURITES_PATH, {})
    return str(data.get(str(appid), "")) if isinstance(data, dict) else ""


def favourite_key(appid: int, name: str) -> str:
    """Each character keeps its own pictures, so switching favourites and back loses nothing."""
    return f"fav_{appid}_" + re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-")


def favourite_entries(appid: int) -> list[dict[str, Any]]:
    name = favourite_of(appid)
    return photo_entries(favourite_key(appid, name)) if name else []


def get_slides(appid: int) -> list[dict[str, Any]]:
    favourite = favourite_entries(appid)
    if favourite:
        random.shuffle(favourite)
        return favourite
    entries = photo_entries(appid)
    if len(entries) < MIN_SLIDES:
        entries += photo_entries(GENERIC_KEY)
    random.shuffle(entries)
    return entries


def download_image(url: str, dest_dir: Path) -> Optional[str]:
    from PIL import Image  # Pillow
    data = http_get(url, timeout=45, max_bytes=14_000_000)
    try:
        img = Image.open(io.BytesIO(data))
        img.load()
    except Exception:
        return None
    if img.width < 1000 or img.height < 500:
        return None
    if img.width > 2200:
        img = img.resize((1920, max(1, round(img.height * 1920 / img.width))), Image.LANCZOS)
    img = img.convert("RGB")
    name = hashlib.sha1(url.encode("utf-8")).hexdigest()[:14] + ".jpg"
    dest_dir.mkdir(parents=True, exist_ok=True)
    img.save(dest_dir / name, "JPEG", quality=88)
    return name


def steam_art(appid: int) -> list[dict[str, Any]]:
    """The game's own artwork from its Steam store page: hero and background art, then the screenshots."""
    raw = http_get(f"https://store.steampowered.com/api/appdetails?appids={appid}&l=english", timeout=20)
    node = (json.loads(raw.decode("utf-8", "replace")) or {}).get(str(appid)) or {}
    data = node.get("data") or {}
    devs = ", ".join(str(x) for x in (data.get("developers") or [])) or "the developer"
    out: list[dict[str, Any]] = []

    def add(url: Any, title: str) -> None:
        if url:
            out.append({"page": str(url).split("?")[0], "download": str(url), "title": title, "author": devs,
                        "license": "Official game art", "license_url": "", "source": STEAM_SRC})

    add(f"https://cdn.akamai.steamstatic.com/steam/apps/{appid}/library_hero.jpg", "Official hero art")
    add(data.get("background_raw"), "Official background art")
    for i, shot in enumerate(data.get("screenshots") or []):
        add(shot.get("path_full"), f"Official screenshot {i + 1}")
    return out


def import_image(src: Path, dest_dir: Path) -> Optional[str]:
    """Copy one of the person's own pictures into a game's photo folder (as a JPEG)."""
    from PIL import Image  # Pillow
    try:
        img = Image.open(src)
        img.load()
    except Exception:
        return None
    if img.width < 640 or img.height < 360:
        return None
    if img.width > 2200:
        img = img.resize((1920, max(1, round(img.height * 1920 / img.width))), Image.LANCZOS)
    img = img.convert("RGB")
    name = "own_" + hashlib.sha1(f"{src}|{src.stat().st_mtime_ns}".encode("utf-8")).hexdigest()[:12] + ".jpg"
    dest_dir.mkdir(parents=True, exist_ok=True)
    img.save(dest_dir / name, "JPEG", quality=90)
    return name


def fetch_pool(key: Any, queries: list[str], target: int, label: str, reset: bool = False,
               steam_appid: Optional[int] = None) -> int:
    """Download photos for a game into photos/<key>/. Steam games get their official artwork first; other
    photos are only a fallback. Pictures the person added themselves are never deleted. Returns how many are stored."""
    d = photo_dir(key)
    if reset and d.exists():
        keep = [e for e in load_index(key) if e.get("source") == OWN_SRC and (d / str(e.get("file", ""))).exists()]
        keep_files = {str(e["file"]) for e in keep} | {"index.json"}
        for f in d.iterdir():
            if f.name not in keep_files:
                try:
                    f.unlink()
                except OSError:
                    pass
        write_json(d / "index.json", keep)
    d.mkdir(parents=True, exist_ok=True)
    index = [e for e in load_index(key) if (d / str(e.get("file", ""))).exists()]
    have = {e.get("page") for e in index}
    if steam_appid:
        steam_n = sum(1 for e in index if e.get("source") == STEAM_SRC)
        if steam_n < target:
            try:
                art = steam_art(steam_appid)
            except Exception as exc:
                log(f"Steam artwork lookup for {label} failed: {exc!r}")
                art = []
            for c in art:
                if steam_n >= target:
                    break
                if c["page"] in have:
                    continue
                try:
                    name = download_image(c["download"], d)
                except Exception as exc:
                    log(f"Steam artwork download failed: {exc!r}")
                    continue
                if not name:
                    continue
                have.add(c["page"])
                steam_n += 1
                index.append({"file": name, "title": c["title"], "author": c["author"], "license": c["license"],
                              "license_url": c["license_url"], "page": c["page"], "source": STEAM_SRC})
                write_json(d / "index.json", index)
        if steam_n >= MIN_GAME_PHOTOS:      # real game art found: drop any stock photos picked up earlier
            for e in index:
                if e.get("source") not in (STEAM_SRC, OWN_SRC):
                    try:
                        (d / str(e["file"])).unlink()
                    except OSError:
                        pass
            index = [e for e in index if e.get("source") in (STEAM_SRC, OWN_SRC)]
            write_json(d / "index.json", index)
            log(f"Photos for {label}: {len(index)} stored (official artwork)")
            return len(index)
    if len(index) >= target:
        return len(index)

    def gather(search) -> list[dict[str, Any]]:
        lists = []
        for q in queries:
            try:
                lists.append(search(q))
            except Exception as exc:
                log(f"Photo search '{q}' ({search.__name__}) failed: {exc!r}")
        merged = [c for c in itertools.chain.from_iterable(itertools.zip_longest(*lists)) if c]
        return merged

    candidates = gather(commons_search)
    if len(candidates) < target * 1.5:
        candidates += gather(openverse_search)
    seen_dl: set[str] = set()
    failures = 0
    attempts = 0
    for c in candidates:
        if len(index) >= target or attempts >= target * 4 or failures >= 6:
            break
        if c["page"] in have or c["download"] in seen_dl:
            continue
        seen_dl.add(c["download"])
        attempts += 1
        try:
            name = download_image(c["download"], d)
        except Exception as exc:
            failures += 1
            log(f"Photo download failed ({c['source']}): {exc!r}")
            continue
        if not name:
            continue
        failures = 0
        have.add(c["page"])
        index.append({"file": name, "title": c["title"], "author": c["author"],
                      "license": c["license"], "license_url": c["license_url"],
                      "page": c["page"], "source": c["source"]})
        write_json(d / "index.json", index)
    write_json(d / "index.json", index)
    log(f"Photos for {label}: {len(index)} stored")
    return len(index)


class PhotoManager:
    """Single background worker that keeps each game's photo folder topped up."""

    def __init__(self, cfg: "Config") -> None:
        self.cfg = cfg
        self.q: "queue.Queue[tuple[int, bool]]" = queue.Queue()
        self.pending: set[int] = set()
        self.lock = threading.Lock()
        self.thread: Optional[threading.Thread] = None

    def request(self, appid: int, force: bool = False) -> None:
        with self.lock:
            if appid in self.pending:
                return
            self.pending.add(appid)
            self.q.put((appid, force))
            if self.thread is None or not self.thread.is_alive():
                self.thread = threading.Thread(target=self._run, daemon=True, name="photos")
                self.thread.start()

    def count(self, appid: int) -> int:
        return len(photo_entries(appid))

    def _run(self) -> None:
        while True:
            try:
                appid, force = self.q.get(timeout=5)
            except queue.Empty:
                with self.lock:
                    if self.q.empty():
                        self.thread = None
                        return
                continue
            try:
                settings = self.cfg.settings
                game = self.cfg.get_game(appid)
                if game is not None:
                    target = int(settings["photos_per_game"])
                    queries = game.get("photo_keywords") or [game["name"]]
                    log(f"Fetching open-licensed photos for {game['name']}...")
                    n = fetch_pool(appid, queries, target, game["name"], reset=force,
                                   steam_appid=appid if game.get("launcher") == "steam" else None)
                    if n < MIN_GAME_PHOTOS and len(photo_entries(GENERIC_KEY)) < GENERIC_TARGET:
                        log(f"Only {n} game-specific photos found - adding generic city/landscape photos")
                        fetch_pool(GENERIC_KEY, GENERIC_QUERIES, GENERIC_TARGET, "generic pool")
                    emit("photos_changed", appid)
            except Exception:
                log("Photo worker error:\n" + traceback.format_exc())
            finally:
                with self.lock:
                    self.pending.discard(appid)


# --------------------------------------------------------------------------- config
def coerce_setting(key: str, value: Any) -> Any:
    default = DEFAULT_SETTINGS[key]
    try:
        if isinstance(default, bool):
            return bool(value)
        if isinstance(default, int):
            return int(value)
        return str(value)
    except (ValueError, TypeError):
        return default


class Config:
    """Settings + accounts. Account -> launchers -> games. No passwords anywhere: an account is
    just a named profile. The engine sees one flat list of games from all enabled accounts."""

    def __init__(self) -> None:
        self.lock = threading.RLock()
        self.settings: dict[str, Any] = dict(DEFAULT_SETTINGS)
        self.accounts: list[dict[str, Any]] = []
        self.active: str = ""
        self.first_run = False

    @classmethod
    def load(cls) -> "Config":
        cfg = cls()
        raw = read_json(CONFIG_PATH, {})
        raw = raw if isinstance(raw, dict) else {}
        for k, v in (raw.get("settings") or {}).items():
            if k in DEFAULT_SETTINGS:
                cfg.settings[k] = coerce_setting(k, v)
        migrated = False
        if isinstance(raw.get("accounts"), list):
            for a in raw["accounts"]:
                na = normalize_account(a)
                if na and all(na["id"] != x["id"] for x in cfg.accounts):
                    cfg.accounts.append(na)
        elif isinstance(raw.get("games"), list):          # config from the single-launcher version
            steam_path = str((raw.get("settings") or {}).get("steam_path") or "")
            acc = normalize_account({"name": default_account_name(), "launchers": [
                {"type": "steam", "path": steam_path, "games": raw["games"]}]})
            if acc:
                cfg.accounts.append(acc)
                migrated = True
        if not cfg.accounts:
            cfg.first_run = not CONFIG_PATH.exists()
            acc = normalize_account({"name": default_account_name(), "launchers": [
                {"type": "steam", "games": [new_game(MARVEL_RIVALS_APPID, "Marvel Rivals")]}]})
            assert acc is not None
            cfg.accounts.append(acc)
            migrated = True
        wanted = str(raw.get("active_account") or "")
        cfg.active = wanted if any(a["id"] == wanted for a in cfg.accounts) else cfg.accounts[0]["id"]
        if migrated:
            cfg.save()
        return cfg

    def save(self) -> None:
        with self.lock:
            write_json(CONFIG_PATH, {"version": 2, "settings": self.settings, "active_account": self.active,
                                     "accounts": self.accounts})

    # ---- read side
    def flat_games(self) -> list[dict[str, Any]]:
        """Every game of every enabled account/launcher, once. The same game in two accounts is
        updated once, using the combined schedules."""
        out: dict[int, dict[str, Any]] = {}
        with self.lock:
            for acc in self.accounts:
                if not acc["enabled"]:
                    continue
                for lc in acc["launchers"]:
                    if not lc["enabled"]:
                        continue
                    for g in lc["games"]:
                        e = copy.deepcopy(g)
                        e.update({"launcher": lc["type"], "launcher_name": lc["name"], "launcher_path": lc["path"],
                                  "launcher_args": lc["args"], "accounts": [acc["name"]]})
                        ex = out.get(g["appid"])
                        if ex is None:
                            out[g["appid"]] = e
                            continue
                        ex["enabled"] = ex["enabled"] or e["enabled"]
                        ex["weekly"] += [r for r in e["weekly"] if r not in ex["weekly"]]
                        ex["dates"] = sorted(set(ex["dates"]) | set(e["dates"]))
                        ex["accounts"].append(acc["name"])
        return list(out.values())

    def snapshot(self) -> tuple[dict[str, Any], list[dict[str, Any]]]:
        with self.lock:
            return copy.deepcopy(self.settings), self.flat_games()

    def get_game(self, appid: int) -> Optional[dict[str, Any]]:
        with self.lock:
            for a in self.accounts:
                for l in a["launchers"]:
                    for g in l["games"]:
                        if g["appid"] == appid:
                            e = copy.deepcopy(g)
                            e.update({"launcher": l["type"], "launcher_name": l["name"], "launcher_path": l["path"],
                                      "launcher_args": l["args"], "accounts": [a["name"]]})
                            return e
        return None

    def tree(self) -> list[dict[str, Any]]:
        with self.lock:
            return copy.deepcopy(self.accounts)

    def account(self, aid: str) -> Optional[dict[str, Any]]:
        with self.lock:
            return next((copy.deepcopy(a) for a in self.accounts if a["id"] == aid), None)

    def _acc(self, aid: str) -> Optional[dict[str, Any]]:
        return next((a for a in self.accounts if a["id"] == aid), None)

    def _lc(self, aid: str, lid: str) -> Optional[dict[str, Any]]:
        acc = self._acc(aid)
        return next((l for l in acc["launchers"] if l["id"] == lid), None) if acc else None

    def used_appids(self) -> set[int]:
        with self.lock:
            return {g["appid"] for a in self.accounts for l in a["launchers"] for g in l["games"]}

    # ---- write side (each saves)
    def set_active(self, aid: str) -> None:
        with self.lock:
            if self._acc(aid):
                self.active = aid
        self.save()

    def add_account(self, name: str) -> str:
        with self.lock:
            acc = normalize_account({"name": name, "launchers": []})
            assert acc is not None
            self.accounts.append(acc)
            self.active = acc["id"]
        self.save()
        return acc["id"]

    def edit_account(self, aid: str, name: str, enabled: bool) -> None:
        with self.lock:
            a = self._acc(aid)
            if a:
                a["name"] = name.strip() or a["name"]
                a["enabled"] = bool(enabled)
        self.save()

    def remove_account(self, aid: str) -> bool:
        with self.lock:
            if len(self.accounts) <= 1:
                return False
            self.accounts = [a for a in self.accounts if a["id"] != aid]
            if self.active == aid:
                self.active = self.accounts[0]["id"]
        self.save()
        return True

    def add_launcher(self, aid: str, ltype: str, name: str = "", path: str = "", args: str = "") -> Optional[str]:
        with self.lock:
            a = self._acc(aid)
            lc = normalize_launcher({"type": ltype, "name": name, "path": path, "args": args, "games": []})
            if not a or not lc:
                return None
            a["launchers"].append(lc)
        self.save()
        return lc["id"]

    def update_launcher(self, aid: str, lid: str, **fields: Any) -> None:
        with self.lock:
            lc = self._lc(aid, lid)
            if lc:
                for k in ("name", "path", "args", "enabled"):
                    if k in fields:
                        lc[k] = fields[k]
        self.save()

    def remove_launcher(self, aid: str, lid: str) -> list[int]:
        """Removes the launcher; returns appids that no account uses any more (their photos can go)."""
        with self.lock:
            a = self._acc(aid)
            gone: set[int] = set()
            if a:
                gone = {g["appid"] for l in a["launchers"] if l["id"] == lid for g in l["games"]}
                a["launchers"] = [l for l in a["launchers"] if l["id"] != lid]
            left = self.used_appids()
        self.save()
        return sorted(gone - left)

    def add_game(self, aid: str, lid: str, appid: int, name: str) -> bool:
        with self.lock:
            lc = self._lc(aid, lid)
            if not lc or any(g["appid"] == appid for g in lc["games"]):
                return False
            lc["games"].append(new_game(appid, name))
        self.save()
        return True

    def update_game(self, aid: str, lid: str, game: dict[str, Any]) -> None:
        with self.lock:
            lc = self._lc(aid, lid)
            if lc:
                for i, g in enumerate(lc["games"]):
                    if g["appid"] == game["appid"]:
                        lc["games"][i] = normalize_game(game) or g
        self.save()

    def remove_game(self, aid: str, lid: str, appid: int) -> bool:
        """Returns True when no other account/launcher still uses the game (so photos can be deleted)."""
        with self.lock:
            lc = self._lc(aid, lid)
            if lc:
                lc["games"] = [g for g in lc["games"] if g["appid"] != appid]
            still = appid in self.used_appids()
        self.save()
        return not still


# --------------------------------------------------------------------------- engine
class Session:
    def __init__(self, game: dict[str, Any], key: str, manual: bool,
                 window_end: Optional[datetime], tracked: bool = False) -> None:
        self.game = game
        self.appid = int(game["appid"])
        self.name = str(game["name"])
        self.key = key
        self.manual = manual
        self.tracked = tracked           # only following a download: never opens Steam or the loading screen
        self.live_seen = time.time()
        self.window_end = window_end
        self.phase = "watching"          # watching -> launching -> downloading -> done
        self.result: Optional[str] = None  # updated | up-to-date | failed | skipped
        self.msg = ""
        self.last_poll = 0.0
        self.remote: Optional[dict[str, int]] = None
        self.blind = False
        self.initial_build = 0
        self.launch_attempts = 0
        self.launch_time = 0.0
        self.dl_started = 0.0
        self.last_change = 0.0
        self.sig: Any = None
        self.saw_activity = False
        self.progress = 0.0
        self.bytes_done = 0
        self.bytes_total = 0
        self.speed = 0.0
        self.prev_t = 0.0
        self.prev_dl = 0
        self.hinted_running = False
        self.last_stall_log = 0.0
        self.net_since = 0.0
        self.lc = Launcher(game)
        self.act_since = 0.0
        self.last_busy = 0.0
        self.io_total = 0.0
        self.quiet_since = 0.0


class Engine(threading.Thread):
    TICK = 4.0
    INFO_REFRESH = 1800.0

    def __init__(self, cfg: Config) -> None:
        super().__init__(daemon=True, name="engine")
        self.cfg = cfg
        self.stop_evt = threading.Event()
        self.lock = threading.Lock()
        self.sessions: dict[int, Session] = {}
        self.manual_requests: list[Optional[int]] = []
        self.track_requests: list[tuple[int, bool]] = []
        self.track_off: set[int] = set()     # the user pressed Stop tracking: leave this download alone
        self.live: dict[int, dict[str, Any]] = {}
        self.tick_cpu_ms = 0.0
        st = read_json(STATE_PATH, {})
        self.state: dict[str, Any] = st if isinstance(st, dict) else {}
        self.state.setdefault("handled", {})
        self.info: dict[int, dict[str, Any]] = {}
        self.last_info_refresh = 0.0
        self.info_busy = False
        self.last_result: dict[int, str] = {}
        self.run_results: list[tuple[str, str, bool]] = []
        self.shutdown: Optional[dict[str, Any]] = None
        self.countdown_answer: Optional[bool] = None
        self._steam_up_cache: Optional[bool] = None
        self.wake = WakeTimer("schedule")
        self.test_timer = WakeTimer("test")
        self._wake_target: Optional[float] = None
        self._awake_on = False
        self._power_hold_until = 0.0     # keep the PC awake until a shutdown/hibernate has really happened
        self._last_tick = time.time()
        self._net_t = 0.0
        self._net_val = True
        self.monitor = ActivityMonitor()
        self._names_cache: Optional[set[str]] = None
        self._act_cache: dict[str, Any] = {}

    # ---- launcher helpers
    def _steam_dir(self, games: list[dict[str, Any]]) -> Optional[Path]:
        path = next((g["launcher_path"] for g in games if g["launcher"] == "steam"), "")
        return find_steam_path({"steam_path": path})

    def _running(self, lc: Launcher) -> bool:
        if lc.type == "steam":
            return self._steam_up()
        if self._names_cache is None:
            self._names_cache = running_process_names()
        return lc.running(self._names_cache)

    # ---- public (called from the UI thread)
    def request_check(self, appid: Optional[int]) -> None:
        with self.lock:
            self.manual_requests.append(appid)

    def set_tracking(self, appid: int, on: bool) -> None:
        with self.lock:
            self.track_requests.append((appid, on))

    def save_resume(self) -> None:
        """Remember what we're following, so the restarted app carries on: a scheduled update still powers down."""
        self.state["resume"] = [{"at": time.time(), "appid": s.appid, "key": s.key, "manual": s.manual, "tracked": s.tracked,
                                 "end": s.window_end.isoformat() if s.window_end else None, "build": s.initial_build}
                                for s in list(self.sessions.values()) if s.phase != "done"]
        try:
            write_json(STATE_PATH, self.state)
        except OSError:
            pass

    def countdown_done(self, proceed: bool) -> None:
        self.countdown_answer = proceed

    def stop(self) -> None:
        self.stop_evt.set()

    def test_wake(self, seconds: int) -> str:
        """Arms a one-off wake timer so the user can check that this PC really wakes from sleep."""
        due = time.time() + seconds
        res = self.test_timer.arm(due)
        if res in ("ok", "unsupported"):
            log(f"Wake test armed for {datetime.fromtimestamp(due, SAST):%H:%M:%S} SAST - put the PC to sleep now")
        return res

    # ---- thread loop
    def run(self) -> None:
        log(f"{APP_TITLE} {APP_VERSION} started (times are SAST)")
        while not self.stop_evt.is_set():
            started = time.process_time()
            try:
                self.tick()
            except Exception:
                log("Engine error:\n" + traceback.format_exc())
            self.tick_cpu_ms = (time.process_time() - started) * 1000
            self.stop_evt.wait(self.TICK)

    def _steam_up(self) -> bool:
        if self._steam_up_cache is None:
            self._steam_up_cache = steam_running()
        return self._steam_up_cache

    def tick(self) -> None:
        self._steam_up_cache = None
        self._names_cache = None
        self._act_cache = {}
        t_now = time.time()
        gap = t_now - self._last_tick
        self._last_tick = t_now
        if gap > 90:
            log(f"The PC resumed after about {gap / 60:.0f} min asleep or suspended")
            self._net_t = 0.0
        settings, games = self.cfg.snapshot()
        now = now_sast()
        steam = self._steam_dir(games)
        self._refresh_info(games)
        self.live = steam_live(steam)

        resume = self.state.pop("resume", None)     # what we were following before restarting for an app update
        if resume is not None:
            try:
                write_json(STATE_PATH, self.state)  # used once only: an old note must never revive a finished update
            except OSError:
                pass
        for r in resume or []:
            g = next((x for x in games if x["appid"] == r["appid"]), None)
            if g is None or r["key"] in self.state["handled"] or time.time() - r["at"] > 300:
                continue
            end = datetime.fromisoformat(r["end"]) if r["end"] else None
            self._begin(g, r["key"], r["manual"], end, tracked=r["tracked"])
            s = self.sessions[r["appid"]]
            if r["build"]:
                s.initial_build, s.saw_activity = r["build"], True
                s.phase, s.dl_started, s.last_change = "downloading", time.time(), time.time()

        with self.lock:
            requests, self.manual_requests = self.manual_requests, []
            tracks, self.track_requests = self.track_requests, []
        for appid in requests:
            for g in games:
                if (appid is None or g["appid"] == appid) and g["appid"] not in self.sessions:
                    self._begin(g, f"manual|{g['appid']}|{now.isoformat()}", True, None)
        for appid, on in tracks:
            s = self.sessions.get(appid)
            if on:
                self.track_off.discard(appid)
            elif s is not None and s.tracked:
                self.track_off.add(appid)
                del self.sessions[appid]
                log(f"{s.name}: stopped tracking (the download itself carries on)")

        if not settings["paused"]:
            handled = self.state["handled"]
            for g in games:
                if g["enabled"] and g["appid"] not in self.sessions:
                    t = active_trigger(g, now, settings, handled)
                    if t:
                        end = t + timedelta(minutes=int(settings["watch_minutes"]))
                        self._begin(g, trigger_key(g["appid"], t), False, end)

        for g in games:         # after the schedule, so a download in an update window counts as scheduled
            if g["launcher"] != "steam":
                continue
            appid = g["appid"]
            active = self.live.get(appid, {}).get("active")
            if not active:
                self.track_off.discard(appid)
            wanted = (appid, True) in tracks or (active and settings["auto_track"] and appid not in self.track_off
                                                 and self._steam_up())
            if wanted and appid not in self.sessions:
                self._begin(g, f"track|{appid}|{now.isoformat()}", True, None, tracked=True)

        for s in list(self.sessions.values()):
            self._advance(s, settings, steam, now)
        finished_now = [s for s in self.sessions.values() if s.phase == "done"]
        for s in finished_now:
            del self.sessions[s.appid]
        self._handle_shutdown(settings, steam)
        self._power(settings, games, now)
        self._emit(games, settings, steam, now, finished_now)

    # ---- keep the PC awake while needed, and wake it for the next window
    def _net_ok(self) -> bool:
        t = time.time()
        if t - self._net_t < 5:
            return self._net_val
        self._net_t = t
        ok = False
        for host in ("store.steampowered.com", "1.1.1.1"):     # second one needs no DNS
            try:
                socket.create_connection((host, 443), 4).close()
                ok = True
                break
            except OSError:
                continue
        self._net_val = ok
        return ok

    def _power(self, settings: dict[str, Any], games: list[dict[str, Any]], now: datetime) -> None:
        busy = (any(s.phase != "done" for s in self.sessions.values())
                or self.shutdown is not None or bool(self.run_results)
                or time.time() < self._power_hold_until)
        upcoming: list[float] = []
        soon = False
        if settings["wake_from_sleep"] and not settings["paused"]:
            handled = self.state["handled"]
            pre = timedelta(minutes=int(settings["start_early_minutes"]) + int(settings["wake_lead_minutes"]))
            for g in games:
                if not g["enabled"]:
                    continue
                for t in candidate_triggers(g, now, days_back=0, days_ahead=14):
                    if t > now and trigger_key(g["appid"], t) not in handled:
                        w = t - pre
                        if w <= now + timedelta(seconds=60):
                            soon = True                      # we are inside the wake lead time
                        else:
                            upcoming.append(w.timestamp())
        want = busy or soon
        if want != self._awake_on:
            self._awake_on = want
            set_keep_awake(want)
            log("Keeping the PC awake" if want else "No longer keeping the PC awake")
        target = min(upcoming) if upcoming else None
        if target != self._wake_target:
            self._wake_target = target
            res = self.wake.arm(target)
            if target is not None:
                when = f"{datetime.fromtimestamp(target, SAST):%a %d %b %H:%M} SAST"
                if res == "ok":
                    log(f"Wake timer set: a sleeping PC will wake at {when}")
                elif res == "unsupported":
                    log(f"Wake timer set for {when}, but Windows says this PC does not support waking from sleep")
                else:
                    log(f"Could not set the wake timer: {res}")

    # ---- sessions
    def _begin(self, game: dict[str, Any], key: str, manual: bool, end: Optional[datetime], tracked: bool = False) -> None:
        s = Session(game, key, manual, end, tracked)
        self.sessions[s.appid] = s
        if tracked:
            s.phase = "downloading"
            s.dl_started = s.last_change = time.time()
            log(f"{s.name}: tracking the download")
        elif manual:
            log(f"{s.name}: manual check started")
        else:
            log(f"{s.name}: update window open (until {end:%H:%M} SAST)")

    def _finish(self, s: Session, result: str, msg: str) -> None:
        s.phase = "done"
        s.result = result
        s.msg = msg
        log(f"{s.name}: {result.upper()} - {msg}")
        self.last_result[s.appid] = f"{result.replace('-', ' ').capitalize()} ({now_sast():%d %b %H:%M})"
        if not s.manual:
            handled = self.state["handled"]
            handled[s.key] = now_sast().isoformat()
            cutoff = (now_sast() - timedelta(days=40)).isoformat()
            for k in [k for k, v in handled.items() if str(v) < cutoff]:
                del handled[k]
            try:
                write_json(STATE_PATH, self.state)
            except OSError:
                pass
        self.run_results.append((s.name, result, s.manual))
        if result == "updated":
            emit("notify", "Update finished", f"{s.name} is up to date.")
        elif result == "failed":
            emit("notify", "Update problem", f"{s.name}: {msg}")

    def _advance(self, s: Session, settings: dict[str, Any], steam: Optional[Path], now: datetime) -> None:
        if s.phase == "done":
            return
        lc = s.lc
        m: Optional[dict[str, Any]] = None
        if lc.precise:
            steam = lc.steam_dir()
            if steam is None:
                self._finish(s, "failed", "Steam was not found - set its folder under Launchers")
                return
            m = read_manifest(s.appid, steam)
            if m is None:
                self._finish(s, "skipped", "not installed in Steam - install it once and it will be kept up to date")
                return
        elif lc.exe() is None:
            self._finish(s, "failed", f"{lc.name} was not found - set its location under Launchers")
            return
        if s.phase == "watching":
            self._watching(s, m, settings, now)
        elif s.phase == "launching":
            self._launching(s)
        elif s.phase == "downloading":
            if m is None:
                self._downloading_generic(s, settings)
            else:
                self._downloading(s, m, settings, steam)  # type: ignore[arg-type]

    def _watching(self, s: Session, m: Optional[dict[str, Any]], settings: dict[str, Any], now: datetime) -> None:
        t = time.time()
        if not self._net_ok():
            if not s.net_since:
                s.net_since = t
                log(f"{s.name}: waiting for the internet connection (it can take a while after waking)")
            if t - s.net_since > 600 or (s.window_end and now > s.window_end):
                self._finish(s, "failed", "no internet connection")
            return
        if s.net_since:
            log(f"{s.name}: the internet connection is back")
            s.net_since = 0.0
        if m is None:           # launcher that cannot be queried: open it and watch what it does
            s.blind = True
            s.phase = "launching"
            log(f"{s.name}: opening {s.lc.name} so it can update the game ({s.lc.name} cannot be checked ahead of time)")
            return
        poll = max(60, int(settings["remote_poll_seconds"]))
        if settings["remote_check"] and (s.last_poll == 0 or t - s.last_poll >= poll):
            s.last_poll = t
            s.remote = fetch_remote_build(s.appid)
            if s.remote:
                self.info[s.appid] = {**s.remote, "checked": t}
        need, reason = False, ""
        if s.remote and s.remote["build"] != m["buildid"]:
            need, reason = True, f"new build {s.remote['build']} available (installed {m['buildid']})"
        elif m["state"] & PENDING_MASK or m["target"] not in (0, m["buildid"]):
            need, reason = True, "Steam already reports an update"
        elif s.remote is None:
            need, reason = True, "online build check unavailable - opening Steam to let it decide"
            s.blind = True
        if need:
            s.initial_build = m["buildid"]
            s.phase = "launching"
            log(f"{s.name}: {reason}")
        elif s.manual:
            self._finish(s, "up-to-date", f"already on the latest build ({m['buildid']})")
        elif s.window_end and now > s.window_end:
            self._finish(s, "up-to-date", "no update appeared during this window")

    def _launching(self, s: Session) -> None:
        t = time.time()
        lc = s.lc
        if self._running(lc):
            s.phase = "downloading"
            s.dl_started = t
            s.last_change = t
            log(f"{s.name}: {lc.name} is running - waiting for the download")
            return
        if s.launch_time and t - s.launch_time < 60:
            return
        if s.launch_attempts >= 3:
            self._finish(s, "failed", f"{lc.name} would not start")
            return
        s.launch_attempts += 1
        s.launch_time = t
        log(f"{s.name}: starting {lc.name} (attempt {s.launch_attempts})")
        try:
            lc.start()
        except OSError as exc:
            log(f"Could not start {lc.name}: {exc}")

    def _downloading(self, s: Session, m: dict[str, Any], settings: dict[str, Any], steam: Path) -> None:
        t = time.time()
        if not self._steam_up():
            if s.tracked:
                self._finish(s, "skipped", "Steam was closed")
            elif t - s.launch_time > 60:
                log(f"{s.name}: Steam is no longer running - restarting it")
                s.phase = "launching"
            return
        live = self.live.get(s.appid, {})
        live_active = bool(live.get("active"))
        if s.tracked and not s.initial_build:
            s.initial_build = m["buildid"]
        if live_active:
            s.live_seen = t
            s.last_change = t
        sig = (m["state"], m["buildid"], m["target"], m["dl"], m["staged"])
        if sig != s.sig:
            s.sig = sig
            s.last_change = t
        busy = manifest_busy(m)
        if busy or m["buildid"] != s.initial_build:
            s.saw_activity = True
        total = m["to_dl"] + m["to_stage"]
        done = m["dl"] + m["staged"]
        if live_active and live.get("total"):
            s.saw_activity = True
            s.bytes_total, s.bytes_done = live["total"], int(live["dl"])
            s.progress = s.bytes_done / s.bytes_total
            s.speed = live["speed"]
        elif busy and total > 0:
            s.bytes_total, s.bytes_done = total, done
            s.progress = max(0.0, min(1.0, done / total))
        if not live_active:
            if s.prev_t == 0:
                s.prev_t, s.prev_dl = t, m["dl"]
            elif t - s.prev_t >= 3:
                s.speed = max(0.0, (m["dl"] - s.prev_dl) / (t - s.prev_t))
                s.prev_t, s.prev_dl = t, m["dl"]
        if (m["state"] & FLAG_RUNNING or running_app_id() == s.appid) and not s.hinted_running:
            s.hinted_running = True
            log(f"{s.name}: the game is running - Steam updates it after it closes")
        if m["state"] & 512 and t - s.last_stall_log > 600:
            s.last_stall_log = t
            log(f"{s.name}: Steam has the update paused")

        target = s.remote["build"] if s.remote else None
        if manifest_idle(m) and (s.saw_activity or (target and m["buildid"] == target)) and not (s.tracked and live_active):
            s.progress = 1.0
            self._finish(s, "updated", f"now on build {m['buildid']}")
            return
        if s.tracked and t - s.live_seen > 60:
            self._finish(s, "skipped", "the download was paused or stopped in Steam" if s.saw_activity
                         else "nothing is downloading")
            return
        waited = t - s.dl_started
        if not s.saw_activity:
            limit = 600 if s.blind else int(settings["stall_minutes"]) * 60
            if waited > limit:
                if s.blind:
                    self._finish(s, "up-to-date", "Steam opened and found nothing to download")
                else:
                    self._finish(s, "failed", "Steam did not start the update. In Steam: right-click the game > "
                                 "Properties > Updates > 'Always keep this game up to date'")
                return
        elif t - s.last_change > int(settings["stall_minutes"]) * 60 and t - s.last_stall_log > 900:
            s.last_stall_log = t
            log(f"{s.name}: no download progress for {int((t - s.last_change) / 60)} min - still waiting")
        if waited > int(settings["max_download_hours"]) * 3600:
            self._finish(s, "failed", f"gave up after {settings['max_download_hours']} hours")

    def _downloading_generic(self, s: Session, settings: dict[str, Any]) -> None:
        """Launchers we cannot query: watch their disk/network activity. 'Updated' needs real, sustained
        activity (so just opening the launcher never counts), and 'finished' means it has gone quiet."""
        t = time.time()
        lc = s.lc
        if not self._running(lc):
            if t - s.launch_time > 60:
                log(f"{s.name}: {lc.name} is no longer running - restarting it")
                s.phase = "launching"
            return
        waited = t - s.dl_started
        if lc.ident not in self._act_cache:
            self._act_cache[lc.ident] = self.monitor.sample(lc.ident, lc.procs())
        smp = self._act_cache[lc.ident]
        if smp is None:
            if waited > GENERIC_BLIND_WAIT:
                self._finish(s, "up-to-date", f"{lc.name} was opened (watching its activity needs the psutil package)")
            return
        io, rx, readable = smp
        dt = t - s.prev_t if s.prev_t else 0.0
        s.prev_t = t
        busy = waited > 90 and (io >= GENERIC_ACTIVE_BPS or (not readable and rx >= GENERIC_RX_BPS))
        rate = io if readable else rx
        if busy:
            s.io_total += rate * dt
            s.last_busy = t
            s.quiet_since = 0.0
            s.speed = rate
            if not s.act_since:
                s.act_since = t
            if not s.saw_activity and t - s.act_since >= 30 and s.io_total >= GENERIC_MIN_BYTES:
                s.saw_activity = True
                s.last_change = t
                log(f"{s.name}: {lc.name} is downloading")
        else:
            s.speed = 0.0
            if s.last_busy and t - s.last_busy > 20 and not s.saw_activity:
                s.act_since = 0.0
            if s.saw_activity:
                if not s.quiet_since:
                    s.quiet_since = t
                elif t - s.quiet_since >= int(settings["generic_quiet_minutes"]) * 60:
                    s.progress = 1.0
                    self._finish(s, "updated", f"{lc.name} has gone quiet - the update looks finished")
                    return
        if not s.saw_activity and waited > GENERIC_BLIND_WAIT:
            self._finish(s, "up-to-date", f"{lc.name} opened and found nothing to download")
            return
        if waited > int(settings["max_download_hours"]) * 3600:
            self._finish(s, "failed", f"gave up after {settings['max_download_hours']} hours")

    # ---- remote info for the table (and to learn the real patch rhythm)
    def _refresh_info(self, games: list[dict[str, Any]]) -> None:
        if self.info_busy or time.time() - self.last_info_refresh < self.INFO_REFRESH:
            return
        self.last_info_refresh = time.time()
        self.info_busy = True

        def work() -> None:
            try:
                for g in games:
                    if g["launcher"] != "steam":
                        continue
                    rb = fetch_remote_build(g["appid"])
                    if rb:
                        self.info[g["appid"]] = {**rb, "checked": time.time()}
            finally:
                self.info_busy = False

        threading.Thread(target=work, daemon=True, name="info").start()

    # ---- shutdown flow
    def _handle_shutdown(self, settings: dict[str, Any], steam: Optional[Path]) -> None:
        if any(s.phase != "done" for s in self.sessions.values()):
            if self.shutdown is not None:
                log("New update activity - shutdown postponed")
                self.shutdown = None
            return
        if self.shutdown is None:
            if not self.run_results:
                return
            results = self.run_results
            updated = any(r == "updated" for _n, r, _m in results)
            failed = any(r == "failed" for _n, r, _m in results)
            manual = any(m for _n, _r, m in results)
            if updated and not failed and settings["shutdown_enabled"] and (not manual or settings["shutdown_after_manual"]):
                self.shutdown = {"phase": "waiting", "since": time.time()}
                log("All updates finished - waiting for the PC to be idle before powering down")
            else:
                if updated and manual:
                    log("Started by hand - the PC stays on (Settings > When updates are done can change this)")
                elif updated and failed:
                    log("An update failed - leaving the PC on")
                self.run_results = []
            return
        sd = self.shutdown
        now = time.time()
        if sd["phase"] == "waiting":
            idle_ok = user_idle_seconds() >= int(settings["shutdown_idle_minutes"]) * 60
            still_downloading = self._steam_up() and any(a["active"] for a in self.live.values())
            if idle_ok and running_app_id() == 0 and not still_downloading:
                sd["phase"], sd["since"] = "countdown", now
                self.countdown_answer = None
                names = ", ".join(sorted({n for n, r, _m in self.run_results if r == "updated"}))
                emit("countdown", int(settings["countdown_seconds"]), names, str(settings["after_action"]))
                log(f"Shutdown countdown started ({settings['countdown_seconds']}s)")
            elif now - sd["since"] > int(settings["shutdown_wait_minutes"]) * 60:
                log("The PC is in use - shutdown skipped")
                self.shutdown = None
                self.run_results = []
        elif sd["phase"] == "countdown":
            ans = self.countdown_answer
            if ans is None:
                if now - sd["since"] > int(settings["countdown_seconds"]) + 30:
                    log("Countdown window lost - shutdown skipped")
                    self.shutdown = None
                    self.run_results = []
            elif ans:
                self._do_shutdown(settings, steam)
                self.shutdown = None
                self.run_results = []
            else:
                log("Shutdown cancelled")
                self.shutdown = None
                self.run_results = []

    def _do_shutdown(self, settings: dict[str, Any], steam: Optional[Path]) -> None:
        action = str(settings["after_action"])
        if action not in POWER_ACTIONS:
            action = "sleep"
        verb = POWER_ACTIONS[action]
        if settings["dry_run_shutdown"]:
            log(f"DRY RUN: the PC would {verb} now")
            emit("notify", "Dry run", f"The PC would {verb} now.")
            return
        if settings["close_steam_before_shutdown"] and steam is not None and self._steam_up():
            log("Closing Steam first")
            close_steam(steam)
        log(f"The PC will {verb} now")
        if action in ("shutdown", "hibernate"):
            # Windows would otherwise put an idle PC to sleep the moment we stop holding it awake, before the
            # shutdown has run (this is what happened on 15 Oct). Hold it awake for 5 minutes; if it works the
            # PC is off long before that.
            self._power_hold_until = time.time() + 300
            set_keep_awake(True)
            self._awake_on = True
        try:
            run_power_action(action)
        except (OSError, subprocess.SubprocessError) as exc:
            log(f"Power command failed: {exc}")

    # ---- status for the UI
    def _emit(self, games: list[dict[str, Any]], settings: dict[str, Any], steam: Optional[Path],
              now: datetime, finished_now: list[Session]) -> None:
        rows: dict[int, dict[str, Any]] = {}
        for g in games:
            appid = g["appid"]
            s = self.sessions.get(appid)
            m = read_manifest(appid, steam) if g["launcher"] == "steam" else None
            info = self.info.get(appid) or {}
            if s is not None:
                if s.phase == "watching" and s.net_since:
                    status = "Waiting for the internet"
                elif s.phase == "downloading" and s.saw_activity and not s.lc.precise:
                    status = "Updating"
                elif s.phase == "downloading" and s.saw_activity:
                    status = self._steam_status(s)
                elif s.phase == "downloading" and not s.lc.precise:
                    status = f"Waiting for {s.lc.name}"
                elif s.phase == "downloading":
                    status = "Waiting for Steam"
                elif s.phase == "launching":
                    status = f"Starting {s.lc.name}"
                else:
                    status = "Watching for an update"
            elif not g["enabled"]:
                status = "Disabled"
            elif settings["paused"]:
                status = "Paused"
            else:
                status = self.last_result.get(appid, "Idle")
            rows[appid] = {"local_build": m["buildid"] if m else None,
                           "remote_build": info.get("build"),
                           "remote_updated": info.get("updated", 0),
                           "status": status, "next": next_trigger(g, now) if g["enabled"] else None}
        emit("status", rows)

        active = [s for s in self.sessions.values() if s.phase != "done"]
        emit("live", [self._live_item(s, rows, settings) for s in active])
        note = power_note(settings)
        if active:
            s = next((x for x in active if x.phase == "downloading"), active[0])
            if s.phase == "launching":
                detail, prog = f"Starting {s.lc.name}...", None
            elif s.phase == "downloading" and not s.lc.precise:
                if s.saw_activity:
                    detail = f"{s.lc.name} is updating" + (f"  \u00b7  {fmt_mbps(s.speed)}" if s.speed > 0 else "")
                else:
                    detail = f"Waiting for {s.lc.name} to start the update..."
                prog = None
            elif s.phase == "downloading" and s.saw_activity and s.bytes_total > 0:
                detail = f"{s.progress * 100:.0f}%  \u00b7  {self._download_text(s)}"
                prog = s.progress
            elif s.phase == "downloading":
                detail, prog = "Waiting for Steam to start the update...", None
            else:
                detail, prog = "Watching for the update...", None
            emit("progress", {"state": "active", "appid": s.appid, "game": s.name, "phase": s.phase, "launcher": s.lc.name,
                              "progress": prog, "detail": detail, "note": note, "count": len(active),
                              "tracked": s.tracked})
        elif finished_now:
            s = finished_now[-1]
            label = {"updated": "UPDATE COMPLETE", "up-to-date": "UP TO DATE", "failed": "UPDATE FAILED",
                     "skipped": "SKIPPED"}.get(s.result or "", "DONE")
            emit("progress", {"state": "finished", "appid": s.appid, "game": s.name, "phase": "finished", "launcher": s.lc.name,
                              "label": label, "progress": 1.0 if s.result == "updated" else None,
                              "detail": s.msg, "note": note})
        else:
            emit("progress", {"state": "idle"})

    def _download_text(self, s: Session) -> str:
        """The same line everywhere: size, the launcher's speed in Mbps, and the time left at that speed."""
        known = s.saw_activity and s.bytes_total > 0
        parts = [f"{fmt_bytes(s.bytes_done)} of {fmt_bytes(s.bytes_total)}"] if known else []
        if s.speed > 0:
            parts.append(fmt_mbps(s.speed))
            if known:
                mins = max(1, int((s.bytes_total - s.bytes_done) / s.speed / 60))
                parts.append(f"about {mins // 60} h {mins % 60} min left" if mins >= 60 else f"about {mins} min left")
        return "  ·  ".join(parts)

    def _steam_status(self, s: Session) -> str:
        """Say what Steam says it is doing, so a pause or the install step never looks like a download."""
        live = self.live.get(s.appid, {})
        state = live.get("state", "")
        if "Downloading" in state or not live:
            return f"Downloading {s.progress * 100:.0f}%"
        if not live.get("active"):
            return "Paused in Steam"
        if "Verifying" in state or "Validating" in state:
            return "Verifying files"
        return "Installing"

    def _live_item(self, s: Session, rows: dict[int, dict[str, Any]], settings: dict[str, Any]) -> dict[str, Any]:
        """One card in the main window's live panel."""
        known = s.saw_activity and s.bytes_total > 0
        return {"appid": s.appid, "name": s.name, "tracked": s.tracked, "progress": s.progress if known else None,
                "status": rows.get(s.appid, {}).get("status", ""), "detail": self._download_text(s),
                "note": power_note(settings) if not s.manual or settings["shutdown_after_manual"]
                else "PC stays on after this, because you started it. You can change this in Settings" if settings["shutdown_enabled"] else ""}


# --------------------------------------------------------------------------- web UI plumbing
webview: Any = None            # the pywebview module, imported in main()


def web_dir() -> Path:
    """The folder holding index.html, app.css, app.js ... (inside the exe when frozen)."""
    base = getattr(sys, "_MEIPASS", None) or Path(__file__).resolve().parent
    return Path(base) / "web"


def brand_bytes(kind: str) -> bytes:
    """The icon / logo PNG. A gaus_icon.png / gaus_logo.png in the data folder overrides the built-in art."""
    custom = APP_DIR / f"gaus_{kind}.png"
    try:
        if custom.exists():
            return custom.read_bytes()
    except OSError:
        pass
    return base64.b64decode(_ICON_B64 if kind == "icon" else _LOGO_B64)


_MIME = {".html": "text/html; charset=utf-8", ".css": "text/css; charset=utf-8",
         ".js": "text/javascript; charset=utf-8", ".json": "application/json", ".png": "image/png",
         ".jpg": "image/jpeg", ".jpeg": "image/jpeg", ".svg": "image/svg+xml", ".ico": "image/x-icon",
         ".woff2": "font/woff2", ".txt": "text/plain; charset=utf-8"}


class AssetServer:
    """A tiny read-only web server on 127.0.0.1 (random port) that hands the UI files, the downloaded
    photos and the brand art to the app's own windows. It never accepts input and exposes no API."""

    def __init__(self) -> None:
        owner = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *_a: Any) -> None:
                pass

            def do_GET(self) -> None:  # noqa: N802
                try:
                    code, ctype, body = owner.resolve(urllib.parse.urlsplit(self.path).path)
                except Exception:
                    code, ctype, body = 500, "text/plain", b"error"
                self.send_response(code)
                self.send_header("Content-Type", ctype)
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Cache-Control", "no-store" if code != 200 or "photos" not in self.path else "max-age=86400")
                self.send_header("X-Content-Type-Options", "nosniff")
                self.end_headers()
                self.wfile.write(body)

        self.httpd = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.httpd.daemon_threads = True
        self.port = int(self.httpd.server_address[1])
        threading.Thread(target=self.httpd.serve_forever, daemon=True, name="assets").start()

    def url(self, path: str) -> str:
        return f"http://127.0.0.1:{self.port}/{path.lstrip('/')}"

    def resolve(self, path: str) -> tuple[int, str, bytes]:
        parts = [urllib.parse.unquote(p) for p in path.split("/") if p]
        if not parts:
            return 404, "text/plain", b"not found"
        if parts == ["favicon.ico"]:
            return 200, "image/png", brand_bytes("icon")
        if parts == ["ui", "version.txt"]:
            return 200, _MIME[".txt"], APP_VERSION.encode()
        if parts[0] == "brand" and len(parts) == 2:
            kind = Path(parts[1]).stem
            if kind in ("icon", "logo"):
                return 200, "image/png", brand_bytes(kind)
            return 404, "text/plain", b"not found"
        if parts[0] == "ui":
            base = web_dir()
        elif parts[0] == "photos":
            base = PHOTO_DIR
        else:
            return 404, "text/plain", b"not found"
        target = base.joinpath(*parts[1:]).resolve()
        if base.resolve() not in target.parents or not target.is_file():
            return 404, "text/plain", b"not found"
        return 200, _MIME.get(target.suffix.lower(), "application/octet-stream"), target.read_bytes()


class InstanceLock:
    """One copy of Gaus at a time. The OS drops the lock if the app dies, so there are no stale lock files."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.fh: Any = None

    def acquire(self, wait: float) -> bool:
        deadline = time.monotonic() + wait
        while True:
            fh = None
            try:
                fh = open(self.path, "a+b")
                if IS_WINDOWS:
                    import msvcrt  # type: ignore
                    fh.seek(0)
                    msvcrt.locking(fh.fileno(), msvcrt.LK_NBLCK, 1)
                else:
                    import fcntl
                    fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                self.fh = fh
                return True
            except (OSError, ImportError):
                if fh is not None:
                    try:
                        fh.close()
                    except OSError:
                        pass
                if time.monotonic() >= deadline:
                    return False
                time.sleep(0.25)

    def release(self) -> None:
        fh, self.fh = self.fh, None
        if fh is None:
            return
        try:
            if IS_WINDOWS:
                import msvcrt  # type: ignore
                fh.seek(0)
                msvcrt.locking(fh.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                import fcntl
                fcntl.flock(fh.fileno(), fcntl.LOCK_UN)
        except (OSError, ImportError):
            pass
        try:
            fh.close()
        except OSError:
            pass


def message_box(text: str) -> None:
    if IS_WINDOWS:
        try:
            ctypes.windll.user32.MessageBoxW(None, text, APP_TITLE, 0x40)  # type: ignore[attr-defined]
            return
        except Exception:
            pass
    print(f"{APP_TITLE}: {text}", file=sys.stderr)


def _api(fn):  # type: ignore[no-untyped-def]
    """Every call from the page is wrapped: a bug becomes an error toast and a log entry, never a dead window."""
    @functools.wraps(fn)
    def wrapper(self, *args, **kwargs):  # type: ignore[no-untyped-def]
        try:
            return fn(self, *args, **kwargs)
        except Exception as exc:
            log(f"UI call {fn.__name__} failed:\n{traceback.format_exc()}")
            return {"error": f"{type(exc).__name__}: {exc}"}
    return wrapper


class Api:
    """What the page can call (window.pywebview.api.*). Thin: the work lives in Controller."""

    def __init__(self, ctl: "Controller") -> None:
        self._ctl = ctl

    # state ---------------------------------------------------------------
    @_api
    def ready(self) -> dict[str, Any]:
        self._ctl.ui_ready.set()
        return self._ctl.state()

    @_api
    def state(self) -> dict[str, Any]:
        return self._ctl.state()

    @_api
    def log_tail(self) -> list[str]:
        try:
            return LOG_PATH.read_text(encoding="utf-8", errors="replace").splitlines()[-150:]
        except OSError:
            return []

    @_api
    def welcome_done(self, name: str) -> dict[str, Any]:
        return self._ctl.welcome_done(name)

    # accounts ------------------------------------------------------------
    @_api
    def switch_account(self, aid: str) -> dict[str, Any]:
        return self._ctl.switch_account(aid)

    @_api
    def add_account(self, name: str) -> dict[str, Any]:
        return self._ctl.add_account(name)

    @_api
    def edit_account(self, aid: str, name: str, enabled: bool) -> dict[str, Any]:
        return self._ctl.edit_account(aid, name, enabled)

    @_api
    def remove_account(self, aid: str) -> dict[str, Any]:
        return self._ctl.remove_account(aid)

    # launchers -----------------------------------------------------------
    @_api
    def launcher_probe(self, key: str) -> dict[str, Any]:
        return self._ctl.launcher_probe(key)

    @_api
    def browse(self, kind: str) -> str:
        return self._ctl.browse(kind)

    @_api
    def add_launcher(self, ltype: str, name: str, path: str, args: str, enabled: bool, force: bool) -> dict[str, Any]:
        return self._ctl.add_launcher(ltype, name, path, args, enabled, force)

    @_api
    def update_launcher(self, lid: str, name: str, path: str, args: str, enabled: bool) -> dict[str, Any]:
        return self._ctl.update_launcher(lid, name, path, args, enabled)

    @_api
    def remove_launcher(self, lid: str) -> dict[str, Any]:
        return self._ctl.remove_launcher(lid)

    # games ---------------------------------------------------------------
    @_api
    def search_games(self, lid: str, term: str) -> dict[str, Any]:
        return self._ctl.search_games_for(lid, term)

    @_api
    def installed_games(self, lid: str) -> list[dict[str, Any]]:
        return self._ctl.installed_games(lid)

    @_api
    def add_game(self, lid: str, name: str, appid: Optional[int]) -> dict[str, Any]:
        return self._ctl.add_game(lid, name, appid)

    @_api
    def game_detail(self, lid: str, appid: int) -> dict[str, Any]:
        return self._ctl.game_detail(lid, int(appid))

    @_api
    def save_game(self, lid: str, appid: int, enabled: bool, weekly: str, dates: str, keywords: str) -> dict[str, Any]:
        return self._ctl.save_game(lid, int(appid), enabled, weekly, dates, keywords)

    @_api
    def remove_game(self, lid: str, appid: int) -> dict[str, Any]:
        return self._ctl.remove_game(lid, int(appid))

    @_api
    def check_now(self, appid: Optional[int]) -> dict[str, Any]:
        return self._ctl.check_now(appid)

    @_api
    def track(self, appid: int, on: bool) -> dict[str, Any]:
        self._ctl.engine.set_tracking(int(appid), bool(on))
        return {"ok": True}

    @_api
    def start_saver(self, appid: int, dim: int, others: str, source: str, ask: bool) -> dict[str, Any]:
        return self._ctl.start_saver(int(appid), to_int(dim, 60), str(others), str(source), bool(ask))

    @_api
    def favourite(self, appid: int, hero: str = "") -> dict[str, Any]:
        return self._ctl.favourite(int(appid), str(hero))

    @_api
    def set_favourite(self, appid: int, name: str) -> dict[str, Any]:
        return self._ctl.set_favourite(int(appid), str(name))

    @_api
    def add_favourite_images(self, appid: int, hero: str = "") -> dict[str, Any]:
        return self._ctl.add_favourite_images(int(appid), str(hero))

    @_api
    def remove_favourite_image(self, appid: int, file: str, hero: str = "") -> dict[str, Any]:
        return self._ctl.remove_favourite_image(int(appid), str(file), str(hero))

    @_api
    def open_official(self, kind: str) -> dict[str, Any]:
        return self._ctl.open_official(str(kind))

    @_api
    def latest_patch(self, appid: int) -> dict[str, str]:
        try:
            return fetch_latest_patch(int(appid))
        except Exception:       # the pill just shows "Patch notes" without a date
            return {}

    @_api
    def patch_notes(self, appid: int) -> dict[str, Any]:
        return self._ctl.patch_notes(int(appid))

    @_api
    def open_news(self, url: str) -> dict[str, Any]:
        return self._ctl.open_news(str(url))

    @_api
    def find_art(self, appid: int, site: str, hero: str = "") -> dict[str, Any]:
        return self._ctl.find_art(int(appid), str(site), str(hero))

    @_api
    def add_favourite_data(self, appid: int, data_url: str, title: str, hero: str = "") -> dict[str, Any]:
        return self._ctl.add_favourite_data(int(appid), str(data_url), str(title), str(hero))

    @_api
    def add_favourite_url(self, appid: int, url: str, hero: str = "") -> dict[str, Any]:
        return self._ctl.add_favourite_url(int(appid), str(url), str(hero))

    @_api
    def nerd_stats(self) -> dict[str, Any]:
        return self._ctl.nerd_stats()

    @_api
    def saver_images(self) -> list[dict[str, str]]:
        return self._ctl.saver_images()

    @_api
    def add_saver_images(self) -> dict[str, Any]:
        return self._ctl.add_images(SAVER_KEY)

    @_api
    def remove_saver_image(self, file: str) -> list[dict[str, str]]:
        return self._ctl.remove_saver_image(str(file))

    @_api
    def preview(self, appid: int) -> dict[str, Any]:
        return self._ctl.preview(int(appid))

    @_api
    def add_images(self, lid: str, appid: int) -> dict[str, Any]:
        return self._ctl.add_images(int(appid))

    @_api
    def refresh_photos(self, appid: int) -> dict[str, Any]:
        self._ctl.photos.request(int(appid), force=True)
        return {"ok": True}

    # settings / maintenance ---------------------------------------------
    @_api
    def save_settings(self, values: dict[str, Any]) -> dict[str, Any]:
        return self._ctl.save_settings(values)

    @_api
    def wake_check(self) -> dict[str, Any]:
        return self._ctl.wake_check()

    @_api
    def wake_fix(self) -> dict[str, Any]:
        return self._ctl.wake_fix()

    @_api
    def wake_test(self) -> dict[str, Any]:
        return self._ctl.wake_test()

    @_api
    def check_updates(self, manual: bool) -> dict[str, Any]:
        self._ctl.check_updates(manual=bool(manual))
        return {"ok": True}

    @_api
    def install_update(self) -> dict[str, Any]:
        return self._ctl.install_update()

    @_api
    def open_data_folder(self) -> dict[str, Any]:
        return self._ctl.open_data_folder()

    # loading screen / countdown ----------------------------------------
    @_api
    def loading_init(self) -> dict[str, Any]:
        return self._ctl.screen.payload()

    @_api
    def loading_dismiss(self) -> dict[str, Any]:
        self._ctl.screen_dismissed_by_user()
        return {"ok": True}

    @_api
    def countdown_init(self) -> dict[str, Any]:
        return self._ctl.countdown_payload()

    @_api
    def countdown_cancel(self) -> dict[str, Any]:
        self._ctl.countdown_cancel()
        return {"ok": True}


class LoadingScreen:
    """The photo slideshow shown while a game downloads. It is a frameless pywebview window that is
    created when needed and destroyed when it hides; the page does the animation."""

    def __init__(self, ctl: "Controller") -> None:
        self.ctl = ctl
        self.window: Any = None
        self.entries: list[dict[str, Any]] = []
        self.slide_seconds = 7.0
        self.appid = 0
        self.state: dict[str, Any] = {"game": "", "label": "UPDATING", "detail": "", "progress": None, "note": "", "dim": 0, "saver": False}
        self.lock = threading.RLock()

    @property
    def visible(self) -> bool:
        return self.window is not None

    def set_slides(self, appid: int, entries: list[dict[str, Any]], slide_seconds: float) -> None:
        with self.lock:
            self.appid = appid
            self.entries = list(entries)
            self.slide_seconds = max(3.0, float(slide_seconds))
        self._push_slides()

    def set_state(self, st: dict[str, Any]) -> None:
        with self.lock:
            self.state.update(st)
        self._eval(f"Loading.update({json.dumps(st)})")

    def _slides(self) -> list[dict[str, str]]:
        out = []
        for e in self.entries:
            try:
                rel = Path(e["path"]).resolve().relative_to(PHOTO_DIR.resolve()).as_posix()
            except (ValueError, OSError, KeyError):
                continue
            credit = f"Photo: {e.get('title', '')} — {e.get('author', '')} · {e.get('license', '')} · {e.get('source', '')}"
            out.append({"url": "/photos/" + urllib.parse.quote(rel), "credit": credit})
        return out

    def payload(self) -> dict[str, Any]:
        with self.lock:
            return {"slides": self._slides(), "seconds": self.slide_seconds, "state": dict(self.state)}

    def _push_slides(self) -> None:
        self._eval(f"Loading.setSlides({json.dumps(self._slides())}, {self.slide_seconds})")

    def _eval(self, js: str) -> None:
        w = self.window
        if w is None:
            return
        try:
            w.evaluate_js(js)
        except Exception:
            pass

    def present(self, fullscreen: bool) -> None:
        with self.lock:
            if self.window is not None:
                self._push_slides()
                return
            w = self.ctl.new_window("loading.html", fullscreen=fullscreen, frameless=True, on_top=True,
                                    width=1100, height=620, background_color="#0c0b08", easy_drag=False)
            w.events.closed += lambda: self._closed(w)
            self.window = w

    def _closed(self, w: Any) -> None:
        with self.lock:
            if self.window is not w:
                return
            self.window = None
        self.ctl.screen_closed_by_user()

    def hide(self) -> None:
        with self.lock:
            w, self.window = self.window, None
        if w is not None:
            try:
                w.destroy()
            except Exception:
                pass


class Countdown:
    """The cancel countdown before the PC powers down. Ends by itself, on activity, or on Cancel."""

    def __init__(self, ctl: "Controller", seconds: int, names: str, action: str) -> None:
        self.ctl = ctl
        self.total = max(5, int(seconds))
        self.remaining = self.total
        self.names = names
        self.verb = POWER_ACTIONS.get(action, "shut down")
        self.cancel_evt = threading.Event()
        self.finished = False
        self.window: Any = None

    def start(self) -> None:
        self.window = self.ctl.new_window("countdown.html", width=460, height=380, frameless=False, on_top=True,
                                          resizable=False, easy_drag=False, background_color="#0f1422")
        self.window.events.closed += self.cancel_evt.set
        threading.Thread(target=self._run, daemon=True, name="countdown").start()

    def payload(self) -> dict[str, Any]:
        return {"remaining": self.remaining, "total": self.total, "verb": self.verb, "names": self.names}

    def _run(self) -> None:
        elapsed = 0
        proceed = False
        while True:
            if self.cancel_evt.wait(1.0):
                break
            elapsed += 1
            self.remaining -= 1
            if elapsed > 3 and user_idle_seconds() < 2.5:
                log("Activity detected during the countdown - power-down cancelled")
                break
            if self.remaining <= 0:
                proceed = True
                break
            try:
                self.window.evaluate_js(f"Countdown.tick({self.remaining})")
            except Exception:
                pass
        self.finished = True
        try:
            self.window.destroy()
        except Exception:
            pass
        self.ctl.countdown_end(proceed)


# --------------------------------------------------------------------------- controller
class Controller:
    """Everything between the engine and the windows: tray, UI state, loading screen, updates."""

    def __init__(self, cfg: Config, engine: Engine, photos: PhotoManager, server: AssetServer,
                 instance_lock: Optional[InstanceLock] = None) -> None:
        self.cfg, self.engine, self.photos, self.server = cfg, engine, photos, server
        self.instance_lock = instance_lock
        self.api = Api(self)
        self.main: Any = None
        self.tray: Any = None
        self.ui_ready = threading.Event()
        self.stop_evt = threading.Event()
        self.quitting = False
        self.preview_active = False
        self.run_dismissed = False
        self.screen_appid = 0
        self.status: dict[int, dict[str, Any]] = {}
        self.update_info: Optional[dict[str, str]] = None
        self.update_busy = False
        self.install_busy = False
        self.countdown: Optional[Countdown] = None
        self.screen = LoadingScreen(self)
        self.dimmer = MonitorDimmer()
        self.saver_on = False
        self._covers: dict[int, str] = {}
        self._news_links: set[str] = set()
        self._official: dict[str, Any] = {}
        self.saver_asked: set[int] = set()
        # just restarted for an app update: don't offer or show anything for a download already under way
        self.no_prompt_until = time.time() + 90 if "--after-update" in sys.argv else 0.0
        self.run_dismissed = "--after-update" in sys.argv
        self.shown = False               # the main window has been on screen at least once
        self.parked = False              # the main window is hidden with its page unloaded, to use less memory
        self.pending_prompt: Optional[dict[str, Any]] = None
        self.tray_stats: Optional[dict[str, Any]] = None
        self._nerd_prev: dict[int, tuple[float, float]] = {}
        self.started_at = time.time()
        self._hide_timer: Optional[threading.Timer] = None
        BUS.on("status", self.on_status)
        BUS.on("log", lambda line: self.push("log", line))
        BUS.on("live", self.on_live)
        BUS.on("progress", self.on_progress)
        BUS.on("countdown", self.on_countdown)
        BUS.on("notify", self.on_notify)
        BUS.on("photos_changed", lambda _a: (self._covers.clear(), self.push("rows", self.rows())))

    # ---- windows
    def new_window(self, page: str, **kw: Any) -> Any:
        title = kw.pop("title", APP_TITLE)
        url = kw.pop("url", self.server.url("ui/" + page))
        return webview.create_window(title, url=url, js_api=self.api, text_select=True, **kw)

    def push(self, fn: str, *args: Any) -> None:
        w = self.main
        if w is None or self.quitting or not self.ui_ready.is_set():
            return
        js = f"window.Gaus && Gaus.{fn}({', '.join(json.dumps(a, default=str) for a in args)})"
        try:
            w.evaluate_js(js)
        except Exception:
            pass

    def show_window(self) -> None:
        w = self.main
        if w is None:
            return
        self.shown = True
        try:
            if self.parked:
                self.parked = False
                w.load_url(self.server.url("ui/index.html"))
            w.show()
            w.restore()
        except Exception:
            pass
        self.push("state", self.state())

    def park(self) -> None:
        """The window is hidden, so unload its page: an open browser page is most of what Gaus would use in the tray."""
        self.ui_ready.clear()
        self.parked = True
        try:
            self.main.load_url("about:blank")
        except Exception:
            pass
        self._settle_later()

    def _settle_later(self) -> None:
        timer = threading.Timer(20, self._settled)
        timer.daemon = True
        timer.start()

    def _settled(self) -> None:
        if not self.parked or psutil is None:
            return
        try:
            me = psutil.Process()
            trim_memory([me.pid] + [p.pid for p in me.children(recursive=True)])
            time.sleep(10)
            if self.parked:
                t0, c0 = time.time(), self._tree_cpu()
                time.sleep(20)
                stats = self.nerd_stats()
                stats["cpu_pc"] = (self._tree_cpu() - c0) / (time.time() - t0) * 100 / (psutil.cpu_count() or 1)
                self.tray_stats = {"ram_mb": stats["ram_mb"], "cpu_pc": stats["cpu_pc"], "when": f"{now_sast():%H:%M}"}
        except psutil.Error:
            pass

    # ---- stats for nerds: every process that is Gaus, the built-in browser included
    def _tree(self) -> list[Any]:
        me = psutil.Process()
        procs = [me] + me.children(recursive=True)
        parent = me.parent()
        if is_frozen() and parent is not None and parent.name() == me.name():
            procs.insert(0, parent)     # the small launcher process that a one-file exe keeps running
        return procs

    def _tree_cpu(self) -> float:
        total = 0.0
        for p in self._tree():
            try:
                c = p.cpu_times()
                total += c.user + c.system
            except psutil.Error:
                pass
        return total

    def nerd_stats(self) -> dict[str, Any]:
        if psutil is None:
            return {"error": "Stats need the psutil package."}
        now = time.time()
        cores = psutil.cpu_count() or 1
        me = os.getpid()
        rows, prev = [], self._nerd_prev
        self._nerd_prev = {}
        for p in self._tree():
            try:
                with p.oneshot():
                    mem = p.memory_full_info()
                    c = p.cpu_times()
                    used = c.user + c.system
                    name = p.name()
                    threads = p.num_threads()
                role = ("Gaus (engine, tray)" if p.pid == me else "Gaus (launcher stub)" if name.lower().startswith("gaus")
                        else "Edge WebView2 (the window)" if "webview" in name.lower() else name)
                old = prev.get(p.pid)
                self._nerd_prev[p.pid] = (used, now)
                rows.append({"role": role, "pid": p.pid, "ram": mem.uss / 1048576, "commit": getattr(mem, "private", mem.vms) / 1048576,
                             "threads": threads, "cpu": (used - old[0]) / max(.001, now - old[1]) * 100 / cores if old else None,
                             "cpu_total": used})
            except psutil.Error:
                continue        # it exited while we looked
        rows.sort(key=lambda r: -r["ram"])
        sys_mem = psutil.virtual_memory()
        ready = bool(prev) and all(r["cpu"] is not None for r in rows)
        return {"rows": rows, "ram_mb": sum(r["ram"] for r in rows), "commit_mb": sum(r["commit"] for r in rows),
                "cpu_pc": sum(r["cpu"] or 0 for r in rows) if ready else None, "cores": cores,
                "cpu_total_s": sum(r["cpu_total"] for r in rows), "uptime_s": now - self.started_at,
                "ram_of_pc_pc": sum(r["ram"] for r in rows) * 1048576 / sys_mem.total * 100,
                "pc_ram_gb": sys_mem.total / 1024 ** 3, "tick_ms": self.engine.tick_cpu_ms, "tick_s": self.engine.TICK,
                "tray": self.tray_stats}

    def quit(self, why: str) -> None:
        if self.quitting:
            return
        self.quitting = True
        log(f"Gaus is closing: {why}")
        self.dimmer.hide()
        self.stop_evt.set()
        try:
            self.engine.stop()
        except Exception:
            pass
        try:
            if self.tray is not None:
                self.tray.stop()
        except Exception:
            pass
        self.screen.hide()
        for w in list(getattr(webview, "windows", [])):
            try:
                w.destroy()
            except Exception:
                pass

    # ---- state for the page
    def state(self) -> dict[str, Any]:
        cfg = self.cfg
        prompt, self.pending_prompt = self.pending_prompt, None
        accounts = []
        for a in cfg.tree():
            accounts.append({"id": a["id"], "name": a["name"], "enabled": a["enabled"], "launchers": [
                {"id": l["id"], "type": l["type"], "name": l["name"], "path": l["path"], "args": l["args"],
                 "enabled": l["enabled"], "games": len(l["games"])} for l in a["launchers"]]})
        return {
            "app": {"title": APP_TITLE, "tagline": APP_TAGLINE, "version": APP_VERSION, "is_windows": IS_WINDOWS,
                    "frozen": is_frozen(), "feed_builtin": bool(DEFAULT_UPDATE_FEED.strip())},
            "settings": dict(cfg.settings), "active": cfg.active, "accounts": accounts, "rows": self.rows(),
            "launcher_types": {k: {"name": v["name"], "precise": bool(v["precise"]), "tip": v["tip"]}
                               for k, v in LAUNCHER_TYPES.items()},
            "update": self.update_info, "first_run": bool(cfg.first_run), "shown": self.shown, "prompt": prompt,
        }

    def reply(self, **extra: Any) -> dict[str, Any]:
        out = {"ok": True, "state": self.state()}
        out.update(extra)
        return out

    def rows(self) -> list[dict[str, Any]]:
        acc = self.cfg.account(self.cfg.active)
        if acc is None:
            return []
        now = now_sast()
        out = []
        for lc in acc["launchers"]:
            precise = bool(LAUNCHER_TYPES[lc["type"]]["precise"])
            for g in lc["games"]:
                st = self.status.get(g["appid"], {})
                nxt = st["next"] if "next" in st else next_trigger(g, now)
                on = acc["enabled"] and lc["enabled"] and g["enabled"]
                if not on:
                    nxt_txt = "-"
                elif nxt is None:
                    nxt_txt = "no windows set"
                else:
                    nxt_txt = f"{nxt:%a %d %b %H:%M}"
                upd = st.get("remote_updated") or 0
                upd_txt = datetime.fromtimestamp(upd, SAST).strftime("%a %d %b %H:%M") if upd else "-"
                if not acc["enabled"]:
                    status = "Account off"
                elif not lc["enabled"]:
                    status = "Launcher off"
                else:
                    status = str(st.get("status", "Idle"))
                out.append({
                    "key": f"{lc['id']}:{g['appid']}", "lid": lc["id"], "appid": g["appid"], "name": g["name"],
                    "enabled": bool(g["enabled"]), "launcher": lc["name"],
                    "installed": str(st.get("local_build") or "not installed") if precise else "-",
                    "latest": str(st.get("remote_build") or "-") if precise else "-",
                    "patched": upd_txt if precise else "-", "next": nxt_txt,
                    "next_ts": nxt.timestamp() if on and nxt is not None else None,
                    "precise": precise, "photos": self.photos.count(g["appid"]), "status": status,
                    "favourite": favourite_of(g["appid"]),
                    "cover": self._cover(g["appid"])})
        return out

    def _cover(self, appid: int) -> str:
        """The game's art for the library page: a new pick each launch. A favourite character's pictures come first,
        then the user's own pictures for the game, then its official art."""
        if appid not in self._covers:
            entries = favourite_entries(appid) or photo_entries(appid)
            own = [e for e in entries if e.get("source") == OWN_SRC]
            random.shuffle(own or entries)
            for e in own or entries:
                try:
                    self._covers[appid] = "/photos/" + urllib.parse.quote(Path(e["path"]).resolve().relative_to(PHOTO_DIR.resolve()).as_posix())
                    break
                except (ValueError, OSError, KeyError):
                    continue
        return self._covers.get(appid, "")

    def on_status(self, rows: dict) -> None:
        self.status = rows
        if self.ui_ready.is_set():
            self.push("rows", self.rows())

    def on_notify(self, title: str, text: str) -> None:
        try:
            if self.tray is not None:
                self.tray.notify(text, title)
        except Exception:
            pass

    def _lookup(self, lid: str) -> tuple[Optional[dict[str, Any]], Optional[dict[str, Any]]]:
        acc = self.cfg.account(self.cfg.active)
        lc = next((l for l in (acc["launchers"] if acc else []) if l["id"] == lid), None)
        return acc, lc

    # ---- accounts
    def welcome_done(self, name: str) -> dict[str, Any]:
        self.cfg.first_run = False
        acc = self.cfg.account(self.cfg.active)
        if acc and name.strip():
            self.cfg.edit_account(acc["id"], name.strip(), True)
            log(f"Welcome, {name.strip()}")
        self.after_accounts_changed()
        return self.reply()

    def after_accounts_changed(self) -> None:
        try:
            if self.tray is not None:
                self.tray.update_menu()
        except Exception:
            pass

    def switch_account(self, aid: str) -> dict[str, Any]:
        if aid != self.cfg.active:
            self.cfg.set_active(aid)
            self.after_accounts_changed()
        return self.reply()

    def add_account(self, name: str) -> dict[str, Any]:
        name = name.strip()
        if not name:
            return {"error": "Type a name first."}
        self.cfg.add_account(name)
        log(f"Added account {name}")
        self.after_accounts_changed()
        return self.reply()

    def edit_account(self, aid: str, name: str, enabled: bool) -> dict[str, Any]:
        self.cfg.edit_account(aid, name, bool(enabled))
        log(f"Saved account {name} ({'on' if enabled else 'off'})")
        self.after_accounts_changed()
        return self.reply()

    def remove_account(self, aid: str) -> dict[str, Any]:
        acc = self.cfg.account(aid)
        if len(self.cfg.tree()) <= 1:
            return {"error": "You need at least one account."}
        if self.cfg.remove_account(aid):
            log(f"Removed account {acc['name'] if acc else aid}")
            used = self.cfg.used_appids()
            for lc in (acc["launchers"] if acc else []):
                for g in lc["games"]:
                    if g["appid"] not in used:
                        shutil.rmtree(photo_dir(g["appid"]), ignore_errors=True)
            self.after_accounts_changed()
        return self.reply()

    # ---- launchers
    def launcher_probe(self, key: str) -> dict[str, Any]:
        spec = LAUNCHER_TYPES.get(key)
        if spec is None:
            return {"error": "Unknown launcher."}
        found = Launcher({"launcher": key, "launcher_path": ""}).exe()
        if key == "steam":
            label = "Steam folder"
            ph = f"Found automatically: {Path(found).parent}" if found else "Folder that contains steam.exe"
        elif key == "custom":
            label, ph = "Launcher .exe", "Required: choose the launcher's .exe"
        else:
            label = "Launcher .exe"
            ph = f"Found automatically: {found}" if found else "Not found - choose its .exe"
        tip = spec["tip"] + ("" if spec["precise"] else
                             "  Gaus cannot ask this launcher whether an update exists, so it opens it and watches "
                             "its disk activity until the download has finished.")
        return {"label": label, "placeholder": ph, "tip": tip, "default_name": spec["name"], "precise": bool(spec["precise"])}

    def browse(self, kind: str) -> str:
        w = self.main
        if w is None or webview is None:
            return ""
        fd = getattr(webview, "FileDialog", None)
        if kind == "folder":
            res = w.create_file_dialog(fd.FOLDER if fd else webview.FOLDER_DIALOG)
        else:
            res = w.create_file_dialog(fd.OPEN if fd else webview.OPEN_DIALOG,
                                       file_types=("Programs (*.exe)", "All files (*.*)"))
        return str(res[0]) if res else ""

    def add_launcher(self, ltype: str, name: str, path: str, args: str, enabled: bool, force: bool) -> dict[str, Any]:
        spec = LAUNCHER_TYPES.get(ltype)
        if spec is None:
            return {"error": "Unknown launcher."}
        path = path.strip()
        if ltype == "steam" and path and not (Path(path) / "steam.exe").exists():
            return {"error": "That folder does not contain steam.exe."}
        if ltype == "custom" and not path:
            return {"error": "Choose the launcher's .exe first."}
        if ltype not in ("steam", "custom") and not path and Launcher({"launcher": ltype}).exe() is None and not force:
            return {"needs_confirm": f"{spec['name']} was not found on this PC. Add it anyway? You can set its location later."}
        lid = self.cfg.add_launcher(self.cfg.active, ltype, name.strip() or spec["name"], path, args.strip())
        if not lid:
            return {"error": "Could not add the launcher."}
        if not enabled:
            self.cfg.update_launcher(self.cfg.active, lid, enabled=False)
        log(f"Added launcher {name.strip() or spec['name']}")
        return self.reply(lid=lid)

    def update_launcher(self, lid: str, name: str, path: str, args: str, enabled: bool) -> dict[str, Any]:
        _acc, lc = self._lookup(lid)
        if lc is None:
            return {"error": "That launcher no longer exists."}
        path = path.strip()
        if lc["type"] == "steam" and path and not (Path(path) / "steam.exe").exists():
            return {"error": "That folder does not contain steam.exe."}
        if lc["type"] == "custom" and not path:
            return {"error": "Choose the launcher's .exe first."}
        self.cfg.update_launcher(self.cfg.active, lid, name=name.strip() or lc["name"], path=path,
                                 args=args.strip(), enabled=bool(enabled))
        log(f"Saved launcher {name.strip() or lc['name']}")
        return self.reply()

    def remove_launcher(self, lid: str) -> dict[str, Any]:
        for appid in self.cfg.remove_launcher(self.cfg.active, lid):
            shutil.rmtree(photo_dir(appid), ignore_errors=True)
        log("Removed a launcher")
        return self.reply()

    # ---- games
    def search_games_for(self, lid: str, term: str) -> dict[str, Any]:
        _acc, lc = self._lookup(lid)
        if lc is None:
            return {"error": "That launcher no longer exists."}
        have = {g["appid"] for g in lc["games"]}
        try:
            results = search_games(term, find_steam_path({"steam_path": lc["path"]}))
        except Exception as exc:
            return {"error": str(exc)}
        return {"results": [{"name": r["name"], "appid": r["appid"], "installed": bool(r.get("installed")),
                             "dup": r["appid"] in have} for r in results]}

    def installed_games(self, lid: str) -> list[dict[str, Any]]:
        _acc, lc = self._lookup(lid)
        if lc is None:
            return []
        have = {g["appid"] for g in lc["games"]}
        out = []
        for name in list_launcher_games(lc["type"]):
            appid = synthetic_appid(lc["type"], name)
            out.append({"name": name, "appid": appid, "dup": appid in have})
        return out

    def add_game(self, lid: str, name: str, appid: Optional[int]) -> dict[str, Any]:
        acc, lc = self._lookup(lid)
        if acc is None or lc is None:
            return {"error": "That launcher no longer exists."}
        name = name.strip()
        if not name:
            return {"error": "Type the game's title first."}
        if appid is None:
            if lc["type"] == "steam":
                return {"error": "Pick a game from the list first."}
            appid = synthetic_appid(lc["type"], name)
        appid = int(appid)
        if not self.cfg.add_game(acc["id"], lid, appid, name):
            return {"error": "That game is already in this launcher."}
        log(f"Added {name}")
        self.photos.request(appid)
        return self.reply()

    def _find_game(self, lid: str, appid: int) -> tuple[Optional[dict[str, Any]], Optional[dict[str, Any]]]:
        acc, lc = self._lookup(lid)
        g = next((x for x in (lc["games"] if lc else []) if x["appid"] == appid), None)
        return acc, g

    def game_detail(self, lid: str, appid: int) -> dict[str, Any]:
        _acc, g = self._find_game(lid, appid)
        if g is None:
            return {"error": "That game no longer exists."}
        return {"name": g["name"], "enabled": bool(g["enabled"]), "weekly": format_weekly_text(g["weekly"]),
                "dates": "\n".join(g["dates"]), "keywords": "\n".join(g["photo_keywords"])}

    def save_game(self, lid: str, appid: int, enabled: bool, weekly: str, dates: str, keywords: str) -> dict[str, Any]:
        acc, g = self._find_game(lid, appid)
        if acc is None or g is None:
            return {"error": "That game no longer exists."}
        try:
            wk = parse_weekly_text(weekly)
            dt = parse_dates_text(dates)
        except ValueError as exc:
            return {"error": str(exc)}
        kws = [k.strip() for k in keywords.splitlines() if k.strip()]
        changed = kws != g["photo_keywords"]
        g = copy.deepcopy(g)
        g.update({"enabled": bool(enabled), "weekly": wk, "dates": dt, "photo_keywords": kws or [g["name"]]})
        self.cfg.update_game(acc["id"], lid, g)
        log(f"Saved schedule for {g['name']}")
        if changed:
            self.photos.request(appid, force=True)
        return self.reply()

    def remove_game(self, lid: str, appid: int) -> dict[str, Any]:
        acc, g = self._find_game(lid, appid)
        if acc is None or g is None:
            return self.reply()
        if self.cfg.remove_game(acc["id"], lid, appid):
            shutil.rmtree(photo_dir(appid), ignore_errors=True)
        log(f"Removed game {g['name']}")
        return self.reply()

    def add_images(self, appid: Any) -> dict[str, Any]:
        w = self.main
        if w is None or webview is None:
            return {"added": 0}
        fd = getattr(webview, "FileDialog", None)
        res = w.create_file_dialog(fd.OPEN if fd else webview.OPEN_DIALOG, allow_multiple=True,
                                   file_types=("Images (*.jpg;*.jpeg;*.png;*.webp;*.bmp)", "All files (*.*)"))
        if not res:
            return {"added": 0}
        return self.import_images([Path(p) for p in res], appid)

    def import_images(self, paths: list[Path], appid: Any, title: str = "") -> dict[str, Any]:
        d = photo_dir(appid)
        d.mkdir(parents=True, exist_ok=True)
        index = load_index(appid)
        have = {e.get("page") for e in index}
        added = 0
        for p in paths:
            page = "file:" + str(p)
            if page in have:
                continue
            try:
                name = import_image(p, d)
            except OSError:
                name = None
            if name:
                index.append({"file": name, "title": (title or p.stem)[:80], "author": "You", "license": "Your own image",
                              "license_url": "", "page": page, "source": OWN_SRC})
                have.add(page)
                added += 1
        write_json(d / "index.json", index)
        if added:
            log(f"Added {added} of your own image(s)")
            self.screen_appid = 0
            self._covers.pop(appid, None)
            self.push("rows", self.rows())
        return {"added": added, "skipped": len(paths) - added}

    def check_now(self, appid: Optional[int]) -> dict[str, Any]:
        self.engine.request_check(int(appid) if appid is not None else None)
        log("Manual check requested" + (f" for app {appid}" if appid else " for all games"))
        return {"ok": True}

    # ---- settings
    def save_settings(self, values: dict[str, Any]) -> dict[str, Any]:
        with self.cfg.lock:
            for k, v in values.items():
                if k in DEFAULT_SETTINGS:
                    self.cfg.settings[k] = coerce_setting(k, v)
            s = self.cfg.settings
            if s["after_action"] not in POWER_ACTIONS:
                s["after_action"] = DEFAULT_SETTINGS["after_action"]
            if s["loading_screen"] not in ("auto", "fullscreen", "windowed", "off"):
                s["loading_screen"] = "auto"
            if s["saver_others"] not in ("keep", "dim", "black"):
                s["saver_others"] = "dim"
            if s["saver_source"] not in ("gaus", "mine"):
                s["saver_source"] = "gaus"
        self.cfg.save()
        set_autostart(bool(self.cfg.settings["start_with_windows"]))
        self.after_accounts_changed()
        log("Settings saved")
        return self.reply()

    def set_paused(self, paused: bool) -> None:
        with self.cfg.lock:
            self.cfg.settings["paused"] = bool(paused)
        self.cfg.save()
        self.push("paused", bool(paused))
        self.after_accounts_changed()
        log("Scheduling paused" if paused else "Scheduling resumed")

    def wake_check(self) -> dict[str, Any]:
        if not IS_WINDOWS:
            return {"message": "Wake timers only work on Windows."}
        val = wake_timers_ac_setting()
        if val is None:
            return {"message": "Could not read the Windows power setting 'Allow wake timers'. Use 'Test wake' to check directly."}
        if val == 1:
            return {"message": "Windows 'Allow wake timers' is Enabled (plugged in).\n\nUse 'Test wake' to confirm that this PC's hardware really wakes up."}
        names = {0: "Disabled", 2: "Important wake timers only"}
        return {"fixable": True, "message": f"Windows 'Allow wake timers' is currently: {names.get(val, val)} (plugged in).\n\nThe scheduler needs it Enabled. Change it now?"}

    def wake_fix(self) -> dict[str, Any]:
        enable_wake_timers()
        if wake_timers_ac_setting() == 1:
            return {"message": "Done - 'Allow wake timers' is now Enabled."}
        return {"message": "Windows did not accept the change (a work or admin policy may control it).\nSet it yourself: Control Panel > Power Options > Change plan settings > Change advanced power settings > Sleep > Allow wake timers > Enable."}

    def wake_test(self) -> dict[str, Any]:
        res = self.engine.test_wake(120)
        if res == "ok":
            return {"message": "Wake test armed.\n\nPut the PC to sleep NOW (Start > Power > Sleep). It should wake by itself in about 2 minutes (the screen may stay dark). Then open the Log tab and look for \"Wake timer 'test' fired\"."}
        if res == "unsupported":
            return {"message": "Windows says this PC does not support waking from sleep with a timer. You can still try the test."}
        return {"message": f"Could not arm the test: {res}"}

    def open_data_folder(self) -> dict[str, Any]:
        try:
            if IS_WINDOWS:
                os.startfile(str(APP_DIR))  # type: ignore[attr-defined]
            else:
                subprocess.Popen(["xdg-open", str(APP_DIR)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except OSError as exc:
            return {"error": str(exc)}
        return {"ok": True}

    # ---- app self-update
    def check_updates(self, manual: bool = False) -> None:
        settings = self.cfg.settings
        if not manual and not settings["auto_update_check"]:
            return
        if self.update_busy:
            return
        url = effective_feed(settings)
        if not url:
            if manual:
                self.push("notice", "No update feed is set yet. Paste the update.json link into Settings > Update feed URL.")
            return
        self.update_busy = True
        threading.Thread(target=self._check_run, args=(url, manual), daemon=True, name="update-check").start()

    def _check_run(self, url: str, manual: bool) -> None:
        try:
            info, err = fetch_update_manifest(url), None
        except Exception as exc:
            info, err = None, exc
        self.update_busy = False
        self._update_checked(info, err, manual)

    def _update_checked(self, info: Any, err: Any, manual: bool) -> None:
        if err is not None:
            log(f"App update check failed: {err}")
            if manual:
                self.push("notice", f"Could not check for updates:\n{err}")
            return
        if version_tuple(info["version"]) > version_tuple(APP_VERSION):
            first = self.update_info is None or self.update_info["version"] != info["version"]
            self.update_info = info
            self.push("update", info)
            self.after_accounts_changed()
            log(f"App update available: version {info['version']}")
            if first:
                auto = self.cfg.settings["auto_install_updates"] and is_frozen()
                self.on_notify("Gaus update available",
                               f"Version {info['version']} is out. " +
                               ("It installs by itself, and any game download keeps going." if auto
                                else "Open Gaus to install it."))
            if manual:
                self.show_window()
            self._auto_install_tick()
        else:
            self.update_info = None
            self.push("update", None)
            self.after_accounts_changed()
            log("The app is up to date")
            if manual:
                self.push("notice", f"You are on the latest version ({APP_VERSION}).")

    def _idle_for_install(self) -> bool:
        """A game download doesn't matter: the launcher does that work, and Gaus picks it back up after restarting.
        Only things Gaus itself is in the middle of have to finish first."""
        e = self.engine
        return (e.shutdown is None and not e.run_results
                and self.countdown is None and not self.preview_active and not self.saver_on and not self.install_busy)

    def _auto_install_tick(self) -> None:
        """Remote updates: when a newer version has been published, install it quietly,
        so it never needs anyone to click."""
        if (self.update_info is not None and self.cfg.settings["auto_install_updates"] and is_frozen()
                and self._idle_for_install()):
            log("Installing the new app version automatically")
            self.install_update(silent=True)

    def install_update(self, silent: bool = False) -> dict[str, Any]:
        info = self.update_info
        if info is None:
            return {"error": "No update is available."}
        if self.install_busy:
            return {"error": "An update is already being installed."}
        if not is_frozen():
            return {"error": "Self-update only works in the built .exe. In this script version, copy the new gaus.pyw and web folder over the old ones."}
        self.install_busy = True
        threading.Thread(target=self._install_run, args=(info, silent), daemon=True, name="self-update").start()
        return {"started": True}

    def _install_run(self, info: dict[str, str], silent: bool) -> None:
        last = [-1]

        def prog(p: int) -> None:
            if not silent and p != last[0]:
                last[0] = p
                self.push("installProgress", int(p))

        try:
            download_and_swap(info, prog)
            err: Optional[Exception] = None
        except Exception as exc:
            err = exc
        self._install_done(err, silent)

    def _install_done(self, err: Optional[Exception], silent: bool) -> None:
        self.install_busy = False
        if err is not None:
            log(f"App update failed: {err}")
            if not silent:
                self.push("installFailed", str(err))
            return
        log("App update installed - restarting")
        self.engine.save_resume()
        if self.instance_lock is not None:
            self.instance_lock.release()
        try:
            relaunch_self(not self.parked)
        except OSError as exc:
            log(f"Could not restart automatically: {exc}")
        self.quit("restarting to install an update")

    def background_loop(self) -> None:
        """Replaces the old timers: look for app updates now and then, and install quietly when idle."""
        t0 = time.monotonic()
        next_check = t0 + 20
        next_install = t0 + 120
        while not self.stop_evt.wait(5):
            now = time.monotonic()
            if now >= next_check:
                next_check = now + UPDATE_CHECK_SECONDS
                self.check_updates(manual=False)
            if now >= next_install:
                next_install = now + 120
                self._auto_install_tick()

    # ---- loading screen
    def _prepare_screen(self, appid: int, name: str) -> None:
        if self.screen_appid != appid or not self.screen.entries:
            self.screen.set_slides(appid, get_slides(appid), float(self.cfg.settings["slide_seconds"]))
            self.screen_appid = appid
        self.screen.set_state({"game": name})

    def _present(self) -> None:
        mode = self.cfg.settings["loading_screen"]
        if mode == "off" or self.screen.visible:
            return
        if mode == "fullscreen":
            full = True
        elif mode == "windowed":
            full = False
        else:
            full = user_idle_seconds() >= 120
        self.screen.present(full)

    def _start_hide(self, seconds: float) -> None:
        if self._hide_timer is not None:
            self._hide_timer.cancel()
        self._hide_timer = threading.Timer(seconds, self._maybe_hide)
        self._hide_timer.daemon = True
        self._hide_timer.start()

    def _stop_hide(self) -> None:
        if self._hide_timer is not None:
            self._hide_timer.cancel()
            self._hide_timer = None

    # ---- screen saver: the loading screen, fullscreen and darkened, for a download being tracked
    def on_live(self, items: list[dict[str, Any]]) -> None:
        self.push("live", items)
        self.saver_asked &= {i["appid"] for i in items}
        for i in items:
            if i["tracked"] and i["progress"] is not None and i["appid"] not in self.saver_asked:
                self.saver_asked.add(i["appid"])
                if (time.time() >= self.no_prompt_until and self.cfg.settings["saver_ask"] and not self.saver_on
                        and not self.screen.visible and running_app_id() == 0):
                    self.pending_prompt = i      # the page may need to load first, so it arrives with the state
                    self.show_window()

    def saver_images(self) -> list[dict[str, str]]:
        return self._own_images(SAVER_KEY)

    def remove_saver_image(self, file: str) -> list[dict[str, str]]:
        return self._remove_own_image(SAVER_KEY, file)

    def _own_images(self, key: str) -> list[dict[str, str]]:
        return [{"file": e["file"], "title": e.get("title", ""), "url": f"/photos/{key}/{urllib.parse.quote(e['file'])}"}
                for e in photo_entries(key)]

    def _remove_own_image(self, key: str, file: str) -> list[dict[str, str]]:
        index = load_index(key)
        keep = [e for e in index if e.get("file") != file]
        if len(keep) != len(index):       # only a name from the list is ever deleted
            try:
                (photo_dir(key) / file).unlink()
            except OSError:
                pass
            write_json(photo_dir(key) / "index.json", keep)
        return self._own_images(key)

    # ---- favourite character: the player picks one and adds its art; with none picked the official art rotates
    def favourite(self, appid: int, hero: str = "") -> dict[str, Any]:
        """The pictures for one character: the one named, or else the game's favourite."""
        name = hero or favourite_of(appid)
        return {"name": name, "roster": ROSTERS.get(appid, []), "images": self._own_images(favourite_key(appid, name)) if name else []}

    def _favourite_changed(self, appid: int, hero: str = "") -> dict[str, Any]:
        self._covers.pop(appid, None)
        self.screen_appid = 0
        if self.ui_ready.is_set():
            self.push("rows", self.rows())
        return self.favourite(appid, hero)

    def set_favourite(self, appid: int, name: str) -> dict[str, Any]:
        data = read_json(FAVOURITES_PATH, {})
        data = data if isinstance(data, dict) else {}
        name = name.strip()[:60]
        if name:
            data[str(appid)] = name
        else:
            data.pop(str(appid), None)
        write_json(FAVOURITES_PATH, data)
        log(f"Favourite character for game {appid}: {name or 'none'}")
        return self._favourite_changed(appid)

    def add_favourite_images(self, appid: int, hero: str = "") -> dict[str, Any]:
        name = hero or favourite_of(appid)
        if not name:
            return {"error": "Choose a character first."}
        res = self.add_images(favourite_key(appid, name))
        return {**res, **self._favourite_changed(appid, hero)}

    def remove_favourite_image(self, appid: int, file: str, hero: str = "") -> dict[str, Any]:
        self._remove_own_image(favourite_key(appid, hero or favourite_of(appid)), file)
        return self._favourite_changed(appid, hero)

    def patch_notes(self, appid: int) -> dict[str, Any]:
        """Fetched only when someone opens them, so nothing runs in the background."""
        game = self.cfg.get_game(appid)
        site = NEWS_PAGES.get(appid, "")
        out: dict[str, Any] = {"notes": [], "site": site, "steam": bool(game and game.get("launcher") == "steam")}
        self._news_links = {site} if site else set()
        if out["steam"]:
            try:
                out["notes"] = fetch_patch_notes(appid)
                self._news_links |= {n["url"] for n in out["notes"] if n["url"].startswith("https://")}
                for note in out["notes"]:
                    for hero in note["heroes"]:      # the player's own picture of this character, if they added one
                        pictures = self._own_images(favourite_key(appid, hero["name"]))
                        hero["image"] = pictures[0]["url"] if pictures else ""
            except Exception as exc:
                log(f"Could not get patch notes for game {appid}: {exc!r}")
                out["error"] = "Couldn't get the patch notes. Check your internet connection and try again."
        return out

    def open_official(self, kind: str) -> dict[str, Any]:
        """Shows the publisher's page in its own window, with no access to Gaus's functions. Closing it frees its memory."""
        if kind not in OFFICIAL_PAGES or webview is None:
            return {"error": "That page isn't available."}
        win = self._official.get(kind)
        if win is not None:
            win.restore()
            win.show()
            return {"ok": True}
        title, url = OFFICIAL_PAGES[kind]
        win = webview.create_window(title, url=url, width=1280, height=840, background_color="#0f1422")
        self._official[kind] = win
        win.events.closed += lambda: self._official.pop(kind, None)
        return {"ok": True}

    def open_news(self, url: str) -> dict[str, Any]:
        if url not in self._news_links:     # only links the patch notes list just gave us
            return {"error": "That link isn't available."}
        webbrowser.open(url)
        return {"ok": True}

    def find_art(self, appid: int, site: str, hero: str = "") -> dict[str, Any]:
        game, name = self.cfg.get_game(appid), hero or favourite_of(appid)
        if game is None or not name or site not in ART_SEARCHES:
            return {"error": "Choose a character first."}
        webbrowser.open(ART_SEARCHES[site] + urllib.parse.quote_plus(f"{name} {game['name']} art"))
        return {"ok": True}

    def _add_favourite_picture(self, appid: int, data: bytes, title: str, hero: str = "") -> dict[str, Any]:
        """A picture the player dragged or pasted in. It goes through the same checks as a file they pick."""
        name = hero or favourite_of(appid)
        if not name:
            return {"error": "Choose a character first."}
        if len(data) > MAX_PICTURE_BYTES:
            return {"error": "That picture is too large (the limit is 30 MB)."}
        folder = APP_DIR / "incoming"
        folder.mkdir(parents=True, exist_ok=True)
        src = folder / hashlib.sha1(data).hexdigest()[:16]    # the same picture twice is noticed and skipped
        src.write_bytes(data)
        try:
            key = favourite_key(appid, name)
            res = self.import_images([src], key, title or name)
            res["duplicate"] = not res.get("added") and any(e.get("page") == f"file:{src}" for e in load_index(key))
        finally:
            src.unlink(missing_ok=True)
        return {**res, **self._favourite_changed(appid, hero)}

    def add_favourite_data(self, appid: int, data_url: str, title: str, hero: str = "") -> dict[str, Any]:
        try:
            data = base64.b64decode(data_url.split(",", 1)[-1], validate=True)
        except ValueError:
            return {"error": "That didn't come through as a picture."}
        return self._add_favourite_picture(appid, data, title, hero)

    def add_favourite_url(self, appid: int, url: str, hero: str = "") -> dict[str, Any]:
        """A plain public download, with no login. If a site protects the picture this fails, and the player
        can drag or copy it from their own browser instead."""
        help_text = ("Gaus couldn't get a picture from that link. If the site needs you to sign in, "
                     "sign in with your browser, then drag the picture here or copy and paste it.")
        if not url.lower().startswith(("https://", "http://")):
            return {"error": help_text}
        try:
            data = http_get(url, timeout=30, max_bytes=MAX_PICTURE_BYTES)
        except Exception:
            return {"error": help_text}
        res = self._add_favourite_picture(appid, data, Path(urllib.parse.urlsplit(url).path).stem[:80], hero)
        return {**res, "error": help_text} if res.get("skipped") and not res.get("added") and not res.get("duplicate") else res

    def start_saver(self, appid: int, dim: int, others: str, source: str, ask: bool) -> dict[str, Any]:
        game = self.cfg.get_game(appid)
        if game is None:
            return {"error": "That game no longer exists."}
        dim = max(0, min(90, dim))
        mine = photo_entries(SAVER_KEY) if source == "mine" else []
        if source == "mine" and not mine:
            return {"error": "Add some pictures for your screen saver first."}
        with self.cfg.lock:
            self.cfg.settings.update(saver_dim=dim, saver_others=others if others in ("keep", "dim", "black") else "dim",
                                     saver_source="mine" if mine else "gaus", saver_ask=ask)
        self.cfg.save()
        self._end_saver()
        self.screen.hide()
        self._stop_hide()
        self.saver_on = True
        self.run_dismissed = False
        self.screen_appid = 0
        if mine:
            random.shuffle(mine)
            self.screen.set_slides(appid, mine, float(self.cfg.settings["slide_seconds"]))
            self.screen_appid = appid
        self._prepare_screen(appid, game["name"])
        self.screen.set_state({"dim": dim / 100, "saver": True, "label": "UPDATING"})
        self.screen.present(True)
        if self.cfg.settings["saver_others"] != "keep":
            self.dimmer.show(255 if self.cfg.settings["saver_others"] == "black" else 200)
        minimize_windows_of(list(Launcher(game).procs()))    # the screen saver shows the same numbers
        log(f"{game['name']}: screen saver started")
        return self.reply()

    def _end_saver(self) -> None:
        if self.saver_on:
            self.saver_on = False
            self.screen_appid = 0        # the next loading screen goes back to the game's own art
            self.dimmer.hide()
            self.screen.set_state({"dim": 0, "saver": False})

    def on_progress(self, p: dict) -> None:
        if self.preview_active:
            return
        state = p.get("state")
        if (state == "active" and (not p.get("tracked") or self.saver_on)
                and p.get("phase") in ("launching", "downloading")):
            self._stop_hide()
            self._prepare_screen(p["appid"], p["game"])
            label = (f"STARTING {str(p.get('launcher') or 'LAUNCHER').upper()}" if p["phase"] == "launching"
                     else "UPDATING")
            self.screen.set_state({"label": label, "detail": p["detail"], "progress": p["progress"], "note": p.get("note", "")})
            if not self.run_dismissed:
                self._present()
        elif state == "finished":
            if self.screen.visible:
                self._prepare_screen(p["appid"], p["game"])
                self.screen.set_state({"label": p["label"], "detail": p["detail"], "progress": p["progress"], "note": p.get("note", "")})
                self._start_hide(15)
        elif state == "idle":
            self.run_dismissed = False
            if self.screen.visible and self._hide_timer is None and self.countdown is None:
                self._start_hide(8)

    def screen_dismissed_by_user(self) -> None:
        self.screen.hide()
        self._dismissed()

    def screen_closed_by_user(self) -> None:
        self._dismissed()

    def _dismissed(self) -> None:
        self._end_saver()
        if self.preview_active:
            self.preview_active = False
        else:
            self.run_dismissed = True

    def _maybe_hide(self) -> None:
        self._hide_timer = None
        if self.countdown is None and not self.preview_active:
            self._end_saver()
            self.screen.hide()

    def show_screen_now(self) -> None:
        if self.screen.entries or self.screen_appid:
            self.run_dismissed = False
            self._present()
        else:
            _s, games = self.cfg.snapshot()
            if games:
                self.preview(games[0]["appid"])

    def preview(self, appid: int) -> dict[str, Any]:
        game = self.cfg.get_game(appid)
        if game is None:
            return {"error": "That game no longer exists."}
        message = None
        if self.photos.count(appid) == 0:
            self.photos.request(appid)
            message = ("No photos downloaded for this game yet. They are being fetched now - preview again in a "
                       "minute. (Showing the fallback background meanwhile.)")
        self.preview_active = True
        self.screen_appid = appid
        self.screen.set_slides(appid, get_slides(appid), float(self.cfg.settings["slide_seconds"]))
        self.screen.set_state({"game": game["name"], "label": "PREVIEW", "progress": 0.42,
                               "detail": "42%  ·  27.3 GB of 65.0 GB  ·  18.4 MB/s   (sample - press Esc to close)",
                               "note": power_note(self.cfg.settings)})
        self.screen.present(False)
        return {"ok": True, "message": message}

    # ---- shutdown countdown
    def on_countdown(self, seconds: int, names: str, action: str) -> None:
        if self.countdown is not None:
            return
        self.countdown = Countdown(self, seconds, names, action)
        self.countdown.start()

    def countdown_payload(self) -> dict[str, Any]:
        return self.countdown.payload() if self.countdown is not None else {"remaining": 0, "total": 1, "verb": "shut down", "names": ""}

    def countdown_cancel(self) -> None:
        if self.countdown is not None:
            self.countdown.cancel_evt.set()

    def countdown_end(self, proceed: bool) -> None:
        self.countdown = None
        self.engine.countdown_done(proceed)
        if not proceed:
            self._start_hide(2)

    # ---- tray
    def build_tray(self, pystray: Any, image_mod: Any) -> None:
        img = image_mod.open(io.BytesIO(brand_bytes("icon"))).convert("RGBA")
        item = pystray.MenuItem

        def accounts_menu():  # type: ignore[no-untyped-def]
            def make(aid: str):  # type: ignore[no-untyped-def]
                # pystray only accepts callbacks taking (icon, item) - no default arguments
                return (lambda _i, _it: self._tray_switch(aid)), (lambda _it: aid == self.cfg.active)
            for a in self.cfg.tree():
                action, is_on = make(a["id"])
                yield item(a["name"] + ("" if a["enabled"] else " (off)"), action, checked=is_on, radio=True)

        menu = pystray.Menu(
            item("Open", lambda _i, _it: self.show_window(), default=True),
            item("Account", pystray.Menu(accounts_menu)),
            item("Check all games now", lambda _i, _it: self.check_now(None)),
            item("Show loading screen", lambda _i, _it: self.show_screen_now()),
            item("Install app update...", lambda _i, _it: (self.show_window(), self.push("askInstall")),
                 visible=lambda _it: self.update_info is not None),
            item("Pause scheduling", lambda _i, _it: self.set_paused(not self.cfg.settings["paused"]),
                 checked=lambda _it: bool(self.cfg.settings["paused"])),
            pystray.Menu.SEPARATOR,
            item("Quit", lambda _i, _it: self.quit("Quit was chosen in the tray")))
        self.tray = pystray.Icon("Gaus", img, APP_TITLE, menu)

    def _tray_switch(self, aid: str) -> None:
        self.switch_account(aid)
        self.push("state", self.state())


# --------------------------------------------------------------------------- entry point
def _install_excepthooks() -> None:
    def hook(exc_type, exc, tb) -> None:
        log("Unhandled error:\n" + "".join(traceback.format_exception(exc_type, exc, tb)))

    sys.excepthook = hook
    threading.excepthook = lambda a: hook(a.exc_type, a.exc_value, a.exc_traceback)


def main() -> int:
    global webview
    APP_DIR.mkdir(parents=True, exist_ok=True)
    _install_excepthooks()
    migrate_old_data()
    trim_log()
    cleanup_old_update_files()
    lock = InstanceLock(LOCK_PATH)
    # right after a self-update the old copy is still shutting down, so wait for it
    if not lock.acquire(15 if "--after-update" in sys.argv else 0.3):
        message_box(f"{APP_TITLE} is already running (check the system tray).")
        return 0
    try:
        import webview as wv  # type: ignore
        import pystray  # type: ignore
        from PIL import Image  # type: ignore
    except ImportError as exc:
        message_box(f"A required package is missing: {exc}\n\nRun:  pip install pywebview pystray pillow psutil")
        lock.release()
        return 1
    webview = wv

    cfg = Config.load()
    photos = PhotoManager(cfg)
    engine = Engine(cfg)
    server = AssetServer()
    ctl = Controller(cfg, engine, photos, server, lock)
    ctl.build_tray(pystray, Image)

    # after an update it comes back as it was: an open window stays open, and none pops up in the middle of a game
    minimized = "--minimized" in sys.argv or ("--after-update" in sys.argv and "--show" not in sys.argv)
    splash = None
    if not minimized:
        try:
            lw, lh = Image.open(io.BytesIO(brand_bytes("logo"))).size
        except Exception:
            lw, lh = 520, 200
        scaled = int(400 * lh / max(1, lw))
        splash = ctl.new_window("splash.html", width=456, height=scaled + 112, frameless=True, on_top=True,
                                resizable=False, easy_drag=False, background_color="#0f1422")
    ctl.main = ctl.new_window("index.html", title=f"{APP_TITLE}  v{APP_VERSION}", width=1180, height=780,
                              min_size=(940, 620), hidden=True, background_color="#0f1422",
                              **({"url": "about:blank"} if minimized else {}))
    if minimized:                        # started into the tray: load the page only when someone opens it
        ctl.parked = True
        ctl._settle_later()

    def on_closing() -> bool:
        if ctl.quitting:
            return True
        try:
            ctl.main.hide()
        except Exception:
            pass
        threading.Thread(target=ctl.park, daemon=True, name="park").start()
        return False

    ctl.main.events.closing += on_closing

    _s, games = cfg.snapshot()
    for g in games:
        no_official = g.get("launcher") == "steam" and not any(
            e.get("source") == STEAM_SRC for e in load_index(g["appid"]))
        if photos.count(g["appid"]) < MIN_GAME_PHOTOS or no_official:
            photos.request(g["appid"])
    engine.start()

    def tray_main() -> None:
        try:
            def ready(icon: Any) -> None:
                icon.visible = True
                log("Tray icon is visible (look for it in the taskbar's hidden-icons area)")
                if "--after-update" in sys.argv:
                    ctl.on_notify("Gaus updated", f"You are now on version {APP_VERSION}.")
            ctl.tray.run(ready)
        except Exception:
            log("The tray icon could not start:\n" + traceback.format_exc())

    threading.Thread(target=tray_main, daemon=True, name="tray").start()
    threading.Thread(target=ctl.background_loop, daemon=True, name="app-updates").start()

    def boot() -> None:
        if splash is not None:
            time.sleep(2.3)
            try:
                splash.destroy()
            except Exception:
                pass
            ctl.show_window()

    try:
        webview.start(boot, debug=False)
    except Exception as exc:
        log(f"The window could not start: {exc!r}\n{traceback.format_exc()}")
        message_box("The Gaus window could not start. It needs Microsoft Edge WebView2 (it is included with "
                    f"Windows 11 and Microsoft Edge).\n\n{exc}")
    ctl.quit("the app window closed")
    engine.stop()
    lock.release()
    return 0


# --------------------------------------------------------------------------- embedded artwork
# The icon and the splash logo are built in so the app does not need image files. To try other artwork
# without rebuilding, drop gaus_icon.png / gaus_logo.png into the data folder; those are used first.
_ICON_B64 = (
    "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"
    "/j8GpudqQXMcXwAAAABJRU5ErkJggg=="
)
_LOGO_B64 = (
    "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"
)


if __name__ == "__main__":
    sys.exit(main())
