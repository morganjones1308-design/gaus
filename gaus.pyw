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
APP_VERSION = "1.6"
USER_AGENT = f"Gaus/{APP_VERSION} (personal home app; Python urllib)"
SAST = timezone(timedelta(hours=2), "SAST")

APP_DIR = Path(os.environ.get("GAUS_HOME") or (Path(os.environ.get("APPDATA") or Path.home()) / "Gaus"))
OLD_APP_DIR = Path(os.environ.get("APPDATA") or Path.home()) / "SteamUpdateScheduler"   # earlier name, migrated once
PHOTO_DIR = APP_DIR / "photos"
CONFIG_PATH = APP_DIR / "config.json"
STATE_PATH = APP_DIR / "state.json"
LOG_PATH = APP_DIR / "scheduler.log"
LOCK_PATH = APP_DIR / "app.lock"
GENERIC_KEY = "_generic"

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
    "remote_check": True,
    "remote_poll_seconds": 180,
    "start_early_minutes": 5,
    "watch_minutes": 180,
    "stall_minutes": 20,
    "max_download_hours": 8,
    "shutdown_enabled": True,
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
    "auto_install_updates": True,       # install a new app version by itself when nothing is downloading
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
                "path": f, "name": vget(state, "name", ""),
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
    _run_hidden(["shutdown", "/s", "/t", "10", "/c", "Gaus: game updates finished"])


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


def set_autostart(enabled: bool) -> None:
    if winreg is None:
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


def relaunch_self() -> None:
    env = dict(os.environ)
    env["PYINSTALLER_RESET_ENVIRONMENT"] = "1"   # lets a one-file build start a fresh, independent copy
    flags = (DETACHED_PROCESS | 0x00000200) if IS_WINDOWS else 0
    subprocess.Popen([sys.executable, "--after-update"], env=env, creationflags=flags, close_fds=True)


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


def get_slides(appid: int) -> list[dict[str, Any]]:
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
                 window_end: Optional[datetime]) -> None:
        self.game = game
        self.appid = int(game["appid"])
        self.name = str(game["name"])
        self.key = key
        self.manual = manual
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
            try:
                self.tick()
            except Exception:
                log("Engine error:\n" + traceback.format_exc())
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

        with self.lock:
            requests, self.manual_requests = self.manual_requests, []
        for appid in requests:
            for g in games:
                if (appid is None or g["appid"] == appid) and g["appid"] not in self.sessions:
                    self._begin(g, f"manual|{g['appid']}|{now.isoformat()}", True, None)

        if not settings["paused"]:
            handled = self.state["handled"]
            for g in games:
                if g["enabled"] and g["appid"] not in self.sessions:
                    t = active_trigger(g, now, settings, handled)
                    if t:
                        end = t + timedelta(minutes=int(settings["watch_minutes"]))
                        self._begin(g, trigger_key(g["appid"], t), False, end)

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
                or self.shutdown is not None or bool(self.run_results))
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
    def _begin(self, game: dict[str, Any], key: str, manual: bool, end: Optional[datetime]) -> None:
        s = Session(game, key, manual, end)
        self.sessions[s.appid] = s
        if manual:
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
            if t - s.launch_time > 60:
                log(f"{s.name}: Steam is no longer running - restarting it")
                s.phase = "launching"
            return
        sig = (m["state"], m["buildid"], m["target"], m["dl"], m["staged"])
        if sig != s.sig:
            s.sig = sig
            s.last_change = t
        busy = manifest_busy(m)
        if busy or m["buildid"] != s.initial_build:
            s.saw_activity = True
        total = m["to_dl"] + m["to_stage"]
        done = m["dl"] + m["staged"]
        if busy and total > 0:
            s.bytes_total, s.bytes_done = total, done
            s.progress = max(0.0, min(1.0, done / total))
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
        if manifest_idle(m) and (s.saw_activity or (target and m["buildid"] == target)):
            s.progress = 1.0
            self._finish(s, "updated", f"now on build {m['buildid']}")
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
            if updated and not failed and not manual and settings["shutdown_enabled"]:
                self.shutdown = {"phase": "waiting", "since": time.time()}
                log("All updates finished - waiting for the PC to be idle before powering down")
            else:
                if updated and manual:
                    log("Manual check - the PC will not be shut down automatically")
                elif updated and failed:
                    log("An update failed - leaving the PC on")
                self.run_results = []
            return
        sd = self.shutdown
        now = time.time()
        if sd["phase"] == "waiting":
            idle_ok = user_idle_seconds() >= int(settings["shutdown_idle_minutes"]) * 60
            if idle_ok and running_app_id() == 0:
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
                    status = f"Downloading {s.progress * 100:.0f}%"
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
        note = power_note(settings)
        if active:
            s = next((x for x in active if x.phase == "downloading"), active[0])
            if s.phase == "launching":
                detail, prog = f"Starting {s.lc.name}...", None
            elif s.phase == "downloading" and not s.lc.precise:
                if s.saw_activity:
                    detail = f"{s.lc.name} is updating" + (f"  \u00b7  {fmt_bytes(s.speed)}/s" if s.speed > 0 else "")
                else:
                    detail = f"Waiting for {s.lc.name} to start the update..."
                prog = None
            elif s.phase == "downloading" and s.saw_activity and s.bytes_total > 0:
                detail = f"{s.progress * 100:.0f}%  \u00b7  {fmt_bytes(s.bytes_done)} of {fmt_bytes(s.bytes_total)}"
                if s.speed > 0:
                    detail += f"  \u00b7  {fmt_bytes(s.speed)}/s"
                prog = s.progress
            elif s.phase == "downloading":
                detail, prog = "Waiting for Steam to start the update...", None
            else:
                detail, prog = "Watching for the update...", None
            emit("progress", {"state": "active", "appid": s.appid, "game": s.name, "phase": s.phase, "launcher": s.lc.name,
                              "progress": prog, "detail": detail, "note": note, "count": len(active)})
        elif finished_now:
            s = finished_now[-1]
            label = {"updated": "UPDATE COMPLETE", "up-to-date": "UP TO DATE", "failed": "UPDATE FAILED",
                     "skipped": "SKIPPED"}.get(s.result or "", "DONE")
            emit("progress", {"state": "finished", "appid": s.appid, "game": s.name, "phase": "finished", "launcher": s.lc.name,
                              "label": label, "progress": 1.0 if s.result == "updated" else None,
                              "detail": s.msg, "note": note})
        else:
            emit("progress", {"state": "idle"})


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
        self.state: dict[str, Any] = {"game": "", "label": "UPDATING", "detail": "", "progress": None, "note": ""}
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
                                          resizable=False, easy_drag=False, background_color="#f6f4f0")
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
        self._hide_timer: Optional[threading.Timer] = None
        BUS.on("status", self.on_status)
        BUS.on("log", lambda line: self.push("log", line))
        BUS.on("progress", self.on_progress)
        BUS.on("countdown", self.on_countdown)
        BUS.on("notify", self.on_notify)
        BUS.on("photos_changed", lambda _a: self.push("rows", self.rows()))

    # ---- windows
    def new_window(self, page: str, **kw: Any) -> Any:
        title = kw.pop("title", APP_TITLE)
        return webview.create_window(title, url=self.server.url("ui/" + page), js_api=self.api, text_select=True, **kw)

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
        try:
            w.show()
            w.restore()
        except Exception:
            pass
        self.push("state", self.state())

    def quit(self) -> None:
        if self.quitting:
            return
        self.quitting = True
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
            "update": self.update_info, "first_run": bool(cfg.first_run),
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
                if not (acc["enabled"] and lc["enabled"] and g["enabled"]):
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
                    "photos": self.photos.count(g["appid"]), "status": status})
        return out

    def on_status(self, rows: dict) -> None:
        self.status = rows
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

    def add_images(self, appid: int) -> dict[str, Any]:
        w = self.main
        if w is None or webview is None:
            return {"added": 0}
        fd = getattr(webview, "FileDialog", None)
        res = w.create_file_dialog(fd.OPEN if fd else webview.OPEN_DIALOG, allow_multiple=True,
                                   file_types=("Images (*.jpg;*.jpeg;*.png;*.webp;*.bmp)", "All files (*.*)"))
        if not res:
            return {"added": 0}
        return self.import_images([Path(p) for p in res], appid)

    def import_images(self, paths: list[Path], appid: int) -> dict[str, Any]:
        d = photo_dir(appid)
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
                index.append({"file": name, "title": p.stem[:80], "author": "You", "license": "Your own image",
                              "license_url": "", "page": page, "source": OWN_SRC})
                have.add(page)
                added += 1
        write_json(d / "index.json", index)
        if added:
            log(f"Added {added} of your own image(s) to game {appid}")
            self.screen_appid = 0
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
                self.on_notify("Update available", f"Version {info['version']} is ready to install.")
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
        return (not any(s.phase != "done" for s in list(self.engine.sessions.values()))
                and self.engine.shutdown is None and self.countdown is None and not self.preview_active
                and not self.install_busy)

    def _auto_install_tick(self) -> None:
        """Remote updates: when a newer version has been published, install it quietly as soon as
        nothing is downloading, so it never needs anyone to click."""
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
        if any(s.phase != "done" for s in list(self.engine.sessions.values())):
            return {"error": "A game update is in progress. Install the app update when it has finished."}
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
        if self.instance_lock is not None:
            self.instance_lock.release()
        try:
            relaunch_self()
        except OSError as exc:
            log(f"Could not restart automatically: {exc}")
        self.quit()

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

    def on_progress(self, p: dict) -> None:
        if self.preview_active:
            return
        state = p.get("state")
        if state == "active" and p.get("phase") in ("launching", "downloading"):
            self._stop_hide()
            self._prepare_screen(p["appid"], p["game"])
            label = f"STARTING {str(p.get('launcher') or 'LAUNCHER').upper()}" if p["phase"] == "launching" else "UPDATING"
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
        if self.preview_active:
            self.preview_active = False
        else:
            self.run_dismissed = True

    def _maybe_hide(self) -> None:
        self._hide_timer = None
        if self.countdown is None and not self.preview_active:
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
            item("Quit", lambda _i, _it: self.quit()))
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

    minimized = "--minimized" in sys.argv
    splash = None
    if not minimized:
        try:
            lw, lh = Image.open(io.BytesIO(brand_bytes("logo"))).size
        except Exception:
            lw, lh = 520, 200
        scaled = int(400 * lh / max(1, lw))
        splash = ctl.new_window("splash.html", width=456, height=scaled + 112, frameless=True, on_top=True,
                                resizable=False, easy_drag=False, background_color="#f6f4f0")
    ctl.main = ctl.new_window("index.html", title=f"{APP_TITLE}  v{APP_VERSION}", width=1180, height=780,
                              min_size=(940, 620), hidden=True, background_color="#f6f4f0")

    def on_closing() -> bool:
        if ctl.quitting:
            return True
        try:
            ctl.main.hide()
        except Exception:
            pass
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
    ctl.quit()
    engine.stop()
    lock.release()
    return 0


# --------------------------------------------------------------------------- embedded artwork
# The icon and the splash logo are built in so the app does not need image files. To try other artwork
# without rebuilding, drop gaus_icon.png / gaus_logo.png into the data folder; those are used first.
_ICON_B64 = (
    "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"
)
_LOGO_B64 = (
    "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"
    "51eGP9CppD9VcTnVr9XObwqf4k+Wj3+TfLYz/Gm1/7M/V+k/ka+EL0TpyzWF8/FFqeFqLu8Ph49PLs+kvnllkr9Y+OpCDZ/Ax5vp"
    "qeUoyfhj6erz3x873KFwQr41/ODH1wEJgQkHpa2atm2buhQmLLCybpqmpLVjZOUfNhWRQpb0sJaW/lZJo+ioyr9Hyzoc4k9Vj6ey"
    "dzhYj6dT/nR1qehd9HZ+4YxKerHBl9X6x4oO59dLT4rJNY0X5U+TX79fVNOTyfGZv7Ab+4Om12t/yeGrl2p6fPh64zMVblH4WPsn"
    "t78/drhD/oT+u4lwr/yZxfh1RK5BQuCag2VzCmgrZqFfOPSszjyPbFaPj4c/Nxn/zS9Z2dJ7bK5N5s/g3+uPaK9P9Wu1q7LjcxBz"
    "y/7UEqksvz0br+IUPjAvGxceO88Ko2UzXsh4TfQJNuOLqjKrfry/ujyphKjHxx3z+Oc9oK/mvxhdVHvqSpldjveUEs3lWXi3DffC"
    "f0nbTj+2yqrzHaLzmHCvMquVrbtwTF97SQsSAlMh4JfdqamqqgnLhpZk3Xdd1xi/Y/tF5B92TDXR0EPPPvobkZCe0wrzb+i6yv9h"
    "cqq2vKWRes7w6bzkog/uRhL6t2dV7dH6z6V//fKmk9RVVdM56XC+kEYVnr/DhRi6fH7cSJ1fv58+qK0DKkUX6P/e8LbBIv4nCf3r"
    "AwnposLxDR3fV4I+Y3w3CV1SX+lje38Jtv71sY2w9H6+NeFe+TPn49fphu0DJAQugtCvjsaSPUMPaH3mfndvm1NHwox28q6lx5b/"
    "3J0acZaE/piu94SyJGj8ESSMGkMmmhdit1aa1v4Qf2rnJRezfyIJhZKSJVCV+UeFFzVdW5GdVbW8nCVdiP80L5iIKD1/gJes7alp"
    "mFiS3t9c3u8vlR5JcoYEeaSUpZM1v7YHE44eJCGTcDjef5FGST5r7t9NzGL9u+zc5WNVRncr8480S0Ii4anr+a4NktB/HX/t/HX4"
    "loGEwNXy84tCWEtCyiuXSvODugobNpOw6Ujf44Xa/yBhE5YYcUeG9SX5VCRwlP79aV4bbWidSmN+ktBqTUyjj9K6UK1jScInc14S"
    "00t0IYIWdNtcLu9UjW/SrDjyw0ArWbLPshiv2K+Cqu+JGykkFOGzm3I4K7371HttQV8+Vhj6WCYhf4EJCRu6gIGEXmt1fUVfR6uW"
    "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"
    "FY+Nby6nAAlBQiCNhaIsq1JRPWEx9F9im/CfQvL/i+IPpZIGRw5nlf7Dj8dXjRT/+BPYLEQkLmeATQgSAmkwRkkhtZn0ghoyP/WY"
    "/0ndpMaDL30sLr2YKNCRD8dczgDvKEgIJAvDpwmDdG2QEAAAkBAAQEIAAEBCAAAJAQAACQEAJAQAACQEAJAQAACQEABAQgAACQEA"
    "AAkBACQEAAAkBACQEAAAkBAAQEIAAEBCAAAJAQAACQEAJAQAACQEAJAQAACQEABAQgAAQEIAAAkBAAAJAQAkBLaDtsZYAk9cMsO/"
    "/OfzMWY8hP82PrN6eO1yFL3R2PHgMDbNWH0+4zhYLRxgr85mJp92nqtmMTkNJPx8hIGfWZaJQv8xNNKTiZJPp3fKy0TPYpzv6d9B"
    "4z4vxw2Pfg0QHc/IL8jrs6np2fRA1uGt48XhJwIJPxtGlE1AXRVK67ppKmELLenPlQy0UHVzhi3k+KwuhVF0XOmPC+8olSwvx1ZC"
    "VuFfW5jwQq2sqC5HlNKez1ZJHpttRM0fbYaLq22OmYYg4SfDZtVpRFMWwj9rS2lsVvvndhgmr5rzMV1ZyHZ80nrelP7ZQMLWvyrF"
    "5XynOpM1nziz4wc1kk89ohT2fDZXeylIA+9bPk4PF9dajLQHCT+dhF3X1nXddL0njZWN/0dYz4Suqzx3BhJ2XVMHWC3Cs6ZlvtKB"
    "Iwm7lkgYzkeopKy7ruuJ1oYfdkzCy9m8JBzO3Z76UxXISsfxOflxAxKChF8gCZtcKFm7vrHGc6jvSkXSqs5GnwhJwipTkuB1RC/x"
    "/DNRts4fE+TfIAkDCb0YE3ys8qrlqSc6e1rb1rXdKAm9jGTkuW34bF5Zda6RRmvZnNqmow1huDiQECT8BhKWlv71JMytID3UU8u1"
    "pdRTEsqSfZgDCYV/R+M1yEBC5V9QFxK2dvCeGj5bS7JVVqeuOaujtQxH/BtI6M9GdG0KMh1b15SerfofDRKChN9DwizLCpZPlgSa"
    "68rwpNCEURIypL5Fwkz4/+xFEoZjs4JJ6DXNRhD12vpCwnCA0GdJmNWsDhuyKetsYCZICBJ+CQldS97JU1fbnP7AwssFf0juEUjY"
    "jGaeDeqokZXXLismYV0R6oskHI4NkrD29CsL0ZyaaiShO59NMwnLsqw79ggZ0Th/dnqbMCAhSPg1JBx8nTUtdxO8k6fglfE2mmES"
    "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"
)


if __name__ == "__main__":
    sys.exit(main())
