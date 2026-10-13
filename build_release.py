#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
build_release.py - builds Gaus.exe and the update.json that goes with it.

Run it from the folder that contains gaus.pyw, the web folder and gaus.ico, in the VS Code terminal:

    python build_release.py --repo YOURNAME/gaus --notes "What changed"

Needs (once):  pip install pyinstaller pywebview pystray pillow psutil
Output      :  dist\\Gaus.exe   and   dist\\update.json

Every release:
  1. Change APP_VERSION in gaus.pyw (for example "1.0" -> "1.1").
  2. Run this script.
  3. Upload BOTH files in dist\\ to a new GitHub Release tagged v<version>.
     The apps check  https://github.com/<repo>/releases/latest/download/update.json
     and offer the new version automatically.
"""
import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "gaus.pyw"
WEB = HERE / "web"
ICON = HERE / "gaus.ico"
EXE_NAME = "Gaus"


def read_version() -> str:
    text = SOURCE.read_text(encoding="utf-8")
    m = re.search(r'^APP_VERSION\s*=\s*"([^"]+)"', text, re.M)
    if not m:
        sys.exit("Could not find APP_VERSION in gaus.pyw")
    return m.group(1)


def sha256_of(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser(description="Build the .exe and update.json")
    ap.add_argument("--repo", help="GitHub repo as OWNER/NAME (used to build the download links)")
    ap.add_argument("--base-url", help="Use instead of --repo: https:// folder that will hold the .exe")
    ap.add_argument("--notes", default="", help="Short 'what changed' text shown in the update banner")
    args = ap.parse_args()
    if not args.repo and not args.base_url:
        sys.exit("Give --repo OWNER/NAME (or --base-url https://...)")
    if not SOURCE.exists():
        sys.exit(f"{SOURCE.name} must be in the same folder as build_release.py")

    if not (WEB / "index.html").exists():
        sys.exit("The web folder (index.html, app.js, app.css ...) must sit next to build_release.py")
    missing = [m for m in ("PyInstaller", "webview", "pystray", "PIL", "psutil") if importlib.util.find_spec(m) is None]
    if missing:
        sys.exit("Missing packages: " + ", ".join(missing) +
                 "\nRun:  pip install pyinstaller pywebview pystray pillow psutil")

    version = read_version()
    print(f"Building version {version} ...")

    work = HERE / "build_tmp"
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir()
    script = work / "gaus.py"       # PyInstaller is happiest with a .py file
    shutil.copyfile(SOURCE, script)

    dist = HERE / "dist"
    cmd = [
        sys.executable, "-m", "PyInstaller", "--noconfirm", "--clean", "--onefile", "--windowed",
        "--name", EXE_NAME, "--distpath", str(dist), "--workpath", str(work / "pyi"),
        "--specpath", str(work), "--exclude-module", "tkinter", "--hidden-import", "psutil",
        "--add-data", f"{WEB}{os.pathsep}web",
        "--collect-all", "webview", "--hidden-import", "pystray._win32",
    ]
    if importlib.util.find_spec("clr_loader") is not None:      # pywebview's Windows bridge (pythonnet)
        cmd += ["--collect-all", "clr_loader", "--hidden-import", "clr"]
    if ICON.exists():
        cmd += ["--icon", str(ICON)]
    else:
        print("Note: gaus.ico not found next to this script, so the exe gets the default icon.")
    cmd.append(str(script))
    if subprocess.call(cmd) != 0:
        sys.exit("PyInstaller failed - see the messages above.")

    exe = dist / f"{EXE_NAME}.exe"
    if not exe.exists():
        sys.exit(f"Expected {exe} but it was not created.")

    base = args.base_url.rstrip("/") if args.base_url else \
        f"https://github.com/{args.repo}/releases/download/v{version}"
    manifest = {"version": version, "url": f"{base}/{EXE_NAME}.exe",
                "sha256": sha256_of(exe), "notes": args.notes}
    (dist / "update.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    shutil.rmtree(work, ignore_errors=True)

    print("\nDone.")
    print(f"  {exe}  ({exe.stat().st_size / 1_048_576:.1f} MB)")
    print(f"  {dist / 'update.json'}")
    if args.repo:
        print("\nUpload both files to a GitHub Release tagged v" + version + ", e.g.:")
        print(f'  gh release create v{version} "{exe}" "{dist / "update.json"}" --title "v{version}" '
              f'--notes "{args.notes}"')
        print("\nUpdate feed URL (put this in DEFAULT_UPDATE_FEED once, or in Settings):")
        print(f"  https://github.com/{args.repo}/releases/latest/download/update.json")


if __name__ == "__main__":
    main()
