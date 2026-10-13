"""Usage: python set_feed.py OWNER/REPO   - writes the update feed link into gaus.pyw."""
import re, sys
from pathlib import Path

if len(sys.argv) != 2 or "/" not in sys.argv[1]:
    sys.exit("Usage: python set_feed.py OWNER/REPO")
p = Path(__file__).with_name("gaus.pyw")
text = p.read_text(encoding="utf-8")
url = f"https://github.com/{sys.argv[1]}/releases/latest/download/update.json"
new, n = re.subn(r'^DEFAULT_UPDATE_FEED = ".*"$', f'DEFAULT_UPDATE_FEED = "{url}"', text, flags=re.M)
if n != 1:
    sys.exit("Could not find the DEFAULT_UPDATE_FEED line in gaus.pyw")
p.write_text(new, encoding="utf-8")
print("Update feed set to", url)
