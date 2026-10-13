Gaus  -  Gaming - Automated - Updating - Service

Run from source:   pip install -r requirements.txt   then double-click gaus.pyw
Build the exe:     python build_release.py --repo YOURNAME/gaus --notes "What changed"
                   (set DEFAULT_UPDATE_FEED in gaus.pyw first; publish dist\Gaus.exe and dist\update.json in a GitHub Release tagged v<APP_VERSION>)
The window is HTML/CSS in the web folder; keep it next to gaus.pyw.
