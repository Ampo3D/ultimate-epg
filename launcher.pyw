"""Ultimate EPG launcher - no black window.

Double-click (or the desktop icon): starts Ultimate EPG if needed and opens the editor.
With --background: just starts it quietly.
"""
import ctypes
import os
import socket
import sys
import threading
import time
import urllib.error
import urllib.request

BASE = os.path.dirname(os.path.abspath(__file__))
PORT = int(os.environ.get("EPG_PORT", "8787"))
URL = f"http://localhost:{PORT}"
LOG = os.path.join(BASE, "data", "log.txt")
os.makedirs(os.path.join(BASE, "data"), exist_ok=True)


def note(msg):
    with open(LOG, "a", encoding="utf-8") as f:
        f.write(time.strftime("%H:%M:%S ") + "[icon] " + msg + "\n")


def popup(msg):
    ctypes.windll.user32.MessageBoxW(None, msg, "Ultimate EPG", 0x40)


def port_owner(timeout=3):
    """"ours" (the editor answers), "starting" (takes calls, no answer yet), "other" (another program), or "none"."""
    try:
        with urllib.request.urlopen(f"http://127.0.0.1:{PORT}/", timeout=timeout) as r:
            return "ours" if b"<title>Ultimate EPG</title>" in r.read(4096) else "other"
    except urllib.error.HTTPError:
        return "other"
    except (TimeoutError, socket.timeout):
        return "starting"
    except urllib.error.URLError as ex:
        return "starting" if isinstance(ex.reason, (TimeoutError, socket.timeout)) else "none"
    except (OSError, ValueError):
        return "none"


def wait_and_open():
    """Open the browser once the editor answers (loading the guides can take a minute), not on a blank page."""
    end = time.time() + 240
    while time.time() < end:
        if port_owner() == "ours":
            return open_editor()
        time.sleep(1)
    note("the editor did not answer within 4 minutes")
    popup(f"Ultimate EPG is taking long to start. Try {URL} in your browser in a minute.")


def port_taken():
    note(f"port {PORT} is used by another program")
    popup(f"Ultimate EPG can't start: port {PORT} is used by another program.\n\n"
          f"Close that program and try again, or set EPG_PORT to another number (for example 8788).")


def open_editor():
    try:
        os.startfile(URL)  # opens your default browser
        note("opened the editor in the browser")
    except OSError as ex:
        note(f"could not open the browser: {ex}")
        popup(f"Ultimate EPG is running.\n\nOpen this address in your browser:\n{URL}")


note("clicked")
owner = port_owner()
if owner == "other":
    port_taken()
    sys.exit()
if owner != "none":  # already running, or still starting
    if "--background" not in sys.argv:
        wait_and_open() if owner == "starting" else open_editor()
    sys.exit()

note("starting Ultimate EPG")
os.chdir(BASE)
if os.path.exists(LOG) and os.path.getsize(LOG) > 5_000_000:
    os.remove(LOG)
sys.stdout = sys.stderr = open(LOG, "a", encoding="utf-8", buffering=1)
sys.path.insert(0, BASE)
try:
    import ultimate_epg

    if "--background" not in sys.argv:
        threading.Thread(target=wait_and_open, daemon=True).start()
    ultimate_epg.main()
except (Exception, SystemExit) as ex:  # "config.json has git clash marks" is a SystemExit: say so too
    if not (isinstance(ex, SystemExit) and ex.code in (0, None)):
        note(f"crashed: {ex!r}")
        popup(f"Ultimate EPG could not start:\n\n{ex.code if isinstance(ex, SystemExit) else ex}\n\nDetails are in {LOG}")
