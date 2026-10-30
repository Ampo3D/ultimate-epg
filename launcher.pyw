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


def running():
    try:
        socket.create_connection(("127.0.0.1", PORT), timeout=2).close()
        return True
    except OSError:
        return False


def open_editor():
    try:
        os.startfile(URL)  # opens your default browser
        note("opened the editor in the browser")
    except OSError as ex:
        note(f"could not open the browser: {ex}")
        popup(f"Ultimate EPG is running.\n\nOpen this address in your browser:\n{URL}")


note("clicked")
if running():
    if "--background" not in sys.argv:
        open_editor()
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
        def wait_and_open():  # open the browser once the editor is ready to answer
            for _ in range(60):
                if running():
                    return open_editor()
                time.sleep(0.5)
            popup(f"Ultimate EPG is taking long to start. Try {URL} in your browser in a minute.")
        threading.Thread(target=wait_and_open, daemon=True).start()
    ultimate_epg.main()
except Exception as ex:
    note(f"crashed: {ex!r}")
    popup(f"Ultimate EPG could not start:\n\n{ex}\n\nDetails are in {LOG}")
