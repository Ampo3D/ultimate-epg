# Ultimate EPG

Your own free "IPTV Editor": merge any number of M3U playlists and XMLTV guides,
edit every channel, and get **one playlist link + one guide link** for any player.

## Start it
Double-click the **Ultimate EPG** icon on your desktop.
Your browser opens the editor as soon as it is ready. There's no black window; it runs quietly in the background.
Clicking the icon again just reopens the editor. To stop it: **Links & Settings -> Stop Ultimate EPG**.
If another program already uses its port, a message says so (see `EPG_PORT` under Notes).

If something goes wrong, `data\log.txt` in the `UltimateEPG` folder says what happened.

## Use it
1. **Sources tab** – it starts preloaded with recommended free sources. Browse the
   **Free source library** to add more (filter by country), or add your playlists (M3U) and guides (XMLTV `.xml` / `.xml.gz`).
   URLs or files on your PC both work. Press **Save sources**; they download automatically.
   Order matters for guides: the one higher up wins when two cover the same channel.
   A link with a username/password in it is refused here – those go under **My providers** (see below).
2. **Channels tab**
   - Tick/untick **On** to keep or hide channels. Select many rows for bulk enable/disable,
     set group, or renumber.
   - Rename, regroup, renumber, change logo inline; ✎ edits everything incl. the stream URL.
   - **Guide column**: green = real guide, orange = placeholder guide, red = none.
     Press **Auto-match guide** to match channels to guides by name, or 🔍 to pick one by hand.
   - **+ Add 24/7 / custom channel** – paste any stream URL. Without a real guide it gets
     a placeholder guide (channel name + your description) so it never shows "No information".
   - Press **Save changes**. Your edits survive every re-download of the sources.
   - The count at the top is the number of channels really in your playlist. Channels of a source that was
     removed automatically or switched off are marked "source removed" / "source off" and are not in it.
3. **Links & Settings tab** – copy your links and change settings. If the app can't use a value you typed
   (for example 1.5 hours), it tells you and leaves it in the box.

## The universal guide (any player, any provider)
- Every copy of a real channel (ESPN listed on five guide sites under five codes) is grouped into one channel
  that answers to **every known channel code** and **every common way of writing its name**
  (`ESPN`, `ESPN HD`, `US: ESPN`, `US| ESPN HD`...), so players match it by code *or* by name.
- English listings are preferred for US/UK/Canada; East/West feeds and local stations (call letters) are kept apart.
- Junk listings ("Channel No Longer Available") are ignored. When no guide can be trusted for a channel,
  it shows a plain label instead of someone else's shows: empty is better than wrong.
- **Sources tab -> My providers:** add every provider you use (as many as you like). Their channel lists are read
  on this PC only and **teach the universal guide** their codes and names. Their links (with passwords) stay in
  `data\private.json` on this PC and are never uploaded.

## The files you get
Online (see **Put it online** below) they are at `https://<your-github-name>.github.io/<repo-name>/<file>`;
at home at `http://<this-PC-IP>:8787/<file>`.

| File | What it is |
|---|---|
| `playlist.m3u` | Your playlist: every channel that is switched on (the guide link is built in) |
| `epg.xml.gz` | The guide made for that playlist – the one most players should use |
| `epg-full.xml.gz` | Universal guide: all channels of your priority countries, for any provider (big: about 130 MB, 1 GB unpacked) |
| `epg-lite.xml.gz` | Your providers' channels only (much smaller than the universal guide, for weaker devices) |
| `epg-week.xml.gz` | Your providers' channels, up to 7 days |
| `epg-us.xml.gz`, `epg-uk.xml.gz`, `epg-ca.xml.gz` | Universal guide per country – one file for each of your **priority countries** (Settings) |
| `health.html` / `health.json` | How the last update went (online only) |

The universal, light, week and country guides are only made while **"Also make a full guide for any provider"** is on (Settings).
The universal guides cover 2 days by default ("Days in the any-provider guides").

## Sources that stop working
Every source is checked every few minutes (**Sources tab -> Source health**).
- A source that stays **dead** for 12 hours, or a guide that stays **out of date** (no upcoming shows) for 48 hours, is
  taken out of use automatically (both changeable in Settings, 0 = never). Not when most sources fail at once –
  that is a network problem, not dead sources.
- Removed sources are asked again after 1 hour, then 2, 4, 8... hours up to every 3 days (out-of-date ones every 3 days),
  and come back by themselves as soon as they work. **Restore** brings one back now and never removes it automatically.

## It finds guides by itself
Every time your sources update (every 12 hours at home, every 3 hours on GitHub), Ultimate EPG:
1. Checks that every guide still works and has upcoming shows (see above). Auto-found guides that stay
   broken for 2 days are dropped and looked at again later.
2. Searches the internet for more guides: guides your playlists point to, the built-in library,
   i.mjh.nz, epgshare01, iptv-epg.org, epg.pw (every country) and guide projects on GitHub.
3. Tests the most promising ones (your channels' countries first) and **adds only guides that
   cover channels that still have no guide**. The rest are remembered and re-checked every 1-2 weeks.

See them on the **Sources tab → Auto-found guides**: press **Keep** to make one permanent or
**Remove** to never add it again. Settings let you change how many guides are tested per search
(default 30) and the biggest download allowed (default 80 MB).

## Links for your players
- Playlist: `http://<this-PC-IP>:8787/playlist.m3u` (the guide link is embedded in it)
- Guide: `http://<this-PC-IP>:8787/epg.xml` (or `epg.xml.gz`)

These work in TiviMate, IPTV Smarters, OTT Navigator, Kodi (PVR IPTV Simple), VLC, Plex/Jellyfin
Live TV, etc., on any device on your home network while this PC is on.
Sources re-download every 12 hours by default (change it in Settings). These home links
need this PC on — see below for links that don't.

## Put it online — links that work with your PC OFF (free)
GitHub rebuilds your playlist and guide on its own servers every 3 hours and hosts the links
for free (GitHub Pages). Your PC is only needed when you want to edit.

**One-time setup (about 3 minutes):**
1. Make a free account at github.com if you don't have one.
2. In the editor go to **Links & Settings** and press **Put it online**. A window opens:
   sign in to GitHub in the browser when asked, pick a name (e.g. `my-epg`), type `y`.
3. About 1-2 hours later (the first build downloads every guide) your permanent links are live:
   - Playlist: `https://<your-github-name>.github.io/my-epg/playlist.m3u`
   - Guide: `https://<your-github-name>.github.io/my-epg/epg.xml.gz`
   They're also shown in the editor under **Links & Settings → Online links**.

**Changing things later:** start the editor, make your edits, press **☁ Publish online**.
The online links update about 1-2 hours later (GitHub rebuilds the whole guide; watch it in the **Actions** tab).

**Good to know**
- The repository is **public** (free GitHub Pages requires it), so anyone with the link can
  see your playlist and your **Sources** links. Never put a link with your username/password under Sources
  (the editor refuses them); paid providers go under **My providers**, which stays on this PC.
- GitHub also searches for new guides on every run and saves what it finds, so your guide keeps
  improving while your PC is off. When you start the editor, it downloads what GitHub found.
- If the guide stops updating, or a build fails, GitHub mentions you on an issue called **Guide needs attention**
  (the same warning at most once every 12 hours), which GitHub emails to you. `health.html` shows the details.
- A watchdog workflow starts a build whenever none has worked for 3 hours (GitHub's own timer often skips runs).
  To stop it, disable the **Watchdog** workflow in the **Actions** tab.
- If GitHub ever emails you that a scheduled workflow was paused (it does this for repos that
  look inactive), open the repo's **Actions** tab and click **Enable workflow**.
- Changing only text files such as this README does not start a build.

## Notes
- Everything lives in the `data` folder (`config.json` = your sources + edits, `private.json` = your provider links). Back it up.
- Change the port with the `EPG_PORT` environment variable (for example `8788`).
- Only add streams you have the right to watch. The starter sources are free ad-supported services
  (Pluto TV, Samsung TV Plus, Plex, Roku, Tubi, Xumo). Your **priority countries** setting also adds every library
  source for those countries, including community lists such as iptv-org. Those lists also contain unofficial
  re-streams of pay channels; Ultimate EPG passes on what the lists contain and does not check rights.
