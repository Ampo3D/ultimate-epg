# Ultimate EPG

Your own free "IPTV Editor": merge any number of M3U playlists and XMLTV guides,
edit every channel, and get **one playlist link + one guide link** for any player.

## Start it
Double-click the **Ultimate EPG** icon on your desktop.
Your browser opens the editor. There's no black window; it runs quietly in the background.
Clicking the icon again just reopens the editor. To stop it: **Links & Settings -> Stop Ultimate EPG**.

The program lives in `C:\Users\Ampo3D\UltimateEPG`. If something goes wrong, `data\log.txt` there
says what happened.

## Use it
1. **Sources tab** â€“ it starts preloaded with recommended free sources. Browse the
   **Free source library** to add more (filter by country), or add your playlists (M3U) and guides (XMLTV `.xml` / `.xml.gz`).
   URLs or files on your PC both work. Press **Save sources**; they download automatically.
   Order matters for guides: the one higher up wins when two cover the same channel.
2. **Channels tab**
   - Tick/untick **On** to keep or hide channels. Select many rows for bulk enable/disable,
     set group, or renumber.
   - Rename, regroup, renumber, change logo inline; âœŽ edits everything incl. the stream URL.
   - **Guide column**: green = real guide, orange = placeholder guide, red = none.
     Press **Auto-match guide** to match channels to guides by name, or ðŸ” to pick one by hand.
   - **+ Add 24/7 / custom channel** â€“ paste any stream URL. Without a real guide it gets
     a placeholder guide (channel name + your description) so it never shows "No information".
   - Press **Save changes**. Your edits survive every re-download of the sources.
3. **Links & Settings tab** â€“ copy your links.

## The universal guide (any player, any provider)
`https://ampo3d.github.io/ultimate-epg/epg-full.xml.gz` (or `epg-us` / `epg-uk` / `epg-ca`.xml.gz)

- Every copy of a real channel (ESPN listed on five guide sites under five codes) is grouped into one channel
  that answers to **every known channel code** and **every common way of writing its name**
  (`ESPN`, `ESPN HD`, `US: ESPN`, `US| ESPN HD`...), so players match it by code *or* by name.
- English listings are preferred for US/UK/Canada; East/West feeds and local stations (call letters) are kept apart.
- Junk listings ("Channel No Longer Available") are ignored.
- **Sources tab -> My providers:** add every provider you use (as many as you like). Their channel lists are read
  on this PC only and **teach the universal guide** their codes and names. Links with passwords are never uploaded.

## It finds guides by itself
Every time your sources update (every 12 hours at home, every 6 hours on GitHub), Ultimate EPG:
1. Checks every guide you have still works and has upcoming shows. Broken or out-of-date
   guides are switched off, and auto-found ones that fail twice are removed.
2. Searches the internet for more guides: guides your playlists point to, the built-in library,
   i.mjh.nz, epgshare01, iptv-epg.org, epg.pw (every country) and guide projects on GitHub.
3. Tests the most promising ones (your channels' countries first) and **adds only guides that
   cover channels that still have no guide**. The rest are remembered and re-checked every 1-2 weeks.

See them on the **Sources tab â†’ Auto-found guides**: press **Keep** to make one permanent or
**Remove** to never add it again. Settings let you change how many guides are tested per search
(default 15) and the biggest download allowed (default 80 MB).

## Links for your players
- Playlist: `http://<this-PC-IP>:8787/playlist.m3u` (the guide link is embedded in it)
- Guide: `http://<this-PC-IP>:8787/epg.xml` (or `epg.xml.gz`)

These work in TiviMate, IPTV Smarters, OTT Navigator, Kodi (PVR IPTV Simple), VLC, Plex/Jellyfin
Live TV, etc., on any device on your home network while this PC is on.
Sources re-download every 12 hours by default (change it in Settings). These home links
need this PC on â€” see below for links that don't.

## Put it online â€” links that work with your PC OFF (free)
GitHub rebuilds your playlist and guide on its own servers every 6 hours and hosts the links
for free (GitHub Pages). Your PC is only needed when you want to edit.

**One-time setup (about 3 minutes):**
1. Make a free account at github.com if you don't have one.
2. In the editor go to **Links & Settings** and press **Put it online**. A window opens:
   sign in to GitHub in the browser when asked, pick a name (e.g. `my-epg`), type `y`.
3. About 5 minutes later your permanent links are live:
   - Playlist: `https://<your-github-name>.github.io/my-epg/playlist.m3u`
   - Guide: `https://<your-github-name>.github.io/my-epg/epg.xml.gz`
   They're also shown in the editor under **Links & Settings â†’ Online links**.

**Changing things later:** start the editor, make your edits, press **â˜ Publish online**.
The online links update a few minutes later.

**Good to know**
- The repository is **public** (free GitHub Pages requires it), so anyone with the link can
  see your playlist and source links. Use it for free channels; **never** add a paid provider link
  that has your username/password in it.
- GitHub also searches for new guides on every run and saves what it finds, so your guide keeps
  improving while your PC is off. When you start the editor, it downloads what GitHub found.
- If GitHub ever emails you that the scheduled workflow was paused (it does this for repos that
  look inactive), open the repo's **Actions** tab and click **Enable workflow**.
- You can watch builds in your repo's **Actions** tab on github.com.

## Notes
- Everything lives in the `data` folder (`config.json` = your sources + edits). Back it up.
- Change the port with the `EPG_PORT` environment variable.
- Only add streams you have the right to watch. The starter sources are free, legal
  ad-supported channels (iptv-org public lists, Pluto TV / Samsung TV Plus / Plex guides).

