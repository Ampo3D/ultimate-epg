@echo off
title Ultimate EPG
cd /d "%~dp0"
where python >nul 2>nul
if errorlevel 1 (
  echo Python is not installed. Get it free from https://www.python.org/downloads/
  echo Tick "Add python.exe to PATH" during install, then try again.
  pause
  exit /b
)
python ultimate_epg.py --open
echo.
echo Ultimate EPG stopped. If you saw an error above, copy it and send it to Claude.
pause
