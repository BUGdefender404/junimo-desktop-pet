@echo off
rem Launch Junimo desktop pet without a console window
cd /d "%~dp0"
where pythonw >nul 2>nul
if %errorlevel%==0 (
  start "JunimoPet" pythonw junimo_pet.py
) else (
  start "JunimoPet" /b python junimo_pet.py
)
