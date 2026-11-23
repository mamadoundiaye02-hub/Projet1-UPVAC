@echo off
rem Lance UPVac sur le reseau local : accessible depuis tous les postes a l'adresse http://IP-DE-CE-PC:5000
rem Double-cliquer sur ce fichier. Fermer la fenetre (ou Ctrl+C) arrete la plateforme.
title UPVac - serveur reseau
cd /d "%~dp0"
echo.
echo  UPVac - demarrage en mode reseau...
echo  Adresse(s) de ce PC sur le reseau :
for /f "tokens=2 delims=:" %%a in ('ipconfig ^| findstr /c:"IPv4"') do for /f "tokens=*" %%b in ("%%a") do echo     http://%%b:5000
echo.
".venv\Scripts\python.exe" app.py --reseau --port 5000
pause
