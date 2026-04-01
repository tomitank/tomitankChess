@echo off

REM 0. Get node version
for /f "delims=" %%v in ('node -v') do set NODE_VERSION=%%v

REM remove 'v' from version string
set NODE_VERSION=%NODE_VERSION:v=%
for /f "tokens=1 delims=." %%a in ("%NODE_VERSION%") do set NODE_MAJOR=%%a
echo Node version: %NODE_VERSION%
echo Major version: %NODE_MAJOR%

set EXE_NAME=tomitankChess_60_x64_node%NODE_MAJOR%_false.exe

REM 1. SEA blob build
node --experimental-sea-config sea-config.json

REM 2. Copy executable
copy "%ProgramFiles%\nodejs\node.exe" %EXE_NAME%

REM 3. Remove signature
REM signtool remove /s %EXE_NAME%

REM 4. Inject blob
npx postject %EXE_NAME% NODE_SEA_BLOB tomitankChess.blob --sentinel-fuse NODE_SEA_FUSE_fce680ab2cc467b6e072b8b5df1996b2

REM 5. Sign the executable

echo Build done!
pause