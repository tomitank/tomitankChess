@echo off
REM 1. SEA blob build
node --experimental-sea-config sea-config.json

REM 2. Copy executable
copy "%ProgramFiles%\nodejs\node.exe" tomitankChess_60_x64_node24_v8cache.exe

REM 3. Remove signature
REM signtool remove /s tomitankChess_60_x64_node24_v8cache.exe

REM 4. Inject blob
npx postject tomitankChess_60_x64_node24_v8cache.exe NODE_SEA_BLOB tomitankChess.blob --sentinel-fuse NODE_SEA_FUSE_fce680ab2cc467b6e072b8b5df1996b2

REM 5. Sign the executable

echo Build done!
pause