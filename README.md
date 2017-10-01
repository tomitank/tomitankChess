tomitankChess is pure JavaScript Chess Engine
-----------------------------------------
- No Emscripten, no V8 optimization: unlike stockfish-js
- tomitankChess use node.js for UCI protokol.

Usage:
------------------
- Arena GUI with node.js
- Comand line: direct acces to node.exe (C:\Program Files\nodejs\node.exe)
- Command line parameters: direct acces to tomitankChess.js (C:\Program Files\nodejs\tomitankChessUCI.js)

Features:
------------------
- Pawn bitboard with 32 bit integers (http://talkchess.com/forum/viewtopic.php?t=65198)
- Hash 28MB
- PVS, fail-low
- IID
- LMR
- LMP
- Razoring
- Futility Pruning
- Null Move Pruning
- Static null move pruning
- See pruning at Qsearch
- Delta Pruning at Qsearch
- Evaluation based on Fruit 2.1

Thanks:
------------------
- Thanks Fabien Letouzey for the great source code of the program Fruit 2.1.
- Thanks again Colin Jenkins (Lozza author) for the great source code.
- Thanks Gary Linscott for the garbochess source code
- Thanks Stockfish authors
- Thanks VICE author
- http://talkchess.com
- https://chessprogramming.wikispaces.com/

Estimated level:
------------------
- ~2500 elo (Strongest JavaScript Chess Engine /2017.09.30/)
- CCRL: http://www.computerchess.org.uk/ccrl/404/cgi/engine_details.cgi?print=Details&each_game=1&eng=tomitankChess%201.4%2064-bit#tomitankChess_1_4_64-bit

Links:
------------------
- Web: http://tanky.hu or http://mobil.tanky.hu
- Android app: https://play.google.com/store/apps/details?id=sakk.tanky.hu
- iOS app: https://itunes.apple.com/us/app/sakk-ingyenes/id1150654415?l=hu&ls=1&mt=8

TODO:
------------------
- Pawn Eval Hash
- Use TT at depth == 0
- Tune Search algorithm

Have fun with tomitankChess!

Tamas Kuzmics
