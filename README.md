# tomitankChess
Hungarian JavaScript Chess Engine

-tomitankChess is pure JavaScript Engine /relative slow/.

-No Emscripten, no V8 optimization: unlike stockfish-js

-tomitankChess use node.js for UCI protokol.

-Usage: Arena GUI with node.js
Comand line: direct acces to node.exe (C:\Program Files\nodejs\node.exe)

Command line parameters: direct acces to tomitankChess.js (C:\Program Files\nodejs\tomitankChessUCI.js)

Features:
-Pawn bitboard with 32 bit integers (http://talkchess.com/forum/viewtopic.php?t=65198)
-PVS, fail-low
-IID
-LMR
-LMP
-Razoring
-Futility Pruning
-Null Move Pruning
-Static null move pruning
-See pruning at Qsearch
-Delta Pruning at Qsearch

Evaluation based on Fruit 2.1

Thanks Fabien Letouzey for the great source code of the program Fruit 2.1.
Thanks Colin Jenkins for the UCI interface code.

Estimated level: Lozza 1.7 or better. (Around 2400 elo)

Have fun with tomitankChess!

-Tamas Kuzmics
