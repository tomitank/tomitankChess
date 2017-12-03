tomitankChess is (pure) Hungarian JavaScript Chess Engine
--------------------------------------------------------
- No Emscripten, no V8 optimization: unlike stockfish-js
- tomitankChess use node.js for UCI protokol.

Usage:
------------------
- Arena GUI with node.js
  + Comand line: direct acces to node.exe (C:\Program Files\nodejs\node.exe)
  + Command line parameters: direct acces to tomitankChess.js (C:\Program Files\nodejs\tomitankChessUCI.js)

- Web browser: tomitankChess runing with and without WebWorker as well. (Recommended: WebWorker)
  + Input (standard UCI commands) to the engine is posted as a message to the worker. Example:
  + var tomitankChess = new Worker('tomitankChess.js'); 
  + tomitankChess.postMessage('ucinewgame');
  + tomitankChess.postMessage('go depth 12');
  
 - JSUCI: https://sourceforge.net/projects/jsuci/

Version 1.5 (Probably the Last Mailbox Version):
------------------
- New UI interface code (now working with JSUCI as well)
- Tuned Search algorithm
- Use TT at depth == 0

Estimated level:
------------------
- v.1.5: ~2540 elo (Strongest JavaScript Chess Engine /2017.12.03/)
- v.1.4: ~2500 elo (Strongest JavaScript Chess Engine /2017.09.30/)

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

Links:
------------------
- Web: http://tanky.hu or http://mobil.tanky.hu
- Android app: https://play.google.com/store/apps/details?id=sakk.tanky.hu
- iOS app: https://itunes.apple.com/us/app/sakk-ingyenes/id1150654415?l=hu&ls=1&mt=8

TODO:
------------------
- Pawn Eval Hash

Have fun with tomitankChess!

Tamas Kuzmics
