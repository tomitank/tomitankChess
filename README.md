tomitankChess is Hungarian (pure) JavaScript Chess Engine
------------------------------------------------------------------
- tomitankChess 2.0 was the first full BitBoard JavaScript chess engine on the World!
- Why pure? Because it is No Emscripten (unlike stockfish-js), so the code is readable.
- Pure JavaScript ~5X slower than "C" language, and ~2.5 slower than Emscripten JavaScript.
- The Engine is running in your browser and with UCI GUI (eg: Arena) as well.

Usage:
-----------------------------
- tomitankChess (with node.js) run in Arena, in WinBoard and in Cutechess as well.

- Example for Arena GUI with node.js
  + Command line: direct acces to node.exe (C:\Program Files\nodejs\node.exe)
  + Command line parameters: direct acces to tomitankChess.js (C:\Program Files\nodejs\tomitankChessUCI.js)

- Web browser: tomitankChess runing with and without WebWorker as well. (Recommended: WebWorker)
  + Input (standard UCI commands) to the engine is posted as a message to the worker. Example:
  + var tomitankChess = new Worker('tomitankChess.js');
  + tomitankChess.postMessage('ucinewgame');
  + tomitankChess.postMessage('isready');
  + at this point you need to wait (eg with Promise) for readyok response
  + tomitankChess.postMessage('go depth 12');

 - JSUCI: https://sourceforge.net/projects/jsuci/

Estimated level (CCRL 40/40):
-----------------------------
- 5.1: ~2920 elo (Strongest JavaScript Chess Engine /2021.08.08/)
- 5.0: ~2900 elo (Strongest JavaScript Chess Engine /2021.01.18/)
- 4.2: ~2830 elo (Strongest JavaScript Chess Engine /2020.09.24/)
- 4.0: ~2820 elo (Strongest JavaScript Chess Engine /2020.01.24/)
- 3.0: ~2780 elo (Strongest JavaScript Chess Engine /2019.01.14/)
- 2.1: ~2660 elo (Strongest JavaScript Chess Engine /2018.11.26/)
- 2.0: ~2660 elo (Strongest JavaScript Chess Engine /2018.07.11/)
- 1.5: ~2590 elo (Strongest JavaScript Chess Engine /2017.12.03/)
- 1.4: ~2550 elo (Strongest JavaScript Chess Engine /2017.09.30/)
- [Click here to see all CCRL 40/40 results of tomitankChess](http://ccrl.chessdom.com/ccrl/4040/cgi/compare_engines.cgi?family=tomitankChess&print=Rating+list&print=Results+table&print=LOS+table&print=Ponder+hit+table&print=Eval+difference+table&print=Comopp+gamenum+table&print=Overlap+table&print=Score+with+common+opponents)

Links:
-----------------------------
- Web: http://tanky.hu or http://mobil.tanky.hu
- Android app: https://play.google.com/store/apps/details?id=sakk.tanky.hu
- iOS app: https://itunes.apple.com/us/app/sakk-ingyenes/id1150654415?l=hu&ls=1&mt=8

Have fun with tomitankChess!

-Tamás Kuzmics

Changes log:
-----------------------------
- v5.1
  + network is trained with 4M example instead of 2.7M as in the previous version. (same size 768x16x1)
  + better hash table usage (prune more in Qsearch as well, and improve hash store)
  + around 20 elo better than previous version

- v5.0
  + Added eval (NN)! Network size is only 768x16x1. Smaller than I've seen before.
  + it does not replace evaluation, it only compensates that.
  + trained only with 2.7M example.
  + The network is not compatible with other engines and it's integrated into the code. (hardcoded)
  + I wrote the network from scratch. I don't use machine learning platform.
  + I have around 10 elo better net (768x32x1) in fix depth test, but JavaScript is too slow, and don’t have AVX or similar methode in JavaScript (so i use vanilla approach). Essentially the smaller net has nearly the same strength in both short and long TC tests.

- v4.2
  + revisited code
  + rewrite pawn eval
  + fixed a bug that's caused problem in IE

- v4.0
  + see pruning
  + better lmr
  + rewrited pawn eval
  + new pawn shield code
  + new see (add discovered checks)
  + lots of little things (revisited code)

- v3.0
  + new pawn shield code (idea from Senpai 2, but a bit better)
  + use 3x3 squares king ring (idea from Senpai 2)
  + new king safety code (simple, but bit better)
  + all parameters scoring by logistic regression
  + better time management (take more time when unsure)
  + 4-way transposition table
  + lots of little things (revisited code)

- v2.1
  + Revisited code (threats, move gen, some bug-fix, etc..)
  + Store eval score in hash
  + Smaller king-ring
  + Added logo.png
  + Strength: similar to the previous version, maybe a bit stronger

- v2.0
  + first full BitBoard JavaScript chess engine on the World
  + added check evasions code
  + added threats for all pieces
  + added new passed pawn eval
  + new King Safety (bigger and pawn-safe king ring)
  + new non-linear and pawn-safe mobility (Same in mg and eg)
  + better aspiration window
  + a bit better delta pruning
  + Don't give back the "upper bounds" moves
  + pre-calculate and transmit the "gives check"
  + added pawn hash (there is no elo gain yet, but it will be useful for a more complex pawn evaluation.)
  + Typed Arrays Hash table for better memory usage
  + added "Hash option" (default 32 min 1 max 256)
  + added "eval" command (show the static evaluation)
  + lots of little things
