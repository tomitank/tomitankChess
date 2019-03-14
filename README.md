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
  + tomitankChess.postMessage('go depth 12');
  
 - JSUCI: https://sourceforge.net/projects/jsuci/

Estimated level (CCRL 40/40):
-----------------------------
- 3.0: ~2780 elo (Strongest JavaScript Chess Engine /2019.01.14/)
- 2.1: ~2660 elo (Strongest JavaScript Chess Engine /2018.11.26/)
- 2.0: ~2660 elo (Strongest JavaScript Chess Engine /2018.07.11/)
- 1.5: ~2590 elo (Strongest JavaScript Chess Engine /2017.12.03/)
- 1.4: ~2550 elo (Strongest JavaScript Chess Engine /2017.09.30/)
- [Click here to see all CCRL 40/40 results of tomitankChess](http://ccrl.chessdom.com/ccrl/4040/cgi/compare_engines.cgi?family=tomitankChess&print=Rating+list&print=Results+table&print=LOS+table&print=Ponder+hit+table&print=Eval+difference+table&print=Comopp+gamenum+table&print=Overlap+table&print=Score+with+common+opponents)

Thanks:
-----------------------------
- Thanks Fabien Letouzey (Fruit and Senpai author)
- Thanks Colin Jenkins (Lozza author)
- Thanks Gary Linscott (garbochess)
- Thanks Stockfish authors
- Thanks VICE author
- http://talkchess.com
- https://www.chessprogramming.org/

Links:
-----------------------------
- Web: http://tanky.hu or http://mobil.tanky.hu
- Android app: https://play.google.com/store/apps/details?id=sakk.tanky.hu
- iOS app: https://itunes.apple.com/us/app/sakk-ingyenes/id1150654415?l=hu&ls=1&mt=8

Have fun with tomitankChess!

Tamás Kuzmics
