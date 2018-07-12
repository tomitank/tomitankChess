tomitankChess is Hungarian (pure) JavaScript Chess Engine
------------------------------------------------------------------
- tomitankChess 2.0 is the first full BitBoard JavaScript chess engine on the World!
- Why pure? Because it is No Emscripten (unlike stockfish-js), so the code is readable.
- Pure JavaScript ~5X slower than "C" language, and ~2.5 slower than Emscripten JavaScript.
- The Engine is running in your browser and with UCI GUI (eg: Arena) as well.

Usage:
-----------------------------
- tomitankChess (with node.js) run in Arena, in WinBoard and in Cutechess as well.

- Example for Arena GUI with node.js
  + Comand line: direct acces to node.exe (C:\Program Files\nodejs\node.exe)
  + Command line parameters: direct acces to tomitankChess.js (C:\Program Files\nodejs\tomitankChessUCI.js)

- Web browser: tomitankChess runing with and without WebWorker as well. (Recommended: WebWorker)
  + Input (standard UCI commands) to the engine is posted as a message to the worker. Example:
  + var tomitankChess = new Worker('tomitankChess.js'); 
  + tomitankChess.postMessage('ucinewgame');
  + tomitankChess.postMessage('go depth 12');
  
 - JSUCI: https://sourceforge.net/projects/jsuci/
