- tomitankChess (with node.js) run in Arena, in WinBoard and in Cutechess as well.

- Example for Arena GUI with node.js
  + Download Node.js from https://nodejs.org/en/
  + Open Arena GUI -> Engine Management -> Details menu
  + Command line: direct acces to node.exe (C:\Program Files\nodejs\node.exe)
  + Command line parameters: direct acces to tomitankChess.js (C:\Program Files\nodejs\tomitankChessUCI.js)

- Web browser: tomitankChess runing with and without WebWorker as well. (Recommended: WebWorker)
  + Input (standard UCI commands) to the engine is posted as a message to the worker. Example:
  + var tomitankChess = new Worker('tomitankChess.js');
  + tomitankChess.postMessage('ucinewgame');
  + tomitankChess.postMessage('go depth 12');

- JSUCI: https://sourceforge.net/projects/jsuci/

Have fun with tomitankChess!

Tamás Kuzmics
