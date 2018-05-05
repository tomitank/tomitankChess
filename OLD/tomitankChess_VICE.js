/*
* tomitankChess v.1.0 by tomitank
* Date:2017.09.28.
* Contact:tomitank@freemail.hu , tanky.hu@gmail.com
* [^:]// .* regular search->comment del
*/

// Valtozok
var VERSION				= '1.0'; // Verzio
var nodes				= 0; // Csomopontok
var hashUsed			= 0; // Hash szam
var boardPly			= 0; // Lepes szam
var MoveTime			= 0; // Keresesi ido
var maxDepth			= 64; // Max melyseg
var bestMove			= 0; // A legjobb lepes
var timeStop			= 0; // Ido vagas(cutoff)
var currDepth			= 0; // Aktualis melyseg
var moveCount			= 0; // Szinten lepest szamol
var startTime			= 0; // Kereses kezdeti ideje
var SideKeyLow			= 0; // Oldal hashKey also
var SideKeyHigh			= 0; // Oldal hashKey felso
var castleRights		= 0; // Sancolas 4 biten
var maxSearchTime		= 0; // Maximalis keresesi ido
var currentPlayer		= 0; // Aki lephet (Feher: 0)
var brd_fiftyMove		= 0; // 50 lepes szamlalo
var brd_hashKeyLow		= 0; // Aktualis hashKey also bit
var brd_hashKeyHigh		= 0; // Aktualis hashKey felso bit
var brd_HashTable		= null; // Atultetesi tabla uresen
var brd_Material		= new Array(8); // Anyag(Feher,Fekete)
var brd_pieceCount		= new Array(16); // Babuk szama
var brd_pieceList		= new Array(256); // Babuk helyzete
var brd_pieceIndex		= new Array(120); // Babuk azonositoja
var brd_PvArray			= new Array(maxDepth); // Mentett lepesek
var searchKillers		= new Array(maxDepth); // "Gyilkos" heurisztika
var brd_moveList		= new Array(maxDepth * 256); // Lepes lista
var brd_moveScores		= new Array(maxDepth * 256); // Lepes pont
var brd_moveStart		= new Array(maxDepth); // Lepes tomb index
var CastleKeysHigh		= new Array(16); // Sancolas hashKey felso
var CastleKeysLow		= new Array(16); // Sancolas hashKey also
var PieceKeysHigh		= new Array(16); // Babuk hashKey felso
var PieceKeysLow		= new Array(16); // Babuk hashKey also
var PawnRanksBlack		= new Array(10); // Fekete Gyalog tomb
var PawnRanksWhite		= new Array(10); // Feher Gyalog tomb
var historyTable		= new Array(16); // Elozmeny tabla
var MOVE_HISTORY		= new Array(); // Lepeselozmenyek
brd_moveStart[0]		= 0; // Hack: Lepes lista index


// Allandok definialasa a jobb olvashatosag miatt
var WHITE			= 0x0;
var BLACK			= 0x8;

var PAWN			= 0x01;
var KNIGHT			= 0x02;
var KING			= 0x03;
var BISHOP			= 0x05;
var ROOK			= 0x06;
var QUEEN			= 0x07;
var EMPTY			= 0x08;


// Feher babukat 4 bit tarolja
var WHITE_PAWN		= 0x01;
var WHITE_KNIGHT	= 0x02;
var WHITE_KING		= 0x03;
var WHITE_BISHOP	= 0x05;
var WHITE_ROOK		= 0x06;
var WHITE_QUEEN		= 0x07;


// Fekete babukat 4 bit tarolja
var BLACK_PAWN		= 0x09;
var BLACK_KNIGHT	= 0x0A;
var BLACK_KING		= 0x0B;
var BLACK_BISHOP	= 0x0D;
var BLACK_ROOK		= 0x0E;
var BLACK_QUEEN		= 0x0F;


// Allandok
var FLAG_EXACT		= 3; // Hash zaszlo 3
var FLAG_ALPHA		= 2; // Hash zaszlo 2
var FLAG_BETA		= 1; // Hash zaszlo 1
var FLAG_NONE		= 0; // Hash zaszlo 0
var NOMOVE			= 0; // Nincs lepes 0
var NOT_IN_CHECK	= 0; // Nincs Sakkban
var UNKNOWN_CHECK	= 2; // Sakk ismeretlen
var EN_PASSANT		= 0; // En passant mezo
var QueenSemiOpen	= 3; // Felig nyitott Vezer
var QueenOpenFile	= 5; // Nyitott oszlop Vezer
var RookSemiOpen	= 5; // Felig nyitott Bastya
var RookOpenFile	= 10; // Nyitt oszlop Bastya
var BishopPair		= 30; // Futo par plusz pont
var PawnIsolated	= -10; // Elkulonitett Gyalog
var INFINITE		= 30000; // Infinity / Vegtelen
var CAPTURE_MASK	= 0x4000; // Leutes jelzo maszk
var DANGER_MASK		= 0xFC000; // Fontos lepes maszk
var CASTLED_MASK	= 0x80000; // Sancolas jelzo maszk
var TACTICAL_MASK	= 0x7C000; // Utes, Bevaltas maszk
var ISMATE			= INFINITE - 2 * maxDepth; // Matt
var HASHENTRIES		= (28 << 20) / 14; // Hashtabla merete 28 MB / 1 Hash merete (14 Byte)
var HASHMASK		= HASHENTRIES - 1; // Hashtabla maszk, csak ketto hatvanya lehet & MASK
var CASTLEBIT		= { WQCA : 1, WKCA : 2, BQCA : 4, BKCA : 8 }; // Sancolas ellenorzeshez
var PawnPassed		= [ 0, 0, 5, 10, 20, 35, 60, 100, 200 ]; // Telt Gyalog elorehaladasi pontjai (RANK_0, RANK_8)
var MvvLvaScores	= [ 0, 1, 2, 6, 0, 3, 4, 5, 0, 1, 2, 6, 0, 3, 4, 5 ]; // MVV-LVA Babuk erteke (P, N, B, R, Q, K)
var KnightMoves		= [ 14, -14, 18, -18, 31, -31, 33, -33 ]; // Huszar lepesek
var KingMoves		= [ 1, -1, 15, -15, 16, -16, 17, -17 ]; // Kiraly lepesek
var BishopMoves		= [ 15, -15, 17, -17 ]; // Futo lepesek
var RookMoves		= [ 1, -1, 16, -16 ]; // Bastya lepesek
var DirNum			= [ 0, 0, 8, 8, 0, 4, 4, 8 ]; // Lepesek szama babunkent
var Letters			= [ 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h' ]; // Betuzes
var PieceDir		= [ 0, 0, KnightMoves, KingMoves, 0, BishopMoves, RookMoves, KingMoves ]; // Lepesek tomb
var PieceValue		= [ 0, 100, 325, 20000, 0, 325, 550, 1000, 0, 100, 325, 20000, 0, 325, 550, 1000 ]; // (P, N, K, B, R, Q)
var EndGameMate		= 1 * PieceValue[ROOK] + 2 * PieceValue[KNIGHT] + 2 * PieceValue[PAWN] + PieceValue[KING]; // Vegjatek ertek
var RANKS			= { RANK_1 : 1, RANK_2 : 2, RANK_3 : 3, RANK_4 : 4, RANK_5 : 5, RANK_6 : 6, RANK_7 : 7, RANK_8 : 8 }; // Sorok
var FILES			= { FILE_A : 1, FILE_B : 2, FILE_C : 3, FILE_D : 4, FILE_E : 5, FILE_F : 6, FILE_G : 7, FILE_H : 8 }; // Oszlopok


// Mezok elnevezese
var SQUARES			= { A8:  0, 	B8:  1, 	C8:  2, 	D8:  3, 	E8:  4, 	F8:  5, 	G8:  6, 	H8:  7,
						A7: 16, 	B7: 17, 	C7: 18, 	D7: 19, 	E7: 20, 	F7: 21, 	G7: 22, 	H7: 23,
						A6: 32, 	B6: 33, 	C6: 34, 	D6: 35, 	E6: 36, 	F6: 37, 	G6: 38, 	H6: 39,
						A5: 48, 	B5: 49, 	C5: 50, 	D5: 51, 	E5: 52, 	F5: 53, 	G5: 54, 	H5: 55,
						A4: 64, 	B4: 65, 	C4: 66, 	D4: 67, 	E4: 68, 	F4: 69, 	G4: 70, 	H4: 71,
						A3: 80, 	B3: 81, 	C3: 82, 	D3: 83, 	E3: 84, 	F3: 85, 	G3: 86, 	H3: 87,
						A2: 96, 	B2: 97, 	C2: 98, 	D2: 99, 	E2:100, 	F2:101, 	G2:102, 	H2:103,
						A1:112, 	B1:113, 	C1:114, 	D1:115, 	E1:116, 	F1:117, 	G1:118, 	H1:119 };


// Kezdeti allapot
var CHESS_BOARD		= [	BLACK_ROOK, BLACK_KNIGHT, BLACK_BISHOP, BLACK_QUEEN, BLACK_KING, BLACK_BISHOP, BLACK_KNIGHT, BLACK_ROOK, 0, 0, 0, 0, 0, 0, 0, 0,
						BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, 0, 0, 0, 0, 0, 0, 0, 0,
						0, 0, 0, 0, 0, 0, 0, 0,	0, 0, 0, 0, 0, 0, 0, 0,
						0, 0, 0, 0, 0, 0, 0, 0,	0, 0, 0, 0, 0, 0, 0, 0,
						0, 0, 0, 0, 0, 0, 0, 0,	0, 0, 0, 0, 0, 0, 0, 0,
						0, 0, 0, 0, 0, 0, 0, 0,	0, 0, 0, 0, 0, 0, 0, 0,
						WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, 0, 0, 0, 0, 0, 0, 0, 0,
						WHITE_ROOK, WHITE_KNIGHT, WHITE_BISHOP, WHITE_QUEEN, WHITE_KING, WHITE_BISHOP, WHITE_KNIGHT, WHITE_ROOK, 0, 0, 0, 0, 0, 0, 0, 0 ];


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function validateMove(from, to, currentPlayer) {
		if (isPseudoLegal(from, to, currentPlayer))
		{
		// Gyalog bevaltas
			var PROMOTED = 0;

		// Akival lepunk
			var fromPiece = CHESS_BOARD[from] & 0x07;

		// En Passant?
			var EP_MOVE = 0;
			if (!CHESS_BOARD[to] && fromPiece === PAWN && EN_PASSANT != 0 && EN_PASSANT === to) {
				EP_MOVE = 1;
			}

		// Utes?
			var CAPTURED = EP_MOVE; // Hack: En Passant is utes!
			if (CHESS_BOARD[to]) {
				CAPTURED = 1;
			}

		// Sancolas?
			var CASTLING = 0;
			if (fromPiece === KING && Math.abs(from - to) === 2) {
				CASTLING = 1;
			}

		// Ervenyes lepes?
			if (makeMove(BIT_MOVE(from, to, CAPTURED, PROMOTED, CASTLING))) {
				unMakeMove();
				MOVE_HISTORY.splice(moveCount); // Elozmeny torlese
				return true;
			}
		}
		return false;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function isPseudoLegal(from, to, currentPlayer) {

		var fromPiece = CHESS_BOARD[from];
		var toPiece = CHESS_BOARD[to];

		if (!fromPiece) { // Moving an empty square?
			return false;
		}

		if (to & 0x88) { // moving to outside valid board?
			return false;
		}

		if ((fromPiece & 0x8) ^ currentPlayer) { // not your turn?
			return false;
		}
		
		if (toPiece && (toPiece & 0x8) === currentPlayer) { // cannot attack one of your own
			return false;
		}

		var pieceType = fromPiece & 0x07;

		if (pieceType === QUEEN) { // queen
			if ((Math.abs(from - to) % 15 && Math.abs(from - to) % 17) && // bishop move
				((from & 0x0F) !== (to & 0x0F) && (from & 0xF0) !== (to & 0xF0))) { // rook move
				return false;
			}
		} else if (pieceType === ROOK) { // rook
			if ((from & 0x0F) !== (to & 0x0F) && (from & 0xF0) !== (to & 0xF0)) { // move in a file or a rank
				return false;
			}
		} else if (pieceType === BISHOP) { // bishop
			if (Math.abs(from - to) % 15 && Math.abs(from - to) % 17) { // bishop can only move diagonally
				return false;
			}
		} else if (pieceType === KING) { // king
			var diff = Math.abs(from - to);
			var direction = from - to > 0 ? 0x0 : 0x1;

			if (diff === 1 || diff === 15 || diff === 16 || diff === 17) {
				// valid
			}
			else if (diff === 2) // castling
			{
				if (direction == 0 && CHESS_BOARD[from - 3]) { // Queen Side: All square is empty in this direction?!
					return false;
				}
				if (toPiece || CHESS_BOARD[(direction ? from + 1 : from - 1)]) { // All square is empty in this direction?!
					return false;
				}
				if (((castleRights >> (currentPlayer/4 + direction)) & 1) == 0) { // casling is available in this direction?!
					return false;
				}
				if (isSquareUnderAttack(from, currentPlayer)) { // king is not in check now
					return false;
				}
				if (isSquareUnderAttack(from + (direction ? 1 : -1), currentPlayer)) { // the next square is not in check
					return false;
				}
			} else {
				return false;
			}
		} else if (pieceType === KNIGHT) { // knight
			var diff = Math.abs(from - to);
			if (diff !== 14  && diff !== 18 && diff !== 31 && diff !== 33) {
				return false;
			}
		} else if (pieceType === PAWN) { // pawn
			var direction = from - to > 0 ? 0x0 : 0x8;
			var diff = Math.abs(from - to);
			var fromRow = from & 0x70;

			if (direction !== currentPlayer) { // a pawn can only move forward
				return false;
			}

			if (diff === 16 && !toPiece) { // single move forward?
				// valid
			} else if (diff === 32 && (fromRow === 0x60 || fromRow === 0x10) && !toPiece && !CHESS_BOARD[from + (direction ? 16 : -16)]) { // double move from start
				// valid
			} else if ((diff === 15 || diff === 17) && toPiece) { // capture
				// valid
			} else if ((diff === 15 || diff === 17) && !toPiece && EN_PASSANT != 0 && EN_PASSANT === to) { // en passant
				// valid en passant
			} else {
				return false;
			}
		}

		if (fromPiece & 0x04) { // sliding piece
			var diff = to - from;
			var step;

			if (diff % 17 === 0) {
				step = 17;
			} else if (diff % 15 === 0) {
				step = 15;
			} else if (diff % 16 === 0) {
				step = 16;
			} else {
				step = 1;
			}

			var iterations = diff/step;
			if (iterations < 0) {
				step = -step;
				iterations = -iterations;
			}

			var path = from + step;
			for (var index = 1; index < iterations; index++, path+=step) {
				if (CHESS_BOARD[path]) {
					return false;
				}
			}
		}

		return true;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function GetPvLine(depth) { // Fo lepesvonal
		var count = 0;
		var move = ProbeHashMove();

		while (move != NOMOVE && count < depth) {
			makeMove(move.move);
			brd_PvArray[count++] = move;
			move = ProbeHashMove();
		}

		while (boardPly > 0) {
			unMakeMove();
		}

		return count;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function StoreHashMove(move, score, flags, depth) { // Hash mentes

		if (score > ISMATE) {
			score += boardPly;
		} else if (score < -ISMATE) {
			score -= boardPly;
		}

		if (brd_HashTable[brd_hashKeyLow & HASHMASK] == null) {
			hashUsed++;
		}

		brd_HashTable[brd_hashKeyLow & HASHMASK] = new HashEntry(move, score, flags, depth, brd_hashKeyLow, brd_hashKeyHigh); // 108 bit /14 Byte/
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function HashEntry(move, score, flags, depth, hashLow, hashHigh) { // Hash Objektum
		this.move			= move; // 20 bit
		this.flags			= flags; // 2 bit
		this.depth			= depth; // 7 bit
		this.score			= score; // 15 bit
		this.hashKeyLow		= hashLow; // 32 bit
		this.hashKeyHigh	= hashHigh; // 32 bit
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function ProbeHashMove() { // Hash kiolvasas

		var hash = brd_HashTable[brd_hashKeyLow & HASHMASK];

		if (hash != null && hash.hashKeyLow == brd_hashKeyLow && hash.hashKeyHigh == brd_hashKeyHigh) {
			return hash;
		}

		return NOMOVE;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function IsRepetition() { // Lepesismetles + 50 lepesszabaly

		if (brd_fiftyMove >= 100) { // 50 lepesszabaly (TODO: 100 !isCheck)
			return true;
		}

		for (var index = 2; index <= brd_fiftyMove; index += 2) {
			if (MOVE_HISTORY[moveCount-index].hashKeyLow == brd_hashKeyLow
			&& MOVE_HISTORY[moveCount-index].hashKeyHigh == brd_hashKeyHigh) { // Lepesismetles
				return true;
			}
		}

		return false;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function FROMSQ(m) { return (m & 0x7F); } // Ahonnan lepunk
	function TOSQ(m) { return ((m >> 7) & 0x7F); } // Ahova lepunk
	function PROMOTED(m) { return ((m >> 15) & 0xF); } // Gyalog bevaltas
	function HASH_SIDE() {
		brd_hashKeyLow  ^= SideKeyLow; // Aki lephet hashKey
		brd_hashKeyHigh ^= SideKeyHigh; // Aki lephet hashKey
	}
	function HASH_PCE(pce, sq) {
		brd_hashKeyLow  ^= PieceKeysLow[pce][sq]; // Babu hashKey
		brd_hashKeyHigh ^= PieceKeysHigh[pce][sq]; // Babu hashKey
	}
	function HASH_CA() {
		brd_hashKeyLow  ^= CastleKeysLow[castleRights]; // Sancolas hashKey
		brd_hashKeyHigh ^= CastleKeysHigh[castleRights]; // Sancolas hashKey
	}
	function HASH_EP() {
		brd_hashKeyLow  ^= PieceKeysLow[0][EN_PASSANT]; // En Passant hashKey
		brd_hashKeyHigh ^= PieceKeysHigh[0][EN_PASSANT]; // En Passant hashKey
	}
	function MOVE_PCE(pce, from, to) {
		CHESS_BOARD[from] = 0; // Babu torlese
		CHESS_BOARD[to] = pce; // Babu mozgatas
		brd_pieceIndex[to] = brd_pieceIndex[from];
		brd_pieceList[(pce << 4) | brd_pieceIndex[to]] = to;
	}
	function ADDING_PCE(pce, sq, currentPlayer) {
		CHESS_BOARD[sq] = pce; // Babu hozzadasa
		brd_pieceIndex[sq] = brd_pieceCount[pce];
		brd_pieceList[(pce << 4) | brd_pieceIndex[sq]] = sq;
		brd_Material[currentPlayer] += PieceValue[pce];
		brd_pieceCount[pce]++; // Babu szamanak novelese
	}
	function DELETE_PCE(pce, sq, currentPlayer) {
		CHESS_BOARD[sq] = 0; // Babu torlese
		brd_pieceCount[pce]--; // Babu szamanak csokkentese
		var lastPceSquare = brd_pieceList[(pce << 4) | brd_pieceCount[pce]];
		brd_pieceIndex[lastPceSquare] = brd_pieceIndex[sq];
		brd_pieceList[(pce << 4) | brd_pieceIndex[lastPceSquare]] = lastPceSquare;
		brd_pieceList[(pce << 4) | brd_pieceCount[pce]] = EMPTY; // Ures
		brd_Material[currentPlayer] -= PieceValue[pce];
	}
	function BIT_MOVE(from, to, captured, promoted, castled) {
		return (from | (to << 7) | (captured << 14) | (promoted << 15) | (castled << 19)); // Lepes tarolasa 20 bit
	}
	/*
	0000 0000 0000 0111 1111 -> Ahonnan lepunk (m & 0x7F)
	0000 0011 1111 1000 0000 -> Ahova lepunk ((m >> 7) & 0x7F)
	0000 0100 0000 0000 0000 -> Leutes jelzes (m & CAPTURE_MASK)
	0111 1000 0000 0000 0000 -> Gyalog bevaltas ((m >> 15) & 0xF)
	1000 0000 0000 0000 0000 -> Sancolas jelzes (m & CASTLED_MASK)
	-----------------------------------------------------------------
	0111 1100 0000 0000 0000 -> Utes vagy Bevaltas (m & TACTICAL_MASK)
	1111 1100 0000 0000 0000 -> Utes, Bevaltas, Sanc (m & DANGER_MASK)
	*/


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function makeMove(move) {

		var to = TOSQ(move); // Ahova lepunk
		var from = FROMSQ(move); // Ahonnan lepunk
		var MOVED_PIECE = CHESS_BOARD[from]; // Akivel leptunk
		var PROMOTED_PIECE = PROMOTED(move); // Gyalog bevaltas
		var CAPTURED_PIECE = CHESS_BOARD[to]; // Ahova leptunk

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		MOVE_HISTORY[moveCount] = { // Lepeselozmeny mentese
			capturedPCE	: CAPTURED_PIECE,
			hashKeyHigh	: brd_hashKeyHigh,
			hashKeyLow	: brd_hashKeyLow,
			fiftyMove	: brd_fiftyMove,
			castleBIT	: castleRights,
			EPsquare	: EN_PASSANT,
			move		: move
		};

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		brd_fiftyMove++; // 50 lepes szabaly

		if (EN_PASSANT != 0) HASH_EP(); // En Passant hashKey

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (CAPTURED_PIECE) // Ha leutottunk valakit
		{
			brd_fiftyMove = 0; // 50 lepes nullazasa
			HASH_PCE(CAPTURED_PIECE, to); // Babu hashKey
			DELETE_PCE(CAPTURED_PIECE, to, (currentPlayer^8)); // Babu Torlese
		} 
		else if (move & CAPTURE_MASK) // En Passant Lepes
		{
			if (currentPlayer) // Fekete Gyaloggal
			{
				EN_PASSANT = to-16; // Koztes tarolasra
				HASH_PCE(WHITE_PAWN, EN_PASSANT); // Babu hashKey
				DELETE_PCE(WHITE_PAWN, EN_PASSANT, WHITE); // Feher Gyalog Torlese
			}
			else // Feher Gyaloggal
			{
				EN_PASSANT = to+16; // Koztes tarolasra
				HASH_PCE(BLACK_PAWN, EN_PASSANT); // Babu hashKey
				DELETE_PCE(BLACK_PAWN, EN_PASSANT, BLACK); // Fekete Gyalog Torlese
			}
		}
		else if (move & CASTLED_MASK) // Sancolaskor Bastya mozgatasa
		{
			switch(to) {
				case SQUARES.C1:
					HASH_PCE(WHITE_ROOK, SQUARES.A1); // Babu hashKey
					HASH_PCE(WHITE_ROOK, SQUARES.D1); // Babu hashKey
					MOVE_PCE(WHITE_ROOK, SQUARES.A1, SQUARES.D1); // Babu mozgatasa
				break;
				case SQUARES.C8:
					HASH_PCE(BLACK_ROOK, SQUARES.A8); // Babu hashKey
					HASH_PCE(BLACK_ROOK, SQUARES.D8); // Babu hashKey
					MOVE_PCE(BLACK_ROOK, SQUARES.A8, SQUARES.D8); // Babu mozgatasa
				break;
				case SQUARES.G1:
					HASH_PCE(WHITE_ROOK, SQUARES.H1); // Babu hashKey
					HASH_PCE(WHITE_ROOK, SQUARES.F1); // Babu hashKey
					MOVE_PCE(WHITE_ROOK, SQUARES.H1, SQUARES.F1); // Babu mozgatasa
				break;
				case SQUARES.G8:
					HASH_PCE(BLACK_ROOK, SQUARES.H8); // Babu hashKey
					HASH_PCE(BLACK_ROOK, SQUARES.F8); // Babu hashKey
					MOVE_PCE(BLACK_ROOK, SQUARES.H8, SQUARES.F8); // Babu mozgatasa
				break;
				default: break;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		EN_PASSANT = 0; // En passant torles

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if ((MOVED_PIECE & 0x07) === PAWN) // Ha Gyaloggal leptunk
		{
			brd_fiftyMove = 0; // 50 lepes nullazasa

			if (Math.abs(from - to) === 32) // En Passant mentese
			{
				EN_PASSANT = (to + (currentPlayer ? -16 : 16));
				HASH_EP(); // En Passant hashKey
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		HASH_PCE(MOVED_PIECE, from); // Babu hashKey
		HASH_PCE(MOVED_PIECE, to); // Babu hashKey
		MOVE_PCE(MOVED_PIECE, from, to); // Babu mozgatasa

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (PROMOTED_PIECE != 0) // Gyalog bevaltasa
		{
			HASH_PCE(MOVED_PIECE, to); // Babu hashKey (Gyalog)
			HASH_PCE(PROMOTED_PIECE, to); // Babu hashKey (Tiszt)
			DELETE_PCE(MOVED_PIECE, to, currentPlayer); // Gyalog torlese
			ADDING_PCE(PROMOTED_PIECE, to, currentPlayer); // Tiszt hozzaadasa
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		HASH_CA(); // Sancolas hashKey

		castleRights &= CastlePerm[from] & CastlePerm[to]; // Sancolas maszk

		HASH_CA(); // Sancolas hashKey

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		currentPlayer ^= 8; // Ember valtas
		HASH_SIDE(); // Aki lephet hashKey
		moveCount++; // Lepes szamlalo
		boardPly++; // Melyseg szamlalo

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (isCheck(currentPlayer^8)) { // Sakk miatt ervenytelen
			unMakeMove();
			return false;
		}

		return true;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function unMakeMove() {

		moveCount--; // Lepes szamlalo
		boardPly--; // Melyseg szamlalo

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var move = MOVE_HISTORY[moveCount].move;
		EN_PASSANT = MOVE_HISTORY[moveCount].EPsquare;
		castleRights = MOVE_HISTORY[moveCount].castleBIT;
		brd_fiftyMove = MOVE_HISTORY[moveCount].fiftyMove;
		brd_hashKeyLow = MOVE_HISTORY[moveCount].hashKeyLow;
		brd_hashKeyHigh = MOVE_HISTORY[moveCount].hashKeyHigh;
		var CAPTURED_PIECE = MOVE_HISTORY[moveCount].capturedPCE;

		var to = TOSQ(move); // Ahova leptunk
		var from = FROMSQ(move); // Ahonnan leptunk
		var MOVED_PCE = CHESS_BOARD[to]; // Akivel visszalepunk
		var PROMOTED_PIECE = PROMOTED(move); // Gyalog bevaltas

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		MOVE_PCE(MOVED_PCE, to, from); // Babu mozgatasa (TO->FROM)

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (CAPTURED_PIECE) // Leutott babu visszavonasa
		{
			ADDING_PCE(CAPTURED_PIECE, to, currentPlayer); // Leutott babu hozzaadasa
		}
		else if (move & CAPTURE_MASK) // En Passant Lepes visszavonasa
		{
			currentPlayer ? ADDING_PCE(BLACK_PAWN, (EN_PASSANT + 16), BLACK) // Fekete Gyalog vissza
						  : ADDING_PCE(WHITE_PAWN, (EN_PASSANT - 16), WHITE); // Feher Gyalog vissza
		}
		else if (move & CASTLED_MASK) // Sancolas torlesekor a Bastya mozgatasa
		{
			switch(to) {
				case SQUARES.C1: MOVE_PCE(WHITE_ROOK, SQUARES.D1, SQUARES.A1); break;
				case SQUARES.C8: MOVE_PCE(BLACK_ROOK, SQUARES.D8, SQUARES.A8); break;
				case SQUARES.G1: MOVE_PCE(WHITE_ROOK, SQUARES.F1, SQUARES.H1); break;
				case SQUARES.G8: MOVE_PCE(BLACK_ROOK, SQUARES.F8, SQUARES.H8); break;
				default: break;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		currentPlayer ^= 8; // Ember valtas

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (PROMOTED_PIECE != 0) // Gyalog bevaltasanak visszavonasa
		{
			DELETE_PCE(PROMOTED_PIECE, from, currentPlayer); // Tiszt torlese
			ADDING_PCE((currentPlayer | PAWN), from, currentPlayer); // Gyalog hozzaadasa
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		return true;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function isMate(Score) { return Score >= ISMATE || Score <= -ISMATE; }

	function isCheck(Side) { return isSquareUnderAttack(brd_pieceList[(Side | KING) << 4], Side); }


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function isSquareUnderAttack(square, us) {

		var next_sq	= 0; // Ahol keresunk
		var enemy	= us^8; // Ellenfel
		var dir		= 0; // Lepes irany

		// Gyalog tamadas
		if (us === WHITE) {
			if (CHESS_BOARD[(square - 15)] === BLACK_PAWN
			 || CHESS_BOARD[(square - 17)] === BLACK_PAWN) { // Feher Kiraly
				return 1;
			}
		} else {
			if (CHESS_BOARD[(square + 15)] === WHITE_PAWN
			 || CHESS_BOARD[(square + 17)] === WHITE_PAWN) { // Fekete Kiraly
				return 1;
			}
		}

		// Huszar tamadas
		for (dir = 0; dir < 8; dir++)
		{
			next_sq = (square + KnightMoves[dir]);

			if (!(next_sq & 0x88) && CHESS_BOARD[next_sq] === (enemy | KNIGHT)) {
				return 1;
			}
		}

		// Futo, Vezer tamadas
		for (dir = 0; dir < 4; dir++)
		{
			next_sq = (square + BishopMoves[dir]);

			while (!(next_sq & 0x88))
			{
				if (CHESS_BOARD[next_sq]) {
					if (CHESS_BOARD[next_sq] === (enemy | QUEEN)
					 || CHESS_BOARD[next_sq] === (enemy | BISHOP)) {
						return 1;
					}
					break;
				}
				next_sq += BishopMoves[dir]; // Kovetkezo Mezo
			}
		}

		// Bastya, Vezer tamadas
		for (dir = 0; dir < 4; dir++)
		{
			next_sq = (square + RookMoves[dir]);

			while (!(next_sq & 0x88))
			{
				if (CHESS_BOARD[next_sq]) {
					if (CHESS_BOARD[next_sq] === (enemy | QUEEN)
					 || CHESS_BOARD[next_sq] === (enemy | ROOK)) {
						return 1;
					}
					break;
				}
				next_sq += RookMoves[dir]; // Kovetkezo Mezo
			}
		}

		// Kiraly "tamadas"
		for (dir = 0; dir < 8; dir++)
		{
			next_sq = (square + KingMoves[dir]);

			if (!(next_sq & 0x88) && CHESS_BOARD[next_sq] === (enemy | KING)) {
				return 1;
			}
		}

		return NOT_IN_CHECK;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function Evaluation() {

		var Rank		= 0; // Sor
		var Score		= 0; // Pont
		var PCE			= 0; // Babu
		var File		= 0; // Oszlop
		var Draw		= 1; // Dontetlen
		var pieceIdx	= 0; // Babu index

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	//											DONTETLEN
	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (brd_pieceCount[WHITE_PAWN] == 0 && brd_pieceCount[BLACK_PAWN] == 0) { // Nincs Gyalog
			if (brd_pieceCount[WHITE_QUEEN] == 0 && brd_pieceCount[BLACK_QUEEN] == 0) { // Nincs Vezer
				if (brd_pieceCount[WHITE_ROOK] == 0 && brd_pieceCount[BLACK_ROOK] == 0) { // Nincs Bastya
					if (brd_pieceCount[WHITE_BISHOP] == 0 && brd_pieceCount[BLACK_BISHOP] == 0) { // Nincs Futo
						if (brd_pieceCount[WHITE_KNIGHT] < 3 && brd_pieceCount[BLACK_KNIGHT] < 3) { // Max 2-2 Huszar
							return 0;
						}
					} else if (brd_pieceCount[WHITE_KNIGHT] == 0 && brd_pieceCount[BLACK_KNIGHT] == 0) { // Nincs Huszar
						if (Math.abs(brd_pieceCount[WHITE_BISHOP] - brd_pieceCount[BLACK_BISHOP]) < 2) { // Max Futo diff < 2
							return 0;
						}
					} else if ((brd_pieceCount[WHITE_KNIGHT] < 3 && brd_pieceCount[WHITE_BISHOP] == 0) // Max 2 Huszar, 0 Futo (Feher) ->
						    || (brd_pieceCount[WHITE_KNIGHT] == 0 && brd_pieceCount[WHITE_BISHOP] == 1)) { // -> 0 Huszar, 1 Futo (Feher)
						if ((brd_pieceCount[BLACK_KNIGHT] < 3 && brd_pieceCount[BLACK_BISHOP] == 0) // Max 2 Huszar, 0 Futo (Fekete) ->
						 || (brd_pieceCount[BLACK_KNIGHT] == 0 && brd_pieceCount[BLACK_BISHOP] == 1)) { // -> 0 Huszar, 1 Futo (Fekete)
							return 0;
						 }
					}
				} else if (brd_pieceCount[WHITE_ROOK] == 1 && brd_pieceCount[BLACK_ROOK] == 1) { // 1-1 Bastya
					if ((brd_pieceCount[WHITE_KNIGHT] + brd_pieceCount[WHITE_BISHOP]) == 0 // Feher(Huszar+Futo) == 0
					 && (brd_pieceCount[BLACK_KNIGHT] + brd_pieceCount[BLACK_BISHOP]) == 0) { // Fekete(Huszar+Futo) == 0
							return 0;
					} else if ((brd_pieceCount[WHITE_KNIGHT] + brd_pieceCount[WHITE_BISHOP]) < 2 // Feher(Huszar+Futo) < 2
					 && (brd_pieceCount[BLACK_KNIGHT] + brd_pieceCount[BLACK_BISHOP]) < 2) { // Fekete(Huszar+Futo) < 2
						Draw = 10;
					}
				} else if (brd_pieceCount[WHITE_ROOK] == 1 && brd_pieceCount[BLACK_ROOK] == 0) { // 1-0 Bastya
					if ((brd_pieceCount[WHITE_KNIGHT] + brd_pieceCount[WHITE_BISHOP]) == 0 // Feher(Huszar+Futo) == 0
					&& ((brd_pieceCount[BLACK_KNIGHT] + brd_pieceCount[BLACK_BISHOP]) == 1 // Fekete(Huszar+Futo) == 1 ->
					 || (brd_pieceCount[BLACK_KNIGHT] + brd_pieceCount[BLACK_BISHOP]) == 2)) { // -> Fekete(Huszar+Futo) == 2
						Draw = 4;
					}
				} else if (brd_pieceCount[WHITE_ROOK] == 0 && brd_pieceCount[BLACK_ROOK] == 1) { // 0-1 Bastya
					if ((brd_pieceCount[BLACK_KNIGHT] + brd_pieceCount[BLACK_BISHOP]) == 0 // Fekete(Huszar+Futo) == 0
					&& ((brd_pieceCount[WHITE_KNIGHT] + brd_pieceCount[WHITE_BISHOP]) == 1 // Feher(Huszar+Futo) == 1 ->
					 || (brd_pieceCount[WHITE_KNIGHT] + brd_pieceCount[WHITE_BISHOP]) == 2)) { // -> Feher(Huszar+Futo) == 2
						Draw = 4;
					}
				}
			}
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		Score = brd_Material[WHITE] - brd_Material[BLACK]; // Anyag ertekelese

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Gyalog oszlopok inicializalasa
		for (var index = 0; index < 10; index++) {
			PawnRanksWhite[index] = RANKS.RANK_8; // Feher Gyalog Oszlop
			PawnRanksBlack[index] = RANKS.RANK_1; // Fekete Gyalog Oszlop
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Gyalog inicializalas
		pieceIdx = WHITE_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			if (PawnRanksWhite[File] > Rank) { // Leghatso Feher gyalog az oszlopban
				PawnRanksWhite[File] = Rank;
			}

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Gyalog inicializalas
		pieceIdx = BLACK_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			if (PawnRanksBlack[File] < Rank) { // Leghatso Fekete gyalog az oszlopban
				PawnRanksBlack[File] = Rank;
			}

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	//											BABUK ERTEKELESE
	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Kiraly
		PCE = brd_pieceList[WHITE_KING << 4];
		if (brd_Material[BLACK] <= EndGameMate) { // Vegjatek esten

			Score += KingEndMask[PCE]; // Pozicio pontozas

		} else { // Kozepjatek

			Score += KingMask[PCE]; // Pozicio pontozas

		}

	// Fekete Kiraly
		PCE = brd_pieceList[BLACK_KING << 4];
		if (brd_Material[WHITE] <= EndGameMate) { // Vegjatek esten

			Score -= KingEndMask[TableMirror[PCE]]; // Pozicio pontozas

		} else { // Kozepjatek

			Score -= KingMask[TableMirror[PCE]]; // Pozicio pontozas

		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Vezer
		pieceIdx = WHITE_QUEEN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			File = TableFiles[PCE];

			if (PawnRanksWhite[File] == RANKS.RANK_8) { // Felig nyitott oszlop
				if (PawnRanksBlack[File] == RANKS.RANK_1) { // Teljesen Nyitott
					Score += QueenOpenFile;
				} else {
					Score += QueenSemiOpen;
				}
			}

			Score += RookMask[PCE]; // Pozicio pontozas

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Vezer
		pieceIdx = BLACK_QUEEN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			File = TableFiles[PCE];

			if (PawnRanksBlack[File] == RANKS.RANK_1) { // Felig nyitott oszlop
				if (PawnRanksWhite[File] == RANKS.RANK_8) { // Teljesen Nyitott
					Score -= QueenOpenFile;
				} else {
					Score -= QueenSemiOpen;
				}
			}

			Score -= RookMask[TableMirror[PCE]]; // Pozicio pontozas

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Bastya
		pieceIdx = WHITE_ROOK << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			File = TableFiles[PCE];

			if (PawnRanksWhite[File] == RANKS.RANK_8) { // Felig nyitott oszlop
				if (PawnRanksBlack[File] == RANKS.RANK_1) { // Teljesen Nyitott
					Score += RookOpenFile;
				} else {
					Score += RookSemiOpen;
				}
			}

			Score += RookMask[PCE]; // Pozicio pontozas

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Bastya
		pieceIdx = BLACK_ROOK << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			File = TableFiles[PCE];

			if (PawnRanksBlack[File] == RANKS.RANK_1) { // Felig nyitott oszlop
				if (PawnRanksWhite[File] == RANKS.RANK_8) { // Teljesen Nyitott
					Score -= RookOpenFile;
				} else {
					Score -= RookSemiOpen;
				}
			}

			Score -= RookMask[TableMirror[PCE]]; // Pozicio pontozas

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Futo
		pieceIdx = WHITE_BISHOP << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Score += BishopMask[PCE]; // Pozicio pontozas

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Futo
		pieceIdx = BLACK_BISHOP << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Score -= BishopMask[TableMirror[PCE]]; // Pozicio pontozas

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Huszar
		pieceIdx = WHITE_KNIGHT << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Score += KnightMask[PCE]; // Pozicio pontozas

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Huszar
		pieceIdx = BLACK_KNIGHT << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Score -= KnightMask[TableMirror[PCE]]; // Pozicio pontozas

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Gyalog
		pieceIdx = WHITE_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			if (PawnRanksWhite[File-1] == RANKS.RANK_8 && PawnRanksWhite[File+1] == RANKS.RANK_8) { // Elkulonitett Gyalog
				Score += PawnIsolated;
			}

			if (PawnRanksBlack[File] <= Rank && PawnRanksBlack[File-1] <= Rank && PawnRanksBlack[File+1] <= Rank) { // Telt Gyalog
				Score += PawnPassed[Rank];
			}

			Score += PawnMask[PCE]; // Pozicio pontozas

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Gyalog
		pieceIdx = BLACK_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			if (PawnRanksBlack[File-1] == RANKS.RANK_1 && PawnRanksBlack[File+1] == RANKS.RANK_1) { // Elkulonitett Gyalog
				Score -= PawnIsolated;
			}

			if (PawnRanksWhite[File] >= Rank && PawnRanksWhite[File-1] >= Rank && PawnRanksWhite[File+1] >= Rank) { // Telt Gyalog
				Score -= PawnPassed[9-Rank];
			}

			Score -= PawnMask[TableMirror[PCE]]; // Pozicio pontozas

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (brd_pieceCount[WHITE_BISHOP] >= 2) Score += BishopPair; // Feher Futopar
		if (brd_pieceCount[BLACK_BISHOP] >= 2) Score -= BishopPair; // Fekete Futopar

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		Score = Score / Draw | 0; // Ketes dontetlennel nem 0-at adunk vissza

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (currentPlayer === WHITE) {
			return Score;
		} else {
			return -Score;
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function GenerateAllMoves(capturesOnly) {

		var pieceType	= 0; // Akivel lepunk
		var pieceIdx	= 0; // Babu indexeles
		var from		= 0; // Ahonnan lepunk
		var next		= 0; // Ahova lepunk
		var Score		= 0; // Lepes pont
		var Move		= 0; // Lepes bit
		var dir			= 0; // Lepes irany

		brd_moveStart[boardPly + 1] = brd_moveStart[boardPly]; // Hack

		if (currentPlayer === WHITE) // FEHER OLDAL
		{
			pieceIdx = WHITE_PAWN << 4;
			from = brd_pieceList[pieceIdx++];
			while (from != EMPTY)
			{
				next = from - 16; // Elore lepes

				if (capturesOnly === false) // Ures mezok
				{
					if (CHESS_BOARD[next] == 0) // Ures mezo
					{
						if (TableRanks[from] == RANKS.RANK_7) // Gyalog bevaltas
						{
							AddQuietMove(from, next, WHITE_QUEEN, 0);
							AddQuietMove(from, next, WHITE_ROOK,  0);
							AddQuietMove(from, next, WHITE_BISHOP, 0);
							AddQuietMove(from, next, WHITE_KNIGHT, 0);
						} else {
							AddQuietMove(from, next, 0, 0); // Sima lepes

							if (TableRanks[from] == RANKS.RANK_2 && CHESS_BOARD[from - 32] == 0) // Dupla lepes
							{
								AddQuietMove(from, from - 32, 0, 0);
							}
						}
					}
				} else if (CHESS_BOARD[next] == 0 && TableRanks[from] == RANKS.RANK_7) { // Vezer Promocio (Quiescence)

					AddQuietMove(from, next, WHITE_QUEEN, 0);
				}

				next = from - 15; // Utes egyik oldal

				if (!(next & 0x88)) { // Nem logunk ki a tablarol

					if (CHESS_BOARD[next] && (CHESS_BOARD[next] & 0x8) === BLACK) // Ellenfel
					{
						Score = 1000005 + (100 * MvvLvaScores[CHESS_BOARD[next]]); // Pontszam

						if (TableRanks[from] == RANKS.RANK_7) // Gyalog bevaltas
						{
							AddCaptureMove(BIT_MOVE(from, next, 1, WHITE_QUEEN, 0), Score);
							AddCaptureMove(BIT_MOVE(from, next, 1, WHITE_ROOK,  0), Score);
							AddCaptureMove(BIT_MOVE(from, next, 1, WHITE_BISHOP, 0), Score);
							AddCaptureMove(BIT_MOVE(from, next, 1, WHITE_KNIGHT, 0), Score);
						} else {
							AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), Score); // Nincs gyalogbevaltas
						}
					} else if (CHESS_BOARD[next] == 0 && EN_PASSANT != 0 && EN_PASSANT == next) { // En Passant

						Score = 1000105; // En Passant Pontszam

						AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), Score);
					}
				}

				next = from - 17; // Utes masik oldal

				if (!(next & 0x88)) { // Nem logunk ki a tablarol

					if (CHESS_BOARD[next] && (CHESS_BOARD[next] & 0x8) === BLACK) // Ellenfel
					{
						Score = 1000005 + (100 * MvvLvaScores[CHESS_BOARD[next]]); // Pontszam

						if (TableRanks[from] == RANKS.RANK_7) // Gyalog bevaltas
						{
							AddCaptureMove(BIT_MOVE(from, next, 1, WHITE_QUEEN, 0), Score);
							AddCaptureMove(BIT_MOVE(from, next, 1, WHITE_ROOK,  0), Score);
							AddCaptureMove(BIT_MOVE(from, next, 1, WHITE_BISHOP, 0), Score);
							AddCaptureMove(BIT_MOVE(from, next, 1, WHITE_KNIGHT, 0), Score);
						} else {
							AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), Score); // Nincs gyalogbevaltas
						}
					} else if (CHESS_BOARD[next] == 0 && EN_PASSANT != 0 && EN_PASSANT == next) { // En Passant

						Score = 1000105; // En Passant Pontszam

						AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), Score);
					}
				}

				from = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (capturesOnly === false) // Ures mezok
			{
				// Sancolas Kiraly oldal
				if (castleRights & CASTLEBIT.WKCA) {
					if (CHESS_BOARD[SQUARES.F1] == 0 && CHESS_BOARD[SQUARES.G1] == 0) {
						if (!isSquareUnderAttack(SQUARES.E1, WHITE) && !isSquareUnderAttack(SQUARES.F1, WHITE)) {
							AddQuietMove(SQUARES.E1, SQUARES.G1, 0, 1);
						}
					}
				}
				// Sancolas Vezer oldal
				if (castleRights & CASTLEBIT.WQCA) {
					if (CHESS_BOARD[SQUARES.D1] == 0 && CHESS_BOARD[SQUARES.C1] == 0 && CHESS_BOARD[SQUARES.B1] == 0) {
						if (!isSquareUnderAttack(SQUARES.E1, WHITE) && !isSquareUnderAttack(SQUARES.D1, WHITE)) {
							AddQuietMove(SQUARES.E1, SQUARES.C1, 0, 1);
						}
					}
				}
			}

		} else { // FEKETE OLDAL >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			pieceIdx = BLACK_PAWN << 4;
			from = brd_pieceList[pieceIdx++];
			while (from != EMPTY)
			{
				next = from + 16; // Elore lepes

				if (capturesOnly === false) // Ures mezok
				{
					if (CHESS_BOARD[next] == 0) // Ures mezo
					{
						if (TableRanks[from] == RANKS.RANK_2) // Gyalog bevaltas
						{
							AddQuietMove(from, next, BLACK_QUEEN, 0);
							AddQuietMove(from, next, BLACK_ROOK,  0);
							AddQuietMove(from, next, BLACK_BISHOP, 0);
							AddQuietMove(from, next, BLACK_KNIGHT, 0);
						} else {
							AddQuietMove(from, next, 0, 0); // Sima lepes

							if (TableRanks[from] == RANKS.RANK_7 && CHESS_BOARD[from + 32] == 0) // Dupla lepes
							{
								AddQuietMove(from, from + 32, 0, 0);
							}
						}
					}
				} else if (CHESS_BOARD[next] == 0 && TableRanks[from] == RANKS.RANK_2) { // Vezer Promocio (Quiescence)

					AddQuietMove(from, next, BLACK_QUEEN, 0);
				}

				next = from + 15; // Utes egyik oldal

				if (!(next & 0x88)) { // Nem logunk ki a tablarol

					if (CHESS_BOARD[next] && (CHESS_BOARD[next] & 0x8) === WHITE) // Ellenfel
					{
						Score = 1000005 + (100 * MvvLvaScores[CHESS_BOARD[next]]); // Pontszam

						if (TableRanks[from] == RANKS.RANK_2) // Gyalog bevaltas
						{
							AddCaptureMove(BIT_MOVE(from, next, 1, BLACK_QUEEN, 0), Score);
							AddCaptureMove(BIT_MOVE(from, next, 1, BLACK_ROOK,  0), Score);
							AddCaptureMove(BIT_MOVE(from, next, 1, BLACK_BISHOP, 0), Score);
							AddCaptureMove(BIT_MOVE(from, next, 1, BLACK_KNIGHT, 0), Score);
						} else {
							AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), Score); // Nincs gyalogbevaltas
						}
					} else if (CHESS_BOARD[next] == 0 && EN_PASSANT != 0 && EN_PASSANT == next) { // En Passant

						Score = 1000105; // En Passant Pontszam

						AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), Score);
					}
				}

				next = from + 17; // Utes masik oldal

				if (!(next & 0x88)) { // Nem logunk ki a tablarol

					if (CHESS_BOARD[next] && (CHESS_BOARD[next] & 0x8) === WHITE) // Ellenfel
					{
						Score = 1000005 + (100 * MvvLvaScores[CHESS_BOARD[next]]); // Pontszam

						if (TableRanks[from] == RANKS.RANK_2) // Gyalog bevaltas
						{
							AddCaptureMove(BIT_MOVE(from, next, 1, BLACK_QUEEN, 0), Score);
							AddCaptureMove(BIT_MOVE(from, next, 1, BLACK_ROOK,  0), Score);
							AddCaptureMove(BIT_MOVE(from, next, 1, BLACK_BISHOP, 0), Score);
							AddCaptureMove(BIT_MOVE(from, next, 1, BLACK_KNIGHT, 0), Score);
						} else {
							AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), Score); // Nincs gyalogbevaltas
						}
					} else if (CHESS_BOARD[next] == 0 && EN_PASSANT != 0 && EN_PASSANT == next) { // En Passant

						Score = 1000105; // En Passant Pontszam

						AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), Score);
					}
				}

				from = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (capturesOnly === false) // Ures mezok
			{
				// Sancolas Kiraly oldal
				if (castleRights & CASTLEBIT.BKCA) {
					if (CHESS_BOARD[SQUARES.F8] == 0 && CHESS_BOARD[SQUARES.G8] == 0) {
						if (!isSquareUnderAttack(SQUARES.E8, BLACK) && !isSquareUnderAttack(SQUARES.F8, BLACK)) {
							AddQuietMove(SQUARES.E8, SQUARES.G8, 0, 1);
						}
					}
				}
				// Sancolas Vezer oldal
				if (castleRights & CASTLEBIT.BQCA) {
					if (CHESS_BOARD[SQUARES.D8] == 0 && CHESS_BOARD[SQUARES.C8] == 0 && CHESS_BOARD[SQUARES.B8] == 0) {
						if (!isSquareUnderAttack(SQUARES.E8, BLACK) && !isSquareUnderAttack(SQUARES.D8, BLACK)) {
							AddQuietMove(SQUARES.E8, SQUARES.C8, 0, 1);
						}
					}
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Huszar, Kiraly
		for (pieceType = KNIGHT; pieceType <= KING; pieceType++)
		{
			pieceIdx = (currentPlayer | pieceType) << 4;
			from = brd_pieceList[pieceIdx++];
			while (from != EMPTY)
			{
				for (dir = 0; dir < DirNum[pieceType]; dir++)
				{
					next = (from + PieceDir[pieceType][dir]); // Ahova lepunk

					if (next & 0x88) { // Kilogunk a tablarol!
						continue;
					}

					if (CHESS_BOARD[next]) { // Nem ures mezo

						if ((CHESS_BOARD[next] & 0x8) !== currentPlayer) { // Tamadas

							Move = BIT_MOVE(from, next, 1, 0, 0);

							Score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam

							AddCaptureMove(Move, Score);
						}

					} else if (capturesOnly === false) { // Ures mezok

						AddQuietMove(from, next, 0, 0);
					}
				}

				from = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Futo, Bastya, Vezer
		for (pieceType = BISHOP; pieceType <= QUEEN; pieceType++)
		{
			pieceIdx = (currentPlayer | pieceType) << 4;
			from = brd_pieceList[pieceIdx++];
			while (from != EMPTY)
			{
				for (dir = 0; dir < DirNum[pieceType]; dir++)
				{
					next = (from + PieceDir[pieceType][dir]); // Ahova lepunk

					while (!(next & 0x88))
					{
						if (CHESS_BOARD[next]) { // Nem ures mezo

							if ((CHESS_BOARD[next] & 0x8) !== currentPlayer) { // Tamadas

								Move = BIT_MOVE(from, next, 1, 0, 0);

								Score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam

								AddCaptureMove(Move, Score);
							}

							break; // Az adott iranyba nem vizsgalunk tovabb

						} else if (capturesOnly === false) { // Ures mezok

							AddQuietMove(from, next, 0, 0);
						}

						next += PieceDir[pieceType][dir]; // Kovetkezo Mezo
					}
				}

				from = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
			}
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function AddQuietMove(from, to, prom, castle) {

		var Move = BIT_MOVE(from, to, 0, prom, castle);

		if (prom != 0) { // Gyalog bevaltas
			var Score = 950000 + prom;
		} else if (searchKillers[boardPly][0] == Move) { // Gyilkos lepes 1.
			var Score = 900000;
		} else if (searchKillers[boardPly][1] == Move) { // Gyilkos lepes 2.
			var Score = 800000;
		} else {
			var Score = historyTable[CHESS_BOARD[from]][to]; // Elozmeny tabla alapjan
		}

		brd_moveList[brd_moveStart[boardPly + 1]] = Move;
		brd_moveScores[brd_moveStart[boardPly + 1]++] = Score;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function AddCaptureMove(Move, Score) {
		brd_moveList[brd_moveStart[boardPly + 1]] = Move;
		brd_moveScores[brd_moveStart[boardPly + 1]++] = Score;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function PickNextMove(moveNum) {

		var bestNum = moveNum;
		for (var index = moveNum; index < brd_moveStart[boardPly + 1]; ++index) {
			if (brd_moveScores[index] > brd_moveScores[bestNum]) {
				bestNum = index;
			}
		}

		var temp = brd_moveList[moveNum];
		brd_moveList[moveNum] = brd_moveList[bestNum];
		brd_moveList[bestNum] = temp;

		temp = brd_moveScores[moveNum];
		brd_moveScores[moveNum] = brd_moveScores[bestNum];
		brd_moveScores[bestNum] = temp;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function CheckUp() {
		MoveTime = (Date.now() - startTime); // Keresesi ido
		if (MoveTime > maxSearchTime) { // Lejart az ido
			timeStop = 1;
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function Quiescence(alpha, beta) {

		if ((nodes & 2047) == 0) { // Ido ellenorzese
			CheckUp();
		}

		nodes++; // Csomopontok novelese

		if (IsRepetition()) { // Lepesismetles
			return 0;
		}

		if (boardPly > maxDepth - 1) { // Melyseg limit
			return Evaluation();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var Score = Evaluation(); // Ertekeles

		if (Score >= beta) { // Vagas
			return beta;
		}

		if (Score > alpha) { // Update alpha
			alpha = Score;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var Score = -INFINITE; // Pont nullazas
		var currentMove = NOMOVE; // Aktualis lepes
		GenerateAllMoves(true); // Utes lepesek

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; ++index)
		{
			PickNextMove(index);

			currentMove = brd_moveList[index];

			if (!makeMove(currentMove)) { // Lepes ervenyesitese
				continue;
			}

			Score = -Quiescence(-beta, -alpha);

			unMakeMove(); // Lepes visszavonasa

			if (timeStop == 1) { // Ido vagas
				return 0;
			}

			if (Score > alpha) {
				if (Score >= beta) {
					return beta;
				}
				alpha = Score;
			}
		}

		return alpha;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function AlphaBeta(alpha, beta, depth, nullMove) {

		if (depth <= 0) { // Melyseg eleresekor kiertekeles
			return Quiescence(alpha, beta);
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if ((nodes & 2047) == 0) { // Ido ellenorzese
			CheckUp();
		}

		nodes++; // Csomopontok novelese

		if (boardPly != 0 && IsRepetition()) { // Lepesismetles
			return 0;
		}

		if (boardPly > maxDepth - 1) { // Melyseg limit
			return Evaluation();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var Score = -INFINITE;
		var inCheck = isCheck(currentPlayer); // Sakk?

		if (inCheck) { // Sakk vonal tamogatasa
			depth++;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var hashMove = ProbeHashMove(); // Atultetesi tabla

		if (hashMove != NOMOVE && hashMove.depth >= depth) {

			var value = hashMove.score;

			if (value > ISMATE) {
				value -= boardPly;
			} else if (value < -ISMATE) {
				value += boardPly;
			}

			if (hashMove.flags == FLAG_ALPHA && value <= alpha) return value;
			if (hashMove.flags == FLAG_BETA  && value >= beta)  return value;
			if (hashMove.flags == FLAG_EXACT) return value;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (!inCheck && boardPly != 0 && nullMove && depth >= 4
		&& (brd_pieceCount[currentPlayer | KNIGHT] != 0
		 || brd_pieceCount[currentPlayer | BISHOP] != 0
		 || brd_pieceCount[currentPlayer | ROOK]   != 0
		 || brd_pieceCount[currentPlayer | QUEEN]  != 0)) // Metszesek
		{
			if (EN_PASSANT != 0) HASH_EP();
			var enPassant = EN_PASSANT;
			currentPlayer ^= 8;
			EN_PASSANT = 0;
			HASH_SIDE();

			Score = -AlphaBeta(-beta, -beta+1, depth-4, false);

			HASH_SIDE();
			currentPlayer ^= 8;
			EN_PASSANT = enPassant;
			if (EN_PASSANT != 0) HASH_EP();

			if (timeStop == 1) { // Ido vagas
				return 0;
			}

			if (Score >= beta && !isMate(Score)) {
				return beta;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		Score = -INFINITE; // Pont nullazas
		var LegalMove = 0; // Ervenyes lepes
		var OldAlpha = alpha; // Alpha mentese
		var BestMove = NOMOVE; // Legjobb lepes
		var currentMove = NOMOVE; // Aktualis lepes
		var BestScore = -INFINITE; // Legjobb pontszam
		GenerateAllMoves(false); // Minden lepes

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (hashMove != NOMOVE) { // Atultetesi tablabol lepes
			for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; ++index)
			{
				if (brd_moveList[index] == hashMove.move) { // Elore soroljuk
					brd_moveScores[index] = 2000000;
					break;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; ++index)
		{
			PickNextMove(index);

			currentMove = brd_moveList[index];

			if (!makeMove(currentMove)) { // Lepes ervenyesitese
				continue;
			}

			Score = -AlphaBeta(-beta, -alpha, depth-1, true); // Normal kereses

			LegalMove++; // Ervenyes lepesek

			unMakeMove(); // Lepes visszavonasa

			if (timeStop == 1) { // Ido vagas
				return 0;
			}

			if (Score > BestScore) {

				BestScore = Score;
				BestMove = currentMove;

				if (boardPly == 0 && (LegalMove == 1 || Score > alpha)) {
					UpdatePv(currentMove, Score, depth, alpha, beta);
				}

				if (Score > alpha) {
					if (Score >= beta) {

						if ((currentMove & TACTICAL_MASK) == 0) { // Update Killers
							if (searchKillers[boardPly][0] != currentMove) {
								searchKillers[boardPly][1] = searchKillers[boardPly][0];
								searchKillers[boardPly][0] = currentMove;
							}
						}

						StoreHashMove(currentMove, beta, FLAG_BETA, depth);

						return beta;
					}
					alpha = Score;

					if ((currentMove & TACTICAL_MASK) == 0) { // Update History
						historyTable[CHESS_BOARD[FROMSQ(currentMove)]][TOSQ(currentMove)] += depth;
					}
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (LegalMove == 0)
		{
			// console.log(inCheck ? 'MATT' : 'PATT');
			// postMessage(['Redraw', CHESS_BOARD]);
			// for (var index = 0; index < 1000000000; index++);

			if (inCheck)
			return -INFINITE + boardPly; // Matt
			else
			return 0; // Patt
		}

		if (alpha != OldAlpha) {
			StoreHashMove(BestMove, BestScore, FLAG_EXACT, depth);
		} else {
			StoreHashMove(BestMove, alpha, FLAG_ALPHA, depth);
		}

		return alpha;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function InitEnginSearch() {
		hashUsed = 0; // Hash hasznalat nullazas
		brd_HashTable = null; // Atultetesi tabla urites
		brd_HashTable = new Array(HASHENTRIES); // Ures tabla
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function ClearForSearch() {

		nodes = 0; boardPly = 0; bestMove = 0; timeStop = 0;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var i = 0; i < maxDepth; i++) { // Gyilkosok
			searchKillers[i] = [0, 0];
		}

		for (var i = 0; i < 16; i++) { // Elozmeny tabla
			historyTable[i] = new Array(120);
			for (var j = 0; j < 120; j++) {
				historyTable[i][j] = 0;
			}
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function SearchPosition(maxSearchDepth) {

		ClearForSearch(); // Nullazas

		var alpha = -INFINITE;
		var beta = INFINITE;
		var countMove = 0;
		var Score = 0;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (UI_HOST == HOST_TANKY && maxSearchDepth > 0) { // Also szint
			maxDepth = maxSearchDepth;
		} else {
			maxDepth = 64;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		GenerateAllMoves(false, false); // Minden lepes

		for (var index = brd_moveStart[0]; index < brd_moveStart[1]; ++index)
		{
			if (!makeMove(brd_moveList[index])) { // Lepes ervenyesitese
				continue;
			}

			countMove++; // Lepesek szamolasa

			unMakeMove(); // Lepes visszavonasa
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		startTime = Date.now(); // Kezdo ido

		if (UI_HOST == HOST_TANKY) postMessage(['StartedTime', startTime]); // Kezdesi ido

		for (currDepth = 1; currDepth <= maxSearchDepth; currDepth++) // Iterativ melyites
		{
			if (countMove == 1 && currDepth > 5 && bestMove) break; // Egy ervenyes lepes

			Score = AlphaBeta(alpha, beta, currDepth, true, UNKNOWN_CHECK); // Kereses

			if (timeStop == 1) break; // Lejart az ido
		}

		if (UI_HOST == HOST_TANKY) {
			postMessage(['bestMove', bestMove]); // TanKy UI
		} else {
			sendMessage('bestmove '+FormatMove(bestMove.move));
			sendMessage('info hashfull '+Math.round((1000*hashUsed) / HASHENTRIES));
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function UpdatePv(Move, Score, depth, alpha, beta) {

		var flags = FLAG_NONE;
		if (Score > alpha) flags |= FLAG_BETA;
		if (Score < beta)  flags |= FLAG_ALPHA;

		StoreHashMove(Move, Score, flags, depth);

		var pvNum = GetPvLine(depth); bestMove = brd_PvArray[0];

		if (UI_HOST == HOST_TANKY) // TanKy UI
		{
			postMessage(['SearchInfo', bestMove]); // Info kuldes

			/*MoveTime = (Date.now() - startTime); // Keresesi ido

			var pvLine = ''; // PV
			for (var index = 0; index < pvNum; index++) {
				pvLine += ' '+FormatMove(brd_PvArray[index].move);
			}

			if (flags ==  FLAG_BETA) depth += '+';
			if (flags == FLAG_ALPHA) depth += '-';

			console.log('Depth: '+depth+ ' Score: '+Score+' Nodes: '+nodes+' Time: '+MoveTime+' Pv:'+pvLine);*/
		}
		else // WebWorker, Node.js, JSUCI
		{
			MoveTime = (Date.now() - startTime); // Keresesi ido

			var pvLine = ''; // PV
			for (var index = 0; index < pvNum; index++) {
				pvLine += ' '+FormatMove(brd_PvArray[index].move);
			}

			if (Score < -ISMATE) {
				Score = 'mate '+((-INFINITE - Score) / 2); // -Matt
			} else if (Score > ISMATE) {
				Score = 'mate '+((INFINITE - Score + 1) / 2); // +Matt
			} else {
				Score = 'cp '+Score;
			}

			if (flags ==  FLAG_BETA) Score += ' lowerbound';
			if (flags == FLAG_ALPHA) Score += ' upperbound';

			sendMessage('info depth '+currDepth+' score '+Score+' nodes '+nodes+' time '+MoveTime+' pv'+pvLine);
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function sendMessage(msg) {
		if (UI_HOST == HOST_NODEJS) { // Node.js
			nodefs.writeSync(1, msg+'\n');
		} else if (UI_HOST != HOST_WEB) { // WebWorker, JSUCI
			postMessage(msg);
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	var HOST_WEB = 0;
	var HOST_TANKY = 1;
	var HOST_JSUCI = 2;
	var HOST_NODEJS = 3;
	var HOST_WORKER = 4;
	var UI_HOST = HOST_WEB; // Web

	if ((typeof Worker) != 'undefined') { // WebWorker

		UI_HOST = HOST_WORKER;

	} else if ((typeof process) != 'undefined') { // Node.js

		UI_HOST = HOST_NODEJS;
		var nodefs = require('fs');
		process.stdin.setEncoding('utf8');
		process.stdin.on('readable', function() {
			var command = process.stdin.read();
			if (command !== null) {
				onmessage({ data: command });
			}
		});
		process.stdin.on('end', function() {
			process.exit();
		});

	} else if ((typeof lastMessage) != 'undefined') { // JSUCI

		UI_HOST = HOST_JSUCI;

	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	onmessage = function (command) {

		var tokens = [];
		var spec_id = '';

		if (command !== null)
		{
			if (UI_HOST == HOST_TANKY && command.data.constructor === Array) // TanKy UI
			{
				if (command.data[0] == 'HashKeys') // HashKey Szinkronizalas
				{
					SideKeyLow = command.data[1];
					SideKeyHigh = command.data[2];
					PieceKeysLow = command.data[3];
					PieceKeysHigh = command.data[4];
					CastleKeysLow = command.data[5];
					CastleKeysHigh = command.data[6];
				}
				return;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			var messageList = command.data.split('\n');

			for (var messageNum = 0; messageNum < messageList.length; messageNum++)
			{
				message = messageList[messageNum].replace(/(\r\n|\n|\r)/gm,'');
				message = message.trim();
				message = message.replace(/\s+/g,' ');
				tokens  = message.split(' ');
				command = tokens[0];

				if (!command)
				  continue;

				// ############################################################################################

				if (command == 'u') command = 'ucinewgame';

				if (command == 'b') command = 'board';

				if (command == 'q') command = 'quit';

				if (command == 'p') {
					command = 'position';
					if (tokens[1] == 's') {
						tokens[1] = 'startpos';
					}
				}

				if (command == 'g') {
					command = 'go';
					if (tokens[1] == 'd') {
						tokens[1] = 'depth';
					}
				}

				// ############################################################################################

				switch (command) {

					case 'ucinewgame':

						InitEnginSearch(); // Engine Init
						if (tokens[1] != undefined && tokens[1] == 'tanky') UI_HOST = HOST_TANKY; // TanKy
						if (SideKeyLow == 0 && UI_HOST != HOST_TANKY) InitHashKeys(); // New HashKeys Init

					break;

				// ############################################################################################

					case 'position':

						if (SideKeyLow == 0) { // Nincs HashKey
							if (UI_HOST == HOST_TANKY)
							return postMessage(['debug', 'No HashKey! Inditsd ujra a jatekot!']); // TanKy UI
							else
							return sendMessage('info string First send a "u" command for New Game!');
						}

						moveCount = 0; // Lepesszam nullazas
						brd_fiftyMove = 0; // 50 lepes nullazas
						MOVE_HISTORY = new Array(); // Lepes elozmenyek torlese
						START_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 0';

						var arr = getArr('fen', 'moves', tokens); // FEN Parameter

						if (arr.lo > 0) {
							if (arr.lo <= arr.hi) START_FEN  =     tokens[arr.lo]; arr.lo++; // CHESS_BOARD
							if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo]; arr.lo++; // currentPlayer
							if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo]; arr.lo++; // castleRights
							if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo]; arr.lo++; // En Passant
							if (arr.lo <= arr.hi) START_FEN += ' '+parseInt(tokens[arr.lo]); arr.lo++; // "0"
							if (arr.lo <= arr.hi) START_FEN += ' '+parseInt(tokens[arr.lo]); arr.lo++; // "0"
						}

						CHESS_BOARD = FENToBoard(); // Tabla betoltese

						var arr = getArr('moves', 'fen', tokens); // Lepesek

						if (arr.lo > 0 && tokens[arr.lo] != undefined)
						{
							ClearForSearch(); // Hack: Kereses Nullazasa

							for (var index = arr.lo; index <= arr.hi; index++) {
								makeMove(GetMoveFromString(tokens[index]));
								boardPly = 0; // Hack
							}
						}

					break;

				// ############################################################################################

					case 'go':

						maxSearchTime	= getInt('movetime', 0, tokens); // Ido Parameter
					var maxSearchDepth	= getInt('depth', 0, tokens); // Melyseg Parameter

						if (maxSearchTime == 0)
						{
							var movesToGo = getInt('movestogo', 30, tokens); // Time / Move

							if (currentPlayer == WHITE) {
								var Inc = getInt('winc', 0, tokens); // Ido noveles
								var Time = getInt('wtime', 0, tokens); // Feher ido
							} else {
								var Inc = getInt('binc', 0, tokens); // Ido noveles
								var Time = getInt('btime', 0, tokens); // Fekete ido
							}

							maxSearchTime = ((Time / movesToGo) + Inc - 50) | 0; // 50ms for lag
							maxSearchTime = (maxSearchTime < 10) ? 10 : maxSearchTime; // Hack!!
						}

						if (maxSearchDepth > 0) { // Fix melysegnel max 1 ora
							maxSearchTime = 1000 * 60 * 60;
						}

						if (maxSearchDepth <= 0) { // Max melyseg
							maxSearchDepth = 64;
						}

						SearchPosition(maxSearchDepth); // Kereses

					break;

				// ############################################################################################

					case 'uci':

						sendMessage('id name tomitankChess v.'+VERSION);
						sendMessage('id author Tamas Kuzmics');
						sendMessage('option');
						sendMessage('uciok');

					break;

				// ############################################################################################

					case 'ping':

						sendMessage('info string tomitankChess v.'+VERSION+' is alive');

					break;

				// ############################################################################################

					case 'isready':

						sendMessage('readyok');

					break;
		  
				// ############################################################################################

					case 'board':

						sendMessage('board '+boardToFEN());

					break;

				// ############################################################################################

					case 'id':

						spec_id = tokens[1];

					break;

				// ############################################################################################

					case 'quit':
						
						if (UI_HOST == HOST_NODEJS) { // Node.js
							process.exit();
						} else {
							close();
						}

					break;

				// ############################################################################################

					default:

						sendMessage(command+': unknown command');

					break;
				}
			}
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function FormatMove(Move) {

		if (Move == NOMOVE) return 'NULL';

		var msg = '';
		var to = TOSQ(Move);
		var from = FROMSQ(Move);

		msg += Letters[TableFiles[from]-1]+''+TableRanks[from]; // Ahonnan
		msg += Letters[TableFiles[to]-1]+''+TableRanks[to]; // Ahova

		if (PROMOTED(Move) != 0) { // Promocio
			msg += ['', '', 'n', '', '', 'b', 'r', 'q'][PROMOTED(Move) & 0x07];
		}

		return msg;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function GetMoveFromString(moveString) {
		GenerateAllMoves(false, false); // Minden lepes
		for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; ++index)
		{
			if (FormatMove(brd_moveList[index]) == moveString) {
				return brd_moveList[index];
			}
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function getInt(key, def, tokens) {

		for (var index = 0; index < tokens.length; index++)
			if (tokens[index] == key)
				if (index < tokens.length - 1)
					return parseInt(tokens[index+1]);

		return def;
	}

	function getArr(key, to, tokens) {
		var lo = 0;
		var hi = 0;
		for (var index = 0; index < tokens.length; index++) {
			if (tokens[index] == key) {
				lo = index + 1; // assumes at least one item
				hi = lo;
				for (var j = lo; j < tokens.length; j++) {
					if (tokens[j] == to)
					break;
					hi = j;
				}
			}
		}

		return {lo:lo, hi:hi};
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// 32 bites random szam
	function RAND_32() {
		return (Math.floor((Math.random()*255)+1) << 23) | (Math.floor((Math.random()*255)+1) << 16)
			 | (Math.floor((Math.random()*255)+1) <<  8) | Math.floor((Math.random()*255)+1);
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Haskey inicializalasa
	function InitHashKeys() {
		var sq = 0;
		var index = 0;
		SideKeyLow = RAND_32(); // Aki kezd hashKey
		SideKeyHigh = RAND_32(); // Aki kezd hashKey

		for (index = 0; index < 16; index++) { // Babuk hasKey (0-En Passant)
			PieceKeysLow[index] = new Array(120);
			PieceKeysHigh[index] = new Array(120);
			for (sq = 0; sq < 120; sq++) {
				PieceKeysLow[index][sq] = RAND_32();
				PieceKeysHigh[index][sq] = RAND_32();
			}
		}

		for (index = 0; index < 16; index++) { // Sancolas hashKey
			CastleKeysLow[index] = RAND_32();
			CastleKeysHigh[index] = RAND_32();
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Babuk inicializalasa
	function InitPieceList() {
		brd_Material[0] = 0; // Feher anyag
		brd_Material[8] = 0; // Fekete anyag

		for (var i = 0; i < 16; i++) { // BLACK_QUEEN:15
			brd_pieceCount[i] = 0; // Darabszam nullazas
			for (var j = 0; j < 16; j++) { // Max 15 db azonos lehet
				brd_pieceList[(i << 4) | j] = EMPTY; // Mezo nullazas
				// 64-es Mezon nem lehet babu! (0-as mezot hasznaljuk)
				// Igazabol max 9 Vezer lehet, ez 4 bit, ezert (i << 4)
			}
		}

		for (var sq = 0; sq < 120; sq++)
		{
			brd_pieceIndex[sq] = 0; // Mezo index nullazas

			if (CHESS_BOARD[sq] != 0)
			{
				var piece = CHESS_BOARD[sq]; // Babu
				var color = CHESS_BOARD[sq] & 0x8; // Szin

				ADDING_PCE(piece, sq, color); // Babu mentese!
			}
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Aktualis poziciobol hashKey generalas
	function GenerateHashKey() {
		brd_hashKeyLow = 0; // hashKey Low
		brd_hashKeyHigh = 0; // hashKey High

		for (var sq = 0; sq < 120; sq++) { // Babuk 
			if (CHESS_BOARD[sq]) {
				brd_hashKeyLow ^= PieceKeysLow[CHESS_BOARD[sq]][sq];
				brd_hashKeyHigh ^= PieceKeysHigh[CHESS_BOARD[sq]][sq];
			}
		}

		if (currentPlayer == WHITE) { // Aki lephet
			brd_hashKeyLow ^= SideKeyLow;
			brd_hashKeyHigh ^= SideKeyHigh;
		}

		if (EN_PASSANT != 0) { // En Passant
			brd_hashKeyLow ^= PieceKeysLow[0][EN_PASSANT];
			brd_hashKeyHigh ^= PieceKeysHigh[0][EN_PASSANT];
		}

		brd_hashKeyLow ^= CastleKeysLow[castleRights]; // Sancolas
		brd_hashKeyHigh ^= CastleKeysHigh[castleRights]; // Sancolas
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// CHESS_BOARD -> FEN
	function boardToFEN() {

		var piece, emptySquares = 0, FEN = '';

		for (var index = 0; index < 120; index++) {
			if (!(index & 0x88)) {
				var n = CHESS_BOARD[index];
				if ((n & 0x07) === 0x07) { // queen
					piece = 'Q';
				} else if ((n & 0x06) === 0x06) { // rook
					piece = 'R';
				} else if ((n & 0x05) === 0x05) { // bishop
					piece = 'B';
				} else if ((n & 0x03) === 0x03) { // king
					piece = 'K';
				} else if ((n & 0x02) === 0x02) { // knight
					piece = 'N';
				} else if ((n & 0x01) === 0x01) { // pawn
					piece = 'P';
				}

				if (n === 0) { // empty square
					piece = '';
					emptySquares++;
				} else {
					piece = emptySquares ? emptySquares + piece : piece;                
					emptySquares = 0;
				}

				if (n & 0x8) { // black pieces
					piece = piece.toLowerCase();
				}

				FEN += piece;

				if (index % 8 === 7) { // end of rank
					if (n === 0) {
						FEN += emptySquares;
					}
					emptySquares = 0;
					FEN += '/';
				}
			}
		};

		// whose turn?
		FEN = FEN.substr(0, FEN.length - 1) + ' ';
		FEN += currentPlayer === 0 ? 'w' : 'b';

		if (castleRights === 0) { // Nincs mar sancolas
			FEN += ' -';
		} else {
			FEN += ' '; // Szokoz hozzadasa
			if (castleRights & CASTLEBIT.WKCA) FEN += 'K'; // White King side
			if (castleRights & CASTLEBIT.WQCA) FEN += 'Q'; // White Queen side
			if (castleRights & CASTLEBIT.BKCA) FEN += 'k'; // Black King side
			if (castleRights & CASTLEBIT.BQCA) FEN += 'q'; // Black Queen side
		}

		if (EN_PASSANT == 0) { // Nincs En Passant
			FEN += ' -';
		} else {
			FEN += ' '+(Letters[TableFiles[EN_PASSANT]-1]+''+TableRanks[EN_PASSANT]);
		}

		FEN += ' 0'; // 50 Lepes szamlalo
		FEN += ' 0'; // Osszes lepes

		// FEN += ' KQkq - 0 0'; // alap ertek

		return FEN;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// FEN -> CHESS_BOARD
	function FENToBoard() {

		var pieceValueMap = {
			r: BLACK_ROOK,
			n: BLACK_KNIGHT,
			b: BLACK_BISHOP,
			q: BLACK_QUEEN,
			k: BLACK_KING,
			p: BLACK_PAWN,

			R: WHITE_ROOK,
			N: WHITE_KNIGHT,
			B: WHITE_BISHOP,
			Q: WHITE_QUEEN,
			K: WHITE_KING,
			P: WHITE_PAWN
		};

		CHESS_BOARD = [];

		var Fen = START_FEN.split(' ');

		for (var index = 0, len = Fen[0].length; index < len; index++)
		{
			var value = Fen[0][index];
			if (value === '/') {
				for (var j = 0; j < 8; j++) { // Ures mezok
					CHESS_BOARD.push(0);
				}
				continue;
			}

			if (isNaN(value)) { // Babuk feltoltese
				CHESS_BOARD.push(pieceValueMap[value]);
			} else {
				for (var j = 0; j < parseInt(value, 10); j++) { // Ures mezok
					CHESS_BOARD.push(0);
				}
			}
		}

		for (var j = 0; j < 8; j++) { // Ures mezok
			CHESS_BOARD.push(0);
		}

		currentPlayer = Fen[1] === 'w' ? 0 : 8; // White : Black

		for (j = 0; j < 4; j++) { // Sancolasok
			if (Fen[2][j] == ' ') { // Sancolas vege
				break;
			}
			switch(Fen[2][j]) {
				case 'K': castleRights |= CASTLEBIT.WKCA; break; // White King side
				case 'Q': castleRights |= CASTLEBIT.WQCA; break; // White Queen side
				case 'k': castleRights |= CASTLEBIT.BKCA; break; // Black King side
				case 'q': castleRights |= CASTLEBIT.BQCA; break; // Black Queen side
				default: break;
			}
		}

		if (Fen[3] == '-') { // Nincs En Passant
			EN_PASSANT = '-';
		} else {
			EN_PASSANT = parseInt(SQUARES[Fen[3].toUpperCase()]); // En Passant mezo
		}

		InitPieceList(); // Babuk inicializalasa
		GenerateHashKey(); // HashKey generalasa

		return CHESS_BOARD;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Sancolas
	var CastlePerm = [
	 11,  15,  15,  15,   3,  15,  15,   7,		0, 0, 0, 0, 0, 0, 0, 0,
	 15,  15,  15,  15,  15,  15,  15,  15,		0, 0, 0, 0, 0, 0, 0, 0,
	 15,  15,  15,  15,  15,  15,  15,  15,		0, 0, 0, 0, 0, 0, 0, 0,
	 15,  15,  15,  15,  15,  15,  15,  15,		0, 0, 0, 0, 0, 0, 0, 0,
	 15,  15,  15,  15,  15,  15,  15,  15,		0, 0, 0, 0, 0, 0, 0, 0,
	 15,  15,  15,  15,  15,  15,  15,  15,		0, 0, 0, 0, 0, 0, 0, 0,
	 15,  15,  15,  15,  15,  15,  15,  15,		0, 0, 0, 0, 0, 0, 0, 0,
	 14,  15,  15,  15,  12,  15,  15,  13
	];

	// Tukor tabla
	var TableMirror = [
	112, 113, 114, 115, 116, 117, 118, 119,		0, 0, 0, 0, 0, 0, 0, 0,
	 96,  97,  98,  99, 100, 101, 102, 103,		0, 0, 0, 0, 0, 0, 0, 0,
	 80,  81,  82,  83,  84,  85,  86,  87,		0, 0, 0, 0, 0, 0, 0, 0,
	 64,  65,  66,  67,  68,  69,  70,  71,		0, 0, 0, 0, 0, 0, 0, 0,
	 48,  49,  50,  51,  52,  53,  54,  55,		0, 0, 0, 0, 0, 0, 0, 0,
	 32,  33,  34,  35,  36,  37,  38,  39,		0, 0, 0, 0, 0, 0, 0, 0,
	 16,  17,  18,  19,  20,  21,  22,  23,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   1,   2,   3,   4,   5,   6,   7
	];

	// Oszlop tabla
	var TableFiles = [
	  1,   2,   3,   4,   5,   6,   7,   8,		0, 0, 0, 0, 0, 0, 0, 0,
	  1,   2,   3,   4,   5,   6,   7,   8,		0, 0, 0, 0, 0, 0, 0, 0,
	  1,   2,   3,   4,   5,   6,   7,   8,		0, 0, 0, 0, 0, 0, 0, 0,
	  1,   2,   3,   4,   5,   6,   7,   8,		0, 0, 0, 0, 0, 0, 0, 0,
	  1,   2,   3,   4,   5,   6,   7,   8,		0, 0, 0, 0, 0, 0, 0, 0,
	  1,   2,   3,   4,   5,   6,   7,   8,		0, 0, 0, 0, 0, 0, 0, 0,
	  1,   2,   3,   4,   5,   6,   7,   8,		0, 0, 0, 0, 0, 0, 0, 0,
	  1,   2,   3,   4,   5,   6,   7,   8
	];

	// Sor tabla
	var TableRanks = [
	  8,   8,   8,   8,   8,   8,   8,   8,		0, 0, 0, 0, 0, 0, 0, 0,
	  7,   7,   7,   7,   7,   7,   7,   7,		0, 0, 0, 0, 0, 0, 0, 0,
	  6,   6,   6,   6,   6,   6,   6,   6,		0, 0, 0, 0, 0, 0, 0, 0,
	  5,   5,   5,   5,   5,   5,   5,   5,		0, 0, 0, 0, 0, 0, 0, 0,
	  4,   4,   4,   4,   4,   4,   4,   4,		0, 0, 0, 0, 0, 0, 0, 0,
	  3,   3,   3,   3,   3,   3,   3,   3,		0, 0, 0, 0, 0, 0, 0, 0,
	  2,   2,   2,   2,   2,   2,   2,   2,		0, 0, 0, 0, 0, 0, 0, 0,
	  1,   1,   1,   1,   1,   1,   1,   1
	];

	// Kiraly
	var KingMask = [
	-70, -70, -70, -70, -70, -70, -70, -70,		0, 0, 0, 0, 0, 0, 0, 0,
	-70, -70, -70, -70, -70, -70, -70, -70,		0, 0, 0, 0, 0, 0, 0, 0,
	-70, -70, -70, -70, -70, -70, -70, -70,		0, 0, 0, 0, 0, 0, 0, 0,
	-70, -70, -70, -70, -70, -70, -70, -70,		0, 0, 0, 0, 0, 0, 0, 0,
	-70, -70, -70, -70, -70, -70, -70, -70,		0, 0, 0, 0, 0, 0, 0, 0,
	-50, -50, -50, -50, -50, -50, -50, -50,		0, 0, 0, 0, 0, 0, 0, 0,
	-30, -30, -30, -30, -30, -30, -30, -30,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   5,   5, -10, -10,   0,  10,   5
	];

	// Kiraly vegjatek
	var KingEndMask = [
	-50, -10,   0,   0,   0,   0, -10, -50,		0, 0, 0, 0, 0, 0, 0, 0,
	-10,   0,  10,  10,  10,  10,   0, -10,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,  10,  20,  20,  20,  20,  10,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,  10,  20,  40,  40,  20,  10,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,  10,  20,  40,  40,  20,  10,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,  10,  20,  20,  20,  20,  10,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	-10,   0,  10,  10,  10,  10,   0, -10,		0, 0, 0, 0, 0, 0, 0, 0,
	-50, -10,   0,   0,   0,   0, -10, -50
	];

	// Bastya
	var RookMask = [
	  0,   0,   5,  10,  10,   5,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	 25,  25,  25,  25,  25,  25,  25,  25,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   5,  10,  10,   5,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   5,  10,  10,   5,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   5,  10,  10,   5,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   5,  10,  10,   5,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   5,  10,  10,   5,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   5,  10,  10,   5,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	];

	// Futo
	var BishopMask = [
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,  10,  10,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,  10,  15,  15,  10,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,  10,  15,  20,  20,  15,  10,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,  10,  15,  20,  20,  15,  10,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,  10,  15,  15,  10,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,  10,  10,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0, -10,   0,   0, -10,   0,   0
	];

	// Huszar
	var KnightMask = [
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   5,  10,  10,   5,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  5,  10,  10,  20,  20,  10,  10,   5,		0, 0, 0, 0, 0, 0, 0, 0,
	  5,  10,  15,  20,  20,  15,  10,   5,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,  10,  20,  20,  10,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,  10,  10,  10,  10,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   5,   5,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0, -10,   0,   0,   0,   0, -10,   0
	];

	// Gyalog
	var PawnMask = [
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	 20,  20,  20,  30,  30,  20,  20,  20,		0, 0, 0, 0, 0, 0, 0, 0,
	 10,  10,  10,  20,  20,  10,  10,  10,		0, 0, 0, 0, 0, 0, 0, 0,
	  5,   5,   5,  10,  10,   5,   5,   5,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,  10,  20,  20,  10,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  5,   0,   0,   5,   5,   0,   0,   5,		0, 0, 0, 0, 0, 0, 0, 0,
	 10,  10,   0, -10, -10,   0,  10,  10,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0
	];
