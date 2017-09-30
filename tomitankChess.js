/*
* tomitankChess v.1.4 by tomitank
* Date:2017.09.28.
* Contact:tomitank@freemail.hu , tanky.hu@gmail.com
* [^:]// .* regular search->comment del
*/

// - Thanks Fabien Letouzey for the great source code of the program Fruit 2.1. 
// - Thanks again Colin Jenkins (Lozza author) for the great source code.
// - Thanks Gary Linscott for the garbochess source code
// - Thanks Stockfish authors
// - Thanks VICE author

// - Estimated level: ~2500 elo

// - Download link: https://github.com/tomitank/tomitankChess
// - More info: http://talkchess.com/forum/viewtopic.php?t=65200
// - Web: http://tanky.hu or http://mobil.tanky.hu
// - Android app: https://play.google.com/store/apps/details?id=sakk.tanky.hu
// - iOS app: https://itunes.apple.com/us/app/sakk-ingyenes/id1150654415?l=hu&ls=1&mt=8

// TODO!
// - Pawn Eval Hash
// - Use TT at depth == 0
// - Tune Search algorithm

// Have fun with tomitankChess!

// Tamás Kuzmics

// Valtozok
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
var brd_Material		= new Array(8); // Anyag (Feher,Fekete)
var brd_pieceCount		= new Array(16); // Babuk szama
var brd_vectorDelta		= new Array(256); // Vektor tabla
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
var WKING_ZONE			= new Array(120); // Kiraly zona
var BKING_ZONE			= new Array(120); // Kiraly zona
var DISTANCE			= new Array(120); // SQ Kulonbseg
var MOVE_HISTORY		= new Array(); // Lepeselozmenyek
var UI_MODE				= 0; // Web:0, Worker:1, Node:2
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
var PawnDoubled		= -10; // Dupla Gyalog
var BishopPair		= 50; // Futo par plusz pont
var PawnBackward	= -8; // Hatrahagyott Gyalog
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
var PawnShelter		= [ 72, 70, 64, 54, 40, 22, 0 ]; // Gyalog-Kiraly Pajzs (RANK_8, RANK_2)
var AttackWeight	= [ 0, 0, 0.5, 0.75, 0.88, 0.94, 0.97, 0.99 ]; // Kiraly Tamadas Sulyozasa
var PawnPassed		= [ 0, 0, 0, 0, 0.1, 0.3, 0.6, 1, 0 ]; // Telt Gyalog elorehaladasi pontjai (RANK_0, RANK_8)
var MvvLvaScores	= [ 0, 1, 2, 6, 0, 3, 4, 5, 0, 1, 2, 6, 0, 3, 4, 5 ]; // MVV-LVA Babuk erteke (P, N, B, R, Q, K)
var SeeValue		= [ 0, 1, 3, 900, 0, 3, 5, 9, 0, 1, 3, 900, 0, 3, 5, 9 ]; // See Babuk erteke (P, N, B, R, Q, K)
var KnightMoves		= [ 14, -14, 18, -18, 31, -31, 33, -33 ]; // Huszar lepesek
var KingMoves		= [ 1, -1, 15, -15, 16, -16, 17, -17 ]; // Kiraly lepesek
var BishopMoves		= [ 15, -15, 17, -17 ]; // Futo lepesek
var RookMoves		= [ 1, -1, 16, -16 ]; // Bastya lepesek
var DirNum			= [ 0, 0, 8, 8, 0, 4, 4, 8 ]; // Lepesek szama babunkent
var Letters			= [ 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h' ]; // Betuzes
// MOBILITAS		=   0, P, N, K, 0, B, R, Q, 0, P, N, K, 0, B, R, Q
var MOB_W			= [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1 ]; // Ahova a feher lephet
var MOB_B			= [ 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0 ]; // Ahova a fekete lephet
var PieceDir		= [ 0, 0, KnightMoves, KingMoves, 0, BishopMoves, RookMoves, KingMoves]; // Lepesek tomb
var PieceValue		= [ 0, 80, 325, 20000, 0, 325, 500, 1000, 0, 80, 325, 20000, 0, 325, 500, 1000 ]; // (P, N, K, B, R, Q)
var RANKS			= { RANK_1 : 1, RANK_2 : 2, RANK_3 : 3, RANK_4 : 4, RANK_5 : 5, RANK_6 : 6, RANK_7 : 7, RANK_8 : 8 }; // Sorok
var FILES			= { FILE_A : 1, FILE_B : 2, FILE_C : 3, FILE_D : 4, FILE_E : 5, FILE_F : 6, FILE_G : 7, FILE_H : 8 }; // Oszlopok

// Gyalog bit tabla /BitBoard/
var RankBBMask		= new Array(8); // Bitboard sor maszk
var FileBBMask		= new Array(8); // Bitboard oszlop maszk
var SetMask			= new Array(120); // Bitboard Mentes maszk
var ClearMask		= new Array(120); // Bitboard Torles maszk
var HighSQMask		= new Array(120); // Bitboard HighSQ maszk
var BitFixLow		= new Array(120); // Bitboard BitFix maszk [COLOR]
var BitFixHigh		= new Array(120); // Bitboard BitFix maszk [COLOR|1]
var IsolatedMask	= new Array(120); // Bitboard Isolated maszk
var WhitePassedMask	= new Array(120); // Bitboard Passed maszk Feher
var BlackPassedMask	= new Array(120); // Bitboard Passed maszk Fekete
var WOpenFileMask	= new Array(120); // Bitboard OpenFile maszk Feher
var BOpenFileMask	= new Array(120); // Bitboard OpenFile maszk Fekete
var CandidateMask	= new Array(120); // Bitboard Candidate maszk Feher
var WCandidateMask	= new Array(120); // Bitboard Candidate maszk Feher
var BCandidateMask	= new Array(120); // Bitboard Candidate maszk Fekete
var BlackPawnsLow	= 0x00FF0000; // 0000 0000 1111 1111 0000 0000 0000 0000 -> Fekete Gyalog also 32 bit /A7->H7/
var BlackPawnsHigh	= 0x00000000; // 0000 0000 0000 0000 0000 0000 0000 0000 -> Fekete Gyalog felso 32 bit
var WhitePawnsLow	= 0x00000000; // 0000 0000 0000 0000 0000 0000 0000 0000 -> Feher Gyalog also 32 bit
var WhitePawnsHigh	= 0x0000FF00; // 0000 0000 0000 0000 1111 1111 0000 0000 -> Feher Gyalog felso 32 bit /A2->H2/
var PawnBitBoard	= [ WhitePawnsLow, WhitePawnsHigh, 0, 0, 0, 0, 0, 0, BlackPawnsLow, BlackPawnsHigh ]; // Gyalog Bitboard Tomb

// Bit Tabla Shift ertekek
var BIT_SHIFT		= [ 31,  30,  29,  28,  27,  26,  25,  24,		0, 0, 0, 0, 0, 0, 0, 0,
					    23,  22,  21,  20,  19,  18,  17,  16,		0, 0, 0, 0, 0, 0, 0, 0,
					    15,  14,  13,  12,  11,  10,   9,   8,		0, 0, 0, 0, 0, 0, 0, 0,
					     7,   6,   5,   4,   3,   2,   1,   0,		0, 0, 0, 0, 0, 0, 0, 0,
					    31,  30,  29,  28,  27,  26,  25,  24,		0, 0, 0, 0, 0, 0, 0, 0,
					    23,  22,  21,  20,  19,  18,  17,  16,		0, 0, 0, 0, 0, 0, 0, 0,
					    15,  14,  13,  12,  11,  10,   9,   8,		0, 0, 0, 0, 0, 0, 0, 0,
					     7,   6,   5,   4,   3,   2,   1,   0 ];

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


	function InitEvalMasks() {

		if (SetMask[1] != undefined) { // Mar inicializaltunk
			return false;
		}

		var sq, tsq, f;
		var SQ64_TO_120 = [];

		for (var i in SQUARES) { // 64 -> 120
			SQ64_TO_120.push(SQUARES[i]);
		}

		// Sor es oszlop Bitmaszkok uritese
		for (sq = 0; sq < 8; ++sq) {
			FileBBMask[sq] = 0;
			RankBBMask[sq] = 0;
		}

		// Sor es oszlop Bitmaszkok feltoltese
		for (var r = RANKS.RANK_8; r >= RANKS.RANK_1; r--) {
			for (f = FILES.FILE_H; f >= FILES.FILE_A; f--) {
				sq = (r - 1) * 8 + (8 - f);
				FileBBMask[f] |= (1 << sq);
				RankBBMask[r] |= (1 << sq);
			}
		}

		// Bitmaszkok uritese
		for (sq = 0; sq < 120; sq++) {
			SetMask[sq] = 0;
			ClearMask[sq] = 0;
			HighSQMask[sq] = 0;
			IsolatedMask[sq] = 0;
			WOpenFileMask[sq] = 0;
			BOpenFileMask[sq] = 0;
			CandidateMask[sq] = 0;
			WCandidateMask[sq] = 0;
			BCandidateMask[sq] = 0;
			WhitePassedMask[sq] = 0;
			BlackPassedMask[sq] = 0;
			SetMask[sq] |= (1 << BIT_SHIFT[sq]); // SetMask feltoltese
			HighSQMask[sq] |= ((sq >> 6) & 1); // HighMask feltoltese
			ClearMask[sq] = ~SetMask[sq]; // ClearMask feltoltese
			BitFixLow[sq] = (sq >= 64 ? 119 : 64 + sq); // Also bit fix?(119-Igen)
			BitFixHigh[sq] = (sq >= 64 ? sq - 64 : 0); // Felso bit kell?(0-Nem)
		}

		// Bitmaszkok feltoltese [0 - 119]
		// [0 - 64]-ig szamolunk igy csak a
		// valos mezoket vizsgaljuk (sq & 0x88)
		// A konkret mezoket az [SQ64_TO_120] adja!
		for (sq = 0; sq < 64; sq++) {

			var SQ_120 = SQ64_TO_120[sq]; // 64 -> 120

			tsq = sq + 8;
			while (tsq < 64) {
				BOpenFileMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
				BlackPassedMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
				tsq += 8;
			}

			tsq = sq - 8;
			while (tsq >= 0) {
				WOpenFileMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
				WhitePassedMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
				tsq -= 8;
			}

			if (TableFiles[SQ_120] > FILES.FILE_A) {
				IsolatedMask[SQ_120] |= FileBBMask[TableFiles[SQ_120] - 1];

				tsq = sq + 7;
				while (tsq < 64) {
					WCandidateMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
					BlackPassedMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
					tsq += 8;
				}

				tsq = sq - 9;
				while (tsq >= 0) {
					BCandidateMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
					WhitePassedMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
					tsq -= 8;
				}
			}

			if (TableFiles[SQ_120] < FILES.FILE_H) {
				IsolatedMask[SQ_120] |= FileBBMask[TableFiles[SQ_120] + 1];

				tsq = sq + 9;
				while (tsq < 64) {
					WCandidateMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
					BlackPassedMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
					tsq += 8;
				}

				tsq = sq - 7;
				while (tsq >= 0) {
					BCandidateMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
					WhitePassedMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
					tsq -= 8;
				}
			}
		}

		// Kozvetlen szomszed mezok
		for (sq = 0; sq < 120; sq++) {
			var r = TableRanks[sq];
			if (r > RANKS.RANK_4) {
				CandidateMask[sq] |= (WCandidateMask[sq] & RankBBMask[r-4]);
			} else {
				CandidateMask[sq] |= (WCandidateMask[BitFixHigh[sq]] & RankBBMask[r]);
			}
		}
	}

	function BinaryString(nMask) {
		for (var nFlag = 0, nShifted = nMask, sMask = ""; nFlag < 32;
			nFlag++, sMask += String(nShifted >>> 31), nShifted <<= 1);
		return sMask;
	}

	function PrintBitBoard(BitLow, BitHigh) {
		var msg = '';
		var index = 0;

		console.log('Also:  '+BinaryString(BitLow));
		console.log('Felso: '+BinaryString(BitHigh));

		var BitBoard = BinaryString(BitLow);
		BitBoard += BinaryString(BitHigh);
		BitBoard = BitBoard.split('');

		for (var rank = RANKS.RANK_8; rank >= RANKS.RANK_1; rank--) {
			msg = rank+'. ';
			for (var file = FILES.FILE_A; file <= FILES.FILE_H; file++) {
				if (BitBoard[index] == '1') {
					msg += 'X';
				} else {
					msg += '-';
				}
				index++;
			}
			console.log(msg);
		}
	}

	function PopCount(b) { // only for 32 bit
		b = b - ((b >> 1) & 0x55555555);
		b = (b & 0x33333333) + ((b >> 2) & 0x33333333);
		return ((b + (b >> 4) & 0x0F0F0F0F) * 0x01010101) >> 24;
	}

	function SetBitBoard(SQ, BITBOARD) {
		PawnBitBoard[BITBOARD|HighSQMask[SQ]] |= SetMask[SQ];
	}

	function ClearBitBoard(SQ, BITBOARD) {
		PawnBitBoard[BITBOARD|HighSQMask[SQ]] &= ClearMask[SQ];
	}

	function IsOpenFile(FILE, COLOR) {
		return ((FileBBMask[FILE] & PawnBitBoard[COLOR]) | (FileBBMask[FILE] & PawnBitBoard[COLOR|1]));
	}

	function IsolatedPawn(SQ, COLOR) {
		return ((IsolatedMask[SQ] & PawnBitBoard[COLOR]) | (IsolatedMask[SQ] & PawnBitBoard[COLOR|1]));
	}

	function WhiteCandidatePawn(SQ) {
		var Black = 0;		// [W/B]Candidate Elottunk/Mogottunk van
		var White = 0;		// CandidateMask Mellettunk van, ezert..
		var SQ_1 = SQ + 16; // Kozvetlen vedo tarsakhoz LEFELE lepunk (CandidateMask)
		var SQ_2 = SQ - 16; // Kozvetlen szomszed tarshoz (WCandidateMask), valamint
							// Kozvetlen Tamadokhoz (CandidateMask) FELFELE lepunk
		Black += PopCount((BCandidateMask[SQ] & PawnBitBoard[BLACK]));
		Black += PopCount((BCandidateMask[BitFixHigh[SQ]] & PawnBitBoard[BLACK|1]));
		White += PopCount((WCandidateMask[BitFixLow[SQ_2]] & PawnBitBoard[WHITE]));
		White += PopCount((WCandidateMask[SQ_2] & PawnBitBoard[WHITE|1]));

		if (White >= Black) { // Tobbsegben vagyunk -> Jelenlegi tamadok/vedok szama kell
			Black = PopCount((CandidateMask[SQ_2] & PawnBitBoard[BLACK|HighSQMask[SQ_2]]));
			White = PopCount((CandidateMask[SQ_1] & PawnBitBoard[WHITE|HighSQMask[SQ_1]]));
			if (White >= Black) { // Gyoztunk
				return true;
			}
		}
		return false;
	}

	function BlackCandidatePawn(SQ) {
		var Black = 0;		// [W/B]Candidate Elottunk/Mogottunk van
		var White = 0;		// CandidateMask Mellettunk van, ezert..
		var SQ_1 = SQ - 16; // Kozvetlen vedo tarsakhoz FELFELE lepunk (CandidateMask)
		var SQ_2 = SQ + 16; // Kozvetlen szomszed tarshoz (BCandidateMask), valamint
							// Kozvetlen Tamadokhoz (CandidateMask) LEFELE lepunk
		Black += PopCount((BCandidateMask[SQ_2] & PawnBitBoard[BLACK]));
		Black += PopCount((BCandidateMask[BitFixHigh[SQ_2]] & PawnBitBoard[BLACK|1]));
		White += PopCount((WCandidateMask[BitFixLow[SQ]] & PawnBitBoard[WHITE]));
		White += PopCount((WCandidateMask[SQ] & PawnBitBoard[WHITE|1]));

		if (Black >= White) { // Tobbsegben vagyunk -> Jelenlegi tamadok/vedok szama kell
			Black = PopCount((CandidateMask[SQ_1] & PawnBitBoard[BLACK|HighSQMask[SQ_1]]));
			White = PopCount((CandidateMask[SQ_2] & PawnBitBoard[WHITE|HighSQMask[SQ_2]]));
			if (Black >= White) { // Gyoztunk
				return true;
			}
		}
		return false;
	}

	function WhiteBackwardControl(SQ, RANK) {
		var SQ_1 = SQ - 16; // 1 sorral fentebb
		var SQ_2 = SQ - 32; // 2 sorral fentebb
		if ((CHESS_BOARD[SQ_1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
		&& (CandidateMask[SQ_1] & PawnBitBoard[WHITE|HighSQMask[SQ_1]]) != 0 // 1 sorral fentebb, mellettem van Feher Gyalog
		&& ((CandidateMask[SQ_1] & PawnBitBoard[BLACK|HighSQMask[SQ_1]]) // Kulon-kulon vizsgalok also es felso 32 bitet! Osszekapcsolom "|" ==>
		  | (CandidateMask[SQ_2] & PawnBitBoard[BLACK|HighSQMask[SQ_2]])) == 0) { // (1 | 2) sorral fentebb atlosan 1-1 mezot nezek! Nincs Fekete Gyalog
			return false;
		} else if (RANK == RANKS.RANK_2 // 2. Sorban also es felso 32 bitet meghatarozza
				&& (CHESS_BOARD[SQ_1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
				&& (CHESS_BOARD[SQ_2] & 0x07) !== PAWN // Elottem 2 mezovel nincs Gyalog
				&& (CandidateMask[SQ_2] & PawnBitBoard[WHITE|1]) != 0 // 2 sorral fentebb, mellettem van Feher Gyalog ("FELSO BIT")
				&& ((CandidateMask[SQ_2-16] & PawnBitBoard[BLACK]) | (BCandidateMask[BitFixHigh[SQ]] & PawnBitBoard[BLACK|1])) == 0) { //  Nincs Fekete Gyalog
				// ((3 sorral fentebb atlosan 1-1 mezo "ALSO BIT") | (1-2 sorral fentebb atlosan 1-1 mezo "FELSO BIT")) (RANK == 2 miatt also vagy felso 32 bit)
			return false;
		}
		return true;
	}

	function BlackBackwardControl(SQ, RANK) {
		var SQ_1 = SQ + 16; // 1 sorral lentebb
		var SQ_2 = SQ + 32; // 2 sorral lentebb
		if ((CHESS_BOARD[SQ_1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
		&& (CandidateMask[SQ_1] & PawnBitBoard[BLACK|HighSQMask[SQ_1]]) != 0 // 1 sorral lentebb, mellettem van Fekete Gyalog
		&& ((CandidateMask[SQ_1] & PawnBitBoard[WHITE|HighSQMask[SQ_1]]) // Kulon-kulon vizsgalok also es felso 32 bitet! Osszekapcsolom "|" ==>
		  | (CandidateMask[SQ_2] & PawnBitBoard[WHITE|HighSQMask[SQ_2]])) == 0) { // (1 | 2) sorral lentebb atlosan 1-1 mezot nezek! Nincs Feher Gyalog
			return false;
		} else if (RANK == RANKS.RANK_7 // 7. Sorban also es felso 32 bitet meghatarozza
				&& (CHESS_BOARD[SQ_1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
				&& (CHESS_BOARD[SQ_2] & 0x07) !== PAWN // Elottem 2 mezovel nincs Gyalog
				&& (CandidateMask[SQ_2] & PawnBitBoard[BLACK]) != 0 // 2 sorral lentebb mellettem, van Fekete Gyalog ("ALSO BIT")
				&& ((CandidateMask[SQ_2+16] & PawnBitBoard[WHITE|1]) | (WCandidateMask[BitFixLow[SQ]] & PawnBitBoard[WHITE])) == 0) { //  Nincs Feher Gyalog
				// ((3 sorral lentebb atlosan 1-1 mezo "ALSO BIT")   | (1-2 sorral lentebb atlosan 1-1 mezo "FELSO BIT")) (RANK == 7 miatt also vagy felso 32bit)
			return false;
		}
		return true;
	}

	function WhiteBackwardPawn(SQ) {
		SQ = SQ - 16; // Melletunk levo mezoket igy latjuk
		return ((WCandidateMask[BitFixLow[SQ]] & PawnBitBoard[WHITE]) | (WCandidateMask[SQ] & PawnBitBoard[WHITE|1]));
	}

	function BlackBackwardPawn(SQ) {
		SQ = SQ + 16; // Melletunk levo mezoket igy latjuk
		return ((BCandidateMask[SQ] & PawnBitBoard[BLACK]) | (BCandidateMask[BitFixHigh[SQ]] & PawnBitBoard[BLACK|1]));
	}

	function WhiteMostPawn(SQ) { // Legelso Feher Gyalog
		return ((WOpenFileMask[SQ] & PawnBitBoard[WHITE]) | (WOpenFileMask[BitFixHigh[SQ]] & PawnBitBoard[WHITE|1]));
	}

	function BlackMostPawn(SQ) { // Legelso Fekete Gyalog
		return ((BOpenFileMask[BitFixLow[SQ]] & PawnBitBoard[BLACK]) | (BOpenFileMask[SQ] & PawnBitBoard[BLACK|1]));
	}

	function WhiteOpenFile(SQ) { // Fekete Dupla Gyalog: WhiteOpenFile(SQ) != 0
		return ((WOpenFileMask[SQ] & PawnBitBoard[BLACK]) | (WOpenFileMask[BitFixHigh[SQ]] & PawnBitBoard[BLACK|1]));
	}

	function BlackOpenFile(SQ) { // Feher Dupla Gyalog: BlackOpenFile(SQ) != 0
		return ((BOpenFileMask[BitFixLow[SQ]] & PawnBitBoard[WHITE]) | (BOpenFileMask[SQ] & PawnBitBoard[WHITE|1]));
	}

	function WhitePassedPawn(SQ) {
		return ((WhitePassedMask[SQ] & PawnBitBoard[BLACK]) | (WhitePassedMask[BitFixHigh[SQ]] & PawnBitBoard[BLACK|1]));
	}

	function BlackPassedPawn(SQ) {
		return ((BlackPassedMask[BitFixLow[SQ]] & PawnBitBoard[WHITE]) | (BlackPassedMask[SQ] & PawnBitBoard[WHITE|1]));
	}

	function PawnPush(TO_SQ) { // makeMove (WHITE = BLACK)
		return (CHESS_BOARD[TO_SQ] & 0x07) === PAWN && (currentPlayer === WHITE ?
				 (TableRanks[TO_SQ] <= RANKS.RANK_3 && BlackPassedPawn(TO_SQ) == 0)
				:(TableRanks[TO_SQ] >= RANKS.RANK_6 && WhitePassedPawn(TO_SQ) == 0));
	}

	function PawnOnSeventh() {
		return (currentPlayer === BLACK ? (PawnBitBoard[BLACK|1] & RankBBMask[RANKS.RANK_2]) : (PawnBitBoard[WHITE] & RankBBMask[RANKS.RANK_7]));
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function validateMove(from, to, currentPlayer) {
		if (isPseudoLegal(from, to, currentPlayer))
		{
		// Gyalog bevaltas
			var PROMOTED = 0;

		// Akival lepunk
			var fromPiece = CHESS_BOARD[from] & 0x07;

		// En Passant ?
			var EP_MOVE = 0;
			if (!CHESS_BOARD[to] && fromPiece === PAWN && EN_PASSANT != 0 && EN_PASSANT === to) {
				EP_MOVE = 1;
			}

		// Utes ?
			var CAPTURED = EP_MOVE; // Hack: En Passant is utes!
			if (CHESS_BOARD[to]) {
				CAPTURED = 1;
			}

		// Sancolas ?
			var CASTLING = 0;
			if (fromPiece === KING && Math.abs(from - to) === 2) {
				CASTLING = 1;
			}

		// Ervenyes lepes ?
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
			if ( (Math.abs(from - to) % 15 && Math.abs(from - to) % 17) &&	// bishop move
				((from & 0x0F) !== (to & 0x0F) && (from & 0xF0) !== (to & 0xF0))) { // rook move
				return false;
			}
		} else if (pieceType === ROOK) { // rook
			if ( (from & 0x0F) !== (to & 0x0F) && (from & 0xF0) !== (to & 0xF0)  ) { // move in a file or a rank
				return false;
			}
		} else if (pieceType === BISHOP) { // bishop
			if ( Math.abs(from - to) % 15 && Math.abs(from - to) % 17 ) { // bishop can only move diagonally
				return false;
			}
		} else if (pieceType === KING) { // king
			var diff = Math.abs(from - to);
			var direction = from - to > 0 ? 0x0 : 0x1;

			if ( diff === 1  || diff === 15 || diff === 16 || diff === 17 ) {
				// valid
			}
			else if ( diff === 2 ) // castling
			{
				if (direction == 0 && CHESS_BOARD[from - 3]) { // All square is empty in this direction?
					return false;
				}
				if (toPiece || CHESS_BOARD[(direction ? from + 1 : from - 1)]) { // All square is empty in this direction?
					return false;
				}
				if (((castleRights >> (currentPlayer/4 + direction)) & 1) == 0) { // casling is available in this direction?
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
			if ( diff !== 14  && diff !== 18 && diff !== 31 && diff !== 33 ) {
				return false;
			}
		} else if (pieceType === PAWN) { // pawn
			var direction = from - to > 0 ? 0x0 : 0x8;
			var diff = Math.abs(from - to);
			var fromRow = from & 0x70;

			if ( direction !== currentPlayer ) { // a pawn can only move forward
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


	function StoreHashMove(move, score, flags, depth) { // Aktualis allapothoz tartozo ertekek mentese

		if (score > ISMATE) { // Pontszam fixalasa
			score += boardPly;
		} else if (score < -ISMATE) { // Pontszam fixalasa
			score -= boardPly;
		}

		if (brd_HashTable[brd_hashKeyLow & HASHMASK] == null) {
			hashUsed++;
		}

		brd_HashTable[brd_hashKeyLow & HASHMASK] = new HashEntry(move, score, flags, depth, brd_hashKeyLow, brd_hashKeyHigh); // 108 bit /14 Byte/
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function HashEntry(move, score, flags, depth, hashLow, hashHigh) { // Atultetesi tablaba Objektum letrehozasa
		this.move			= move; // 20 bit
		this.flags			= flags; // 2 bit
		this.depth			= depth; // 7 bit
		this.score			= score; // 15 bit
		this.hashKeyLow		= hashLow; // 32 bit
		this.hashKeyHigh	= hashHigh; // 32 bit
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function ProbeHashMove() { // Aktualis allapothoz tartozo ertek kiolvasasa

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
		brd_hashKeyLow ^= SideKeyLow; // Aki lephet hashKey
		brd_hashKeyHigh ^= SideKeyHigh; // Aki lephet hashKey
	}
	function HASH_PCE(PCE, SQ) {
		brd_hashKeyLow ^= PieceKeysLow[PCE][SQ]; // Babu hashKey
		brd_hashKeyHigh ^= PieceKeysHigh[PCE][SQ]; // Babu hashKey
	}
	function HASH_CA() {
		brd_hashKeyLow ^= CastleKeysLow[castleRights]; // Sancolas hashKey
		brd_hashKeyHigh ^= CastleKeysHigh[castleRights]; // Sancolas hashKey
	}
	function HASH_EP() {
		brd_hashKeyLow ^= PieceKeysLow[0][EN_PASSANT]; // En Passant hashKey
		brd_hashKeyHigh ^= PieceKeysHigh[0][EN_PASSANT]; // En Passant hashKey
	}
	function MOVE_PCE(PCE, FROM, TO) {
		CHESS_BOARD[FROM] = 0; // Babu torlese
		CHESS_BOARD[TO] = PCE; // Babu mozgatas
		brd_pieceIndex[TO] = brd_pieceIndex[FROM];
		brd_pieceList[(PCE << 4) | brd_pieceIndex[TO]] = TO;
	}
	function ADDING_PCE(PCE, SQ, currentPlayer) {
		CHESS_BOARD[SQ] = PCE; // Babu hozzadasa
		brd_pieceIndex[SQ] = brd_pieceCount[PCE];
		brd_pieceList[(PCE << 4) | brd_pieceIndex[SQ]] = SQ;
		brd_Material[currentPlayer] += PieceValue[PCE];
		brd_pieceCount[PCE]++; // Babu szamanak novelese
		if ((PCE & 0x07) === PAWN) SetBitBoard(SQ, currentPlayer);
	}
	function DELETE_PCE(PCE, SQ, currentPlayer) {
		CHESS_BOARD[SQ] = 0; // Babu torlese
		brd_pieceCount[PCE]--; // Babu szamanak csokkentese
		var lastPceSquare = brd_pieceList[(PCE << 4) | brd_pieceCount[PCE]];
		brd_pieceIndex[lastPceSquare] = brd_pieceIndex[SQ];
		brd_pieceList[(PCE << 4) | brd_pieceIndex[lastPceSquare]] = lastPceSquare;
		brd_pieceList[(PCE << 4) | brd_pieceCount[PCE]] = 8; // Ures(8 & 0x88)
		brd_Material[currentPlayer] -= PieceValue[PCE];
		if ((PCE & 0x07) === PAWN) ClearBitBoard(SQ, currentPlayer);
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
			SetBitBoard(to, currentPlayer);
			ClearBitBoard(from, currentPlayer);
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
			if (currentPlayer) {
				ADDING_PCE(BLACK_PAWN, (EN_PASSANT + 16), currentPlayer); // Fekete Gyalog vissza
			} else {
				ADDING_PCE(WHITE_PAWN, (EN_PASSANT - 16), currentPlayer); // Feher Gyalog vissza
			}
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

		if ((MOVED_PCE & 0x07) === PAWN) // Ha Gyaloggal leptunk
		{
			SetBitBoard(from, currentPlayer);
			ClearBitBoard(to, currentPlayer);
		}

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


	function isMate(Score) {
		return Score >= ISMATE || Score <= -ISMATE;
	}

	function isCheck(Side) {
		return isSquareUnderAttack(brd_pieceList[(Side | KING) << 4], Side);
	}

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


	function InitEvalTable() {

		if (WKING_ZONE[1] != undefined) { // Mar inicializaltunk
			return false;
		}

		for (var i = 0; i < 120; i++)
		{
			DISTANCE[i] = new Array(120); // ARRAY[SQ1][SQ2]
			var rankI = TableRanks[i];
			var fileI = TableFiles[i];
			for (var j = 0; j < 120; j++) {
				var rankJ = TableRanks[j];
				var fileJ = TableFiles[j];
				DISTANCE[i][j] = Math.max(Math.abs(rankI-rankJ), Math.abs(fileI-fileJ));
			}
		}

		for (var i = 0; i < 120; i++)
		{
			WKING_ZONE[i] = new Array(120); // ARRAY[KingPos][sqNearKing]
			BKING_ZONE[i] = new Array(120); // ARRAY[KingPos][sqNearKing]

			for (var j = 0; j < 120; j++)
			{
				WKING_ZONE[i][j] = 0; // Feher kiraly zona urites
				BKING_ZONE[i][j] = 0; // Fekete kiraly zona urites

				// FEHER ES FEKETE KIRALY
				if (!((i -  1) & 0x88)) { WKING_ZONE[i][i -  1] = 1; BKING_ZONE[i][i -  1] = 1; } // Egyik oldal
				if (!((i +  1) & 0x88)) { WKING_ZONE[i][i +  1] = 1; BKING_ZONE[i][i +  1] = 1; } // Masik oldal
				if (!((i - 16) & 0x88)) { WKING_ZONE[i][i - 16] = 1; BKING_ZONE[i][i - 16] = 1; } // FEHER: Elotte, FEKETE: Mogotte
				if (!((i + 16) & 0x88)) { WKING_ZONE[i][i + 16] = 1; BKING_ZONE[i][i + 16] = 1; } // FEHER: Mogotte, FEKETE: Elotte

				if (!((i - 15) & 0x88)) { WKING_ZONE[i][i - 15] = 1; BKING_ZONE[i][i - 15] = 1; } // Sregen egyik oldal
				if (!((i + 15) & 0x88)) { WKING_ZONE[i][i + 15] = 1; BKING_ZONE[i][i + 15] = 1; } // Sregen masik oldal
				if (!((i - 17) & 0x88)) { WKING_ZONE[i][i - 17] = 1; BKING_ZONE[i][i - 17] = 1; } // Sregen harmadik oldal
				if (!((i + 17) & 0x88)) { WKING_ZONE[i][i + 17] = 1; BKING_ZONE[i][i + 17] = 1; } // Sregen negyedik oldal
			}
		}

		// Vektor Tabla Inicializalasa
		for (var i = 0; i < 256; i++) {
			brd_vectorDelta[i] = new Object();
			brd_vectorDelta[i].delta = 0;
			brd_vectorDelta[i].pieceMask = new Array(8);
			brd_vectorDelta[i].pieceMask[WHITE] = 0;
			brd_vectorDelta[i].pieceMask[BLACK] = 0;
		}

		for (var square = 0; square < 120; square++) 
		{
		// Gyalog
			var index = square - (square - 17) + 128;
			brd_vectorDelta[index].pieceMask[WHITE] |= (1 << PAWN);
			index = square - (square - 15) + 128;
			brd_vectorDelta[index].pieceMask[WHITE] |= (1 << PAWN);

			index = square - (square + 17) + 128;
			brd_vectorDelta[index].pieceMask[BLACK] |= (1 << PAWN);
			index = square - (square + 15) + 128;
			brd_vectorDelta[index].pieceMask[BLACK] |= (1 << PAWN);

		// Tobbi babu
			for (var i = KNIGHT; i <= QUEEN; i++) {

				if (i == 4) continue; // Ervenytelen babu

				for (var dir = 0; dir < PieceDir[i].length; dir++)
				{
					var target = square + PieceDir[i][dir];

					while (!(target & 0x88))
					{
						index = square - target + 128;

						brd_vectorDelta[index].pieceMask[WHITE] |= (1 << i);
						brd_vectorDelta[index].pieceMask[BLACK] |= (1 << i);

						var flip = -1;
						if (square < target) {
							flip = 1;
						}

						if (TableRanks[square] == TableRanks[target]) {
							brd_vectorDelta[index].delta = flip * 1;
						} else if (TableFiles[square] == TableFiles[target]) {
							brd_vectorDelta[index].delta = flip * 16;
						} else if ((square % 15) == (target % 15)) {
							brd_vectorDelta[index].delta = flip * 15;
						} else if ((square % 17) == (target % 17)) {
							brd_vectorDelta[index].delta = flip * 17;
						}

						if (i == KNIGHT) {
							brd_vectorDelta[index].delta = PieceDir[i][dir];
							break;
						}

						if (i == KING) {
							break;
						}

						target += PieceDir[i][dir];
					}
				}
			}
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function Evaluation() {

		var to				= 0; // sq
		var mob				= 0; // Mob
		var Rank			= 0; // Sor
		var PCE				= 0; // Babu
		var File			= 0; // Oszlop
		var Phase			= 24; // Fazis
		var Open			= 0; // Nyitott
		var att				= 0; // Tamadasok
		var Draw			= 1; // Dontetlen
		var pieceIdx		= 0; // Babu index
		var mgWhite			= 0; // Kezdo Feher
		var mgBlack			= 0; // Kezdo Fekete
		var egWhite			= 0; // Vegjatek Feher
		var egBlack			= 0; // Vegjatek Fekete
		var PassedEG		= 0; // Vegjatek Gyalog
		var WAttackScore	= 0; // Tamadas pont Feher
		var BAttackScore	= 0; // Tamadas pont Fekete
		var WAttackCount	= 0; // Tamadok szama Feher
		var BAttackCount	= 0; // Tamadok szama Fekete

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var wNumQueens	= brd_pieceCount[WHITE_QUEEN];
		var wNumRooks	= brd_pieceCount[WHITE_ROOK];
		var wNumBishops	= brd_pieceCount[WHITE_BISHOP];
		var wNumKnights	= brd_pieceCount[WHITE_KNIGHT];
		var wNumPawns	= brd_pieceCount[WHITE_PAWN];

		var bNumQueens	= brd_pieceCount[BLACK_QUEEN];
		var bNumRooks	= brd_pieceCount[BLACK_ROOK];
		var bNumBishops	= brd_pieceCount[BLACK_BISHOP];
		var bNumKnights	= brd_pieceCount[BLACK_KNIGHT];
		var bNumPawns	= brd_pieceCount[BLACK_PAWN];

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	//											DONTETLEN
	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (wNumPawns == 0 && bNumPawns == 0) { // Nincs Gyalog
			if (wNumQueens == 0 && bNumQueens == 0) { // Nincs Vezer
				if (wNumRooks == 0 && bNumRooks == 0) { // Nincs Bastya
					if (wNumBishops == 0 && bNumBishops == 0) { // Nincs Futo
						if (wNumKnights < 3 && bNumKnights < 3) { // Max 2-2 Huszar
							return 0;
						}
					} else if (wNumKnights == 0 && bNumKnights == 0) { // Nincs Huszar
						if (Math.abs(wNumBishops - bNumBishops) < 2) { // Max Futo diff < 2
							return 0;
						}
					} else if ((wNumKnights < 3 && wNumBishops == 0) // Max 2 Huszar, 0 Futo (Feher) ->
						    || (wNumKnights == 0 && wNumBishops == 1)) { // -> 0 Huszar, 1 Futo (Feher)
						if ((bNumKnights < 3 && bNumBishops == 0) // Max 2 Huszar, 0 Futo (Fekete) ->
						 || (bNumKnights == 0 && bNumBishops == 1)) { // -> 0 Huszar, 1 Futo (Fekete)
							return 0;
						 }
					}
				} else if (wNumRooks == 1 && bNumRooks == 1) { // 1-1 Bastya
					if ((wNumKnights + wNumBishops) == 0 // Feher(Huszar+Futo) == 0
					 && (bNumKnights + bNumBishops) == 0) { // Fekete(Huszar+Futo) == 0
							return 0;
					} else if ((wNumKnights + wNumBishops) < 2 // Feher(Huszar+Futo) < 2
					 && (bNumKnights + bNumBishops) < 2) { // Fekete(Huszar+Futo) < 2
						Draw = 10;
					}
				} else if (wNumRooks == 1 && bNumRooks == 0) { // 1-0 Bastya
					if ((wNumKnights + wNumBishops) == 0 // Feher(Huszar+Futo) == 0
					&& ((bNumKnights + bNumBishops) == 1 // Fekete(Huszar+Futo) == 1 ->
					 || (bNumKnights + bNumBishops) == 2)) { // -> Fekete(Huszar+Futo) == 2
						Draw = 4;
					}
				} else if (wNumRooks == 0 && bNumRooks == 1) { // 0-1 Bastya
					if ((bNumKnights + bNumBishops) == 0 // Fekete(Huszar+Futo) == 0
					&& ((wNumKnights + wNumBishops) == 1 // Feher(Huszar+Futo) == 1 ->
					 || (wNumKnights + wNumBishops) == 2)) { // -> Feher(Huszar+Futo) == 2
						Draw = 4;
					}
				}
			}
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var mobS = 0;
		var mobE = 0;

		var attS = 0;
		var attE = 0;

		var kingS = 0;
		var kingE = 0;

		var rooksS = 0;
		var rooksE = 0;

		var pawnsS = 0;
		var pawnsE = 0;

		var queensS = 0;
		var queensE = 0;

		var knightsS = 0;
		var knightsE = 0;

		var bishopsS = 0;
		var bishopsE = 0;

		var trappedS = 0;
		var trappedE = 0;

	// Gyalog oszlopok inicializalasa
		for (var index = 0; index < 10; index++) {
			PawnRanksWhite[index] = RANKS.RANK_8; // Feher Gyalog Oszlop
			PawnRanksBlack[index] = RANKS.RANK_1; // Fekete Gyalog Oszlop
		}

	// Gyalog ellenorzes
		var BpawnHome = PawnBitBoard[BLACK] & RankBBMask[RANKS.RANK_7]; // Fekete Gyalog 7. Sorban
		var WpawnHome = PawnBitBoard[WHITE|1] & RankBBMask[RANKS.RANK_2]; // Feher Gyalog 2. Sorban

	// Vezer, Tisztek ellenorzese
		var WBigPieces = (wNumKnights || wNumBishops || wNumRooks || wNumQueens);
		var BBigPieces = (bNumKnights || bNumBishops || bNumRooks || bNumQueens);

	// Tamadasi erok
		var WCanAttack = wNumQueens && (wNumKnights || wNumBishops || wNumRooks || wNumQueens >= 2);
		var BCanAttack = bNumQueens && (bNumKnights || bNumBishops || bNumRooks || bNumQueens >= 2);

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	//											BABUK ERTEKELESE
	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// WHITE_KING /Feher Kiraly/
		var WKing = brd_pieceList[WHITE_KING << 4];
		var WKingRank = TableRanks[WKing]; // Kiraly sora
		var WKingFile = TableFiles[WKing]; // Kiraly oszlopa
		var WKZ = WKING_ZONE[WKing]; // Feher Kiraly zonak
		mgWhite += KingMask[WKing];
		egWhite += KingEndMask[WKing];

	// BLACK_KING /Fekete Kiraly/
		var BKing = brd_pieceList[BLACK_KING << 4];
		var BKingRank = TableRanks[BKing]; // Kiraly sora
		var BKingFile = TableFiles[BKing]; // Kiraly oszlopa
		var BKZ = BKING_ZONE[BKing]; // Fekete Kiraly zonak
		mgBlack += KingMask[TableMirror[BKing]];
		egBlack += KingEndMask[TableMirror[BKing]];

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// WHITE_QUEEN /Feher Vezer/
		pieceIdx = WHITE_QUEEN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != 8)
		{
			Rank = TableRanks[PCE];

			if (Rank == RANKS.RANK_7 && (BpawnHome || BKingRank == RANKS.RANK_8)) { // 7. sorban
				queensS += 10;
				queensE += 20;
			}

			att = 0;
			mob = -13;
			to = PCE +  1; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to +=  1; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE -  1; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to -=  1; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE + 16; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to += 16; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE - 16; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to -= 16; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }

			to = PCE + 15; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to += 15; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE - 15; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to -= 15; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE + 17; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to += 17; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE - 17; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to -= 17; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }

			if (att != 0) {
				WAttackCount++;
				WAttackScore += 4;
			}

			Phase -= 4;
			mobS += 1 * mob;
			mobE += 2 * mob;
			mgWhite += QueenMask[PCE];
			egWhite += QueenEndMask[PCE];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// BLACK_QUEEN /Fekete Vezer/
		pieceIdx = BLACK_QUEEN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != 8)
		{
			Rank = TableRanks[PCE];

			if (Rank == RANKS.RANK_2 && (WpawnHome || WKingRank == RANKS.RANK_1)) { // 7. sorban
				queensS -= 10;
				queensE -= 20;
			}

			att = 0;
			mob = -13;
			to = PCE +  1; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to +=  1; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE -  1; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to -=  1; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE + 16; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to += 16; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE - 16; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to -= 16; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }

			to = PCE + 15; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to += 15; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE - 15; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to -= 15; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE + 17; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to += 17; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE - 17; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to -= 17; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }

			if (att != 0) {
				BAttackCount++;
				BAttackScore += 4;
			}

			Phase -= 4;
			mobS -= 1 * mob;
			mobE -= 2 * mob;
			mgBlack += QueenMask[TableMirror[PCE]];
			egBlack += QueenEndMask[TableMirror[PCE]];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// WHITE_ROOK /Feher Bastya/
		pieceIdx = WHITE_ROOK << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != 8)
		{
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			rooksS -= 10; // Nyitott oszlop pont korrekcio
			rooksE -= 10; // Nyitott oszlop pont korrekcio

			if (IsOpenFile(File, WHITE) == 0) { // Felig nyitott oszlop
				if (IsOpenFile(File, BLACK) == 0) { // Teljesen Nyitott
					rooksS += 20;
					rooksE += 20;
				} else {
					rooksS += 10;
					rooksE += 10;
				}

				if (WCanAttack) {
					if (File == BKingFile) { // Ellenseges Kiraly azonos oszlopban
						rooksS += 10;
					}

					if (Math.abs(File - BKingFile) <= 1) { // Max 1. oszlop elteres
						rooksS += 10;
					}
				}
			}

			if (Rank == RANKS.RANK_7 && (BpawnHome || BKingRank == RANKS.RANK_8)) { // 7. sorban
				rooksS += 20;
				rooksE += 40;
			}

			att = 0;
			mob = -7;
			to = PCE +  1; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to +=  1; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE -  1; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to -=  1; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE + 16; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to += 16; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE - 16; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to -= 16; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }

			if (att != 0) {
				WAttackCount++;
				WAttackScore += 2;
			}

			Phase -= 2;
			mobS += 2 * mob;
			mobE += 4 * mob;
			mgWhite += RookMask[PCE];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// BLACK_ROOK /Fekete Bastya/
		pieceIdx = BLACK_ROOK << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != 8)
		{
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			rooksS += 10; // Nyitott oszlop pont korrekcio
			rooksE += 10; // Nyitott oszlop pont korrekcio

			if (IsOpenFile(File, BLACK) == 0) { // Felig nyitott oszlop
				if (IsOpenFile(File, WHITE) == 0) { // Teljesen Nyitott
					rooksS -= 20;
					rooksE -= 20;
				} else {
					rooksS -= 10;
					rooksE -= 10;
				}

				if (BCanAttack) {
					if (File == WKingFile) { // Ellenseges Kiraly azonos oszlopban
						rooksS -= 10;
					}

					if (Math.abs(File - WKingFile) <= 1) { // Max 1. oszlop elteres
						rooksS -= 10;
					}
				}
			}

			if (Rank == RANKS.RANK_2 && (WpawnHome || WKingRank == RANKS.RANK_1)) { // 7. sorban
				rooksS -= 20;
				rooksE -= 40;
			}

			att = 0;
			mob = -7;
			to = PCE +  1; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to +=  1; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE -  1; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to -=  1; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE + 16; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to += 16; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE - 16; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to -= 16; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }

			if (att != 0) {
				BAttackCount++;
				BAttackScore += 2;
			}

			Phase -= 2;
			mobS -= 2 * mob;
			mobE -= 4 * mob;
			mgBlack += RookMask[TableMirror[PCE]];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// WHITE_BISHOP /Feher Futo/
		pieceIdx = WHITE_BISHOP << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != 8)
		{
			att = 0;
			mob = -6;
			to = PCE + 15; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to += 15; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE - 15; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to -= 15; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE + 17; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to += 17; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE - 17; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to -= 17; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }

			if (att != 0) {
				WAttackCount++;
				WAttackScore += 1;
			}

			Phase -= 1;
			mobS += 5 * mob;
			mobE += 5 * mob;
			mgWhite += BishopMask[PCE];
			egWhite += BishopEndMask[PCE];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// BLACK_BISHOP /Fekete Futo/
		pieceIdx = BLACK_BISHOP << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != 8)
		{
			att = 0;
			mob = -6;
			to = PCE + 15; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to += 15; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE - 15; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to -= 15; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE + 17; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to += 17; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE - 17; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to -= 17; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }

			if (att != 0) {
				BAttackCount++;
				BAttackScore += 1;
			}

			Phase -= 1;
			mobS -= 5 * mob;
			mobE -= 5 * mob;
			mgBlack += BishopMask[TableMirror[PCE]];
			egBlack += BishopEndMask[TableMirror[PCE]];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// WHITE_KNIGHT /Feher Huszar/
		pieceIdx = WHITE_KNIGHT << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != 8)
		{
			att = 0;
			mob = -4;
			to = PCE + 14; if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE - 14; if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE + 18; if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE - 18; if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE + 31; if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE - 31; if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE + 33; if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE - 33; if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }

			if (att != 0) {
				WAttackCount++;
				WAttackScore += 1;
			}

			Phase -= 1;
			mobS += 4 * mob;
			mobE += 4 * mob;
			mgWhite += KnightMask[PCE];
			egWhite += KnightEndMask[PCE];

			var outpost = KnightOutpost[PCE]; // Huszar Orszem

			if (outpost && CHESS_BOARD[PCE - 15] != BLACK_PAWN && CHESS_BOARD[PCE - 17] != BLACK_PAWN) { // Nincs fenyegetes
				if (CHESS_BOARD[PCE + 15] == WHITE_PAWN) knightsS += outpost;
				if (CHESS_BOARD[PCE + 17] == WHITE_PAWN) knightsS += outpost;
			}

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// BLACK_KNIGHT /Fekete Huszar/
		pieceIdx = BLACK_KNIGHT << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != 8)
		{
			att = 0;
			mob = -4;
			to = PCE + 14; if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE - 14; if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE + 18; if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE - 18; if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE + 31; if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE - 31; if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE + 33; if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE - 33; if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }

			if (att != 0) {
				BAttackCount++;
				BAttackScore += 1;
			}

			Phase -= 1;
			mobS -= 4 * mob;
			mobE -= 4 * mob;
			mgBlack += KnightMask[TableMirror[PCE]];
			egBlack += KnightEndMask[TableMirror[PCE]];

			var outpost = KnightOutpost[TableMirror[PCE]]; // Huszar Orszem

			if (outpost && CHESS_BOARD[PCE + 15] != WHITE_PAWN && CHESS_BOARD[PCE + 17] != WHITE_PAWN) { // Nincs fenyegetes
				if (CHESS_BOARD[PCE - 15] == BLACK_PAWN) knightsS -= outpost;
				if (CHESS_BOARD[PCE - 17] == BLACK_PAWN) knightsS -= outpost;
			}

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// WHITE_PAWN /Feher Gyalog/
		pieceIdx = WHITE_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != 8)
		{
			Open = 0; // Nyitott
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			if (BlackOpenFile(PCE) != 0) { // Dupla Gyalog
				pawnsS += PawnDoubled;
				pawnsE += 2 * PawnDoubled;
			}

			if (PawnRanksWhite[File] > Rank) { // A leghatso Feher gyalog az adott oszlopban
				PawnRanksWhite[File] = Rank;
			}

			if (WhiteOpenFile(PCE) == 0 && WhiteMostPawn(PCE) == 0) { // Legelso Gyalog nyitott oszlopban
				Open = 1;
			}

			if (IsolatedPawn(PCE, WHITE) == 0) { // Elkulonitett Gyalog
				pawnsS += PawnIsolated + PawnIsolated * Open;
				pawnsE += 2 * PawnIsolated;
			} else if (WhiteBackwardPawn(PCE) == 0 && WhiteBackwardControl(PCE, Rank)) { // Hatrahagyott Gyalog
				pawnsS += PawnBackward + PawnBackward * Open;
				pawnsE += PawnBackward - 2;
			}

			if (Open) {
				if (WhitePassedPawn(PCE) == 0) { // Telt Gyalog
					pawnsS += 10 + 60 * PawnPassed[Rank];
					PassedEG = 120; // Vegjatek alap pont
					PassedEG -= 5  * DISTANCE[WKing][PCE-16]; // Sajat Kiraly Tavolsag
					PassedEG += 20 * DISTANCE[BKing][PCE-16]; // Ellenfel Kiraly Tavolsag

					if (!BBigPieces) {
						if (DISTANCE[WKing][PCE] <= 1 && DISTANCE[WKing][File-1] <= 1 // File-1 -> Bevaltas mezo
						&& (WKingFile != File || (File != FILES.FILE_A && File != FILES.FILE_H))) { // Kiraly Telt Gyalog
							PassedEG += 800;
						} else if ((WKingRank <= Rank || WKingFile != File) && bNumPawns == 0 // Nincs utban a Kiraly, 0 Fekete Gyalog
						&& DISTANCE[PCE][File-1] < DISTANCE[BKing][File-1] + ((currentPlayer == WHITE)|0) - 1) { // Megallithatatlan Telt Gyalog
							PassedEG += 800;
						}
					}

					if (CHESS_BOARD[PCE-16] == 0 && Rank >= RANKS.RANK_4 && See(BIT_MOVE(PCE, PCE-16, 0, 0, 0))) { // Szabad Telt Gyalog
						PassedEG += 60;
					}

					pawnsE += 20 + (PassedEG * PawnPassed[Rank]) | 0; // Vegjatek Pont

				} else if (WhiteCandidatePawn(PCE)) { // Jelolt Gyalog /Candidate/
					pawnsS += 5  + 50 * PawnPassed[Rank];
					pawnsE += 10 + 100 * PawnPassed[Rank];
				}
			}

			mgWhite += PawnMask[PCE];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// BLACK_PAWN /Fekete Gyalog/
		pieceIdx = BLACK_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != 8)
		{
			Open = 0; // Nyitott
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			if (WhiteOpenFile(PCE) != 0) { // Dupla Gyalog
				pawnsS -= PawnDoubled;
				pawnsE -= 2 * PawnDoubled;
			}

			if (PawnRanksBlack[File] < Rank) { // A leghatso Fekete gyalog az adott oszlopban
				PawnRanksBlack[File] = Rank;
			}

			if (BlackOpenFile(PCE) == 0 && BlackMostPawn(PCE) == 0) { // Legelso Gyalog nyitott oszlopban
				Open = 1;
			}

			if (IsolatedPawn(PCE, BLACK) == 0) { // Elkulonitett Gyalog
				pawnsS -= PawnIsolated + PawnIsolated * Open;
				pawnsE -= 2 * PawnIsolated;
			} else if (BlackBackwardPawn(PCE) == 0 && BlackBackwardControl(PCE, Rank)) { // Hatrahagyott Gyalog
				pawnsS -= PawnBackward + PawnBackward * Open;
				pawnsE -= PawnBackward - 2;
			}

			if (Open) {
				if (BlackPassedPawn(PCE) == 0) { // Telt Gyalog
					pawnsS -= 10 + 60 * PawnPassed[9-Rank];
					PassedEG = 120; // Vegjatek alap pont
					PassedEG -= 5  * DISTANCE[BKing][PCE+16]; // Sajat Kiraly Tavolsag
					PassedEG += 20 * DISTANCE[WKing][PCE+16]; // Ellenfel Kiraly Tavolsag

					if (!WBigPieces) {
						if (DISTANCE[BKing][PCE] <= 1 && DISTANCE[BKing][File+111] <= 1 // File+111 -> Bevaltas mezo
						&& (BKingFile != File || (File != FILES.FILE_A && File != FILES.FILE_H))) { // Kiraly Telt Gyalog
							PassedEG += 800;
						} else if ((BKingRank >= Rank || BKingFile != File) && wNumPawns == 0 // Nincs utban a Kiraly, 0 Feher Gyalog
						&& DISTANCE[PCE][File+111] < DISTANCE[WKing][File+111] + ((currentPlayer == BLACK)|0) - 1) { // Megallithatatlan Telt Gyalog
							PassedEG += 800;
						}
					}

					if (CHESS_BOARD[PCE+16] == 0 && Rank <= RANKS.RANK_5 && See(BIT_MOVE(PCE, PCE+16, 0, 0, 0))) { // Szabad Telt Gyalog
						PassedEG += 60;
					}

					pawnsE -= 20 + (PassedEG * PawnPassed[9-Rank]) | 0; // Vegjatek Pont

				} else if (BlackCandidatePawn(PCE)) { // Jelolt Gyalog /Candidate/
					pawnsS -= 5  + 50 * PawnPassed[9-Rank];
					pawnsE -= 10 + 100 * PawnPassed[9-Rank];
				}
			}

			mgBlack += PawnMask[TableMirror[PCE]];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (WCanAttack)
		{
			WAttackCount = Math.min(WAttackCount, 7); // Max 7 tamadoval szamolunk
			attS += (20 * WAttackScore * AttackWeight[WAttackCount]) | 0; // Tamadas pontozas Feher

			var Storm = 0; // Gyalog Vihar
			var Shield = 0; // Gyalog Pajzs
			var Distance = 0; // Gyalog tavolsag

			Distance = PawnRanksBlack[BKingFile] - 1;
			Shield += PawnShelter[Distance];
			Storm += WhitePawnStorm(BKingFile);

			if (BKingFile != FILES.FILE_A) {
				Distance = PawnRanksBlack[BKingFile-1] - 1;
				Shield += PawnShelter[Distance] / 2;
				Storm += WhitePawnStorm(BKingFile-1);
			}

			if (BKingFile != FILES.FILE_H) {
				Distance = PawnRanksBlack[BKingFile+1] - 1;
				Shield += PawnShelter[Distance] / 2;
				Storm += WhitePawnStorm(BKingFile+1);
			}

			if (Shield == 0) Shield = 11; // Kompenzalas

			Shield += Storm; // Gyalog Vihar hozzaadas

			var ShieldCastle = Shield;

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (castleRights & CASTLEBIT.BKCA) { // Sancolhat Kiraly oldal
				Distance = PawnRanksBlack[FILES.FILE_G] - 1;
				var ShieldK = PawnShelter[Distance];
				Storm = WhitePawnStorm(FILES.FILE_G);

				Distance = PawnRanksBlack[FILES.FILE_F] - 1;
				ShieldK += PawnShelter[Distance] / 2;
				Storm += WhitePawnStorm(FILES.FILE_F);

				Distance = PawnRanksBlack[FILES.FILE_H] - 1;
				ShieldK += PawnShelter[Distance] / 2;
				Storm += WhitePawnStorm(FILES.FILE_H);

				if (ShieldK == 0) ShieldK = 11; // Kompenzalas

				ShieldK += Storm; // Gyalog Vihar hozzaadas

				if (ShieldK < ShieldCastle) ShieldCastle = ShieldK;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (castleRights & CASTLEBIT.BQCA) { // Sancolhat Vezer oldal
				Distance = PawnRanksBlack[FILES.FILE_B] - 1;
				var ShieldQ = PawnShelter[Distance];
				Storm = WhitePawnStorm(FILES.FILE_B);

				Distance = PawnRanksBlack[FILES.FILE_A] - 1;
				ShieldQ += PawnShelter[Distance] / 2;
				Storm += WhitePawnStorm(FILES.FILE_A);

				Distance = PawnRanksBlack[FILES.FILE_C] - 1;
				ShieldQ += PawnShelter[Distance] / 2;
				Storm += WhitePawnStorm(FILES.FILE_C);

				if (ShieldQ == 0) ShieldQ = 11; // Kompenzalas

				ShieldQ += Storm; // Gyalog Vihar hozzaadas

				if (ShieldQ < ShieldCastle) ShieldCastle = ShieldQ;
			}

			Shield = ((Shield + ShieldCastle) / 2) | 0;

			kingS += Shield;
			kingE += 0;
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (BCanAttack)
		{
			BAttackCount = Math.min(BAttackCount, 7); // Max 7 tamadoval szamolunk
			attS -= (20 * BAttackScore * AttackWeight[BAttackCount]) | 0; // Tamadas pontozas Fekete

			var Storm = 0; // Gyalog Vihar
			var Shield = 0; // Gyalog Pajzs
			var Distance = 0; // Gyalog tavolsag

			Distance = 8 - PawnRanksWhite[WKingFile];
			Shield += PawnShelter[Distance];
			Storm += BlackPawnStorm(WKingFile);

			if (WKingFile != FILES.FILE_A) {
				Distance = 8 - PawnRanksWhite[WKingFile-1];
				Shield += PawnShelter[Distance] / 2;
				Storm += BlackPawnStorm(WKingFile-1);
			}

			if (WKingFile != FILES.FILE_H) {
				Distance = 8 - PawnRanksWhite[WKingFile+1];
				Shield += PawnShelter[Distance] / 2;
				Storm += BlackPawnStorm(WKingFile+1);
			}

			if (Shield == 0) Shield = 11; // Kompenzalas

			Shield += Storm; // Gyalog Vihar hozzaadas

			var ShieldCastle = Shield;

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (castleRights & CASTLEBIT.WKCA) { // Sancolhat Kiraly oldal
				Distance = 8 - PawnRanksWhite[FILES.FILE_G];
				var ShieldK = PawnShelter[Distance];
				Storm = BlackPawnStorm(FILES.FILE_G);

				Distance = 8 - PawnRanksWhite[FILES.FILE_F];
				ShieldK += PawnShelter[Distance] / 2;
				Storm += BlackPawnStorm(FILES.FILE_F);

				Distance = 8 - PawnRanksWhite[FILES.FILE_H];
				ShieldK += PawnShelter[Distance] / 2;
				Storm += BlackPawnStorm(FILES.FILE_H);

				if (ShieldK == 0) ShieldK = 11; // Kompenzalas

				ShieldK += Storm; // Gyalog Vihar hozzaadas

				if (ShieldK < ShieldCastle) ShieldCastle = ShieldK;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (castleRights & CASTLEBIT.WQCA) { // Sancolhat Vezer oldal
				Distance = 8 - PawnRanksWhite[FILES.FILE_B];
				var ShieldQ = PawnShelter[Distance];
				Storm = BlackPawnStorm(FILES.FILE_B);

				Distance = 8 - PawnRanksWhite[FILES.FILE_A];
				ShieldQ += PawnShelter[Distance] / 2;
				Storm += BlackPawnStorm(FILES.FILE_A);

				Distance = 8 - PawnRanksWhite[FILES.FILE_C];
				ShieldQ += PawnShelter[Distance] / 2;
				Storm += BlackPawnStorm(FILES.FILE_C);

				if (ShieldQ == 0) ShieldQ = 11; // Kompenzalas

				ShieldQ += Storm; // Gyalog Vihar hozzaadas

				if (ShieldQ < ShieldCastle) ShieldCastle = ShieldQ;
			}

			Shield = ((Shield + ShieldCastle) / 2) | 0;

			kingS -= Shield;
			kingE -= 0;
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Sarokba szorult Feher Bastya
		if (( CHESS_BOARD[SQUARES.F1] == WHITE_KING || CHESS_BOARD[SQUARES.G1] == WHITE_KING )
		 && ( CHESS_BOARD[SQUARES.H1] == WHITE_ROOK || CHESS_BOARD[SQUARES.G1] == WHITE_ROOK || CHESS_BOARD[SQUARES.H2] == WHITE_ROOK )) { // Kiraly oldal
			trappedS -= 50;
		}
		if (( CHESS_BOARD[SQUARES.C1] == WHITE_KING || CHESS_BOARD[SQUARES.B1] == WHITE_KING )
		 && ( CHESS_BOARD[SQUARES.A1] == WHITE_ROOK || CHESS_BOARD[SQUARES.B1] == WHITE_ROOK || CHESS_BOARD[SQUARES.A2] == WHITE_ROOK )) { // Vezer oldal
			trappedS -= 50;
		}

	// Sarokba szorult Fekete Bastya
		if (( CHESS_BOARD[SQUARES.F8] == BLACK_KING || CHESS_BOARD[SQUARES.G8] == BLACK_KING )
		 && ( CHESS_BOARD[SQUARES.H8] == BLACK_ROOK || CHESS_BOARD[SQUARES.G8] == BLACK_ROOK || CHESS_BOARD[SQUARES.H7] == BLACK_ROOK )) { // Kiraly oldal
			trappedS += 50;
		}
		if (( CHESS_BOARD[SQUARES.C8] == BLACK_KING || CHESS_BOARD[SQUARES.B8] == BLACK_KING )
		 && ( CHESS_BOARD[SQUARES.A8] == BLACK_ROOK || CHESS_BOARD[SQUARES.B8] == BLACK_ROOK || CHESS_BOARD[SQUARES.A7] == BLACK_ROOK )) { // Vezer oldal
			trappedS += 50;
		}

	// Blokkolt Feher Futo
		if (wNumBishops) {
			if (CHESS_BOARD[SQUARES.A7] == WHITE_BISHOP && CHESS_BOARD[SQUARES.B6] == BLACK_PAWN) { trappedS -= 100; trappedE -= 100; }
			if (CHESS_BOARD[SQUARES.H7] == WHITE_BISHOP && CHESS_BOARD[SQUARES.G6] == BLACK_PAWN) { trappedS -= 100; trappedE -= 100; }
			if (CHESS_BOARD[SQUARES.B8] == WHITE_BISHOP && CHESS_BOARD[SQUARES.C7] == BLACK_PAWN) { trappedS -= 100; trappedE -= 100; }
			if (CHESS_BOARD[SQUARES.G8] == WHITE_BISHOP && CHESS_BOARD[SQUARES.F7] == BLACK_PAWN) { trappedS -= 100; trappedE -= 100; }
			if (CHESS_BOARD[SQUARES.A6] == WHITE_BISHOP && CHESS_BOARD[SQUARES.B5] == BLACK_PAWN) { trappedS -= 100; trappedE -= 100; }
			if (CHESS_BOARD[SQUARES.H6] == WHITE_BISHOP && CHESS_BOARD[SQUARES.G5] == BLACK_PAWN) { trappedS -= 100; trappedE -= 100; }
			if (CHESS_BOARD[SQUARES.F1] == WHITE_BISHOP && CHESS_BOARD[SQUARES.E2] == WHITE_PAWN && CHESS_BOARD[SQUARES.E3]) { trappedS -= 50; }
			if (CHESS_BOARD[SQUARES.C1] == WHITE_BISHOP && CHESS_BOARD[SQUARES.D2] == WHITE_PAWN && CHESS_BOARD[SQUARES.D3]) { trappedS -= 50; }
		}

	// Blokkolt Fekete Futo
		if (bNumBishops) {
			if (CHESS_BOARD[SQUARES.A2] == BLACK_BISHOP && CHESS_BOARD[SQUARES.B3] == WHITE_PAWN) { trappedS += 100; trappedE += 100; }
			if (CHESS_BOARD[SQUARES.H2] == BLACK_BISHOP && CHESS_BOARD[SQUARES.G3] == WHITE_PAWN) { trappedS += 100; trappedE += 100; }
			if (CHESS_BOARD[SQUARES.B1] == BLACK_BISHOP && CHESS_BOARD[SQUARES.C2] == WHITE_PAWN) { trappedS += 100; trappedE += 100; }
			if (CHESS_BOARD[SQUARES.G1] == BLACK_BISHOP && CHESS_BOARD[SQUARES.F2] == WHITE_PAWN) { trappedS += 100; trappedE += 100; }
			if (CHESS_BOARD[SQUARES.A3] == BLACK_BISHOP && CHESS_BOARD[SQUARES.B4] == WHITE_PAWN) { trappedS += 100; trappedE += 100; }
			if (CHESS_BOARD[SQUARES.H3] == BLACK_BISHOP && CHESS_BOARD[SQUARES.G4] == WHITE_PAWN) { trappedS += 100; trappedE += 100; }
			if (CHESS_BOARD[SQUARES.F8] == BLACK_BISHOP && CHESS_BOARD[SQUARES.E7] == BLACK_PAWN && CHESS_BOARD[SQUARES.E6]) { trappedS += 50; }
			if (CHESS_BOARD[SQUARES.C8] == BLACK_BISHOP && CHESS_BOARD[SQUARES.D7] == BLACK_PAWN && CHESS_BOARD[SQUARES.D6]) { trappedS += 50; }
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (wNumBishops >= 2) {
			bishopsS += BishopPair;
			bishopsE += BishopPair;
		}
		if (bNumBishops >= 2) {
			bishopsS -= BishopPair;
			bishopsE -= BishopPair;
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (currentPlayer === WHITE) { // Tempo
			var tempoS = 20;
			var tempoE = 10;
		} else {
			var tempoS = -20;
			var tempoE = -10;
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var materialS = brd_Material[WHITE] - brd_Material[BLACK]; // Anyag ertekelese
		var materialE = materialS + (wNumPawns * 10) - (bNumPawns * 10); // Ertek atadasa

		materialS += mgWhite - mgBlack;
		materialE += egWhite - egBlack;

		var evalS = materialS;
		var evalE = materialE;

		evalS += mobS;
		evalE += mobE;

		evalS += trappedS;
		evalE += trappedE;

		evalS += tempoS;
		evalE += tempoE;

		evalS += attS;
		evalE += attE;

		evalS += pawnsS;
		evalE += pawnsE;

		evalS += knightsS;
		evalE += knightsE;

		evalS += bishopsS;
		evalE += bishopsE;

		evalS += rooksS;
		evalE += rooksE;

		evalS += queensS;
		evalE += queensE;

		evalS += kingS;
		evalE += kingE;

		if (Phase < 0) {  // Minden babu a fedelzeten = 0
			Phase = 0;
		}

		// Linearis interpolacio kezdo es vegjatek kozott
		Phase = (Phase << 8) / 24 + 0.5 | 0;
		var Score = ((evalS * (256 - Phase)) + (evalE * Phase)) >> 8;

		Score = Score / Draw | 0; // Ketes dontetlennel nem 0-at adunk vissza

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (currentPlayer === WHITE) {
			return Score;
		} else {
			return -Score;
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function WhitePawnStorm(BKingFile) {
		if (FileBBMask[BKingFile] & PawnBitBoard[WHITE] & RankBBMask[RANKS.RANK_6]) { // Also bit
			return 60;
		} else if (FileBBMask[BKingFile] & PawnBitBoard[WHITE] & RankBBMask[RANKS.RANK_5]) { // Also bit
			return 30;
		} else if (FileBBMask[BKingFile] & PawnBitBoard[WHITE|1] & RankBBMask[RANKS.RANK_4]) { // Felso bit
			return 10;
		}
		return 0;
	}

	function BlackPawnStorm(WKingFile) {
		if (FileBBMask[WKingFile] & PawnBitBoard[BLACK|1] & RankBBMask[RANKS.RANK_3]) { // Felso bit
			return 60;
		} else if (FileBBMask[WKingFile] & PawnBitBoard[BLACK|1] & RankBBMask[RANKS.RANK_4]) { // Felso bit
			return 30;
		} else if (FileBBMask[WKingFile] & PawnBitBoard[BLACK] & RankBBMask[RANKS.RANK_5]) { // Also bit
			return 10;
		}
		return 0;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function See(move) { // from garbochess.js

		var to = TOSQ(move);
		var from = FROMSQ(move);
		var fromPiece = CHESS_BOARD[from];
		var fromValue = SeeValue[fromPiece];
		var toValue = SeeValue[CHESS_BOARD[to]];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (PROMOTED(move) != 0 // Bevaltas
		|| (move & CASTLED_MASK) // Sancolas
		|| (move & CAPTURE_MASK && toValue == 0)) { // En passant
			return true;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (fromValue <= toValue) { // Nagyobb vagy azonos Babu
			return true;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var us = fromPiece & 0x8; // Akivel leptunk
		var them = us^8; // Aki kovetkezik
		var inc = (us === BLACK) ? 16 : -16; // Gyalog irany

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Ellenfel Gyalog Tamadas
		// Ha egy ellenseges Gyalog letud utni!
		if ((CHESS_BOARD[to + inc + 1] === (them | PAWN))
		 || (CHESS_BOARD[to + inc - 1] === (them | PAWN))) {
			return false;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var themAttacks = new Array(); // Ellenfel Tamadasok tomb

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Ellenfel Huszar Tamadas
		// Ha egy ellenseges Huszar letud utni,
		// es a nyereseg kisebb mint a Huszar erteke!
		var captureDeficit = fromValue - toValue;
		SeeAddKnightAttacks(to, them, themAttacks);
		if (themAttacks.length != 0 && captureDeficit > SeeValue[KNIGHT]) {
			return false;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		CHESS_BOARD[from] = 0; // Tamado babu torlese

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Ellenfel Futo, Bastya, Vezer Tamadas
		// Az elv megegyezik a Huszar tamadasnal leirtakkal.
		for (var pieceType = BISHOP; pieceType <= QUEEN; pieceType++) {
			if (SeeAddSliderAttacks(to, them, themAttacks, pieceType)) {
				if (captureDeficit > SeeValue[pieceType]) {
					CHESS_BOARD[from] = fromPiece; // Babu vissza
					return false;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
		// Ezen a ponton biztos, hogy rossz az utes, DE az ellenfel nem tud minket leutni.
		// El kell dontetni, hogy gyoztes vagy egyenlo merteku allast tudunk-e kiharcolni!
		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Sajat Gyalog Vedelem
		// Ha visszatudunk tamadni egy Gyaloggal!
		if ((CHESS_BOARD[to - inc + 1] === (us | PAWN)) ||
			(CHESS_BOARD[to - inc - 1] === (us | PAWN))) {
			CHESS_BOARD[from] = fromPiece; // Babu vissza
			return true;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Ellenfel Kiraly tamadas
		SeeAddSliderAttacks(to, them, themAttacks, KING);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var usAttacks = new Array(); // Sajat Tamadasok tomb

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Sajat Huszar Vedelem
		SeeAddKnightAttacks(to, us, usAttacks);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Sajat Futo, Bastya, Vezer Vedelem
		for (var pieceType = BISHOP; pieceType <= QUEEN; pieceType++) {
			SeeAddSliderAttacks(to, us, usAttacks, pieceType);
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Sajat Kiraly Vedelem
		SeeAddSliderAttacks(to, us, usAttacks, KING);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		CHESS_BOARD[from] = fromPiece; // Babu vissza

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
		// Jelenleg nyero anyagi helyzetben vagyunk! Most megnezzuk, hogy az ellenfel
		// vissza tud-e tamadni. Feltetelezzuk, hogy az ellenfel megtudja tartani a
		// jelenlegi pontszamat, ezzel jelentosen egyszerusodik a kesobbi kod.
		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var seeValue = toValue - fromValue;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (; ; )
		{
			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Ellenfel fog tamadni
			var capturingPieceValue = 1000;
			var capturingPieceIndex = -1;

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// A ellenfel legkevesbe ertekes babuja, aki tamadni tudja a mezot
			for (var i = 0; i < themAttacks.length; i++) {
				if (themAttacks[i] != 8) {
					var pieceValue = SeeValue[CHESS_BOARD[themAttacks[i]]];
					if (pieceValue < capturingPieceValue) {
						capturingPieceValue = pieceValue;
						capturingPieceIndex = i;
					}
				}
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (capturingPieceIndex == -1) { // Nem tud visszatamadni! Mi nyertunk ;)
				return true;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// A fentebbi tamado erteket hozzaadjuk a pontkulonbseghez
			// es igy is vesztes helyzetben vagyunk! Mi vesztettunk :(
			seeValue += capturingPieceValue;
			if (seeValue < 0) {
				return false;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			var capturingPieceSquare = themAttacks[capturingPieceIndex];
			themAttacks[capturingPieceIndex] = 8;

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Rontgen tamadasok hozzadasa
			SeeAddXrayAttack(to, capturingPieceSquare, us, usAttacks, themAttacks);

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Mi fogunk tamadni
			capturingPieceValue = 1000;
			capturingPieceIndex = -1;

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// A legkevesbe ertekes babunk, aki tamadni tudja a mezot
			for (var i = 0; i < usAttacks.length; i++) {
				if (usAttacks[i] != 8) {
					var pieceValue = SeeValue[CHESS_BOARD[usAttacks[i]]];
					if (pieceValue < capturingPieceValue) {
						capturingPieceValue = pieceValue;
						capturingPieceIndex = i;
					}
				}
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (capturingPieceIndex == -1) { // Nem tudunk visszatamadni! Mi vesztettunk :(
				return false;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Feltesszuk, hogy az ellenfel ujra leut minket,
			// es igy is vesztes helyzetben van! Mi nyertunk ;)
			seeValue -= capturingPieceValue;
			if (seeValue >= 0) {
				return true;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			capturingPieceSquare = usAttacks[capturingPieceIndex];
			usAttacks[capturingPieceIndex] = 8;

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Rontgen tamadasok hozzadasa
			SeeAddXrayAttack(to, capturingPieceSquare, us, usAttacks, themAttacks);
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function IsSquareOnPieceLine(target, from) {
		var index = from - target + 128;
		var piece = CHESS_BOARD[from];
		return (brd_vectorDelta[index].pieceMask[(piece & 0x8)] & (1 << (piece & 0x07))) ? true : false;
	}

	function SeeAddXrayAttack(target, square, currentPlayer, usAttacks, themAttacks) {
		var index = square - target + 128;
		var delta = -brd_vectorDelta[index].delta;
		if (delta == 0) return;

		square += delta;

		while (!(square & 0x88) && CHESS_BOARD[square] == 0) { // Kereses
			square += delta;
		}

		if (!(square & 0x88) && IsSquareOnPieceLine(target, square)) {
			if ((CHESS_BOARD[square] & 0x8) == currentPlayer) {
				usAttacks[usAttacks.length] = square; // Sajat Vedelem
			} else {
				themAttacks[themAttacks.length] = square; // Ellenfel Tamadas
			}
		}
	}

	function SeeAddKnightAttacks(target, currentPlayer, attacks) {
		var pieceIdx = (currentPlayer | KNIGHT) << 4;
		var from_sq = brd_pieceList[pieceIdx++];

		while (from_sq != 8) {
			if (IsSquareOnPieceLine(target, from_sq)) {
				attacks[attacks.length] = from_sq;
			}
			from_sq = brd_pieceList[pieceIdx++];
		}
	}

	function IsSquareAttackableFrom(target, from) {
		var index = from - target + 128;
		if (IsSquareOnPieceLine(target, from)) {
			var inc = brd_vectorDelta[index].delta;
			do {
				from += inc;
				if (from == target)
					return true;
			} while (!(from & 0x88) && CHESS_BOARD[from] == 0);
		}
		return false;
	}

	function SeeAddSliderAttacks(target, currentPlayer, attacks, pieceType) {
		var pieceIdx = (currentPlayer | pieceType) << 4;
		var from_sq = brd_pieceList[pieceIdx++];
		var hit = false;

		while (from_sq != 8) {
			if (IsSquareAttackableFrom(target, from_sq)) {
				attacks[attacks.length] = from_sq;
				hit = true;
			}
			from_sq = brd_pieceList[pieceIdx++];
		}
		return hit;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function GenerateAllMoves(capturesOnly, useSee) {

		var pieceType	= 0; // Akivel lepunk
		var pieceIdx	= 0; // Babu indexeles
		var from_sq		= 0; // Ahonnan lepunk
		var next_sq		= 0; // Ahova lepunk
		var Score		= 0; // Lepes pont
		var dir			= 0; // Lepes irany

		brd_moveStart[boardPly + 1] = brd_moveStart[boardPly]; // Hack

		if (currentPlayer === WHITE) // FEHER OLDAL
		{
			pieceIdx = WHITE_PAWN << 4;
			from_sq = brd_pieceList[pieceIdx++];
			while (from_sq != 8)
			{
				next_sq = from_sq - 16; // Elore lepes

				if (capturesOnly === false) // Ha az ures lepeseket is keressuk
				{
					if (CHESS_BOARD[next_sq] == 0) // Ures mezo
					{
						if (TableRanks[from_sq] == RANKS.RANK_7) // Gyalog bevaltas
						{
							AddQuietMove(from_sq, next_sq, WHITE_QUEEN, 0);
							AddQuietMove(from_sq, next_sq, WHITE_ROOK,  0);
							AddQuietMove(from_sq, next_sq, WHITE_BISHOP, 0);
							AddQuietMove(from_sq, next_sq, WHITE_KNIGHT, 0);
						} else {
							AddQuietMove(from_sq, next_sq, 0, 0); // Sima lepes

							if (TableRanks[from_sq] == RANKS.RANK_2 && CHESS_BOARD[from_sq - 32] == 0) // Dupla lepes
							{
								AddQuietMove(from_sq, from_sq - 32, 0, 0);
							}
						}
					}
				} else if (CHESS_BOARD[next_sq] == 0 && TableRanks[from_sq] == RANKS.RANK_7) { // Vezer Promocio (Quiescence)

					AddQuietMove(from_sq, next_sq, WHITE_QUEEN, 0);
				}

				next_sq = from_sq - 15; // Utes egyik oldal

				if (!(next_sq & 0x88)) { // Nem logunk ki a tablarol

					if (CHESS_BOARD[next_sq] && (CHESS_BOARD[next_sq] & 0x8) === BLACK) // Ellenfel
					{
						Score = 1000005 + (100 * MvvLvaScores[CHESS_BOARD[next_sq]]); // Pontszam

						if (TableRanks[from_sq] == RANKS.RANK_7) // Gyalog bevaltas
						{
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, WHITE_QUEEN, 0), Score);
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, WHITE_ROOK,  0), Score);
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, WHITE_BISHOP, 0), Score);
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, WHITE_KNIGHT, 0), Score);
						} else {
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, 0, 0), Score); // Nincs gyalogbevaltas
						}
					} else if (CHESS_BOARD[next_sq] == 0 && EN_PASSANT != 0 && EN_PASSANT == next_sq) { // En Passant

						Score = 1000105; // En Passant Pontszam

						AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, 0, 0), Score);
					}
				}

				next_sq = from_sq - 17; // Utes masik oldal

				if (!(next_sq & 0x88)) { // Nem logunk ki a tablarol

					if (CHESS_BOARD[next_sq] && (CHESS_BOARD[next_sq] & 0x8) === BLACK) // Ellenfel
					{
						Score = 1000005 + (100 * MvvLvaScores[CHESS_BOARD[next_sq]]); // Pontszam

						if (TableRanks[from_sq] == RANKS.RANK_7) // Gyalog bevaltas
						{
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, WHITE_QUEEN, 0), Score);
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, WHITE_ROOK,  0), Score);
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, WHITE_BISHOP, 0), Score);
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, WHITE_KNIGHT, 0), Score);
						} else {
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, 0, 0), Score); // Nincs gyalogbevaltas
						}
					} else if (CHESS_BOARD[next_sq] == 0 && EN_PASSANT != 0 && EN_PASSANT == next_sq) { // En Passant

						Score = 1000105; // En Passant Pontszam

						AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, 0, 0), Score);
					}
				}

				from_sq = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (capturesOnly === false) // Ha az ures lepeseket is keressuk
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
			from_sq = brd_pieceList[pieceIdx++];
			while (from_sq != 8)
			{
				next_sq = from_sq + 16; // Elore lepes

				if (capturesOnly === false) // Ha az ures lepeseket is keressuk
				{
					if (CHESS_BOARD[next_sq] == 0) // Ures mezo
					{
						if (TableRanks[from_sq] == RANKS.RANK_2) // Gyalog bevaltas
						{
							AddQuietMove(from_sq, next_sq, BLACK_QUEEN, 0);
							AddQuietMove(from_sq, next_sq, BLACK_ROOK,  0);
							AddQuietMove(from_sq, next_sq, BLACK_BISHOP, 0);
							AddQuietMove(from_sq, next_sq, BLACK_KNIGHT, 0);
						} else {
							AddQuietMove(from_sq, next_sq, 0, 0); // Sima lepes

							if (TableRanks[from_sq] == RANKS.RANK_7 && CHESS_BOARD[from_sq + 32] == 0) // Dupla lepes
							{
								AddQuietMove(from_sq, from_sq + 32, 0, 0);
							}
						}
					}
				} else if (CHESS_BOARD[next_sq] == 0 && TableRanks[from_sq] == RANKS.RANK_2) { // Vezer Promocio (Quiescence)

					AddQuietMove(from_sq, next_sq, BLACK_QUEEN, 0);
				}

				next_sq = from_sq + 15; // Utes egyik oldal

				if (!(next_sq & 0x88)) { // Nem logunk ki a tablarol

					if (CHESS_BOARD[next_sq] && (CHESS_BOARD[next_sq] & 0x8) === WHITE) // Ellenfel
					{
						Score = 1000005 + (100 * MvvLvaScores[CHESS_BOARD[next_sq]]); // Pontszam

						if (TableRanks[from_sq] == RANKS.RANK_2) // Gyalog bevaltas
						{
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, BLACK_QUEEN, 0), Score);
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, BLACK_ROOK,  0), Score);
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, BLACK_BISHOP, 0), Score);
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, BLACK_KNIGHT, 0), Score);
						} else {
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, 0, 0), Score); // Nincs gyalogbevaltas
						}
					} else if (CHESS_BOARD[next_sq] == 0 && EN_PASSANT != 0 && EN_PASSANT == next_sq) { // En Passant

						Score = 1000105; // En Passant Pontszam

						AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, 0, 0), Score);
					}
				}

				next_sq = from_sq + 17; // Utes masik oldal

				if (!(next_sq & 0x88)) { // Nem logunk ki a tablarol

					if (CHESS_BOARD[next_sq] && (CHESS_BOARD[next_sq] & 0x8) === WHITE) // Ellenfel
					{
						Score = 1000005 + (100 * MvvLvaScores[CHESS_BOARD[next_sq]]); // Pontszam

						if (TableRanks[from_sq] == RANKS.RANK_2) // Gyalog bevaltas
						{
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, BLACK_QUEEN, 0), Score);
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, BLACK_ROOK,  0), Score);
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, BLACK_BISHOP, 0), Score);
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, BLACK_KNIGHT, 0), Score);
						} else {
							AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, 0, 0), Score); // Nincs gyalogbevaltas
						}
					} else if (CHESS_BOARD[next_sq] == 0 && EN_PASSANT != 0 && EN_PASSANT == next_sq) { // En Passant

						Score = 1000105; // En Passant Pontszam

						AddCaptureMove(BIT_MOVE(from_sq, next_sq, 1, 0, 0), Score);
					}
				}

				from_sq = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (capturesOnly === false) // Ha az ures lepeseket is keressuk
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
			from_sq = brd_pieceList[pieceIdx++];
			while (from_sq != 8)
			{
				for (dir = 0; dir < DirNum[pieceType]; dir++)
				{
					next_sq = (from_sq + PieceDir[pieceType][dir]); // Ahova lepunk

					if (next_sq & 0x88) { // Kilogunk a tablarol
						continue;
					}

					if (CHESS_BOARD[next_sq]) { // Nem ures mezo

						if ((CHESS_BOARD[next_sq] & 0x8) !== currentPlayer) { // Ha ellenfelet tudunk leutni

							var Move = BIT_MOVE(from_sq, next_sq, 1, 0, 0);

							if (useSee === true && !See(Move)) {
								Score = 106 + ((100 * MvvLvaScores[CHESS_BOARD[next_sq]]) - MvvLvaScores[pieceType]); // Pontszam
							} else {
								Score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next_sq]]) - MvvLvaScores[pieceType]); // Pontszam
							}

							AddCaptureMove(Move, Score);
						}

					} else if (capturesOnly === false) { // Ures mezo ha nem csak uteseket keresunk

						AddQuietMove(from_sq, next_sq, 0, 0);
					}
				}

				from_sq = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Futo, Bastya, Vezer
		for (pieceType = BISHOP; pieceType <= QUEEN; pieceType++)
		{
			pieceIdx = (currentPlayer | pieceType) << 4;
			from_sq = brd_pieceList[pieceIdx++];
			while (from_sq != 8)
			{
				for (dir = 0; dir < DirNum[pieceType]; dir++)
				{
					next_sq = (from_sq + PieceDir[pieceType][dir]); // Ahova lepunk

					while (!(next_sq & 0x88))
					{
						if (CHESS_BOARD[next_sq]) { // Nem ures mezo

							if ((CHESS_BOARD[next_sq] & 0x8) !== currentPlayer) { // Ha ellenfelet tudunk leutni

								var Move = BIT_MOVE(from_sq, next_sq, 1, 0, 0);

								if (useSee === true && !See(Move)) {
									Score = 106 + ((100 * MvvLvaScores[CHESS_BOARD[next_sq]]) - MvvLvaScores[pieceType]); // Pontszam
								} else {
									Score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next_sq]]) - MvvLvaScores[pieceType]); // Pontszam
								}

								AddCaptureMove(Move, Score);
							}

							break; // Az adott iranyba nem vizsgalunk tovabb

						} else if (capturesOnly === false) { // Ures mezo ha nem csak uteseket keresunk

							AddQuietMove(from_sq, next_sq, 0, 0);
						}

						next_sq += PieceDir[pieceType][dir]; // Kovetkezo Mezo
					}
				}

				from_sq = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
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
			var Score = 1000 + historyTable[CHESS_BOARD[from]][to]; // Elozmeny tabla alapjan
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


	function Quiescence(alpha, beta, inCheck) {

		if ((nodes & 2047) == 0) { // Ido ellenorzese
			CheckUp();
		}

		nodes++; // Csomopontok novelese

		if (IsRepetition()) { // Lepesismetles
			return 0;
		}

		if (boardPly > maxDepth - 1) { // Tombok tulcsordulasa ellen
			return Evaluation();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (inCheck == UNKNOWN_CHECK) inCheck = isCheck(currentPlayer); // Sakk?

		var BestScore = inCheck ? -INFINITE : Evaluation(); // Allapot ertekelese

		if (!inCheck && BestScore >= beta) { // Vagas
			return BestScore;
		}

		if (!inCheck && BestScore > alpha) { // Alpha ertek mentese
			alpha = BestScore;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var Score = -INFINITE; // Pont nullazas
		var capturedPCE = NOMOVE; // Leutott babu
		var currentMove = NOMOVE; // Aktualis lepes
		var enemy = currentPlayer^8; // Delta metszes
		var DeltaMargin = BestScore + 200; // Delta Margo
		if (!inCheck) {
			GenerateAllMoves(true, false); // Utes lepesek
		} else {
			GenerateAllMoves(false, true); // Minden lepes
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; ++index)
		{
			PickNextMove(index);

			currentMove = brd_moveList[index];
			capturedPCE = CHESS_BOARD[TOSQ(currentMove)];

			if (!inCheck
			&& !PROMOTED(currentMove)
			&& (brd_pieceCount[enemy | ROOK]
			  + brd_pieceCount[enemy | QUEEN]
			  + brd_pieceCount[enemy | KNIGHT]
			  + brd_pieceCount[enemy | BISHOP]) > 1) // Delta metszes
			{
				var FutileValue = DeltaMargin;

				if (capturedPCE == 0) { // En Passant
					FutileValue += PieceValue[PAWN];
				} else {
					FutileValue += PieceValue[capturedPCE];
				}

				if (FutileValue < alpha) {
					if (FutileValue > BestScore) {
						BestScore = FutileValue;
					}
					continue;
				}
			}

			if (!inCheck && !See(currentMove)) { // Rossz utes
				continue;
			}

			if (!makeMove(currentMove)) { // Lepes ervenyesitese
				continue;
			}

			Score = -Quiescence(-beta, -alpha, UNKNOWN_CHECK); // Kereses

			unMakeMove(); // Lepes visszavonasa

			if (timeStop == 1) { // Ido vagas
				return 0;
			}

			if (Score > BestScore) {
				BestScore = Score;
				if (Score > alpha) {
					if (Score >= beta) {
						return Score;
					}
					alpha = Score;
				}
			}
		}

		if (inCheck && Score == -INFINITE) { // Matt
			return -INFINITE + boardPly;
		}

		return BestScore;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function AlphaBeta(alpha, beta, Depth, nullMove, inCheck) {

		if (Depth <= 0) { // Melyseg eleresekor kiertekeles
			return Quiescence(alpha, beta, inCheck);
			// return Evaluation();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if ((nodes & 2047) == 0) { // Ido ellenorzese
			CheckUp();
		}

		nodes++; // Csomopontok novelese

		if (boardPly != 0 && IsRepetition()) { // Lepesismetles
			return 0;
		}

		if (boardPly > maxDepth - 1) { // Tombok tulcsordulasa ellen
			return Evaluation();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (boardPly != 0) { // Matt-tavolsag metszes
			var mate_value = INFINITE - boardPly;
			if (alpha < -mate_value) alpha = -mate_value;
			if (beta > mate_value - 1) beta = mate_value - 1;
			if (alpha >= beta) {
				return alpha;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var IS_PV = (beta != alpha + 1);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var hashMove = ProbeHashMove(); // Egyezo hashKey-t keresunk

		if (!IS_PV && hashMove != NOMOVE) { // Van egyezo hashKey

			if (hashMove.depth >= Depth) { // Pontszamot adunk vissza

				var value = hashMove.score;

				if (value > ISMATE) { // Pontszam fixalasa
					value -= boardPly;
				} else if (value < -ISMATE) { // Pontszam fixalasa
					value += boardPly;
				}

				if (hashMove.flags == FLAG_ALPHA && value <= alpha) {
					return value;
				}
				if (hashMove.flags == FLAG_BETA && value >= beta) {
					return value;
				}
				if (hashMove.flags == FLAG_EXACT) {
					return value;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var pruneNode = false;
		var Score = -INFINITE;
		if (inCheck == UNKNOWN_CHECK) inCheck = isCheck(currentPlayer);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (!IS_PV && !inCheck
		&& (brd_pieceCount[currentPlayer | KNIGHT] != 0
		 || brd_pieceCount[currentPlayer | BISHOP] != 0
		 || brd_pieceCount[currentPlayer | ROOK]   != 0
		 || brd_pieceCount[currentPlayer | QUEEN]  != 0)) { // Metszheto csomopont
			pruneNode = true;
			if (nullMove || Depth <= 4) // Futility depth
			var staticEval = Evaluation();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (pruneNode && nullMove && !isMate(beta)) // Metszesek
		{
			if (Depth <= 2) { // Statikus null lepes
				Score = staticEval - 120 * Depth;
				if (Score >= beta && PawnOnSeventh() == 0) {
					return Score;
				}
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (Depth >= 2 && staticEval >= beta) // Null lepes
			{
				var enPassant = EN_PASSANT; // En Passant bug fix

				if (EN_PASSANT != 0) HASH_EP(); // En Passan hashKey

				EN_PASSANT = 0; // En Passant kikapcsolasa

				currentPlayer ^= 8; // Ember valtas

				HASH_SIDE(); // Aki lephet hashKey

				if (Depth <= 4) {
					Score = -Quiescence(-beta, -beta+1, NOT_IN_CHECK);
				} else {
					Score = -AlphaBeta(-beta, -beta+1, Depth-4, false, UNKNOWN_CHECK);
				}

				currentPlayer ^= 8; // Ember valtas

				HASH_SIDE(); // Aki lephet hashKey

				EN_PASSANT = enPassant; // En Passant vissza

				if (EN_PASSANT != 0) HASH_EP(); // En Passan hashKey

				if (timeStop == 1) { // Ido vagas
					return 0;
				}

				if (Score >= beta && !isMate(Score)) {
					return Score;
				}
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (Depth <= 3 && hashMove == NOMOVE) { // Razoring based on Toga II 3.0
				var threshold = beta - 240 - Depth * 60;
				if (staticEval < threshold && PawnOnSeventh() == 0) {
					Score = Quiescence(threshold-1, threshold, NOT_IN_CHECK);
					if (Score < threshold) return Score;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (IS_PV && boardPly != 0 && Depth >= 4 && hashMove == NOMOVE) { // Belso iterativ melyites /IID/
			Score = AlphaBeta(alpha, beta, Depth-2, false, inCheck);
			if (Score > alpha) hashMove = ProbeHashMove();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		Score = -INFINITE; // Pont nullazas
		var E = 0; // Kiterjesztes valtozo
		var R = 0; // LMR Dinamikus valtozo
		var index = 0; // Forciklus valtozo
		var LegalMove = 0; // Ervenyes lepes
		var moveScore = 0; // Lepes pontszama
		var OldAlpha = alpha; // Alpha mentese
		var BestMove = NOMOVE; // Legjobb lepes
		var Check = NOT_IN_CHECK; // Sakk lepes
		var currentMove = NOMOVE; // Aktualis lepes
		var BestScore = -INFINITE; // Legjobb pontszam
		var PlayedMoves = new Array(); // Lepesek tomb
		GenerateAllMoves(false, true); // Minden lepes

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var LMR_OK = (!inCheck  && Depth >= 3); // Keso lepes csokkentes /LMR/
		var LMP_OK = (pruneNode && Depth <= 2); // Keso lepes metszes /LMP/
		var FUTILE = (pruneNode && Depth <= 4); // Hiabavalosag metszes
		var Margin = [ 0, 150, 200, 250, 300 ]; // Hiabavalosag margok
		if (FUTILE) var FutileValue = staticEval + Margin[Depth];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (hashMove != NOMOVE) { // Atultetesi tablabol lepes
			for (index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; ++index)
			{
				if (brd_moveList[index] == hashMove.move) { // Elore soroljuk
					brd_moveScores[index] = 2000000;
					break;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; ++index)
		{
			PickNextMove(index);

			currentMove = brd_moveList[index];
			moveScore = brd_moveScores[index];

			if (!makeMove(currentMove)) { // Lepes ervenyesitese
				continue;
			}

			Check = isCheck(currentPlayer);

			E = 0; // "E" nullazasa
			R = 0; // "R" nullazasa

			if (moveScore < 800000
			&& !Check && LegalMove
			&& (LMR_OK || FUTILE || LMP_OK)
			&& !(currentMove & DANGER_MASK)
			&& !PawnPush(TOSQ(currentMove)))
			{
				if (LMP_OK && !isMate(BestScore) && LegalMove > Depth*5) { // Late Move Pruning
					unMakeMove();
					continue;
				}
				if (FUTILE && !isMate(BestScore) && FutileValue < alpha) { // Futility Pruning
					if (FutileValue > BestScore) {
						BestScore = FutileValue;
					}
					unMakeMove();
					continue;
				}
				if (LMR_OK && LegalMove >= 3) // Late Move Reduction
				{
					if (!IS_PV) {
						R = 0.33 + Math.log(Depth) * Math.log(Math.min(LegalMove, 63)) / 2.25 | 0; // 2.21
					} else {
						R = 0.00 + Math.log(Depth) * Math.log(Math.min(LegalMove, 63)) / 3.00 | 0; // 2.93
					}
				}
			}

			if (inCheck && (IS_PV || Depth < 5)) { // Sakk kiterjesztes
				E = 1;
			}

			if ((IS_PV && LegalMove != 0) || R != 0) {
				Score = -AlphaBeta(-alpha-1, -alpha, Depth+E-R-1, true, Check); // PVS-LMR
				if (Score > alpha) {
					Score = -AlphaBeta(-beta, -alpha, Depth+E-1, true, Check); // Full
				}
			} else {
				Score = -AlphaBeta(-beta, -alpha, Depth+E-1, true, Check); // Full
			}

			PlayedMoves[LegalMove++] = currentMove; // Ervenyes lepesek

			unMakeMove(); // Lepes visszavonasa

			if (timeStop == 1) { // Ido vagas
				return 0;
			}

			if (Score > BestScore) {

				BestScore = Score;
				BestMove = currentMove;

				if (boardPly == 0 && (LegalMove == 1 || Score > alpha)) {
					UpdatePv(currentMove, Score, Depth, alpha, beta);
				}

				if (Score > alpha) {
					if (Score >= beta) {

						if (!inCheck && (currentMove & TACTICAL_MASK) == 0) { // Update Killers & History
							if (searchKillers[boardPly][0] != currentMove) {
								searchKillers[boardPly][1] = searchKillers[boardPly][0];
								searchKillers[boardPly][0] = currentMove;
							}
							HistoryGood(currentMove);

							for (var h = 0; h < LegalMove-1; h++) {
								HistoryBad(PlayedMoves[h]);
							}
						}

						StoreHashMove(currentMove, Score, FLAG_BETA, Depth);

						return Score;
					}
					alpha = Score;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (LegalMove == 0)
		{
			// console.log(inCheck ? "MATT" : "PATT");
			// postMessage(["Redraw", CHESS_BOARD]);
			// for (var index = 0; index < 1000000000; index++) { }

			if (inCheck)
			return -INFINITE + boardPly; // Matt
			else
			return 0; // Patt
		}

		if (alpha != OldAlpha) {
			StoreHashMove(BestMove, BestScore, FLAG_EXACT, Depth);
		} else {
			StoreHashMove(BestMove, BestScore, FLAG_ALPHA, Depth);
		}

		return BestScore;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function HistoryGood(move) {
		var hist = historyTable[CHESS_BOARD[FROMSQ(move)]][TOSQ(move)];
		historyTable[CHESS_BOARD[FROMSQ(move)]][TOSQ(move)] += (2048 - hist) >> 5;
	}

	function HistoryBad(move) {
		if ((move & TACTICAL_MASK) == 0) {
			var hist = historyTable[CHESS_BOARD[FROMSQ(move)]][TOSQ(move)];
			historyTable[CHESS_BOARD[FROMSQ(move)]][TOSQ(move)] -= hist >> 5;
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function InitEnginSearch() {
		InitEvalMasks(); // Bitmaszk inicializalas
		InitEvalTable(); // Ertekeles inicializalas
		brd_HashTable = null; // Atultetesi tabla urites
		brd_HashTable = new Array(HASHENTRIES); // Ures tabla
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function ClearForSearch() {

		nodes = boardPly = bestMove = timeStop = 0;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		PawnBitBoard = [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ];

		// Feher Gyalogok
		var pieceIdx = WHITE_PAWN << 4;
		var PCE = brd_pieceList[pieceIdx++];
		while (PCE != 8)
		{
			SetBitBoard(PCE, WHITE); // Feher Gyalog Bitboard
			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

		// Fekete Gyalogok
		var pieceIdx = BLACK_PAWN << 4;
		var PCE = brd_pieceList[pieceIdx++];
		while (PCE != 8)
		{
			SetBitBoard(PCE, BLACK); // Fekete Gyalog Bitboard
			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var i = 0; i < maxDepth; i++) { // Gyilkosok
			searchKillers[i] = [0, 0];
		}

		for (var i = 0; i < 16; i++) { // Elozmeny tabla
			historyTable[i] = new Array(120);
			for (var j = 0; j < 120; j++) {
				historyTable[i][j] = 1024;
			}
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function DataUpgrade(board, player, castle, enpassant, material, castlekeysL, piecekeysL, sidekeyL,
	hashkeyL, castlekeysH, piecekeysH, sidekeyH, hashkeyH, pieceList, pieceIndex, pieceCount, b_history) {
		CHESS_BOARD = board; // sakk tabla
		castleRights = castle; // sancolas
		EN_PASSANT = enpassant; // en passant
		currentPlayer = player; // aki lephet
		SideKeyLow = sidekeyL; // oldal hashKey
		SideKeyHigh = sidekeyH; // oldal hashKey
		brd_Material = material; // anyag ertekek
		brd_pieceList = pieceList; // babu listak
		brd_pieceIndex = pieceIndex; // babu index
		brd_pieceCount = pieceCount; // babuk szama
		PieceKeysLow = piecekeysL; // babuk hashKey
		PieceKeysHigh = piecekeysH; // babuk hashKey
		brd_hashKeyLow = hashkeyL; // aktualis hashKey
		brd_hashKeyHigh = hashkeyH; // aktualis hashKey
		CastleKeysLow = castlekeysL; // sancolas hashKey
		CastleKeysHigh = castlekeysH; // sancolas hashKey
		MOVE_HISTORY = b_history; // Lepeselozmenyek atvetele
		moveCount = parseInt(MOVE_HISTORY.length); // Lepesszam
		if (moveCount > 0)
		brd_fiftyMove = MOVE_HISTORY[moveCount-1].fiftyMove; // 50 lepes
		else
		brd_fiftyMove = 0;

		return true;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	onmessage = function (e) {

		if (e.data[0] == "restart")
		{
			InitEnginSearch(); UI_MODE = 1;
		}
		else if (e.data[0] == "search")
		{
			if (DataUpgrade(e.data[3], e.data[4], e.data[5], e.data[6], e.data[7], e.data[8], e.data[9], e.data[10],
			e.data[11], e.data[12], e.data[13], e.data[14], e.data[15], e.data[16], e.data[17], e.data[18], e.data[19]))
			{
				ClearForSearch(); // Nullazas

				var alpha = -INFINITE;
				var beta = INFINITE;
				var countMove = 0;
				var Score = 0;

				// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

				if (e.data[2]) { // Segitseg maximum 2 masodpercig
					maxSearchTime = e.data[1] > 2000 ? 2000 : e.data[1];
				} else {
					maxSearchTime = e.data[1]; // Beallitott ideig keresunk
				}

				if (maxSearchTime >= 1000) { // 1 masodperc felett
					maxDepth = 64;
				} else {
					maxDepth = maxSearchTime / 100; // 1 masodperc alatt
					maxSearchTime = 1000;
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

				postMessage(["SearchStart", startTime]); // Elkezdtuk a keresest

				for (currDepth = 1; currDepth <= maxDepth; currDepth++) // iterativ melyites
				{
					if (countMove == 1 && currDepth > 5 && bestMove) break; // Egy ervenyes lepes

					Score = AlphaBeta(alpha, beta, currDepth, true, UNKNOWN_CHECK); // Kereses

					if (timeStop == 1) break; // Lejart az ido

					if (Score > alpha && Score < beta) { // Ablakon belul
						alpha = Score - 50;
						beta = Score + 50;

						if (alpha < -INFINITE) alpha = -INFINITE;
						if (beta > INFINITE) beta = INFINITE;
					} else if (alpha != -INFINITE) { // Kilogunk az ablakbol
						alpha = -INFINITE;
						beta = INFINITE;
						currDepth--;
					}
				}

				postMessage(["bestMove", bestMove]); // Lepes elkuldese
			}
		}

	};


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function UpdatePv(Move, Score, depth, alpha, beta) {

		var flags = FLAG_NONE;
		if (Score > alpha) flags |= FLAG_BETA;
		if (Score < beta)  flags |= FLAG_ALPHA;

		StoreHashMove(Move, Score, flags, depth);

		var pvNum = GetPvLine(depth); bestMove = brd_PvArray[0];

		if (UI_MODE == 1) // Worker
		{
			postMessage(["SearchInfo", bestMove]); // Info kuldes

			/*MoveTime = (Date.now() - startTime); // Keresesi ido

			var pvLine = ''; // PV
			for (var index = 0; index < pvNum; index++) {
				pvLine += ' '+FormatMove(brd_PvArray[index].move);
			}

			if (flags ==  FLAG_BETA) depth += '+';
			if (flags == FLAG_ALPHA) depth += '-';

			console.log('Depth: '+depth+ ' Score: '+Score+' Nodes: '+nodes+' Time: '+MoveTime+' Pv:'+pvLine);*/
		}
		else if (UI_MODE == 2) // Node.js
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

			nodefs.writeSync(1, 'info depth '+currDepth+' score '+Score+' nodes '+nodes+' time '+MoveTime+' pv'+pvLine+'\n');
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
	-40, -30, -50, -70, -70, -50, -30, -40,		0, 0, 0, 0, 0, 0, 0, 0,
	-30, -20, -40, -60, -60, -40, -20, -30,		0, 0, 0, 0, 0, 0, 0, 0,
	-20, -10, -30, -50, -50, -30, -10, -20,		0, 0, 0, 0, 0, 0, 0, 0,
	-10,   0, -20, -40, -40, -20,   0, -10,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,  10, -10, -30, -30, -10,  10,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	 10,  20,   0, -20, -20,   0,  20,  10,		0, 0, 0, 0, 0, 0, 0, 0,
	 30,  40,  20,   0,   0,  20,  40,  30,		0, 0, 0, 0, 0, 0, 0, 0,
	 40,  50,  30,  10,  10,  30,  50,  40
	];

	// Kiraly vegjatek
	var KingEndMask = [
	-72, -48, -36, -24, -24, -36, -48, -72,		0, 0, 0, 0, 0, 0, 0, 0,
	-48, -24, -12,   0,   0, -12, -24, -48,		0, 0, 0, 0, 0, 0, 0, 0,
	-36, -12,   0,  12,  12,   0, -12, -36,		0, 0, 0, 0, 0, 0, 0, 0,
	-24,   0,  12,  24,  24,  12,   0, -24,		0, 0, 0, 0, 0, 0, 0, 0,
	-24,   0,  12,  24,  24,  12,   0, -24,		0, 0, 0, 0, 0, 0, 0, 0,
	-36, -12,   0,  12,  12,   0, -12, -36,		0, 0, 0, 0, 0, 0, 0, 0,
	-48, -24, -12,   0,   0, -12, -24, -48,		0, 0, 0, 0, 0, 0, 0, 0,
	-72, -48, -36, -24, -24, -36, -48, -72
	];

	// Vezer
	var QueenMask = [
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	 -5,  -5,  -5,  -5,  -5,  -5,  -5,  -5
	];

	// Vezer vegjatek
	var QueenEndMask = [
	-24, -16, -12,  -8,  -8, -12, -16, -24,		0, 0, 0, 0, 0, 0, 0, 0,
	-16,  -8,  -4,   0,   0,  -4,  -8, -16,		0, 0, 0, 0, 0, 0, 0, 0,
	-12,  -4,   0,   4,   4,   0,  -4, -12,		0, 0, 0, 0, 0, 0, 0, 0,
	 -8,   0,   4,   8,   8,   4,   0,  -8,		0, 0, 0, 0, 0, 0, 0, 0,
	 -8,   0,   4,   8,   8,   4,   0,  -8,		0, 0, 0, 0, 0, 0, 0, 0,
	-12,  -4,   0,   4,   4,   0,  -4, -12,		0, 0, 0, 0, 0, 0, 0, 0,
	-16,  -8,  -4,   0,   0,  -4,  -8, -16,		0, 0, 0, 0, 0, 0, 0, 0,
	-24, -16, -12,  -8,  -8, -12, -16, -24
	];

	// Bastya
	var RookMask = [
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6
	];

	// Futo
	var BishopMask = [
	 -8,  -8,  -6,  -4,  -4,  -6,  -8,  -8,		0, 0, 0, 0, 0, 0, 0, 0,
	 -8,   0,  -2,   0,   0,  -2,   0,  -8,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -2,   4,   2,   2,   4,  -2,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -4,   0,   2,   8,   8,   2,   0,  -4,		0, 0, 0, 0, 0, 0, 0, 0,
	 -4,   0,   2,   8,   8,   2,   0,  -4,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -2,   4,   2,   2,   4,  -2,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -8,   0,  -2,   0,   0,  -2,   0,  -8,		0, 0, 0, 0, 0, 0, 0, 0,
	-18, -18, -16, -14, -14, -16, -18, -18
	];

	// Futo vegjatek
	var BishopEndMask = [
	-18, -12,  -9,  -6,  -6,  -9, -12, -18,		0, 0, 0, 0, 0, 0, 0, 0,
	-12,  -6,  -3,   0,   0,  -3,  -6, -12,		0, 0, 0, 0, 0, 0, 0, 0,
	 -9,  -3,   0,   3,   3,   0,  -3,  -9,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,   0,   3,   6,   6,   3,   0,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,   0,   3,   6,   6,   3,   0,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -9,  -3,   0,   3,   3,   0,  -3,  -9,		0, 0, 0, 0, 0, 0, 0, 0,
	-12,  -6,  -3,   0,   0,  -3,  -6, -12,		0, 0, 0, 0, 0, 0, 0, 0,
	-18, -12,  -9,  -6,  -6,  -9, -12, -18
	];

	// Huszar
	var KnightMask = [
   -135, -25, -15, -10, -10, -15, -25,-135,		0, 0, 0, 0, 0, 0, 0, 0,
	-20, -10,   0,   5,   5,   0, -10, -20,		0, 0, 0, 0, 0, 0, 0, 0,
	 -5,   5,  15,  20,  20,  15,   5,  -5,		0, 0, 0, 0, 0, 0, 0, 0,
	 -5,   5,  15,  20,  20,  15,   5,  -5,		0, 0, 0, 0, 0, 0, 0, 0,
	-10,   0,  10,  15,  15,  10,   0, -10,		0, 0, 0, 0, 0, 0, 0, 0,
	-20, -10,   0,   5,   5,   0, -10, -20,		0, 0, 0, 0, 0, 0, 0, 0,
	-35, -25, -15, -10, -10, -15, -25, -35,		0, 0, 0, 0, 0, 0, 0, 0,
	-50, -40, -30, -25, -25, -30, -40, -50
	];

	// Huszar vegjatek
	var KnightEndMask = [
	-40, -30, -20, -15, -15, -20, -30, -40,		0, 0, 0, 0, 0, 0, 0, 0,
	-30, -20, -10,  -5,  -5, -10, -20, -30,		0, 0, 0, 0, 0, 0, 0, 0,
	-20, -10,   0,   5,   5,   0, -10, -20,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   5,  10,  10,   5,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   5,  10,  10,   5,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-20, -10,   0,   5,   5,   0, -10, -20,		0, 0, 0, 0, 0, 0, 0, 0,
	-30, -20, -10,  -5,  -5, -10, -20, -30,		0, 0, 0, 0, 0, 0, 0, 0,
	-40, -30, -20, -15, -15, -20, -30, -40
	];

	// Huszar outpost "orszem"
	var KnightOutpost = [
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   4,   5,   5,   4,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   2,   5,  10,  10,   5,   2,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   2,   5,  10,  10,   5,   2,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0
	];

	// Gyalog
	var PawnMask = [
	-15,  -5,   0,   5,   5,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,   5,   5,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,   5,   5,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,  15,  15,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,  25,  25,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,  15,  15,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,   5,   5,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,   5,   5,   0,  -5, -15
	];


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	if ((typeof process) != undefined) { // Node.js

		UI_MODE = 2;
		var spec_id = '';
		var tokens = [];
		var nodefs = require('fs');
		process.stdin.setEncoding('utf8');

		process.stdin.on('end', function() {
			process.exit();
		});

		process.stdin.on('readable', function()
		{
			var command = process.stdin.read();

			if (command !== null)
			{
				var messageList = command.split('\n');

				for (var messageNum = 0; messageNum < messageList.length; messageNum++)
				{
					message = messageList[messageNum].replace(/(\r\n|\n|\r)/gm,"");
					message = message.trim();
					message = message.replace(/\s+/g,' ');
					tokens  = message.split(' ');
					command = tokens[0];

					if (!command)
					  continue;

					// ############################################################################################

					// Roviditesek ertelmezese
					if (command == 'u')
						command = 'ucinewgame';
					
					if (command == 'b')
						command = 'board';
					
					if (command == 'q')
						command = 'quit';
					
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

						case 'quit':
						
							process.exit(); // Kilepes

						break;

						// ############################################################################################

						case 'id':
					  
							spec_id = tokens[1];
					  
						break;

						// ############################################################################################

						case 'isready':
						  
							nodefs.writeSync(1, 'readyok\n');
						  
						break;

						// ############################################################################################

						case 'ping':
						  
							nodefs.writeSync(1, 'info string tomitankChess is alive\n');
						  
						break;
		  
						// ############################################################################################

						case 'board':
						  
							nodefs.writeSync(1, 'board '+boardToFEN()+'\n');
						  
						break;

						// ############################################################################################

						case 'uci':
						  
							nodefs.writeSync(1, 'id name tomitankChess v.1.4\n');
							nodefs.writeSync(1, 'id author Tamas Kuzmics\n');
							nodefs.writeSync(1, 'option\n');
							nodefs.writeSync(1, 'uciok\n');
						  
						break;

						// ############################################################################################

						case 'ucinewgame':

							hashUsed = 0; // hash nullazas
							moveCount = 0; // lepesek szama
							InitEnginSearch(); // Motor ujrainditas
							brd_fiftyMove = 0; // 50 lepes nullazas
							MOVE_HISTORY = new Array(); // elozmenyek uritese

							if (SideKeyLow == 0 && SideKeyHigh == 0) { // Hash inicializalas
								InitHashKeys();
							}

							START_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR '+(currentPlayer ? 'b' : 'w')+' KQkq - 0 0';

							CHESS_BOARD = FENToBoard(); // Tabla feltoltese

						break;

						// ############################################################################################

						case 'position':

							if (SideKeyLow == 0 && SideKeyHigh == 0) { // Meg nem inditottunk uj jatekot
								nodefs.writeSync(1, 'info string Please type "u" to New Game!\n');
								return;
							}

							moveCount = 0; // lepesek szama
							brd_fiftyMove = 0; // 50 lepes nullazas
							MOVE_HISTORY = new Array(); // Lepes elozmenyek uritese
							START_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 0';

							var arr = getArr('fen', 'moves', tokens); // FEN Parameter

							if (arr.lo > 0) {
								START_FEN = ''; // FEN torlese
								if (arr.lo <= arr.hi) START_FEN += tokens[arr.lo]; arr.lo++; // CHESS_BOARD
								if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo]; arr.lo++; // currentPlayer
								if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo]; arr.lo++; // castleRights
								if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo]; arr.lo++; // En Passant
								if (arr.lo <= arr.hi) START_FEN += ' '+parseInt(tokens[arr.lo]); arr.lo++; // "0"
								if (arr.lo <= arr.hi) START_FEN += ' '+parseInt(tokens[arr.lo]); arr.lo++; // "0"
								// nodefs.writeSync(1, 'Elozmeny FEN:'+START_FEN+'\n');
							}

							CHESS_BOARD = FENToBoard(); // Tabla feltoltese

							var arr = getArr('moves', 'fen', tokens); // Lepesek Parameter

							ClearForSearch(); // BUGFIX: Nullazas

							if (arr.lo > 0) {
								for (var index = arr.lo; index <= arr.hi; index++) { // Lepesek ervenyesitese
									// nodefs.writeSync(1, 'Elozmeny:'+tokens[index]+'\n');
									makeMove(GetMoveFromString(tokens[index]));
									boardPly = 0; // BUGFIX
								}
							}

						break;

						// ############################################################################################

						case 'go':

							if (SideKeyLow == 0 && SideKeyHigh == 0) { // Meg nem inditottunk uj jatekot
								nodefs.writeSync(1, 'info string Please type "u" to New Game!\n');
								return;
							}

						// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

							maxSearchTime	= getInt('movetime', 0, tokens); // Ido Parameter
						var maxSearchDepth	= getInt('depth', 0, tokens); // Melyseg Parameter

							if (maxSearchTime == 0)
							{
								var movesToGo = getInt('movestogo', 30, tokens); // Max lepesek

								if (currentPlayer == WHITE) {
									var Inc = getInt('winc', 0, tokens); // Ido noveles
									var Time = getInt('wtime', 0, tokens); // Feher ido
								} else {
									var Inc = getInt('binc', 0, tokens); // Ido noveles
									var Time = getInt('btime', 0, tokens); // Fekete ido
								}

								maxSearchTime = ((Time / movesToGo) + Inc - 50) | 0;
								// maxSearchTime = (Math.round(Time / movesToGo) + Inc) | 0;

								maxSearchTime = (maxSearchTime < 10) ? 10 : maxSearchTime; // Ido fixalas
							}

							if (maxSearchDepth <= 0) { // Max melyseg
								maxSearchDepth = 64;
							} else {
								maxSearchTime = 1000 * 60 * 60; // Fix melysegnel max 1 ora
							}

						// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

							ClearForSearch(); // Nullazas

							var alpha = -INFINITE;
							var beta = INFINITE;
							var countMove = 0;
							var Score = 0;

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

							startTime = Date.now(); // kezdo ido

							for (currDepth = 1; currDepth <= maxSearchDepth; currDepth++) // iterativ melyites
							{
								if (countMove == 1 && currDepth > 5 && bestMove) break; // Egy ervenyes lepes

								Score = AlphaBeta(alpha, beta, currDepth, true, UNKNOWN_CHECK); // Kereses

								if (timeStop == 1) break; // Lejart az ido

								if (Score > alpha && Score < beta) { // Ablakon belul
									alpha = Score - 50;
									beta = Score + 50;

									if (alpha < -INFINITE) alpha = -INFINITE;
									if (beta > INFINITE) beta = INFINITE;
								} else if (alpha != -INFINITE) { // Kilogunk az ablakbol
									alpha = -INFINITE;
									beta = INFINITE;
									currDepth--;
								}
							}

							nodefs.writeSync(1, 'bestmove '+FormatMove(bestMove.move)+'\n'); // Kuldes a UCI-nak
							nodefs.writeSync(1, 'info hashfull '+Math.round((1000*hashUsed) / HASHENTRIES)+'\n');

						break;

						// ############################################################################################

						default:
							nodefs.writeSync(1, command+': unknown command\n');
						break;
					}
				}
			}
		});
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


	// 32 bites random szam generalasa
		function RAND_32() {
			return (Math.floor((Math.random()*255)+1) << 23) | (Math.floor((Math.random()*255)+1) << 16)
				 | (Math.floor((Math.random()*255)+1) << 8) | Math.floor((Math.random()*255)+1);
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Babuk inicializalasa
		function InitPieceList() {

			var color = 0; // Babu szine
			var piece = 0; // Babu tipusa
			OLD_PIECE_NUM = 0; // Babuk nullazas
			brd_Material[0] = 0; // Feher nullazas
			brd_Material[8] = 0; // Fekete nullazas

			for (var index = 0; index < 16; index++) {
				brd_pieceCount[index] = 0; // Darab tipusonkent nullazas
				for (var j = 0; j < 16; j++) {
					brd_pieceList[(index << 4) | j] = 8; // Lista nullazas
					// 8-as Mezon nem lehet babu!(0-as mezot hasznaljuk)
				}
			}

			for (var index = 0; index < 120; index++)
			{
				brd_pieceIndex[index] = 0; // Babu indexeles nullazas

				if (CHESS_BOARD[index])
				{
					OLD_PIECE_NUM++; // Babuk szamolasa

					piece = CHESS_BOARD[index]; // Babu
					color = CHESS_BOARD[index] & 0x8; // Szin

					brd_Material[color] += PieceValue[CHESS_BOARD[index]]; // Anyag feltoltes
					brd_pieceList[(piece << 4) | brd_pieceCount[piece]] = index; // Lista
					brd_pieceIndex[index] = brd_pieceCount[piece]; // Index
					brd_pieceCount[piece]++; // Darab tipusonkent
				}
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Haskey inicializalasa
		function InitHashKeys() {
			var sq = 0;
			var index = 0;
			SideKeyLow = RAND_32(); // Aki kezd hashKey generalas
			SideKeyHigh = RAND_32(); // Aki kezd hashKey generalas

			for (index = 0; index < 16; index++) { // Babuk hasKey generalas
				PieceKeysLow[index] = new Array(120);
				PieceKeysHigh[index] = new Array(120);
				for (sq = 0; sq < 120; sq++) {
					PieceKeysLow[index][sq] = RAND_32();
					PieceKeysHigh[index][sq] = RAND_32();
				}
			}

			for (index = 0; index < 16; index++) { // Sancolas hashKey generalas
				CastleKeysLow[index] = RAND_32();
				CastleKeysHigh[index] = RAND_32();
			}
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Aktualis poziciobol hashKey generalas
		function GenerateHashKey() {
			brd_hashKeyLow = 0; // hashKey nullazas
			brd_hashKeyHigh = 0; // hashKey nullazas

			for (var sq = 0; sq < 120; sq++) { // Babuk hozzaadasa
				if (CHESS_BOARD[sq]) {
					brd_hashKeyLow ^= PieceKeysLow[CHESS_BOARD[sq]][sq];
					brd_hashKeyHigh ^= PieceKeysHigh[CHESS_BOARD[sq]][sq];
				}
			}

			if (currentPlayer == WHITE) { // Aki kovetkezik hozzaadasa
				brd_hashKeyLow ^= SideKeyLow;
				brd_hashKeyHigh ^= SideKeyHigh;
			}

			if (EN_PASSANT != 0) { // En Passant lepes hozzaadasa
				brd_hashKeyLow ^= PieceKeysLow[0][EN_PASSANT];
				brd_hashKeyHigh ^= PieceKeysHigh[0][EN_PASSANT];
			}

			brd_hashKeyLow ^= CastleKeysLow[castleRights]; // Sancolas hozzaadasa
			brd_hashKeyHigh ^= CastleKeysHigh[castleRights]; // Sancolas hozzaadasa
		}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Tabla elemeit FEN be mentjuk
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


	// FEN bol betoltes a tablara
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

			for (var index = 0, len = Fen[0].length; index < len; index++) {

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
