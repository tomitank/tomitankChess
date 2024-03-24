/*
 tomitankChess 1.5 Copyright (C) 2017-2018 Tamás Kuzmics - tomitank
 Mail: tanky.hu@gmail.com
 Date: 2017.12.03.

 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program. If not, see <http://www.gnu.org/licenses/>.
*/

'use strict';

// Valtozok
var VERSION         = '1.5';
var nodes           = 0; // Csomopont
var hashUsed        = 0; // Hash szam
var boardPly        = 0; // Reteg szam
var maxDepth        = 64; // Max melyseg
var timeStop        = 0; // Ido vagas be
var bestMove        = 0; // A legjobb lepes
var currDepth       = 0; // Aktualis melyseg
var moveCount       = 0; // Osszes lepesszam
var startTime       = 0; // Kereses kezdo ido
var SideKeyLow      = 0; // Oldal hashKey also
var SideKeyHigh     = 0; // Oldal hashKey felso
var castleRights    = 0; // Sancolasok 4 biten!
var maxSearchTime   = 0; // Max keresesi ido (ms)
var currentPlayer   = 0; // Aki lephet (Feher: 0)
var brd_fiftyMove   = 0; // 50 lepes szamlalo..:)
var brd_hashKeyLow  = 0; // Aktualis hashKey also bit
var brd_hashKeyHigh = 0; // Aktualis hashKey felso bit
var brd_HashTable   = null; // Atultetesi tabla uresen
var brd_Material    = new Array(9); // Anyagi ertekek
var brd_pieceCount  = new Array(16); // Babuk szama
var brd_vectorDelta = new Array(256); // Vektor tabla
var brd_pieceList   = new Array(256); // Babuk helyzete
var brd_pieceIndex  = new Array(120); // Babuk azonositoja
var brd_PvArray     = new Array(maxDepth); // Mentett lepesek
var searchKillers   = new Array(maxDepth); // Gyilkos lepesek
var brd_moveList    = new Array(maxDepth * 256); // Lepes lista
var brd_moveScores  = new Array(maxDepth * 256); // Lepes ertek
var brd_moveStart   = new Array(maxDepth + 1); // Tomb hatarolo
var CastleKeysHigh  = new Array(16); // Sancolas hashKey felso
var CastleKeysLow   = new Array(16); // Sancolas hashKey also
var PieceKeysHigh   = new Array(16); // Babuk hashKey felso
var PieceKeysLow    = new Array(16); // Babuk hashKey also
var PawnRanksBlack  = new Array(10); // Fekete Gyalog tomb
var PawnRanksWhite  = new Array(10); // Feher Gyalog tomb
var historyTable    = new Array(16); // Elozmeny tabla
var WKING_ZONE      = new Array(120); // Kiraly zona
var BKING_ZONE      = new Array(120); // Kiraly zona
var DISTANCE        = new Array(120); // SQ Kulonbseg
var MOVE_HISTORY    = new Array(); // Lepeselozmeny
brd_moveStart[0]    = 0; // Hack: Lepes lista index

// Allandok
var WHITE           = 0x0;
var BLACK           = 0x8;

var PAWN            = 0x01;
var KNIGHT          = 0x02;
var KING            = 0x03;
var BISHOP          = 0x05;
var ROOK            = 0x06;
var QUEEN           = 0x07;
var EMPTY           = 0x08;

// Feher babuk 4 bit-en
var WHITE_PAWN      = 0x01;
var WHITE_KNIGHT    = 0x02;
var WHITE_KING      = 0x03;
var WHITE_BISHOP    = 0x05;
var WHITE_ROOK      = 0x06;
var WHITE_QUEEN     = 0x07;

// Fekete babuk 4 bit-en
var BLACK_PAWN      = 0x09;
var BLACK_KNIGHT    = 0x0A;
var BLACK_KING      = 0x0B;
var BLACK_BISHOP    = 0x0D;
var BLACK_ROOK      = 0x0E;
var BLACK_QUEEN     = 0x0F;

// Allandok
var FLAG_EXACT      = 3; // Hash zaszlo 3
var FLAG_ALPHA      = 2; // Hash zaszlo 2
var FLAG_BETA       = 1; // Hash zaszlo 1
var FLAG_NONE       = 0; // Hash zaszlo 0
var NOMOVE          = 0; // Nincs lepes 0
var DEPTH_ZERO      = 0; // Nulla melyseg
var NOT_IN_CHECK    = 0; // Nincs Sakkban
var EN_PASSANT      = 0; // En passant mezo
var PawnDoubled     = -10; // Dupla Gyalog
var BishopPair      = 50; // Futo par plusz pont
var PawnBackward    = -8; // Hatrahagyott Gyalog
var PawnIsolated    = -10; // Elkulonitett Gyalog
var INFINITE        = 30000; // Infinity / Vegtelen
var CAPTURE_MASK    = 0x4000; // Leutes jelzo maszk
var DANGER_MASK     = 0xFC000; // Fontos lepes maszk
var CASTLED_MASK    = 0x80000; // Sancolas jelzo maszk
var TACTICAL_MASK   = 0x7C000; // Utes, Bevaltas maszk
var ISMATE          = INFINITE - maxDepth * 2; // Matt
var HASHENTRIES     = (96 << 20) / 48; // Hashtabla merete 96 MB / 1 Hash merete (48 byte)
var HASHMASK        = HASHENTRIES - 1; // Hashtabla maszk, csak ketto hatvanya lehet & MASK
var CASTLEBIT       = { WQ : 1, WK : 2, BQ : 4, BK : 8, W : 3, B : 12 }; // Sanc-ellenorzes
var PawnShelter     = [ 36, 35, 32, 27, 20, 11, 0 ]; // Gyalog-Kiraly Pajzs (RANK_8, RANK_2)
var AttackWeight    = [ 0, 0, 0.5, 0.75, 0.88, 0.94, 0.97, 0.99 ]; // Kiraly Tamadas Sulyozasa
var PawnPassed      = [ 0, 0, 0, 0, 0.1, 0.3, 0.6, 1, 0 ]; // Telt Gyalog elorehaladasi pontjai (RANK_0, RANK_8)
var MvvLvaScores    = [ 0, 1, 2, 6, 0, 3, 4, 5, 0, 1, 2, 6, 0, 3, 4, 5 ]; // MVV-LVA Babuk erteke (P, N, B, R, Q, K)
var SeeValue        = [ 0, 1, 3, 900, 0, 3, 5, 9, 0, 1, 3, 900, 0, 3, 5, 9 ]; // See Babuk erteke (P, N, B, R, Q, K)
var KnightMoves     = [ 14, -14, 18, -18, 31, -31, 33, -33 ]; // Huszar lepesek
var KingMoves       = [ 1, -1, 15, -15, 16, -16, 17, -17 ]; // Kiraly lepesek
var BishopMoves     = [ 15, -15, 17, -17 ]; // Futo lepesek
var RookMoves       = [ 1, -1, 16, -16 ]; // Bastya lepesek
var DirNum          = [ 0, 0, 8, 8, 0, 4, 4, 8 ]; // Lepesek szama babunkent
var Letters         = [ 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h' ]; // Betuzes
var START_FEN       = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -';
var MOB_W           = [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1 ]; // Ahova a feher lephet
var MOB_B           = [ 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0 ]; // Ahova a fekete lephet
var PieceDir        = [ 0, 0, KnightMoves, KingMoves, 0, BishopMoves, RookMoves, KingMoves ]; // Lepesek tomb
var PieceValue      = [ 0,  80, 325, 20000, 0, 325, 500, 1000, 0,  80, 325, 20000, 0, 325, 500, 1000 ]; // (P, N, K, B, R, Q)
var DeltaValue      = [ 0, 100, 325, 20000, 0, 325, 500, 1000, 0, 100, 325, 20000, 0, 325, 500, 1000 ]; // (P, N, K, B, R, Q)
var RANKS           = { RANK_1 : 1, RANK_2 : 2, RANK_3 : 3, RANK_4 : 4, RANK_5 : 5, RANK_6 : 6, RANK_7 : 7, RANK_8 : 8 }; // Sorok
var FILES           = { FILE_A : 1, FILE_B : 2, FILE_C : 3, FILE_D : 4, FILE_E : 5, FILE_F : 6, FILE_G : 7, FILE_H : 8 }; // Oszlopok

// Gyalog BitBoard
var RankBBMask      = new Array(9); // Bitboard sor maszk
var FileBBMask      = new Array(9); // Bitboard oszlop maszk
var SetMask         = new Array(120); // Bitboard Mentes maszk
var ClearMask       = new Array(120); // Bitboard Torles maszk
var HighSQMask      = new Array(120); // Bitboard HighSQ maszk
var BitFixLow       = new Array(120); // Bitboard BitFix maszk [COLOR]
var BitFixHigh      = new Array(120); // Bitboard BitFix maszk [COLOR|1]
var IsolatedMask    = new Array(120); // Bitboard Isolated maszk
var WhitePassedMask = new Array(120); // Bitboard Passed maszk Feher
var BlackPassedMask = new Array(120); // Bitboard Passed maszk Fekete
var WOpenFileMask   = new Array(120); // Bitboard OpenFile maszk Feher
var BOpenFileMask   = new Array(120); // Bitboard OpenFile maszk Fekete
var NeighbourMask   = new Array(120); // Bitboard Neighbour maszk Kozos
var WCandidateMask  = new Array(120); // Bitboard Candidate maszk Feher
var BCandidateMask  = new Array(120); // Bitboard Candidate maszk Fekete
var BlackPawnsLow   = 0x00FF0000; // 0000 0000 1111 1111 0000 0000 0000 0000 -> Fekete Gyalog  also 32 bit /A7->H7/
var BlackPawnsHigh  = 0x00000000; // 0000 0000 0000 0000 0000 0000 0000 0000 -> Fekete Gyalog felso 32 bit
var WhitePawnsLow   = 0x00000000; // 0000 0000 0000 0000 0000 0000 0000 0000 -> Feher  Gyalog  also 32 bit
var WhitePawnsHigh  = 0x0000FF00; // 0000 0000 0000 0000 1111 1111 0000 0000 -> Feher  Gyalog felso 32 bit /A2->H2/
var PawnBitBoard    = [ WhitePawnsLow, WhitePawnsHigh, 0, 0, 0, 0, 0, 0, BlackPawnsLow, BlackPawnsHigh ]; // Gyalog Bitboard Tomb

// Bit Tabla Shift ertekek
var BIT_SHIFT       = [ 31,  30,  29,  28,  27,  26,  25,  24,        0, 0, 0, 0, 0, 0, 0, 0,
                        23,  22,  21,  20,  19,  18,  17,  16,        0, 0, 0, 0, 0, 0, 0, 0,
                        15,  14,  13,  12,  11,  10,   9,   8,        0, 0, 0, 0, 0, 0, 0, 0,
                         7,   6,   5,   4,   3,   2,   1,   0,        0, 0, 0, 0, 0, 0, 0, 0,
                        31,  30,  29,  28,  27,  26,  25,  24,        0, 0, 0, 0, 0, 0, 0, 0,
                        23,  22,  21,  20,  19,  18,  17,  16,        0, 0, 0, 0, 0, 0, 0, 0,
                        15,  14,  13,  12,  11,  10,   9,   8,        0, 0, 0, 0, 0, 0, 0, 0,
                         7,   6,   5,   4,   3,   2,   1,   0 ];

// Mezok elnevezese
var SQUARES         = { A8:  0,     B8:  1,     C8:  2,     D8:  3,     E8:  4,     F8:  5,     G8:  6,     H8:  7,
                        A7: 16,     B7: 17,     C7: 18,     D7: 19,     E7: 20,     F7: 21,     G7: 22,     H7: 23,
                        A6: 32,     B6: 33,     C6: 34,     D6: 35,     E6: 36,     F6: 37,     G6: 38,     H6: 39,
                        A5: 48,     B5: 49,     C5: 50,     D5: 51,     E5: 52,     F5: 53,     G5: 54,     H5: 55,
                        A4: 64,     B4: 65,     C4: 66,     D4: 67,     E4: 68,     F4: 69,     G4: 70,     H4: 71,
                        A3: 80,     B3: 81,     C3: 82,     D3: 83,     E3: 84,     F3: 85,     G3: 86,     H3: 87,
                        A2: 96,     B2: 97,     C2: 98,     D2: 99,     E2:100,     F2:101,     G2:102,     H2:103,
                        A1:112,     B1:113,     C1:114,     D1:115,     E1:116,     F1:117,     G1:118,     H1:119 };

// Kezdeti allapot
var CHESS_BOARD     = [ BLACK_ROOK, BLACK_KNIGHT, BLACK_BISHOP, BLACK_QUEEN, BLACK_KING, BLACK_BISHOP, BLACK_KNIGHT, BLACK_ROOK, 0, 0, 0, 0, 0, 0, 0, 0,
                        BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
			NeighbourMask[sq] = 0;
			WCandidateMask[sq] = 0;
			BCandidateMask[sq] = 0;
			WhitePassedMask[sq] = 0;
			BlackPassedMask[sq] = 0;
			SetMask[sq] |= (1 << BIT_SHIFT[sq]); // SetMask feltoltese
			HighSQMask[sq] |= ((sq >> 6) & 1);   // HighMask feltoltese
			ClearMask[sq] = ~SetMask[sq];        // ClearMask feltoltese
			BitFixLow[sq] = (sq >= 64 ? 119 : 64 + sq); // Also bit fix?(119-Igen)
			BitFixHigh[sq] = (sq >= 64 ? sq - 64 : 0); // Felso bit kell?(0-Nem)
		}

		// Bitmaszkok feltoltese [0 - 120]-ig
		for (sq = 0; sq < 64; sq++) {

			var SQ_120 = SQ64_TO_120[sq]; // 64 -> 120

			tsq = sq + 8;
			while (tsq < 64) {
				BOpenFileMask[SQ_120]   |= SetMask[SQ64_TO_120[tsq]];
				BlackPassedMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
				tsq += 8;
			}

			tsq = sq - 8;
			while (tsq >= 0) {
				WOpenFileMask[SQ_120]   |= SetMask[SQ64_TO_120[tsq]];
				WhitePassedMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
				tsq -= 8;
			}

			if (TableFiles[SQ_120] > FILES.FILE_A) {
				IsolatedMask[SQ_120] |= FileBBMask[TableFiles[SQ_120] - 1];

				tsq = sq + 7;
				while (tsq < 64) {
					WCandidateMask[SQ_120]  |= SetMask[SQ64_TO_120[tsq]];
					BlackPassedMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
					tsq += 8;
				}

				tsq = sq - 9;
				while (tsq >= 0) {
					BCandidateMask[SQ_120]  |= SetMask[SQ64_TO_120[tsq]];
					WhitePassedMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
					tsq -= 8;
				}
			}

			if (TableFiles[SQ_120] < FILES.FILE_H) {
				IsolatedMask[SQ_120] |= FileBBMask[TableFiles[SQ_120] + 1];

				tsq = sq + 9;
				while (tsq < 64) {
					WCandidateMask[SQ_120]  |= SetMask[SQ64_TO_120[tsq]];
					BlackPassedMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
					tsq += 8;
				}

				tsq = sq - 7;
				while (tsq >= 0) {
					BCandidateMask[SQ_120]  |= SetMask[SQ64_TO_120[tsq]];
					WhitePassedMask[SQ_120] |= SetMask[SQ64_TO_120[tsq]];
					tsq -= 8;
				}
			}
		}

		// Kozvetlen szomszed mezok
		for (sq = 0; sq < 120; sq++) {
			var r = TableRanks[sq];
			if (r > RANKS.RANK_4) {
				NeighbourMask[sq] |= (WCandidateMask[sq] & RankBBMask[r-4]);
			} else {
				NeighbourMask[sq] |= (WCandidateMask[BitFixHigh[sq]] & RankBBMask[r]);
			}
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function BinaryString(nMask) {
		for (var nFlag = 0, nShifted = nMask, sMask = ''; nFlag < 32;
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

	function PopCount(b) { // only 32 bit
		b = b - ((b >>> 1) & 0x55555555);
		b = (b & 0x33333333) + ((b >>> 2) & 0x33333333);
		return ((b + (b >>> 4) & 0x0F0F0F0F) * 0x01010101) >>> 24;
	}

	function SetBitBoard(sq, color) {
		PawnBitBoard[color | HighSQMask[sq]] |= SetMask[sq];
	}

	function ClearBitBoard(sq, color) {
		PawnBitBoard[color | HighSQMask[sq]] &= ClearMask[sq];
	}

	function WhiteCandidatePawn(sq) {
		var Black = 0;      // [W/B]Candidate Elottunk/Mogottunk van
		var White = 0;      // NeighbourMask Mellettunk van, ezert..
		var sq_1 = sq + 16; // Kozvetlen vedo tarsakhoz LEFELE lepunk (NeighbourMask)
		var sq_2 = sq - 16; // Kozvetlen szomszed tarshoz (WCandidateMask), valamint
		                    // Kozvetlen Tamadokhoz (NeighbourMask) FELFELE lepunk
		Black += PopCount(BCandidateMask[sq] & PawnBitBoard[BLACK]);
		Black += PopCount(BCandidateMask[BitFixHigh[sq]] & PawnBitBoard[BLACK|1]);
		White += PopCount(WCandidateMask[BitFixLow[sq_2]] & PawnBitBoard[WHITE]);
		White += PopCount(WCandidateMask[sq_2] & PawnBitBoard[WHITE|1]);

		if (White >= Black) { // Tobbsegben vagyunk -> Jelenlegi tamadok/vedok szama kell
			Black = PopCount(NeighbourMask[sq_2] & PawnBitBoard[BLACK|HighSQMask[sq_2]]);
			White = PopCount(NeighbourMask[sq_1] & PawnBitBoard[WHITE|HighSQMask[sq_1]]);
			if (White >= Black) { // Gyoztunk
				return true;
			}
		}
		return false;
	}

	function BlackCandidatePawn(sq) {
		var Black = 0;      // [W/B]Candidate Elottunk/Mogottunk van
		var White = 0;      // NeighbourMask Mellettunk van, ezert..
		var sq_1 = sq - 16; // Kozvetlen vedo tarsakhoz FELFELE lepunk (NeighbourMask)
		var sq_2 = sq + 16; // Kozvetlen szomszed tarshoz (BCandidateMask), valamint
		                    // Kozvetlen Tamadokhoz (NeighbourMask) LEFELE lepunk
		Black += PopCount(BCandidateMask[sq_2] & PawnBitBoard[BLACK]);
		Black += PopCount(BCandidateMask[BitFixHigh[sq_2]] & PawnBitBoard[BLACK|1]);
		White += PopCount(WCandidateMask[BitFixLow[sq]] & PawnBitBoard[WHITE]);
		White += PopCount(WCandidateMask[sq] & PawnBitBoard[WHITE|1]);

		if (Black >= White) { // Tobbsegben vagyunk -> Jelenlegi tamadok/vedok szama kell
			Black = PopCount(NeighbourMask[sq_1] & PawnBitBoard[BLACK|HighSQMask[sq_1]]);
			White = PopCount(NeighbourMask[sq_2] & PawnBitBoard[WHITE|HighSQMask[sq_2]]);
			if (Black >= White) { // Gyoztunk
				return true;
			}
		}
		return false;
	}

	function WhiteBackwardControl(sq, rank) {
		var sq_1 = sq - 16; // 1 sorral fentebb
		var sq_2 = sq - 32; // 2 sorral fentebb
		if ((CHESS_BOARD[sq_1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
		&& ( NeighbourMask[sq_1] & PawnBitBoard[WHITE|HighSQMask[sq_1]]) != 0 // 1 sorral fentebb mellettem van Feher Gyalog
		&& ((NeighbourMask[sq_1] & PawnBitBoard[BLACK|HighSQMask[sq_1]]) // Kulon-kulon vizsgalok also es felso 32 bitet! Osszekapcsolom "|" ==>
		  | (NeighbourMask[sq_2] & PawnBitBoard[BLACK|HighSQMask[sq_2]])) == 0) { // (1 | 2) sorral fentebb atlosan 1-1 mezot nezek! Nincs Fekete Gyalog
			return false;
		} else if (rank == RANKS.RANK_2 // 2. Sorban also es felso 32 bitet meghatarozza
			   && (CHESS_BOARD[sq_1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
			   && (CHESS_BOARD[sq_2] & 0x07) !== PAWN // Elottem 2 mezovel nincs Gyalog
			   && (NeighbourMask[sq_2] & PawnBitBoard[WHITE|1]) != 0 // 2 sorral fentebb mellettem van Feher Gyalog ("FELSO BIT")
			   && ((NeighbourMask[sq_2-16] & PawnBitBoard[BLACK]) | (BCandidateMask[BitFixHigh[sq]] & PawnBitBoard[BLACK|1])) == 0) { // Nincs Fekete Gyalog
			   // ((3 sorral fentebb atlosan 1-1 mezo "ALSO BIT") | (1-2 sorral fentebb atlosan 1-1 mezo "FELSO BIT")) (rank == 2 miatt also vagy felso 32 bit)
			return false;
		}
		return true;
	}

	function BlackBackwardControl(sq, rank) {
		var sq_1 = sq + 16; // 1 sorral lentebb
		var sq_2 = sq + 32; // 2 sorral lentebb
		if ((CHESS_BOARD[sq_1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
		&& ( NeighbourMask[sq_1] & PawnBitBoard[BLACK|HighSQMask[sq_1]]) != 0 // 1 sorral lentebb mellettem van Fekete Gyalog
		&& ((NeighbourMask[sq_1] & PawnBitBoard[WHITE|HighSQMask[sq_1]]) // Kulon-kulon vizsgalok also es felso 32 bitet! Osszekapcsolom "|" ==>
		  | (NeighbourMask[sq_2] & PawnBitBoard[WHITE|HighSQMask[sq_2]])) == 0) { // (1 | 2) sorral lentebb atlosan 1-1 mezot nezek! Nincs Feher Gyalog
			return false;
		} else if (rank == RANKS.RANK_7 // 7. Sorban also es felso 32 bitet meghatarozza
			   && (CHESS_BOARD[sq_1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
			   && (CHESS_BOARD[sq_2] & 0x07) !== PAWN // Elottem 2 mezovel nincs Gyalog
			   && (NeighbourMask[sq_2] & PawnBitBoard[BLACK]) != 0 // 2 sorral lentebb mellettem van Fekete Gyalog ("ALSO BIT")
			   && ((NeighbourMask[sq_2+16] & PawnBitBoard[WHITE|1]) | (WCandidateMask[BitFixLow[sq]] & PawnBitBoard[WHITE])) == 0) { // Nincs Feher Gyalog
			   // ((3 sorral lentebb atlosan 1-1 mezo "FELSO BIT")  | (1-2 sorral lentebb atlosan 1-1 mezo "ALSO BIT")) (rank == 7 miatt also vagy felso 32 bit)
			return false;
		}
		return true;
	}

	function IsOpenFile(file, color) {
		return (FileBBMask[file] & PawnBitBoard[color]) | (FileBBMask[file] & PawnBitBoard[color|1]);
	}

	function IsolatedPawn(sq, color) {
		return (IsolatedMask[sq] & PawnBitBoard[color]) | (IsolatedMask[sq] & PawnBitBoard[color|1]);
	}

	function WhiteBackwardPawn(sq) {
		sq = sq - 16; // Melletunk levo mezoket igy latjuk
		return (WCandidateMask[BitFixLow[sq]] & PawnBitBoard[WHITE]) | (WCandidateMask[sq] & PawnBitBoard[WHITE|1]);
	}

	function BlackBackwardPawn(sq) {
		sq = sq + 16; // Melletunk levo mezoket igy latjuk
		return (BCandidateMask[sq] & PawnBitBoard[BLACK]) | (BCandidateMask[BitFixHigh[sq]] & PawnBitBoard[BLACK|1]);
	}

	function WhiteMostPawn(sq) { // Legelso Feher Gyalog
		return (WOpenFileMask[sq] & PawnBitBoard[WHITE]) | (WOpenFileMask[BitFixHigh[sq]] & PawnBitBoard[WHITE|1]);
	}

	function BlackMostPawn(sq) { // Legelso Fekete Gyalog
		return (BOpenFileMask[BitFixLow[sq]] & PawnBitBoard[BLACK]) | (BOpenFileMask[sq] & PawnBitBoard[BLACK|1]);
	}

	function WhiteOpenFile(sq) { // Fekete Dupla Gyalog: WhiteOpenFile(sq) != 0
		return (WOpenFileMask[sq] & PawnBitBoard[BLACK]) | (WOpenFileMask[BitFixHigh[sq]] & PawnBitBoard[BLACK|1]);
	}

	function BlackOpenFile(sq) { // Feher Dupla Gyalog: BlackOpenFile(sq) != 0
		return (BOpenFileMask[BitFixLow[sq]] & PawnBitBoard[WHITE]) | (BOpenFileMask[sq] & PawnBitBoard[WHITE|1]);
	}

	function WhitePassedPawn(sq) {
		return (WhitePassedMask[sq] & PawnBitBoard[BLACK]) | (WhitePassedMask[BitFixHigh[sq]] & PawnBitBoard[BLACK|1]);
	}

	function BlackPassedPawn(sq) {
		return (BlackPassedMask[BitFixLow[sq]] & PawnBitBoard[WHITE]) | (BlackPassedMask[sq] & PawnBitBoard[WHITE|1]);
	}

	function PawnPush(to_sq) { // makeMove (WHITE => BLACK)
		return (CHESS_BOARD[to_sq] & 0x07) === PAWN && (currentPlayer === WHITE ?
		         (TableRanks[to_sq] <= RANKS.RANK_3 && BlackPassedPawn(to_sq) == 0)
		        :(TableRanks[to_sq] >= RANKS.RANK_6 && WhitePassedPawn(to_sq) == 0));
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
			brd_PvArray[count++] = move;
			makeMove(move.move);
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

		brd_HashTable[brd_hashKeyLow & HASHMASK] = new HashEntry(move, score, flags, depth, brd_hashKeyLow, brd_hashKeyHigh); // 384 bit /48 byte/
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function HashEntry(move, score, flags, depth, hashLow, hashHigh) { // Hash Objektum
		this.move        = move;
		this.flags       = flags;
		this.depth       = depth;
		this.score       = score;
		this.hashKeyLow  = hashLow;
		this.hashKeyHigh = hashHigh; // A JavaScript-ben minden egesz szam 8 byte-ot foglal!
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


	function FROMSQ(m) { return (m & 0x7F); }
	function TOSQ(m) { return ((m >> 7) & 0x7F); }
	function PROMOTED(m) { return ((m >> 15) & 0xF); }
	function HASH_SIDE() {
		brd_hashKeyLow  ^= SideKeyLow;
		brd_hashKeyHigh ^= SideKeyHigh;
	}
	function HASH_PCE(pce, sq) {
		brd_hashKeyLow  ^= PieceKeysLow[pce][sq];
		brd_hashKeyHigh ^= PieceKeysHigh[pce][sq];
	}
	function HASH_CA() {
		brd_hashKeyLow  ^= CastleKeysLow[castleRights];
		brd_hashKeyHigh ^= CastleKeysHigh[castleRights];
	}
	function HASH_EP() {
		brd_hashKeyLow  ^= PieceKeysLow[0][EN_PASSANT];
		brd_hashKeyHigh ^= PieceKeysHigh[0][EN_PASSANT];
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
		brd_pieceCount[pce]++; // Darabszam novelese
		if ((pce & 0x07) === PAWN) SetBitBoard(sq, currentPlayer);
	}
	function DELETE_PCE(pce, sq, currentPlayer) {
		CHESS_BOARD[sq] = 0; // Babu torlese
		brd_pieceCount[pce]--; // Darabszam csokkentese
		var lastPceSquare = brd_pieceList[(pce << 4) | brd_pieceCount[pce]];
		brd_pieceIndex[lastPceSquare] = brd_pieceIndex[sq];
		brd_pieceList[(pce << 4) | brd_pieceIndex[lastPceSquare]] = lastPceSquare;
		brd_pieceList[(pce << 4) | brd_pieceCount[pce]] = EMPTY; // Ures
		brd_Material[currentPlayer] -= PieceValue[pce];
		if ((pce & 0x07) === PAWN) ClearBitBoard(sq, currentPlayer);
	}
	function BIT_MOVE(from, to, captured, promoted, castled) {
		return (from | (to << 7) | (captured << 14) | (promoted << 15) | (castled << 19)); // Lepes: 20 bit
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

		var to = TOSQ(move);
		var from = FROMSQ(move);
		var MOVED_PIECE = CHESS_BOARD[from];
		var PROMOTED_PIECE = PROMOTED(move);
		var CAPTURED_PIECE = CHESS_BOARD[to];

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
			HASH_PCE(CAPTURED_PIECE, to);
			DELETE_PCE(CAPTURED_PIECE, to, (currentPlayer^8));
		}
		else if (move & CAPTURE_MASK) // En Passant Lepes
		{
			if (currentPlayer) // Fekete
			{
				EN_PASSANT = to-16; // Hack: Koztes tarolo
				HASH_PCE(WHITE_PAWN, EN_PASSANT);
				DELETE_PCE(WHITE_PAWN, EN_PASSANT, WHITE);
			}
			else // Feher
			{
				EN_PASSANT = to+16; // Hack: Koztes tarolo
				HASH_PCE(BLACK_PAWN, EN_PASSANT);
				DELETE_PCE(BLACK_PAWN, EN_PASSANT, BLACK);
			}
		}
		else if (move & CASTLED_MASK) // Sancolaskor Bastya mozgatasa
		{
			switch(to) {
				case SQUARES.C1:
					HASH_PCE(WHITE_ROOK, SQUARES.A1);
					HASH_PCE(WHITE_ROOK, SQUARES.D1);
					MOVE_PCE(WHITE_ROOK, SQUARES.A1, SQUARES.D1);
				break;
				case SQUARES.C8:
					HASH_PCE(BLACK_ROOK, SQUARES.A8);
					HASH_PCE(BLACK_ROOK, SQUARES.D8);
					MOVE_PCE(BLACK_ROOK, SQUARES.A8, SQUARES.D8);
				break;
				case SQUARES.G1:
					HASH_PCE(WHITE_ROOK, SQUARES.H1);
					HASH_PCE(WHITE_ROOK, SQUARES.F1);
					MOVE_PCE(WHITE_ROOK, SQUARES.H1, SQUARES.F1);
				break;
				case SQUARES.G8:
					HASH_PCE(BLACK_ROOK, SQUARES.H8);
					HASH_PCE(BLACK_ROOK, SQUARES.F8);
					MOVE_PCE(BLACK_ROOK, SQUARES.H8, SQUARES.F8);
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

		MOVE_PCE(MOVED_PIECE, from, to); // Babu mozgatasa
		HASH_PCE(MOVED_PIECE, from);
		HASH_PCE(MOVED_PIECE, to);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (PROMOTED_PIECE != 0) // Gyalog bevaltasa
		{
			HASH_PCE(MOVED_PIECE, to);
			HASH_PCE(PROMOTED_PIECE, to);
			DELETE_PCE(MOVED_PIECE, to, currentPlayer);
			ADDING_PCE(PROMOTED_PIECE, to, currentPlayer);
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		HASH_CA(); // Sancolas hashKey

		castleRights &= CastlePerm[from] & CastlePerm[to]; // Sancolas

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

		var to = TOSQ(move);
		var from = FROMSQ(move);
		var MOVED_PCE = CHESS_BOARD[to];
		var PROMOTED_PIECE = PROMOTED(move);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		MOVE_PCE(MOVED_PCE, to, from); // Babu mozgatasa (to->from)

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (CAPTURED_PIECE) // Leutott babu visszavonasa
		{
			ADDING_PCE(CAPTURED_PIECE, to, currentPlayer);
		}
		else if (move & CAPTURE_MASK) // En Passant Lepes visszavonasa
		{
			currentPlayer ? ADDING_PCE(BLACK_PAWN, (EN_PASSANT + 16), BLACK) // Fekete
			              : ADDING_PCE(WHITE_PAWN, (EN_PASSANT - 16), WHITE); // Feher
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
			DELETE_PCE(PROMOTED_PIECE, from, currentPlayer);
			ADDING_PCE((currentPlayer | PAWN), from, currentPlayer);
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function isMate(Score) { return Score > ISMATE || Score < -ISMATE; }

	function isCheck(Side) { return isSquareUnderAttack(brd_pieceList[(Side | KING) << 4], Side); }


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function isSquareUnderAttack(square, us) {

		var next_sq = 0; // Ahol keresunk
		var enemy   = us^8; // Ellenfel
		var dir     = 0; // Lepes irany

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

		for (var i = 0; i < 120; i++) {
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
			WKING_ZONE[i] = new Array(120); // ARRAY[KingPos][NearKing]
			BKING_ZONE[i] = new Array(120); // ARRAY[KingPos][NearKing]

			for (var j = 0; j < 120; j++)
			{
				WKING_ZONE[i][j] = 0; // Nullazas
				BKING_ZONE[i][j] = 0; // Nullazas

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

		// Vektor Tabla Inicializalas
		for (var i = 0; i < 256; i++) {
			brd_vectorDelta[i] = new Object();
			brd_vectorDelta[i].pieceMask = new Array(8);
			brd_vectorDelta[i].pieceMask[WHITE] = 0;
			brd_vectorDelta[i].pieceMask[BLACK] = 0;
			brd_vectorDelta[i].delta = 0;
		}

		for (var from = 0; from < 120; from++)
		{
		// Gyalogok
			var index = from - (from - 17) + 128;
			brd_vectorDelta[index].pieceMask[WHITE] |= (1 << PAWN);
			index = from - (from - 15) + 128;
			brd_vectorDelta[index].pieceMask[WHITE] |= (1 << PAWN);

			index = from - (from + 17) + 128;
			brd_vectorDelta[index].pieceMask[BLACK] |= (1 << PAWN);
			index = from - (from + 15) + 128;
			brd_vectorDelta[index].pieceMask[BLACK] |= (1 << PAWN);

		// Tobbi babu
			for (var pce = KNIGHT; pce <= QUEEN; pce++) {

				for (var dir = 0; dir < PieceDir[pce].length; dir++)
				{
					var to = from + PieceDir[pce][dir];

					while (!(to & 0x88))
					{
						index = from - to + 128;

						brd_vectorDelta[index].pieceMask[WHITE] |= (1 << pce);
						brd_vectorDelta[index].pieceMask[BLACK] |= (1 << pce);

						var flip = -1;
						if (from < to) flip = 1;

						if (TableRanks[from] == TableRanks[to]) {
							brd_vectorDelta[index].delta = flip * 1;
						} else if (TableFiles[from] == TableFiles[to]) {
							brd_vectorDelta[index].delta = flip * 16;
						} else if ((from % 15) == (to % 15)) {
							brd_vectorDelta[index].delta = flip * 15;
						} else if ((from % 17) == (to % 17)) {
							brd_vectorDelta[index].delta = flip * 17;
						}

						if (pce == KNIGHT) {
							brd_vectorDelta[index].delta = PieceDir[pce][dir];
							break;
						}

						if (pce == KING) break;

						to += PieceDir[pce][dir];
					}
				}
			}
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function Evaluation() {

		var to           = 0; // sq
		var mob          = 0; // Mob
		var Rank         = 0; // Sor
		var PCE          = 0; // Babu
		var File         = 0; // Oszlop
		var Phase        = 24; // Fazis
		var Open         = 0; // Nyitott
		var att          = 0; // Tamadasok
		var Draw         = 1; // Dontetlen
		var pieceIdx     = 0; // Babu index
		var PassedEG     = 0; // Vegjatek Gyalog
		var PassedMG     = 0; // Kozepjatek Gyalog
		var wAttackPower = 0; // Tamadas pont Feher
		var bAttackPower = 0; // Tamadas pont Fekete
		var wAttackCount = 0; // Tamadok szama Feher
		var bAttackCount = 0; // Tamadok szama Fekete

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var wNumQueens  = brd_pieceCount[WHITE_QUEEN];
		var wNumRooks   = brd_pieceCount[WHITE_ROOK];
		var wNumBishops = brd_pieceCount[WHITE_BISHOP];
		var wNumKnights = brd_pieceCount[WHITE_KNIGHT];
		var wNumPawns   = brd_pieceCount[WHITE_PAWN];

		var bNumQueens  = brd_pieceCount[BLACK_QUEEN];
		var bNumRooks   = brd_pieceCount[BLACK_ROOK];
		var bNumBishops = brd_pieceCount[BLACK_BISHOP];
		var bNumKnights = brd_pieceCount[BLACK_KNIGHT];
		var bNumPawns   = brd_pieceCount[BLACK_PAWN];

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	//                              DONTETLEN
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

		var attS = 0; var attE = 0;
		var kingS = 0; var kingE = 0;
		var rooksS = 0; var rooksE = 0;
		var pawnsS = 0; var pawnsE = 0;
		var queensS = 0; var queensE = 0;
		var knightsS = 0; var knightsE = 0;
		var bishopsS = 0; var bishopsE = 0;
		var trappedS = 0; var trappedE = 0;
		var posScoreS = 0; var posScoreE = 0;
		var mobScoreS = 0; var mobScoreE = 0;

	// Gyalog oszlopok inicializalasa
		for (var index = 0; index < 10; index++) {
			PawnRanksWhite[index] = RANKS.RANK_8;
			PawnRanksBlack[index] = RANKS.RANK_1;
		}

	// Vezer, Tisztek ellenorzese
		var wBigPieces = (wNumKnights || wNumBishops || wNumRooks || wNumQueens);
		var bBigPieces = (bNumKnights || bNumBishops || bNumRooks || bNumQueens);

	// Gyalog ellenorzes
		var wPawnHome = PawnBitBoard[WHITE|1] & RankBBMask[RANKS.RANK_2]; // wPawn on 2th
		var bPawnHome = PawnBitBoard[BLACK]   & RankBBMask[RANKS.RANK_7]; // bPawn on 7th

	// Tamadasi erok
		var wCanAttack = wNumQueens && (wNumKnights || wNumBishops || wNumRooks || wNumQueens >= 2);
		var bCanAttack = bNumQueens && (bNumKnights || bNumBishops || bNumRooks || bNumQueens >= 2);

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	//                              BABUK ERTEKELESE
	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Kiraly
		var wKing = brd_pieceList[WHITE_KING << 4];
		var wKingRank = TableRanks[wKing]; // Kiraly sora
		var wKingFile = TableFiles[wKing]; // Kiraly oszlopa
		var WKZ = WKING_ZONE[wKing]; // Feher Kiraly zonak
		posScoreS += KingPstMg[wKing];
		posScoreE += KingPstEg[wKing];

	// Fekete Kiraly
		var bKing = brd_pieceList[BLACK_KING << 4];
		var bKingRank = TableRanks[bKing]; // Kiraly sora
		var bKingFile = TableFiles[bKing]; // Kiraly oszlopa
		var BKZ = BKING_ZONE[bKing]; // Fekete Kiraly zonak
		posScoreS -= KingPstMg[TableMirror[bKing]];
		posScoreE -= KingPstEg[TableMirror[bKing]];

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Vezer
		pieceIdx = WHITE_QUEEN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Rank = TableRanks[PCE];

			if (Rank == RANKS.RANK_7 && (bPawnHome || bKingRank == RANKS.RANK_8)) { // 7. sorban
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
				wAttackCount++;
				wAttackPower += 4;
			}

			Phase -= 4;
			mobScoreS += 1 * mob;
			mobScoreE += 2 * mob;
			posScoreS += QueenPstMg[PCE];
			posScoreE += QueenPstEg[PCE];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Vezer
		pieceIdx = BLACK_QUEEN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Rank = TableRanks[PCE];

			if (Rank == RANKS.RANK_2 && (wPawnHome || wKingRank == RANKS.RANK_1)) { // 7. sorban
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
				bAttackCount++;
				bAttackPower += 4;
			}

			Phase -= 4;
			mobScoreS -= 1 * mob;
			mobScoreE -= 2 * mob;
			posScoreS -= QueenPstMg[TableMirror[PCE]];
			posScoreE -= QueenPstEg[TableMirror[PCE]];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Bastya
		pieceIdx = WHITE_ROOK << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			rooksS -= 10; // Nyitott oszlop pont korrekcio
			rooksE -= 10; // Nyitott oszlop pont korrekcio

			if (IsOpenFile(File, WHITE) == 0) { // Felig nyitott oszlop
				if (IsOpenFile(File, BLACK) == 0) { // Teljesen nyitott
					rooksS += 20;
					rooksE += 20;
				} else {
					rooksS += 10;
					rooksE += 10;
				}

				if (wCanAttack) {
					if (File == bKingFile) { // Ellenseges Kiraly azonos oszlopban
						rooksS += 10;
					}

					if (Math.abs(File - bKingFile) <= 1) { // Max 1. oszlop elteres
						rooksS += 10;
					}
				}
			}

			if (Rank == RANKS.RANK_7 && (bPawnHome || bKingRank == RANKS.RANK_8)) { // 7. sorban
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
				wAttackCount++;
				wAttackPower += 2;
			}

			Phase -= 2;
			mobScoreS += 2 * mob;
			mobScoreE += 4 * mob;
			posScoreS += RookPstMg[PCE];
			posScoreE += RookPstEg[PCE];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Bastya
		pieceIdx = BLACK_ROOK << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			rooksS += 10; // Nyitott oszlop pont korrekcio
			rooksE += 10; // Nyitott oszlop pont korrekcio

			if (IsOpenFile(File, BLACK) == 0) { // Felig nyitott oszlop
				if (IsOpenFile(File, WHITE) == 0) { // Teljesen nyitott
					rooksS -= 20;
					rooksE -= 20;
				} else {
					rooksS -= 10;
					rooksE -= 10;
				}

				if (bCanAttack) {
					if (File == wKingFile) { // Ellenseges Kiraly azonos oszlopban
						rooksS -= 10;
					}

					if (Math.abs(File - wKingFile) <= 1) { // Max 1. oszlop elteres
						rooksS -= 10;
					}
				}
			}

			if (Rank == RANKS.RANK_2 && (wPawnHome || wKingRank == RANKS.RANK_1)) { // 7. sorban
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
				bAttackCount++;
				bAttackPower += 2;
			}

			Phase -= 2;
			mobScoreS -= 2 * mob;
			mobScoreE -= 4 * mob;
			posScoreS -= RookPstMg[TableMirror[PCE]];
			posScoreE -= RookPstEg[TableMirror[PCE]];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Futo
		pieceIdx = WHITE_BISHOP << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			att = 0;
			mob = -6;
			to = PCE + 15; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to += 15; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE - 15; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to -= 15; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE + 17; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to += 17; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }
			to = PCE - 17; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += BKZ[to]; to -= 17; } if (!(to & 0x88)) { mob += MOB_W[CHESS_BOARD[to]]; att += BKZ[to]; }

			if (att != 0) {
				wAttackCount++;
				wAttackPower += 1;
			}

			Phase -= 1;
			mobScoreS += 5 * mob;
			mobScoreE += 5 * mob;
			posScoreS += BishopPstMg[PCE];
			posScoreE += BishopPstEg[PCE];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Futo
		pieceIdx = BLACK_BISHOP << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			att = 0;
			mob = -6;
			to = PCE + 15; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to += 15; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE - 15; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to -= 15; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE + 17; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to += 17; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }
			to = PCE - 17; while (!(to & 0x88) && !CHESS_BOARD[to]) { mob++; att += WKZ[to]; to -= 17; } if (!(to & 0x88)) { mob += MOB_B[CHESS_BOARD[to]]; att += WKZ[to]; }

			if (att != 0) {
				bAttackCount++;
				bAttackPower += 1;
			}

			Phase -= 1;
			mobScoreS -= 5 * mob;
			mobScoreE -= 5 * mob;
			posScoreS -= BishopPstMg[TableMirror[PCE]];
			posScoreE -= BishopPstEg[TableMirror[PCE]];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Huszar
		pieceIdx = WHITE_KNIGHT << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
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
				wAttackCount++;
				wAttackPower += 1;
			}

			Phase -= 1;
			mobScoreS += 4 * mob;
			mobScoreE += 4 * mob;
			posScoreS += KnightPstMg[PCE];
			posScoreE += KnightPstEg[PCE];

			var outpost = KnightOutpost[PCE]; // Huszar Orszem

			if (outpost && CHESS_BOARD[PCE - 15] != BLACK_PAWN && CHESS_BOARD[PCE - 17] != BLACK_PAWN) { // Nincs fenyegetes
				if (CHESS_BOARD[PCE + 15] == WHITE_PAWN) knightsS += outpost;
				if (CHESS_BOARD[PCE + 17] == WHITE_PAWN) knightsS += outpost;
			}

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Huszar
		pieceIdx = BLACK_KNIGHT << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
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
				bAttackCount++;
				bAttackPower += 1;
			}

			Phase -= 1;
			mobScoreS -= 4 * mob;
			mobScoreE -= 4 * mob;
			posScoreS -= KnightPstMg[TableMirror[PCE]];
			posScoreE -= KnightPstEg[TableMirror[PCE]];

			var outpost = KnightOutpost[TableMirror[PCE]]; // Huszar Orszem

			if (outpost && CHESS_BOARD[PCE + 15] != WHITE_PAWN && CHESS_BOARD[PCE + 17] != WHITE_PAWN) { // Nincs fenyegetes
				if (CHESS_BOARD[PCE - 15] == BLACK_PAWN) knightsS -= outpost;
				if (CHESS_BOARD[PCE - 17] == BLACK_PAWN) knightsS -= outpost;
			}

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Gyalog
		pieceIdx = WHITE_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Open = 0; // Nyitott
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			if (BlackOpenFile(PCE) != 0) { // Dupla Gyalog
				pawnsS += PawnDoubled;
				pawnsE += PawnDoubled * 2;
			}

			if (PawnRanksWhite[File] > Rank) { // Leghatso Feher Gyalog az oszlopban
				PawnRanksWhite[File] = Rank;
			}

			if (WhiteOpenFile(PCE) == 0 && WhiteMostPawn(PCE) == 0) { // Legelso Gyalog nyitott oszlopban
				Open = 1;
			}

			if (IsolatedPawn(PCE, WHITE) == 0) { // Elkulonitett Gyalog
				pawnsS += PawnIsolated + PawnIsolated * Open;
				pawnsE += PawnIsolated * 2;
			} else if (WhiteBackwardPawn(PCE) == 0 && WhiteBackwardControl(PCE, Rank)) { // Hatrahagyott Gyalog
				pawnsS += PawnBackward + PawnBackward * Open;
				pawnsE += PawnBackward - 2;
			}

			if (Open) {
				if (WhitePassedPawn(PCE) == 0) { // Telt Gyalog
					PassedMG =  60; // Alap Pont Kozepjatek
					PassedEG = 120; // Alap Pont Vegjatek
					PassedEG -=  5 * DISTANCE[wKing][PCE-16]; // Kiraly Tavolsag Sajat
					PassedEG += 20 * DISTANCE[bKing][PCE-16]; // Kiraly Tavolsag Ellenfel

					if (!bBigPieces) {
						if (DISTANCE[wKing][PCE] <= 1 && DISTANCE[wKing][File-1] <= 1 // File-1 -> Bevaltas mezo
						&& (wKingFile != File || (File != FILES.FILE_A && File != FILES.FILE_H))) { // Kiraly Telt Gyalog
							PassedEG += 800;
						} else if (DISTANCE[PCE][File-1] < DISTANCE[bKing][File-1] + ((currentPlayer == WHITE)|0) - 1) { // Fekete Kiraly nem eri el
							for (to = PCE - 16; to >= File-1; to -= 16) { // Tiszta az utvonal?
								if (CHESS_BOARD[to] != 0) break;
								if (to == File-1) PassedEG += 800; // Megallithatatlan Gyalog
							}
						}
					}

					if (CHESS_BOARD[PCE-16] == 0 && Rank >= RANKS.RANK_4 && See(BIT_MOVE(PCE, PCE-16, 0, 0, 0))) { // Szabad Telt Gyalog
						PassedEG += 60;
					}

					pawnsS += 10 + (PassedMG * PawnPassed[Rank]) | 0;
					pawnsE += 20 + (PassedEG * PawnPassed[Rank]) | 0;

				} else if (WhiteCandidatePawn(PCE)) { // Jelolt Gyalog /Candidate/
					pawnsS +=  5 +  50 * PawnPassed[Rank];
					pawnsE += 10 + 100 * PawnPassed[Rank];
				}
			}

			posScoreS += PawnPstMg[PCE];
			posScoreE += PawnPstEg[PCE];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Gyalog
		pieceIdx = BLACK_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Open = 0; // Nyitott
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			if (WhiteOpenFile(PCE) != 0) { // Dupla Gyalog
				pawnsS -= PawnDoubled;
				pawnsE -= PawnDoubled * 2;
			}

			if (PawnRanksBlack[File] < Rank) { // Leghatso Fekete Gyalog az oszlopban
				PawnRanksBlack[File] = Rank;
			}

			if (BlackOpenFile(PCE) == 0 && BlackMostPawn(PCE) == 0) { // Legelso Gyalog nyitott oszlopban
				Open = 1;
			}

			if (IsolatedPawn(PCE, BLACK) == 0) { // Elkulonitett Gyalog
				pawnsS -= PawnIsolated + PawnIsolated * Open;
				pawnsE -= PawnIsolated * 2;
			} else if (BlackBackwardPawn(PCE) == 0 && BlackBackwardControl(PCE, Rank)) { // Hatrahagyott Gyalog
				pawnsS -= PawnBackward + PawnBackward * Open;
				pawnsE -= PawnBackward - 2;
			}

			if (Open) {
				if (BlackPassedPawn(PCE) == 0) { // Telt Gyalog
					PassedMG =  60; // Alap Pont Kozepjatek
					PassedEG = 120; // Alap Pont Vegjatek
					PassedEG -=  5 * DISTANCE[bKing][PCE+16]; // Kiraly Tavolsag Sajat
					PassedEG += 20 * DISTANCE[wKing][PCE+16]; // Kiraly Tavolsag Ellenfel

					if (!wBigPieces) {
						if (DISTANCE[bKing][PCE] <= 1 && DISTANCE[bKing][File+111] <= 1 // File+111 -> Bevaltas mezo
						&& (bKingFile != File || (File != FILES.FILE_A && File != FILES.FILE_H))) { // Kiraly Telt Gyalog
							PassedEG += 800;
						} else if (DISTANCE[PCE][File+111] < DISTANCE[wKing][File+111] + ((currentPlayer == BLACK)|0) - 1) { // Feher Kiraly nem eri el
							for (to = PCE + 16; to <= File+111; to += 16) { // Tiszta az utvonal?
								if (CHESS_BOARD[to] != 0) break;
								if (to == File+111) PassedEG += 800; // Megallithatatlan Gyalog
							}
						}
					}

					if (CHESS_BOARD[PCE+16] == 0 && Rank <= RANKS.RANK_5 && See(BIT_MOVE(PCE, PCE+16, 0, 0, 0))) { // Szabad Telt Gyalog
						PassedEG += 60;
					}

					pawnsS -= 10 + (PassedMG * PawnPassed[9-Rank]) | 0;
					pawnsE -= 20 + (PassedEG * PawnPassed[9-Rank]) | 0;

				} else if (BlackCandidatePawn(PCE)) { // Jelolt Gyalog /Candidate/
					pawnsS -=  5 +  50 * PawnPassed[9-Rank];
					pawnsE -= 10 + 100 * PawnPassed[9-Rank];
				}
			}

			posScoreS -= PawnPstMg[TableMirror[PCE]];
			posScoreE -= PawnPstEg[TableMirror[PCE]];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (wCanAttack)
		{
			if (wAttackCount > 7) wAttackCount = 7; // Max 7 tamado

			attS += (20 * wAttackPower * AttackWeight[wAttackCount]) | 0;

			var Shield = BlackKingShield(bKingFile) * 2; // Gyalog Pajzs
			var Storm  =  WhitePawnStorm(bKingFile);     // Gyalog Vihar

			if (bKingFile != FILES.FILE_A) {
				Shield += BlackKingShield(bKingFile-1);
				Storm  +=  WhitePawnStorm(bKingFile-1);
			}

			if (bKingFile != FILES.FILE_H) {
				Shield += BlackKingShield(bKingFile+1);
				Storm  +=  WhitePawnStorm(bKingFile+1);
			}

			if (Shield == 0) Shield = 11; // Kompenzalas

			Shield += Storm; // Gyalog Vihar hozzaadas

			var BestShield = Shield;

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (castleRights & CASTLEBIT.BK) { // Sancolhat Kiraly oldal
			var ShieldK  = BlackKingShield(FILES.FILE_G) * 2;
				Storm	 =  WhitePawnStorm(FILES.FILE_G);

				ShieldK += BlackKingShield(FILES.FILE_F);
				Storm   +=  WhitePawnStorm(FILES.FILE_F);

				ShieldK += BlackKingShield(FILES.FILE_H);
				Storm   +=  WhitePawnStorm(FILES.FILE_H);

				if (ShieldK == 0) ShieldK = 11; // Kompenzalas

				ShieldK += Storm; // Gyalog Vihar hozzaadas

				if (ShieldK < BestShield) BestShield = ShieldK;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (castleRights & CASTLEBIT.BQ) { // Sancolhat Vezer oldal
			var ShieldQ  = BlackKingShield(FILES.FILE_B) * 2;
				Storm	 =  WhitePawnStorm(FILES.FILE_B);

				ShieldQ += BlackKingShield(FILES.FILE_A);
				Storm   +=  WhitePawnStorm(FILES.FILE_A);

				ShieldQ += BlackKingShield(FILES.FILE_C);
				Storm   +=  WhitePawnStorm(FILES.FILE_C);

				if (ShieldQ == 0) ShieldQ = 11; // Kompenzalas

				ShieldQ += Storm; // Gyalog Vihar hozzaadas

				if (ShieldQ < BestShield) BestShield = ShieldQ;
			}

			kingS += ((Shield + BestShield) / 2) | 0;
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (bCanAttack)
		{
			if (bAttackCount > 7) bAttackCount = 7; // Max 7 tamado

			attS -= (20 * bAttackPower * AttackWeight[bAttackCount]) | 0;

			var Shield = WhiteKingShield(wKingFile) * 2; // Gyalog Pajzs
			var Storm  =  BlackPawnStorm(wKingFile);     // Gyalog Vihar

			if (wKingFile != FILES.FILE_A) {
				Shield += WhiteKingShield(wKingFile-1);
				Storm  +=  BlackPawnStorm(wKingFile-1);
			}

			if (wKingFile != FILES.FILE_H) {
				Shield += WhiteKingShield(wKingFile+1);
				Storm  +=  BlackPawnStorm(wKingFile+1);
			}

			if (Shield == 0) Shield = 11; // Kompenzalas

			Shield += Storm; // Gyalog Vihar hozzaadas

			var BestShield = Shield;

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (castleRights & CASTLEBIT.WK) { // Sancolhat Kiraly oldal
			var ShieldK  = WhiteKingShield(FILES.FILE_G) * 2;
				Storm	 =  BlackPawnStorm(FILES.FILE_G);

				ShieldK += WhiteKingShield(FILES.FILE_F);
				Storm   +=  BlackPawnStorm(FILES.FILE_F);

				ShieldK += WhiteKingShield(FILES.FILE_H);
				Storm   +=  BlackPawnStorm(FILES.FILE_H);

				if (ShieldK == 0) ShieldK = 11; // Kompenzalas

				ShieldK += Storm; // Gyalog Vihar hozzaadas

				if (ShieldK < BestShield) BestShield = ShieldK;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (castleRights & CASTLEBIT.WQ) { // Sancolhat Vezer oldal
			var ShieldQ  = WhiteKingShield(FILES.FILE_B) * 2;
				Storm	 =  BlackPawnStorm(FILES.FILE_B);

				ShieldQ += WhiteKingShield(FILES.FILE_A);
				Storm   +=  BlackPawnStorm(FILES.FILE_A);

				ShieldQ += WhiteKingShield(FILES.FILE_C);
				Storm   +=  BlackPawnStorm(FILES.FILE_C);

				if (ShieldQ == 0) ShieldQ = 11; // Kompenzalas

				ShieldQ += Storm; // Gyalog Vihar hozzaadas

				if (ShieldQ < BestShield) BestShield = ShieldQ;
			}

			kingS -= ((Shield + BestShield) / 2) | 0;
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Sarokba szorult Feher Bastya
		if ((CHESS_BOARD[SQUARES.F1] == WHITE_KING || CHESS_BOARD[SQUARES.G1] == WHITE_KING) // Kiraly oldal
		 && (CHESS_BOARD[SQUARES.H1] == WHITE_ROOK || CHESS_BOARD[SQUARES.G1] == WHITE_ROOK || CHESS_BOARD[SQUARES.H2] == WHITE_ROOK)) {
			trappedS -= 50;
		}
		if ((CHESS_BOARD[SQUARES.C1] == WHITE_KING || CHESS_BOARD[SQUARES.B1] == WHITE_KING) // Vezer oldal
		 && (CHESS_BOARD[SQUARES.A1] == WHITE_ROOK || CHESS_BOARD[SQUARES.B1] == WHITE_ROOK || CHESS_BOARD[SQUARES.A2] == WHITE_ROOK)) {
			trappedS -= 50;
		}

	// Sarokba szorult Fekete Bastya
		if ((CHESS_BOARD[SQUARES.F8] == BLACK_KING || CHESS_BOARD[SQUARES.G8] == BLACK_KING) // Kiraly oldal
		 && (CHESS_BOARD[SQUARES.H8] == BLACK_ROOK || CHESS_BOARD[SQUARES.G8] == BLACK_ROOK || CHESS_BOARD[SQUARES.H7] == BLACK_ROOK)) {
			trappedS += 50;
		}
		if ((CHESS_BOARD[SQUARES.C8] == BLACK_KING || CHESS_BOARD[SQUARES.B8] == BLACK_KING) // Vezer oldal
		 && (CHESS_BOARD[SQUARES.A8] == BLACK_ROOK || CHESS_BOARD[SQUARES.B8] == BLACK_ROOK || CHESS_BOARD[SQUARES.A7] == BLACK_ROOK)) {
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

		var materialS = (brd_Material[WHITE] - brd_Material[BLACK]); // Kozepjatek
		var materialE = (wNumPawns   *   90) - (bNumPawns   *   90)  // Vegjatek
		              + (wNumKnights *  325) - (bNumKnights *  325)
		              + (wNumBishops *  325) - (bNumBishops *  325)
		              + (wNumRooks   *  500) - (bNumRooks   *  500)
		              + (wNumQueens  * 1000) - (bNumQueens  * 1000);

		materialS += posScoreS;
		materialE += posScoreE;

		var evalS = materialS;
		var evalE = materialE;

		evalS += mobScoreS;
		evalE += mobScoreE;

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

		if (Phase < 0) { // Minden babu a fedelzeten = 0
			Phase = 0;
		}

		Phase = (Phase << 8) / 24 + 0.5 | 0; // Jatek fazis

		// Linearis interpolacio kezdo es vegjatek kozott..

		var Score = ((evalS * (256 - Phase)) + (evalE * Phase)) >> 8;

		Score = Score / Draw | 0; // Ketes dontetlennel nem 0-at adunk vissza!

		/*console.log('tempo'			+' MG '+tempoS+		' EG '+tempoE);
		console.log('home pawn'		+' W '+wPawnHome+	' B '+bPawnHome);
		console.log('pawns'			+' MG '+pawnsS+		' EG '+pawnsE);
		console.log('knights'		+' MG '+knightsS+	' EG '+knightsE);
		console.log('bishops'		+' MG '+bishopsS+	' EG '+bishopsE);
		console.log('rooks'			+' MG '+rooksS+		' EG '+rooksE);
		console.log('queens'		+' MG '+queensS+	' EG '+queensE);
		console.log('king'			+' MG '+kingS+		' EG '+kingE);
		console.log('material'		+' MG '+materialS+	' EG '+materialE);
		console.log('attacks'		+' MG '+attS+		' EG '+attE);
		console.log('mobility'		+' MG '+mobScoreS+	' EG '+mobScoreE);
		console.log('trapped'		+' MG '+trappedS+	' EG '+trappedE);
		console.log('evaluation'	+' MG '+evalS+		' EG '+evalE);
		console.log('phased eval'	+' PH '+Phase+		' VAL '+Score);*/

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		return currentPlayer === WHITE ? Score : -Score;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function WhiteKingShield(File) { return PawnShelter[8 - PawnRanksWhite[File]]; }

	function BlackKingShield(File) { return PawnShelter[PawnRanksBlack[File] - 1]; }

	function WhitePawnStorm(File) {
		if (FileBBMask[File] & PawnBitBoard[WHITE] & RankBBMask[RANKS.RANK_6]) {
			return 60;
		} else if (FileBBMask[File] & PawnBitBoard[WHITE] & RankBBMask[RANKS.RANK_5]) {
			return 30;
		} else if (FileBBMask[File] & PawnBitBoard[WHITE|1] & RankBBMask[RANKS.RANK_4]) {
			return 10;
		}
		return 0;
	}

	function BlackPawnStorm(File) {
		if (FileBBMask[File] & PawnBitBoard[BLACK|1] & RankBBMask[RANKS.RANK_3]) {
			return 60;
		} else if (FileBBMask[File] & PawnBitBoard[BLACK|1] & RankBBMask[RANKS.RANK_4]) {
			return 30;
		} else if (FileBBMask[File] & PawnBitBoard[BLACK] & RankBBMask[RANKS.RANK_5]) {
			return 10;
		}
		return 0;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function See(move) {

		var to = TOSQ(move);
		var from = FROMSQ(move);
		var fromPiece = CHESS_BOARD[from];
		var fromValue = SeeValue[fromPiece];
		var toValue = SeeValue[CHESS_BOARD[to]];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (PROMOTED(move) != 0 // Bevaltas
		|| (move & CASTLED_MASK) // Sancolas
		|| (move & CAPTURE_MASK && !toValue)) { // En passant
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

		// Ellenfel Gyalog Tamadas (letud utni!)
		if ((CHESS_BOARD[to + inc + 1] === (them | PAWN))
		 || (CHESS_BOARD[to + inc - 1] === (them | PAWN))) {
			return false;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var themAttacks = new Array(); // Ellenfel Tamadasok tomb

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Ellenfel Huszar Tamadas
		// Ha egy ellenseges Huszar letud utni es
		// a nyereseg kisebb mint a Huszar erteke!
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
				if (themAttacks[i] != EMPTY) {
					var pieceValue = SeeValue[CHESS_BOARD[themAttacks[i]]];
					if (pieceValue < capturingPieceValue) {
						capturingPieceValue = pieceValue;
						capturingPieceIndex = i;
					}
				}
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (capturingPieceIndex == -1) { // Nincs tamado! Mi nyertunk ;)
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
			themAttacks[capturingPieceIndex] = EMPTY;

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
				if (usAttacks[i] != EMPTY) {
					var pieceValue = SeeValue[CHESS_BOARD[usAttacks[i]]];
					if (pieceValue < capturingPieceValue) {
						capturingPieceValue = pieceValue;
						capturingPieceIndex = i;
					}
				}
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (capturingPieceIndex == -1) { // Nincs tamadonk! Mi vesztettunk :(
				return false;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Feltesszuk, hogy az ellenfel ujra leut minket
			// es igy is vesztes helyzetben van! Mi nyertunk ;)
			seeValue -= capturingPieceValue;
			if (seeValue >= 0) {
				return true;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			capturingPieceSquare = usAttacks[capturingPieceIndex];
			usAttacks[capturingPieceIndex] = EMPTY;

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
		if (delta == 0) return false;

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

		while (from_sq != EMPTY) {
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

		while (from_sq != EMPTY) {
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

		var pieceType = 0; // Akivel lepunk
		var pieceIdx  = 0; // Babu indexeles
		var from      = 0; // Ahonnan lepunk
		var next      = 0; // Ahova lepunk
		var Score     = 0; // Lepes pont
		var Move      = 0; // Lepes bit
		var dir       = 0; // Lepes irany

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
				if (castleRights & CASTLEBIT.WK) {
					if (CHESS_BOARD[SQUARES.F1] == 0 && CHESS_BOARD[SQUARES.G1] == 0) {
						if (!isSquareUnderAttack(SQUARES.E1, WHITE) && !isSquareUnderAttack(SQUARES.F1, WHITE)) {
							AddQuietMove(SQUARES.E1, SQUARES.G1, 0, 1);
						}
					}
				}
				// Sancolas Vezer oldal
				if (castleRights & CASTLEBIT.WQ) {
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
				if (castleRights & CASTLEBIT.BK) {
					if (CHESS_BOARD[SQUARES.F8] == 0 && CHESS_BOARD[SQUARES.G8] == 0) {
						if (!isSquareUnderAttack(SQUARES.E8, BLACK) && !isSquareUnderAttack(SQUARES.F8, BLACK)) {
							AddQuietMove(SQUARES.E8, SQUARES.G8, 0, 1);
						}
					}
				}
				// Sancolas Vezer oldal
				if (castleRights & CASTLEBIT.BQ) {
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

							if (useSee && !See(Move))
							Score =     106 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam
							else
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

								if (useSee && !See(Move))
								Score =     106 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam
								else
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
		if (currDepth > 1 && Date.now() - startTime >= maxSearchTime) { // Lejart az ido
			timeStop = 1;
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function Quiescence(alpha, beta, depth, inCheck) {

		if ((nodes & 2047) == 0) { // Ido ellenorzese
			CheckUp();
		}

		nodes++; // Csomopontok novelese

		if (IsRepetition()) { // Lepesismetles
			return 0;
		}

		if (boardPly >= maxDepth) { // Melyseg limit
			return Evaluation();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (depth == DEPTH_ZERO) { // Atultetesi tabla

			var hashMove = ProbeHashMove();

			if (hashMove != NOMOVE) {

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
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var BestScore = inCheck ? -INFINITE : Evaluation(); // Ertekeles

		if (!inCheck && BestScore >= beta) { // Vagas
			return BestScore;
		}

		if (!inCheck && BestScore > alpha) { // Update alpha
			alpha = BestScore;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var Score = -INFINITE; // Pont nullazas
		var Check = NOT_IN_CHECK; // Sakk lepes
		var capturedPCE = NOMOVE; // Leutott babu
		var currentMove = NOMOVE; // Aktualis lepes
		var DeltaMargin = BestScore + 100; // Delta Margo
		if (!inCheck) {
			GenerateAllMoves(true,  false); // Utes lepesek
		} else {
			GenerateAllMoves(false, false); // Minden lepes
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; ++index)
		{
			PickNextMove(index);

			currentMove = brd_moveList[index];
			capturedPCE = CHESS_BOARD[TOSQ(currentMove)];

			if (!inCheck && !See(currentMove)) { // Rossz utes
				continue;
			}

			if (!makeMove(currentMove)) { // Lepes ervenyesitese
				continue;
			}

			Check = isCheck(currentPlayer);

			if (!inCheck && !Check
			&& !PROMOTED(currentMove)
			&& (capturedPCE & 0x07) !== QUEEN
			&& (brd_pieceCount[currentPlayer | ROOK]
			  + brd_pieceCount[currentPlayer | QUEEN]
			  + brd_pieceCount[currentPlayer | KNIGHT]
			  + brd_pieceCount[currentPlayer | BISHOP]) > 1) // Delta metszes
			{
				var FutileValue = DeltaMargin;

				if (capturedPCE == 0) { // En Passant
					FutileValue += DeltaValue[PAWN];
				} else {
					FutileValue += DeltaValue[capturedPCE];
				}

				if (FutileValue <= alpha) {
					if (FutileValue > BestScore) {
						BestScore = FutileValue;
					}
					unMakeMove();
					continue;
				}
			}

			Score = -Quiescence(-beta, -alpha, depth-1, Check);

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


	function AlphaBeta(alpha, beta, depth, nullMove, inCheck) {

		if (depth <= DEPTH_ZERO) { // Melyseg eleresekor kiertekeles
			return Quiescence(alpha, beta, DEPTH_ZERO, inCheck);
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if ((nodes & 2047) == 0) { // Ido ellenorzese
			CheckUp();
		}

		nodes++; // Csomopontok novelese

		if (boardPly != 0 && IsRepetition()) { // Lepesismetles
			return 0;
		}

		if (boardPly >= maxDepth) { // Melyseg limit
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

		var pruneNode = false;
		var Score = -INFINITE;
		var is_pv = (beta != alpha + 1);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var hashMove = ProbeHashMove(); // Atultetesi tabla

		if (!is_pv && hashMove != NOMOVE && hashMove.depth >= depth) {

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

		if (!is_pv && !inCheck
		&& (brd_pieceCount[currentPlayer | KNIGHT] != 0
		 || brd_pieceCount[currentPlayer | BISHOP] != 0
		 || brd_pieceCount[currentPlayer | ROOK]   != 0
		 || brd_pieceCount[currentPlayer | QUEEN]  != 0)) { // Metszheto csomopont
			pruneNode = true;
			if (nullMove || depth <= 4) // Futility depth
			var staticEval = Evaluation();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (pruneNode && nullMove && !isMate(beta)) // Metszesek
		{
			if (depth <= 3) { // Statikus null lepes
				Score = staticEval - 100 * depth;
				if (Score >= beta && PawnOnSeventh() == 0) {
					return Score;
				}
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (depth >= 2 && staticEval >= beta) // Null lepes
			{
				if (EN_PASSANT != 0) HASH_EP();
				var enPassant = EN_PASSANT;
				currentPlayer ^= 8;
				EN_PASSANT = 0;
				HASH_SIDE();

				Score = depth <= 4 ? -Quiescence(-beta, -beta+1, DEPTH_ZERO, NOT_IN_CHECK)
				                   :  -AlphaBeta(-beta, -beta+1, depth-4, 0, NOT_IN_CHECK);

				HASH_SIDE();
				currentPlayer ^= 8;
				EN_PASSANT = enPassant;
				if (EN_PASSANT != 0) HASH_EP();

				if (timeStop == 1) { // Ido vagas
					return 0;
				}

				if (Score >= beta && !isMate(Score)) {
					return Score;
				}
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (depth <= 3 && hashMove == NOMOVE) { // Razoring based on Toga II 3.0
				var threshold = beta - 240 - depth * 60;
				if (staticEval < threshold && PawnOnSeventh() == 0) {
					Score = Quiescence(threshold-1, threshold, DEPTH_ZERO, NOT_IN_CHECK);
					if (Score < threshold) return Score;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (is_pv && boardPly != 0 && depth >= 4 && hashMove == NOMOVE) { // Belso iterativ melyites /IID/
			Score = AlphaBeta(alpha, beta, depth-2, 0, inCheck);
			if (Score > alpha) hashMove = ProbeHashMove();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		Score = -INFINITE; // Pont nullazas
		var E = 0; // Kiterjesztes valtozo
		var R = 0; // LMR Dinamikus valtozo
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

		var Lmr_ok = (!inCheck  && depth >= 3); // Keso lepes csokkentes /LMR/
		var Lmp_ok = (pruneNode && depth <= 2); // Keso lepes metszes /LMP/
		var Futile = (pruneNode && depth <= 4); // Hiabavalosag metszes
		var Margin = [ 0, 100, 200, 300, 400 ]; // Hiabavalosag margok
		if (Futile) var FutileValue = staticEval + Margin[depth];

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
			moveScore = brd_moveScores[index];

			if (!makeMove(currentMove)) { // Lepes ervenyesitese
				continue;
			}

			Check = isCheck(currentPlayer);

			E = 0; // "E" nullazasa
			R = 0; // "R" nullazasa

			if (moveScore < 800000
			&& !Check && LegalMove
			&& (Lmr_ok || Futile || Lmp_ok)
			&& !(currentMove & DANGER_MASK)
			&& !PawnPush(TOSQ(currentMove)))
			{
				if (Lmp_ok && !isMate(BestScore) && LegalMove > depth*5) { // Late Move Pruning
					unMakeMove();
					continue;
				}
				if (Futile && !isMate(BestScore) && FutileValue < alpha) { // Futility Pruning
					if (FutileValue > BestScore) {
						BestScore = FutileValue;
					}
					unMakeMove();
					continue;
				}
				if (Lmr_ok && LegalMove >= 3) // Late Move Reduction
				{
					R = is_pv ? 0.00 + Math.log(depth) * Math.log(Math.min(LegalMove, 63)) / 3.00 | 0
					          : 0.33 + Math.log(depth) * Math.log(Math.min(LegalMove, 63)) / 2.25 | 0;
				}
			}

			if (inCheck && (is_pv || depth < 5)) { // Sakk kiterjesztes
				E = 1;
			}

			if ((is_pv && LegalMove != 0) || R != 0) {
				Score = -AlphaBeta(-alpha-1, -alpha, depth+E-R-1, 1, Check); // PVS-LMR
				if (Score > alpha) {
					Score = -AlphaBeta(-beta, -alpha, depth+E-1, 1, Check); // Full
				}
			} else {
				Score = -AlphaBeta(-beta, -alpha, depth+E-1, 1, Check); // Full
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
					UpdatePv(currentMove, Score, depth, alpha, beta);
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

						StoreHashMove(currentMove, Score, FLAG_BETA, depth);

						return Score;
					}
					alpha = Score;
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
			StoreHashMove(BestMove, BestScore, FLAG_ALPHA, depth);
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
		hashUsed = 0; // Hash hasznalat nullazas
		InitEvalMasks(); // Bitmaszk inicializalas
		InitEvalTable(); // Ertekeles inicializalas
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
				historyTable[i][j] = 1024;
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

		var inCheck = isCheck(currentPlayer); // Sakk..?

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

		if (UI_HOST == HOST_TANKY) postMessage(['StartedTime', startTime]); // Kuldes!

		for (currDepth = 1; currDepth <= maxSearchDepth; currDepth++) { // Iterativ melyites

			if (countMove == 1 && currDepth > 5 && bestMove) break; // Egy ervenyes lepes

			Score = AlphaBeta(alpha, beta, currDepth, 1, inCheck); // Kereses

			if (timeStop == 1) break; // Lejart az ido

			if (Score > alpha && Score < beta) { // Ablakon belul

				alpha = Score - 50; if (alpha < -INFINITE) alpha = -INFINITE;
				beta  = Score + 50; if (beta  >  INFINITE) beta  =  INFINITE;

			} else if (alpha != -INFINITE) { // Ablakon kivul!
				alpha = -INFINITE;
				beta  =  INFINITE;
				currDepth--;
			}
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

			/*var time = (Date.now() - startTime); // Keresesi ido

			var pvLine = ''; // Pv
			for (var index = 0; index < pvNum; index++) {
				pvLine += ' '+FormatMove(brd_PvArray[index].move);
			}

			if (flags ==  FLAG_BETA) depth += '+';
			if (flags == FLAG_ALPHA) depth += '-';

			console.log('Depth: '+depth+ ' Score: '+Score+' Nodes: '+nodes+' Time: '+time+' Pv:'+pvLine);*/
		}
		else // WebWorker, Node.js, JSUCI
		{
			var time = (Date.now() - startTime); // Keresesi ido

			var pvLine = ''; // Pv
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

			sendMessage('info depth '+depth+' score '+Score+' nodes '+nodes+' time '+time+' pv'+pvLine);
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


	var HOST_WEB    = 0;
	var HOST_TANKY  = 1;
	var HOST_JSUCI  = 2;
	var HOST_NODEJS = 3;
	var HOST_WORKER = 4;
	var UI_HOST = HOST_WEB;

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


	var onmessage; // Hack: 'use strict'

	onmessage = function (command) {

		var tokens  = [];
		var spec_id = '';
		var message = '';

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

			var messageList = command.data.toString().split('\n');

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
						START_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -';

						var arr = getArr('fen', 'moves', tokens); // FEN Parameterek

						if (arr.lo > 0) {
							if (arr.lo <= arr.hi) START_FEN  =     tokens[arr.lo]; arr.lo++; // CHESS_BOARD
							if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo]; arr.lo++; // currentPlayer
							if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo]; arr.lo++; // castleRights
							if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo]; arr.lo++; // En Passant
							if (arr.lo <= arr.hi) START_FEN += ' '+parseInt(tokens[arr.lo]); arr.lo++; // 0
							if (arr.lo <= arr.hi) START_FEN += ' '+parseInt(tokens[arr.lo]); arr.lo++; // 0
						}

						CHESS_BOARD = FENToBoard(); // Tabla betoltese

						var arr = getArr('moves', 'fen', tokens); // Lepesek

						if (arr.lo > 0 && tokens[arr.lo] != undefined) {

							ClearForSearch(); // Hack: Kereses Nullazasa

							for (var index = arr.lo; index <= arr.hi; index++) {
								makeMove(GetMoveFromString(tokens[index]));
								boardPly = 0; // Hack!
							}
						}

					break;

				// ############################################################################################

					case 'go':

					    maxSearchTime  = getInt('movetime', 0, tokens); // Time
					var maxSearchDepth = getInt('depth'   , 0, tokens); // Depth

						if (maxSearchTime == 0)
						{
							var movesToGo = getInt('movestogo', 30, tokens); // Time / Move

							if (currentPlayer == WHITE) {
								var Inc  = getInt('winc' , 0, tokens);
								var Time = getInt('wtime', 0, tokens);
							} else {
								var Inc  = getInt('binc' , 0, tokens);
								var Time = getInt('btime', 0, tokens);
							}

							Time = Time - Math.min(1000, Time / 10);

							var total = Time + Inc * (movesToGo - 1);

							maxSearchTime = Math.min(total / movesToGo, Time) | 0;
						}

						if (maxSearchDepth > 0) { // Fix melysegnel max 1 ora!
							maxSearchTime = 1000 * 3600;
						}

						if (maxSearchDepth > 64 || maxSearchDepth <= 0) { // Limit
							maxSearchDepth = 64;
						}

						SearchPosition(maxSearchDepth); // Kereses..

					break;

				// ############################################################################################

					case 'uci':

						sendMessage('id name tomitankChess '+VERSION);
						sendMessage('id author Tamas Kuzmics');
						sendMessage('option');
						sendMessage('uciok');

					break;

				// ############################################################################################

					case 'ping':

						sendMessage('info string tomitankChess '+VERSION+' is alive');

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

		GenerateAllMoves(false, false);

		for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; ++index) {
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

		return { lo : lo, hi : hi };
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// 32 bites random szam
	function RAND_32() {
		return (Math.floor((Math.random()*255)+1) << 23) | (Math.floor((Math.random()*255)+1) << 16)
		     | (Math.floor((Math.random()*255)+1) <<  8) |  Math.floor((Math.random()*255)+1);
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Haskey inicializalasa
	function InitHashKeys() {

		SideKeyLow  = RAND_32(); // Aki kezd hashKey
		SideKeyHigh = RAND_32(); // Aki kezd hashKey

		for (var pce = 0; pce < 16; pce++) { // Babuk hasKey (En Passant: 0)
			PieceKeysLow[pce]  = new Array(120);
			PieceKeysHigh[pce] = new Array(120);
			for (var sq = 0; sq < 120; sq++) {
				PieceKeysLow[pce][sq]  = RAND_32();
				PieceKeysHigh[pce][sq] = RAND_32();
			}
		}

		for (var index = 0; index < 16; index++) { // Sancolas hashKey
			CastleKeysLow[index]  = RAND_32();
			CastleKeysHigh[index] = RAND_32();
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Babuk inicializalasa
	function InitPieceList() {

		brd_Material[0] = 0; // Feher anyag
		brd_Material[8] = 0; // Fekete anyag

		for (var pce = 0; pce < 16; pce++) { // BLACK_QUEEN: 15

			brd_pieceCount[pce] = 0; // Darabszam nullazasa

			for (var num = 0; num < 16; num++) { // Max 15 db azonos lehet (9 Vezer)
				brd_pieceList[(pce << 4) | num] = EMPTY; // Mezo nullazas  (8. mezo)
			}
		}

		PawnBitBoard = [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]; // BitBoard nullazasa

		for (var sq = 0; sq < 120; sq++)
		{
			brd_pieceIndex[sq] = 0; // Mezo index nullazasa

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

		brd_hashKeyLow  = 0; // hashKey Low
		brd_hashKeyHigh = 0; // hashKey High

		for (var sq = 0; sq < 120; sq++) { // Babuk
			if (CHESS_BOARD[sq] != 0) {
				brd_hashKeyLow  ^= PieceKeysLow[CHESS_BOARD[sq]][sq];
				brd_hashKeyHigh ^= PieceKeysHigh[CHESS_BOARD[sq]][sq];
			}
		}

		if (currentPlayer == WHITE) { // Aki lephet
			brd_hashKeyLow  ^= SideKeyLow;
			brd_hashKeyHigh ^= SideKeyHigh;
		}

		if (EN_PASSANT != 0) { // En Passant
			brd_hashKeyLow  ^= PieceKeysLow[0][EN_PASSANT];
			brd_hashKeyHigh ^= PieceKeysHigh[0][EN_PASSANT];
		}

		brd_hashKeyLow  ^= CastleKeysLow[castleRights]; // Sancolas
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
		FEN  = FEN.substr(0, FEN.length - 1) + ' ';
		FEN += currentPlayer === WHITE ? 'w' : 'b';

		if (castleRights == 0) { // Nincs sancolas
			FEN += ' -';
		} else {
			FEN += ' '; // Szokoz hozzadasa
			if (castleRights & CASTLEBIT.WK) FEN += 'K'; // White King side
			if (castleRights & CASTLEBIT.WQ) FEN += 'Q'; // White Queen side
			if (castleRights & CASTLEBIT.BK) FEN += 'k'; // Black King side
			if (castleRights & CASTLEBIT.BQ) FEN += 'q'; // Black Queen side
		}

		if (EN_PASSANT == 0) { // Nincs En Passant
			FEN += ' -';
		} else {
			FEN += ' '+(Letters[TableFiles[EN_PASSANT]-1]+''+TableRanks[EN_PASSANT]);
		}

		FEN += ' 0'; // 50 Lepes szamlalo
		FEN += ' 0'; // Osszes lepes

	//	FEN += ' KQkq - 0 0'; // alap

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

		for (var index = 0; index < Fen[0].length; index++) {

			var value = Fen[0][index];
			if (value === '/') {
				for (var j = 0; j < 8; j++) { // Koztes mezo
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

		currentPlayer = Fen[1] === 'w' ? WHITE : BLACK; // Kezdo!

		castleRights = 0; // Sancolas nullazas!

		for (index = 0; index < Fen[2].length; index++) { // Sancolasok
			switch(Fen[2][index]) {
				case 'K': castleRights |= CASTLEBIT.WK; break; // White King side
				case 'Q': castleRights |= CASTLEBIT.WQ; break; // White Queen side
				case 'k': castleRights |= CASTLEBIT.BK; break; // Black King side
				case 'q': castleRights |= CASTLEBIT.BQ; break; // Black Queen side
				default: break;
			}
		}

		if (Fen[3] == '-') { // Nincs En Passant
			EN_PASSANT = 0;
		} else {
			EN_PASSANT = parseInt(SQUARES[Fen[3].toUpperCase()]); // En Passant
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

	// Kiraly
	var KingPstMg = [
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
	var KingPstEg = [
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
	var QueenPstMg = [
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
	var QueenPstEg = [
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
	var RookPstMg = [
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,		0, 0, 0, 0, 0, 0, 0, 0,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6
	];

	// Bastya vegjatek
	var RookPstEg = [
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0
	];

	// Futo
	var BishopPstMg = [
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
	var BishopPstEg = [
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
	var KnightPstMg = [
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
	var KnightPstEg = [
	-40, -30, -20, -15, -15, -20, -30, -40,		0, 0, 0, 0, 0, 0, 0, 0,
	-30, -20, -10,  -5,  -5, -10, -20, -30,		0, 0, 0, 0, 0, 0, 0, 0,
	-20, -10,   0,   5,   5,   0, -10, -20,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   5,  10,  10,   5,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   5,  10,  10,   5,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-20, -10,   0,   5,   5,   0, -10, -20,		0, 0, 0, 0, 0, 0, 0, 0,
	-30, -20, -10,  -5,  -5, -10, -20, -30,		0, 0, 0, 0, 0, 0, 0, 0,
	-40, -30, -20, -15, -15, -20, -30, -40
	];

	// Gyalog
	var PawnPstMg = [
	-15,  -5,   0,   5,   5,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,   5,   5,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,   5,   5,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,  15,  15,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,  25,  25,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,  15,  15,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,   5,   5,   0,  -5, -15,		0, 0, 0, 0, 0, 0, 0, 0,
	-15,  -5,   0,   5,   5,   0,  -5, -15
	];

	// Gyalog vegjatek
	var PawnPstEg = [
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0,		0, 0, 0, 0, 0, 0, 0, 0,
	  0,   0,   0,   0,   0,   0,   0,   0
	];
