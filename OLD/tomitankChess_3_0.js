/*
 tomitankChess 3.0 Copyright (C) 2017-2019 Tamás Kuzmics - tomitank
 Mail: tanky.hu@gmail.com
 Date: 2019.01.14.

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
var VERSION         = '3.0';
var nodes           = 0; // Csomopont
var hashUsed        = 0; // Hash szam
var boardPly        = 0; // Reteg szam
var maxDepth        = 64; // Max melyseg
var timeStop        = 0; // Ido vagas be
var hashDate        = 0; // Hash ido tag
var bestMove        = 0; // A legjobb lepes
var currDepth       = 0; // Aktualis melyseg
var moveCount       = 0; // Osszes lepesszam
var startTime       = 0; // Kereses kezdo ido
var ScoreDrop       = 0; // Csokkeno pontszam
var SideKeyLow      = 0; // Oldal hashKey also
var SideKeyHigh     = 0; // Oldal hashKey felso
var castleRights    = 0; // Sancolasok 4 biten!
var minSearchTime   = 0; // Min keresesi ido (ms)
var maxSearchTime   = 0; // Max keresesi ido (ms)
var currentPlayer   = 0; // Aki lephet (Feher: 0)
var brd_fiftyMove   = 0; // 50 lepes szamlalo..:)
var brd_hashKeyLow  = 0; // Aktualis hashKey also bit
var brd_pawnKeyLow  = 0; // Aktualis pawnKey also bit
var brd_hashKeyHigh = 0; // Aktualis hashKey felso bit
var brd_pawnKeyHigh = 0; // Aktualis pawnKey felso bit
var brd_PawnTable   = null; // Atultetesi tabla uresen
var ShowEvalForUI   = false; // Ertelekes megjelenites
var brd_Material    = new Array(9); // Anyagi ertekek
var brd_pieceCount  = new Array(15); // Babuk szama
var brd_pieceList   = new Array(240); // Babuk helyzete
var brd_pieceIndex  = new Array(64); // Babuk azonositoja
var searchKillers   = new Array(maxDepth); // Gyilkos lepesek
var brd_moveList    = new Array(maxDepth * 256); // Lepes lista
var brd_moveScores  = new Array(maxDepth * 256); // Lepes ertek
var brd_moveStart   = new Array(maxDepth + 1); // Tomb hatarolo
var PieceKeysHigh   = new Array(16 * 64); // Babu hashKey felso
var PieceKeysLow    = new Array(16 * 64); // Babu hashKey also
var CastleKeysHigh  = new Array(16); // Sancolas hashKey felso
var CastleKeysLow   = new Array(16); // Sancolas hashKey also
var historyTable    = new Array(15); // Elozmeny tabla
var DISTANCE        = new Array(64); // SQ Kulonbseg
var MOVE_HISTORY    = new Array(); // Lepeselozmeny
brd_moveStart[0]    = 0; // Hack: Lepes lista index

// Allandok
var WHITE           = 0x0;
var BLACK           = 0x8;

var PAWN            = 0x01;
var KNIGHT          = 0x02;
var BISHOP          = 0x03;
var ROOK            = 0x04;
var QUEEN           = 0x05;
var KING            = 0x06;
var EMPTY           = 0x40;

// Feher babuk 4 bit-en
var WHITE_PAWN      = 0x01;
var WHITE_KNIGHT    = 0x02;
var WHITE_BISHOP    = 0x03;
var WHITE_ROOK      = 0x04;
var WHITE_QUEEN     = 0x05;
var WHITE_KING      = 0x06;

// Fekete babuk 4 bit-en
var BLACK_PAWN      = 0x09;
var BLACK_KNIGHT    = 0x0A;
var BLACK_BISHOP    = 0x0B;
var BLACK_ROOK      = 0x0C;
var BLACK_QUEEN     = 0x0D;
var BLACK_KING      = 0x0E;

// Allandok
var FLAG_EXACT      = 3; // Hash zaszlo 3
var FLAG_ALPHA      = 2; // Hash zaszlo 2
var FLAG_BETA       = 1; // Hash zaszlo 1
var FLAG_NONE       = 0; // Hash zaszlo 0
var NOMOVE          = 0; // Nincs lepes 0
var DEPTH_ZERO      = 0; // Nulla melyseg
var NOT_IN_CHECK    = 0; // Nincs Sakkban
var EN_PASSANT      = 0; // En passant mezo
var INFINITE        = 30000; // Infinity / Vegtelen
var CAPTURE_MASK    = 0x1000; // Leutes jelzo maszk
var DANGER_MASK     = 0x3F000; // Fontos lepes maszk
var CASTLED_MASK    = 0x20000; // Sancolas jelzo maszk
var TACTICAL_MASK   = 0x1F000; // Utes, Bevaltas maszk
var ISMATE          = INFINITE - maxDepth * 2; // Matt
var PAWNENTRIES     = (1  << 12) /  1; // Gyalog hash max ~1 MB
var PAWNMASK        = PAWNENTRIES - 1; // Gyalog hash maszk, csak ketto hatvanya lehet
var HASHENTRIES     = (32 << 20) / 16; // Hashtabla merete 32 MB / 1 Hash merete (16 byte)
var HASHMASK        = HASHENTRIES - 4; // Hashtabla maszk, csak ketto hatvanya lehet & MASK
var CASTLEBIT       = { WQ : 1, WK : 2, BQ : 4, BK : 8, W : 3, B : 12 }; // Sanc-ellenorzes
var MvvLvaScores    = [ 0, 1, 2, 3, 4, 5, 6, 0, 0, 1, 2, 3, 4, 5, 6 ]; // Mvv-Lva Babuk erteke
var SeeValue        = [ 0, 1, 3, 3, 5, 9, 900, 0, 0, 1, 3, 3, 5, 9, 900 ]; // See Babuk erteke
var KnightMoves     = [ 14, -14, 18, -18, 31, -31, 33, -33 ]; // Huszar lepesek
var KingMoves       = [ 1, -1, 15, -15, 16, -16, 17, -17 ]; // Kiraly lepesek
var BishopMoves     = [ 15, -15, 17, -17 ]; // Futo lepesek
var RookMoves       = [ 1, -1, 16, -16 ]; // Bastya lepesek
var Letters         = [ 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h' ]; // Betuzes
var START_FEN       = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -';
var nonSlider       = [ 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1 ]; // nonSlider (P, N, K)
var PieceDir        = [ 0, 0, KnightMoves, BishopMoves, RookMoves, KingMoves, KingMoves ]; // Lepesek tomb
var RANKS           = { RANK_1 : 1, RANK_2 : 2, RANK_3 : 3, RANK_4 : 4, RANK_5 : 5, RANK_6 : 6, RANK_7 : 7, RANK_8 : 8 }; // Sorok
var FILES           = { FILE_A : 1, FILE_B : 2, FILE_C : 3, FILE_D : 4, FILE_E : 5, FILE_F : 6, FILE_G : 7, FILE_H : 8 }; // Oszlopok

// Typed Arrays for better memory usage. (16 byte)
var hash_move       = new Uint32Array(HASHENTRIES);
var hash_date       = new Uint16Array(HASHENTRIES);
var hash_eval       = new Int16Array (HASHENTRIES);
var hash_lock       = new Int32Array (HASHENTRIES);
var hash_score      = new Int16Array (HASHENTRIES);
var hash_flags      = new Uint8Array (HASHENTRIES);
var hash_depth      = new Uint8Array (HASHENTRIES);

// BitBoard
var LOW             = 0; // Also 32 bit tomb index
var HIGH            = 1; // Felso 32 bit tomb index
var RankBBMask      = new Array(9); // Bitboard sor maszk
var FileBBMask      = new Array(9); // Bitboard oszlop maszk
var SetMask         = new Array(64); // Bitboard Mentes maszk
var ClearMask       = new Array(64); // Bitboard Torles maszk
var HighSQMask      = new Array(64); // Bitboard HighSQ maszk
var BitFixLow       = new Array(64); // Bitboard BitFix maszk [LOW]
var BitFixHigh      = new Array(64); // Bitboard BitFix maszk [HIGH]
var IsolatedMask    = new Array(64); // Bitboard Isolated maszk
var WhitePassedMask = new Array(64); // Bitboard Passed maszk Feher
var BlackPassedMask = new Array(64); // Bitboard Passed maszk Fekete
var WOpenFileMask   = new Array(64); // Bitboard OpenFile maszk Feher
var BOpenFileMask   = new Array(64); // Bitboard OpenFile maszk Fekete
var NeighbourMask   = new Array(64); // Bitboard Neighbour maszk Kozos
var WCandidateMask  = new Array(64); // Bitboard Candidate maszk Feher
var BCandidateMask  = new Array(64); // Bitboard Candidate maszk Fekete
var BlockerBBMask   = new Array(64 *  8 * 2); // Szelek kizaras maszk
var AttackBBMask    = new Array(64 *  8 * 2); // Tamadas tombok maszk
var BehindBBMask    = new Array(64 * 64 * 2); // A mezo mogotti maszk
var BetweenBBMask   = new Array(64 * 64 * 2); // Ket mezo kozti maszk
var BitBoard        = new Array(30); // Index: color/pce << 1 | Low/High

var WhiteLow        = WHITE << 1 | LOW;
var WhiteHigh       = WHITE << 1 | HIGH;
var wPawnLow        = WHITE_PAWN   << 1 | LOW;
var wKnightLow      = WHITE_KNIGHT << 1 | LOW;
var wBishopLow      = WHITE_BISHOP << 1 | LOW;
var wRookLow        = WHITE_ROOK   << 1 | LOW;
var wQueenLow       = WHITE_QUEEN  << 1 | LOW;
var wKingLow        = WHITE_KING   << 1 | LOW;
var wPawnHigh       = WHITE_PAWN   << 1 | HIGH;
var wKnightHigh     = WHITE_KNIGHT << 1 | HIGH;
var wBishopHigh     = WHITE_BISHOP << 1 | HIGH;
var wRookHigh       = WHITE_ROOK   << 1 | HIGH;
var wQueenHigh      = WHITE_QUEEN  << 1 | HIGH;
var wKingHigh       = WHITE_KING   << 1 | HIGH;

var BlackLow        = BLACK << 1 | LOW;
var BlackHigh       = BLACK << 1 | HIGH;
var bPawnLow        = BLACK_PAWN   << 1 | LOW;
var bKnightLow      = BLACK_KNIGHT << 1 | LOW;
var bBishopLow      = BLACK_BISHOP << 1 | LOW;
var bRookLow        = BLACK_ROOK   << 1 | LOW;
var bQueenLow       = BLACK_QUEEN  << 1 | LOW;
var bKingLow        = BLACK_KING   << 1 | LOW;
var bPawnHigh       = BLACK_PAWN   << 1 | HIGH;
var bKnightHigh     = BLACK_KNIGHT << 1 | HIGH;
var bBishopHigh     = BLACK_BISHOP << 1 | HIGH;
var bRookHigh       = BLACK_ROOK   << 1 | HIGH;
var bQueenHigh      = BLACK_QUEEN  << 1 | HIGH;
var bKingHigh       = BLACK_KING   << 1 | HIGH;

// Mezok elnevezese
var SQUARES         = { A8:  0,     B8:  1,     C8:  2,     D8:  3,     E8:  4,     F8:  5,     G8:  6,     H8:  7,
                        A7:  8,     B7:  9,     C7: 10,     D7: 11,     E7: 12,     F7: 13,     G7: 14,     H7: 15,
                        A6: 16,     B6: 17,     C6: 18,     D6: 19,     E6: 20,     F6: 21,     G6: 22,     H6: 23,
                        A5: 24,     B5: 25,     C5: 26,     D5: 27,     E5: 28,     F5: 29,     G5: 30,     H5: 31,
                        A4: 32,     B4: 33,     C4: 34,     D4: 35,     E4: 36,     F4: 37,     G4: 38,     H4: 39,
                        A3: 40,     B3: 41,     C3: 42,     D3: 43,     E3: 44,     F3: 45,     G3: 46,     H3: 47,
                        A2: 48,     B2: 49,     C2: 50,     D2: 51,     E2: 52,     F2: 53,     G2: 54,     H2: 55,
                        A1: 56,     B1: 57,     C1: 58,     D1: 59,     E1: 60,     F1: 61,     G1: 62,     H1: 63 };

// Kezdeti allapot
var CHESS_BOARD     = [ BLACK_ROOK, BLACK_KNIGHT, BLACK_BISHOP, BLACK_QUEEN, BLACK_KING, BLACK_BISHOP, BLACK_KNIGHT, BLACK_ROOK,
                        BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN,
                        0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0,
                        WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN,
                        WHITE_ROOK, WHITE_KNIGHT, WHITE_BISHOP, WHITE_QUEEN, WHITE_KING, WHITE_BISHOP, WHITE_KNIGHT, WHITE_ROOK ];


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function InitEvalMasks() {

		if (SetMask[1] != undefined) { // Mar inicializaltunk!
			return false;
		}

		var sq, sq2, pce, from;

		// Sor + Oszlop nullazas
		for (sq = 0; sq < 8; sq++) {
			FileBBMask[sq] = 0;
			RankBBMask[sq] = 0;
		}

		// Sor + Oszlop feltoltes
		for (var r = RANKS.RANK_8; r >= RANKS.RANK_1; r--)
		for (var f = FILES.FILE_H; f >= FILES.FILE_A; f--) {
			sq = (r - 1) * 8 + (8 - f);
			FileBBMask[f] |= (1 << sq);
			RankBBMask[r] |= (1 << sq);
		}

		// Bitmaszkok nullazasa
		for (sq = 0; sq < 64; sq++)
		{
			IsolatedMask   [sq] = 0;
			WOpenFileMask  [sq] = 0;
			BOpenFileMask  [sq] = 0;
			NeighbourMask  [sq] = 0;
			WCandidateMask [sq] = 0;
			BCandidateMask [sq] = 0;
			WhitePassedMask[sq] = 0;
			BlackPassedMask[sq] = 0;

			// Tamadasok + Kizarasok
			for (pce = KNIGHT; pce <= KING; pce++) {
				AttackBBMask [AttackBBidx(pce, sq,  LOW)] = 0;
				AttackBBMask [AttackBBidx(pce, sq, HIGH)] = 0;
				BlockerBBMask[AttackBBidx(pce, sq,  LOW)] = 0;
				BlockerBBMask[AttackBBidx(pce, sq, HIGH)] = 0;
			}

			// Mogotte + Koztes
			for (sq2 = 0; sq2 < 64; sq2++) {
				BehindBBMask [BetweenBBidx(sq, sq2,  LOW)] = 0;
				BehindBBMask [BetweenBBidx(sq, sq2, HIGH)] = 0;
				BetweenBBMask[BetweenBBidx(sq, sq2,  LOW)] = 0;
				BetweenBBMask[BetweenBBidx(sq, sq2, HIGH)] = 0;
			}

			// Maszkok feltoltese
			SetMask   [sq] = (1 << (sq > 31 ? 63-sq : 31-sq)); // SetMask
			ClearMask [sq] = ~SetMask[sq];                     // ClearMask
			HighSQMask[sq] = (sq > 31 ? HIGH : LOW);           // HighSQMask
			BitFixLow [sq] = (sq > 31 ? 63 : 32 + sq); // Also bit fix?(63-Igen)
			BitFixHigh[sq] = (sq > 31 ? sq - 32 :  0); // Felso bit kell?(0-Nem)

			// Mezo tavolsag
			DISTANCE[sq] = new Array(64);
			var rank1 = TableRanks[sq];
			var file1 = TableFiles[sq];
			for (sq2 = 0; sq2 < 64; sq2++) {
				var rank2 = TableRanks[sq2];
				var file2 = TableFiles[sq2];
				DISTANCE[sq][sq2] = Math.max(Math.abs(rank1-rank2), Math.abs(file1-file2));
			}
		}

		// Bitmaszkok feltoltese
		for (from = 0; from < 64; from++)
		{
			for (sq = from + 8; sq < 64; sq += 8) {
				BOpenFileMask  [from] |= SetMask[sq];
				BlackPassedMask[from] |= SetMask[sq];
			}

			for (sq = from - 8; sq >= 0; sq -= 8) {
				WOpenFileMask  [from] |= SetMask[sq];
				WhitePassedMask[from] |= SetMask[sq];
			}

			if (TableFiles[from] != FILES.FILE_A) {

				IsolatedMask[from] |= FileBBMask[TableFiles[from] - 1];

				for (sq = from + 7; sq < 64; sq += 8) {
					WCandidateMask [from] |= SetMask[sq];
					BlackPassedMask[from] |= SetMask[sq];
				}

				for (sq = from - 9; sq >= 0; sq -= 8) {
					BCandidateMask [from] |= SetMask[sq];
					WhitePassedMask[from] |= SetMask[sq];
				}
			}

			if (TableFiles[from] != FILES.FILE_H) {

				IsolatedMask[from] |= FileBBMask[TableFiles[from] + 1];

				for (sq = from + 9; sq < 64; sq += 8) {
					WCandidateMask [from] |= SetMask[sq];
					BlackPassedMask[from] |= SetMask[sq];
				}

				for (sq = from - 7; sq >= 0; sq -= 8) {
					BCandidateMask [from] |= SetMask[sq];
					WhitePassedMask[from] |= SetMask[sq];
				}
			}

			// Ket szomszedos mezo
			var r = TableRanks[from];
			if (r > RANKS.RANK_4) {
				NeighbourMask[from] |= (WCandidateMask[from] & RankBBMask[r-4]);
			} else {
				NeighbourMask[from] |= (WCandidateMask[BitFixHigh[from]] & RankBBMask[r]);
			}

			// Mobilitas: Gyalog tamadasokat a NeighbourMask adja!
			var from88 = to_88(from); // 64 -> 120
			for (pce = KNIGHT; pce <= KING; pce++)
			{
				for (var dir = 0; dir < PieceDir[pce].length; dir++)
				{
					var delta = PieceDir[pce][dir];

					for (var next88 = from88 + delta; !(next88 & 0x88); next88 += delta)
					{
						var next = from_88(next88); // 120 -> 64

						AttackBBMask[AttackBBidx(pce, from, HighSQMask[next])] |= SetMask[next]; // Tamadas

						if (pce === QUEEN) {

							for (sq = from88 + delta; !(sq & 0x88) && sq != next88; sq += delta) {
								BetweenBBMask[BetweenBBidx(from, next, HighSQMask[from_88(sq)])] |= SetMask[from_88(sq)]; // Koztes
							}

							for (sq = next88 + delta; !(sq & 0x88); sq += delta) {
								BehindBBMask[BetweenBBidx(from, next, HighSQMask[from_88(sq)])] |= SetMask[from_88(sq)]; // Mogotte
							}
						}

						if (nonSlider[pce]) break; // Pawn, Knight, King
					}
				}
			}
		}

		// Szeleket kizaro tomb
		for (from = 0; from < 64; from++)
		{
			for (pce = KNIGHT; pce <= KING; pce++)
			{
				var attacks = PceAttacks(pce, from);

				for (var bb = attacks.Low; bb != 0; bb = restBit(bb)) {
					sq = firstBitLow(bb);
					if ((attacks.Low & BehindBBMask[BetweenBBidx(from, sq, LOW)])  != 0
					|| (attacks.High & BehindBBMask[BetweenBBidx(from, sq, HIGH)]) != 0) {
						BlockerBBMask[AttackBBidx(pce, from, LOW)] |= SetMask[sq];
					}
				}
				for (var bb = attacks.High; bb != 0; bb = restBit(bb)) {
					sq = firstBitHigh(bb);
					if ((attacks.Low & BehindBBMask[BetweenBBidx(from, sq, LOW)])  != 0
					|| (attacks.High & BehindBBMask[BetweenBBidx(from, sq, HIGH)]) != 0) {
						BlockerBBMask[AttackBBidx(pce, from, HIGH)] |= SetMask[sq];
					}
				}
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

		var msg = '', index = 0;

		console.log('Also:  '+BinaryString(BitLow));
		console.log('Felso: '+BinaryString(BitHigh));

		var BitBoard  = BinaryString(BitLow);
		    BitBoard += BinaryString(BitHigh);
		    BitBoard  = BitBoard.split('');

		for (var rank = RANKS.RANK_8; rank >= RANKS.RANK_1; rank--) {
			msg = rank+'. ';
			for (var file = FILES.FILE_A; file <= FILES.FILE_H; file++) {
				if (BitBoard[index++] == '1') {
					msg += 'X';
				} else {
					msg += '-';
				}
			}
			console.log(msg);
		}
	}

	function restBit(b) {
		return b & (b - 1);
	}

	var BitIndexLow = [ // Mezok 0-31-ig
	31, 30, 3, 29, 2, 17, 7, 28, 1, 9, 11, 16, 6, 14, 27, 23,
	0, 4, 18, 8, 10, 12, 15, 24, 5, 19, 13, 25, 20, 26, 21, 22 ];

	function firstBitLow(b) {
		return BitIndexLow[((b & -b) * 0x077CB531) >>> 27];
	}

	var BitIndexHigh = [ // Mezok 32-63-ig
	63, 62, 35, 61, 34, 49, 39, 60, 33, 41, 43, 48, 38, 46, 59, 55,
	32, 36, 50, 40, 42, 44, 47, 56, 37, 51, 45, 57, 52, 58, 53, 54 ];

	function firstBitHigh(b) {
		return BitIndexHigh[((b & -b) * 0x077CB531) >>> 27];
	}

	function PopCount(b) { // for 32 bit
		b = b - ((b >>> 1) & 0x55555555);
		b = (b & 0x33333333) + ((b >>> 2) & 0x33333333);
		return ((b + (b >>> 4) & 0x0F0F0F0F) * 0x01010101) >>> 24;
	}

	function SetBitBoard(sq, pce, color) {
		BitBoard[pce   << 1 | HighSQMask[sq]] |= SetMask[sq];
		BitBoard[color << 1 | HighSQMask[sq]] |= SetMask[sq];
	}

	function ClearBitBoard(sq, pce, color) {
		BitBoard[pce   << 1 | HighSQMask[sq]] &= ClearMask[sq];
		BitBoard[color << 1 | HighSQMask[sq]] &= ClearMask[sq];
	}

	function DefendedByBPawn(sq) {
		sq = sq - 8; // Fekete Gyalog Vedelem
		return (NeighbourMask[sq] & BitBoard[BLACK_PAWN << 1 | HighSQMask[sq]]);
	}

	function DefendedByWPawn(sq) {
		sq = sq + 8; // Feher Gyalog Vedelem
		return (NeighbourMask[sq] & BitBoard[WHITE_PAWN << 1 | HighSQMask[sq]]);
	}

	function WhiteCandidatePawn(sq) {
		var Black = 0;   // [W/B]Candidate Elottunk/Mogottunk van
		var White = 0;   // NeighbourMask Mellettunk van, ezert..
		var s1 = sq + 8; // Kozvetlen vedo tarsakhoz LEFELE lepunk (NeighbourMask)
		var s2 = sq - 8; // Kozvetlen szomszed tarshoz (WCandidateMask), valamint
		                 // Kozvetlen Tamadokhoz (NeighbourMask) FELFELE lepunk
		Black += PopCount(BCandidateMask[sq] & BitBoard[bPawnLow]);
		Black += PopCount(BCandidateMask[BitFixHigh[sq]] & BitBoard[bPawnHigh]);
		White += PopCount(WCandidateMask[BitFixLow[s2]] & BitBoard[wPawnLow]);
		White += PopCount(WCandidateMask[s2] & BitBoard[wPawnHigh]);

		if (White >= Black) { // Tobbsegben vagyunk -> Jelenlegi tamadok/vedok szama kell
			Black = PopCount(NeighbourMask[s2] & BitBoard[BLACK_PAWN << 1 | HighSQMask[s2]]);
			White = PopCount(NeighbourMask[s1] & BitBoard[WHITE_PAWN << 1 | HighSQMask[s1]]);
			if (White >= Black) { // Gyoztunk
				return true;
			}
		}
		return false;
	}

	function BlackCandidatePawn(sq) {
		var Black = 0;   // [W/B]Candidate Elottunk/Mogottunk van
		var White = 0;   // NeighbourMask Mellettunk van, ezert..
		var s1 = sq - 8; // Kozvetlen vedo tarsakhoz FELFELE lepunk (NeighbourMask)
		var s2 = sq + 8; // Kozvetlen szomszed tarshoz (BCandidateMask), valamint
		                 // Kozvetlen Tamadokhoz (NeighbourMask) LEFELE lepunk
		Black += PopCount(BCandidateMask[s2] & BitBoard[bPawnLow]);
		Black += PopCount(BCandidateMask[BitFixHigh[s2]] & BitBoard[bPawnHigh]);
		White += PopCount(WCandidateMask[BitFixLow[sq]] & BitBoard[wPawnLow]);
		White += PopCount(WCandidateMask[sq] & BitBoard[wPawnHigh]);

		if (Black >= White) { // Tobbsegben vagyunk -> Jelenlegi tamadok/vedok szama kell
			Black = PopCount(NeighbourMask[s1] & BitBoard[BLACK_PAWN << 1 | HighSQMask[s1]]);
			White = PopCount(NeighbourMask[s2] & BitBoard[WHITE_PAWN << 1 | HighSQMask[s2]]);
			if (Black >= White) { // Gyoztunk
				return true;
			}
		}
		return false;
	}

	function WhiteBackwardControl(sq, rank) {
		var s1 = sq -  8; // 1 sorral fentebb
		var s2 = sq - 16; // 2 sorral fentebb
		if ((CHESS_BOARD[s1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
		&& ( NeighbourMask[s1] & BitBoard[WHITE_PAWN << 1 | HighSQMask[s1]]) != 0 // 1 sorral fentebb mellettem van Feher Gyalog
		&& ((NeighbourMask[s1] & BitBoard[BLACK_PAWN << 1 | HighSQMask[s1]]) // Kulon-kulon vizsgalok also es felso 32 bitet! Osszekapcsolom "|" ==>
		  | (NeighbourMask[s2] & BitBoard[BLACK_PAWN << 1 | HighSQMask[s2]])) == 0) { // (1 | 2) sorral fentebb atlosan 1-1 mezot nezek! Nincs Fekete Gyalog
			return false;
		} else if (rank == RANKS.RANK_2 // 2. Sorban also es felso 32 bitet meghatarozza
			   && (CHESS_BOARD[s1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
			   && (CHESS_BOARD[s2] & 0x07) !== PAWN // Elottem 2 mezovel nincs Gyalog
			   && (NeighbourMask[s2] & BitBoard[wPawnHigh]) != 0 // 2 sorral fentebb mellettem van Feher Gyalog ("FELSO BIT")
			   && ((NeighbourMask[s2-8] & BitBoard[bPawnLow]) | (BCandidateMask[BitFixHigh[sq]] & BitBoard[bPawnHigh])) == 0) { // Nincs Fekete Gyalog
			   // ((3 sorral fentebb atlosan 1-1 mezot nezek) | (1-2 sorral fentebb atlosan 1-1 mezo "FELSO BIT")) (rank == 2 miatt also vagy felso 32 bit)
			return false;
		}
		return true;
	}

	function BlackBackwardControl(sq, rank) {
		var s1 = sq +  8; // 1 sorral lentebb
		var s2 = sq + 16; // 2 sorral lentebb
		if ((CHESS_BOARD[s1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
		&& ( NeighbourMask[s1] & BitBoard[BLACK_PAWN << 1 | HighSQMask[s1]]) != 0 // 1 sorral lentebb mellettem van Fekete Gyalog
		&& ((NeighbourMask[s1] & BitBoard[WHITE_PAWN << 1 | HighSQMask[s1]]) // Kulon-kulon vizsgalok also es felso 32 bitet! Osszekapcsolom "|" ==>
		  | (NeighbourMask[s2] & BitBoard[WHITE_PAWN << 1 | HighSQMask[s2]])) == 0) { // (1 | 2) sorral lentebb atlosan 1-1 mezot nezek! Nincs Feher Gyalog
			return false;
		} else if (rank == RANKS.RANK_7 // 7. Sorban also es felso 32 bitet meghatarozza
			   && (CHESS_BOARD[s1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
			   && (CHESS_BOARD[s2] & 0x07) !== PAWN // Elottem 2 mezovel nincs Gyalog
			   && (NeighbourMask[s2] & BitBoard[bPawnLow]) != 0 // 2 sorral lentebb mellettem van Fekete Gyalog ("ALSO BIT")
			   && ((NeighbourMask[s2+8] & BitBoard[wPawnHigh]) | (WCandidateMask[BitFixLow[sq]] & BitBoard[wPawnLow])) == 0) { // Nincs Feher Gyalog
			   // ((3 sorral lentebb atlosan 1-1 mezot nezek)  | (1-2 sorral lentebb atlosan 1-1 mezot nezek "ALSO BIT")) (rank == 7 miatt also vagy felso 32 bit)
			return false;
		}
		return true;
	}

	function WhiteBackwardPawn(sq) {
		sq = sq - 8; // Melletunk levo mezoket igy latjuk
		return (WCandidateMask[BitFixLow[sq]] & BitBoard[wPawnLow]) | (WCandidateMask[sq] & BitBoard[wPawnHigh]);
	}

	function BlackBackwardPawn(sq) {
		sq = sq + 8; // Melletunk levo mezoket igy latjuk
		return (BCandidateMask[sq] & BitBoard[bPawnLow]) | (BCandidateMask[BitFixHigh[sq]] & BitBoard[bPawnHigh]);
	}

	function WhiteMostPawn(sq) { // Legelso Feher Gyalog
		return (WOpenFileMask[sq] & BitBoard[wPawnLow]) | (WOpenFileMask[BitFixHigh[sq]] & BitBoard[wPawnHigh]);
	}

	function BlackMostPawn(sq) { // Legelso Fekete Gyalog
		return (BOpenFileMask[BitFixLow[sq]] & BitBoard[bPawnLow]) | (BOpenFileMask[sq] & BitBoard[bPawnHigh]);
	}

	function WhiteOpenFile(sq) { // Fekete Dupla Gyalog: WhiteOpenFile(sq) != 0
		return (WOpenFileMask[sq] & BitBoard[bPawnLow]) | (WOpenFileMask[BitFixHigh[sq]] & BitBoard[bPawnHigh]);
	}

	function BlackOpenFile(sq) { // Feher Dupla Gyalog: BlackOpenFile(sq) != 0
		return (BOpenFileMask[BitFixLow[sq]] & BitBoard[wPawnLow]) | (BOpenFileMask[sq] & BitBoard[wPawnHigh]);
	}

	function WhitePassedPawn(sq) {
		return (WhitePassedMask[sq] & BitBoard[bPawnLow]) | (WhitePassedMask[BitFixHigh[sq]] & BitBoard[bPawnHigh]);
	}

	function BlackPassedPawn(sq) {
		return (BlackPassedMask[BitFixLow[sq]] & BitBoard[wPawnLow]) | (BlackPassedMask[sq] & BitBoard[wPawnHigh]);
	}

	function IsOpenFile(file, color) {
		return (FileBBMask[file] & BitBoard[(color|PAWN) << 1 | LOW]) | (FileBBMask[file] & BitBoard[(color|PAWN) << 1 | HIGH]);
	}

	function IsolatedPawn(sq, color) {
		return (IsolatedMask[sq] & BitBoard[(color|PAWN) << 1 | LOW]) | (IsolatedMask[sq] & BitBoard[(color|PAWN) << 1 | HIGH]);
	}

	function PawnOnSeventh() {
		return (currentPlayer ? (BitBoard[bPawnHigh] & RankBBMask[RANKS.RANK_2]) : (BitBoard[wPawnLow] & RankBBMask[RANKS.RANK_7]));
	}

	function PawnPush(Move) {
		return (CHESS_BOARD[FROMSQ(Move)] & 0x07) == PAWN && (currentPlayer ? (TableRanks[TOSQ(Move)] <= RANKS.RANK_3 && BlackPassedPawn(TOSQ(Move)) == 0)
		                                                                    : (TableRanks[TOSQ(Move)] >= RANKS.RANK_6 && WhitePassedPawn(TOSQ(Move)) == 0));
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function to_88(sq) { return sq + (sq & 56); }

	function from_88(sq) { return (sq + (sq & 0x07)) >> 1; }

	function BetweenBBidx(s1, s2, bit) { return (s1 << 7) | (s2 << 1) | bit; }

	function AttackBBidx(pce, sq, bit) { return (sq << 4) | (pce << 1) | bit; }

	function LineIsEmpty(s1, s2, pieces) {
		return (pieces.Low & BetweenBBMask[BetweenBBidx(s1, s2, LOW)]) | (pieces.High & BetweenBBMask[BetweenBBidx(s1, s2, HIGH)]);
	}

	function GetAllPce() {
		return { Low : (BitBoard[WhiteLow] | BitBoard[BlackLow]), High : (BitBoard[WhiteHigh] | BitBoard[BlackHigh]) };
	}

	function PceBlocker(pce, sq) {
		return { Low : BlockerBBMask[AttackBBidx(pce, sq, LOW)], High : BlockerBBMask[AttackBBidx(pce, sq, HIGH)] };
	}

	function PceAttacks(pce, sq) {
		return { Low : AttackBBMask[AttackBBidx(pce, sq, LOW)], High : AttackBBMask[AttackBBidx(pce, sq, HIGH)] };
	}

	function Behind(s1, s2) {
		return { Low : BehindBBMask[BetweenBBidx(s1, s2, LOW)], High : BehindBBMask[BetweenBBidx(s1, s2, HIGH)] };
	}

	function AllPceByColor(color) {
		return { Low : BitBoard[color << 1 | LOW], High : BitBoard[color << 1 | HIGH] };
	}

	function KingZone(Ring, Rank, File) { // 3x3 square
		if (Rank == RANKS.RANK_1) {
			Ring.High |= Ring.High << 8;
		} else if (Rank == RANKS.RANK_8) {
			Ring.Low  |= Ring.Low >>> 8;
		}
		if (File == FILES.FILE_A) {
			Ring.Low  |= Ring.Low  >>> 1;
			Ring.High |= Ring.High >>> 1;
		} else if (File == FILES.FILE_H) {
			Ring.Low  |= Ring.Low   << 1;
			Ring.High |= Ring.High  << 1;
		}
	}

	function AttacksFrom(pce, from, pieces) { // Based on Senpai!
		var bb, sq;
		var attacks = PceAttacks(pce, from);
		var blocker = PceBlocker(pce, from);

		for (bb = pieces.Low & blocker.Low; bb != 0; bb = restBit(bb)) {
			sq = firstBitLow(bb);
			attacks.Low  &= ~BehindBBMask[BetweenBBidx(from, sq, LOW)];
			attacks.High &= ~BehindBBMask[BetweenBBidx(from, sq, HIGH)];
		}
		for (bb = pieces.High & blocker.High; bb != 0; bb = restBit(bb)) {
			sq = firstBitHigh(bb);
			attacks.Low  &= ~BehindBBMask[BetweenBBidx(from, sq, LOW)];
			attacks.High &= ~BehindBBMask[BetweenBBidx(from, sq, HIGH)];
		}
		return attacks;
	}

	function wPawnAttacks(attacks) {
		// Hack: backward instead of forward on white side!
		attacks.High |= ((BitBoard[wPawnHigh] & ~FileBBMask[FILES.FILE_A]) >>> 7) | ((BitBoard[wPawnHigh] & ~FileBBMask[FILES.FILE_H]) >>> 9);
		attacks.Low  |= ((BitBoard[wPawnLow]  & ~FileBBMask[FILES.FILE_H])  << 7) | ((BitBoard[wPawnLow]  & ~FileBBMask[FILES.FILE_A])  << 9);
		attacks.Low  |= (attacks.High >>> 16); // Add 5th rank attacks to Low
		attacks.High <<= 16; // Hack: forward 2x
	}

	function bPawnAttacks(attacks) {
		// Hack: backward instead of forward on black side!
		attacks.Low  |= ((BitBoard[bPawnLow]  & ~FileBBMask[FILES.FILE_H])  << 7) | ((BitBoard[bPawnLow]  & ~FileBBMask[FILES.FILE_A])  << 9);
		attacks.High |= ((BitBoard[bPawnHigh] & ~FileBBMask[FILES.FILE_A]) >>> 7) | ((BitBoard[bPawnHigh] & ~FileBBMask[FILES.FILE_H]) >>> 9);
		attacks.High |= (attacks.Low  << 16); // Add 4th rank attacks to High
		attacks.Low  >>>= 16; // Hack: forward 2x
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function validateMove(from, to, side) { // for TanKy UI

		var fromPiece = CHESS_BOARD[from];
		var toPiece   = CHESS_BOARD[to];

		if (!fromPiece) { // Moving an empty square?
			return false;
		}

		if ((fromPiece & 0x8) ^ side) { // Not your turn!
			return false;
		}
		
		if (toPiece && (toPiece & 0x8) == side) { // Cannot attack one of your own!
			return false;
		}

		var pieceType = fromPiece & 0x07;

	// Capture move..?
		var capture = 0;
		if (toPiece || (pieceType === PAWN && EN_PASSANT != 0 && EN_PASSANT == to)) {
			capture = 1;
		}

	// Promotion..?
		var promote = 0;
		if (pieceType === PAWN && (to <= SQUARES.H8 || to >= SQUARES.A1)) {
			promote = side|QUEEN;
		}

	// Casling..?
		var castling = 0;
		if (pieceType === KING && Math.abs(from - to) == 2) {
			castling = 1;
		}

	// Create move..
		var Move = BIT_MOVE(from, to, capture, promote, castling);

	// Legal move..?
		for (var index = brd_moveStart[0]; index < brd_moveStart[1]; index++) {
			if (brd_moveList[index] == Move) {
				return isLegal(Move);
			}
		}
		return false;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function StoreHash(move, score, _eval, flags, depth) { // Hash mentes

		var index = brd_hashKeyLow & HASHMASK;

		var oldest = -1;
		var update =  0;

		for (var entry = index; entry < index + 4; entry++) {

			if (hash_lock[entry] == brd_hashKeyHigh) {

				if (hash_depth[entry] <= depth) {
					if (move == NOMOVE) move = hash_move[entry];
					update = entry;
					break;
				}

				if (hash_move[entry] == NOMOVE) { // fill entry with move!
					hash_move[entry] = move;
				}

				hash_date[entry] = hashDate; // update age of deeper entry!

				return;
			}

			var age = (hashDate - hash_date[entry]) * 64 + 64 - hash_depth[entry];
			if (oldest < age) {
				oldest = age;
				update = entry;
			}
		}

		if (hash_lock[update] == 0) { // new
			hashUsed++;
		}

		if (score > ISMATE) {
			score += boardPly;
		} else if (score < -ISMATE) {
			score -= boardPly;
		}

		hash_move [update] = move;
		hash_eval [update] = _eval;
		hash_score[update] = score;
		hash_flags[update] = flags;
		hash_depth[update] = depth;
		hash_date [update] = hashDate;
		hash_lock [update] = brd_hashKeyHigh;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function ProbeHash() { // Hash kiolvasas

		var index = brd_hashKeyLow & HASHMASK;

		for (var entry = index; entry < index + 4; entry++) {

			if (hash_lock[entry] == brd_hashKeyHigh) {
				return {
					move  : hash_move [entry],
					eval  : hash_eval [entry],
					score : hash_score[entry],
					flags : hash_flags[entry],
					depth : hash_depth[entry]
				};
			}
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


	function FROMSQ(m) { return (m & 0x3F); }
	function TOSQ(m) { return ((m >> 6) & 0x3F); }
	function PROMOTED(m) { return ((m >> 13) & 0xF); }
	function HASH_SIDE() {
		brd_hashKeyLow  ^= SideKeyLow;
		brd_hashKeyHigh ^= SideKeyHigh;
	}
	function HASH_PCE(pce, sq) {
		brd_hashKeyLow  ^= PieceKeysLow [(pce << 6) | sq];
		brd_hashKeyHigh ^= PieceKeysHigh[(pce << 6) | sq];
		if ((pce & 0x07) === PAWN) {
			brd_pawnKeyLow  ^= PieceKeysLow [(pce << 6) | sq];
			brd_pawnKeyHigh ^= PieceKeysHigh[(pce << 6) | sq];
		}
	}
	function HASH_CA() {
		brd_hashKeyLow  ^= CastleKeysLow [castleRights];
		brd_hashKeyHigh ^= CastleKeysHigh[castleRights];
	}
	function HASH_EP() {
		brd_hashKeyLow  ^= PieceKeysLow [EN_PASSANT];
		brd_hashKeyHigh ^= PieceKeysHigh[EN_PASSANT];
	}
	function MOVE_PCE(pce, from, to) {
		CHESS_BOARD[from] = 0; // Babu torlese
		CHESS_BOARD[to] = pce; // Babu mozgatas
		brd_pieceIndex[to] = brd_pieceIndex[from];
		brd_pieceList[(pce << 4) | brd_pieceIndex[to]] = to;
		ClearBitBoard(from, pce, (pce & 0x8));
		SetBitBoard(to, pce, (pce & 0x8));
	}
	function ADDING_PCE(pce, sq, currentPlayer) {
		CHESS_BOARD[sq] = pce; // Babu hozzadasa
		brd_pieceIndex[sq] = brd_pieceCount[pce];
		brd_pieceList[(pce << 4) | brd_pieceIndex[sq]] = sq;
		brd_Material[currentPlayer] += PieceValue[pce];
		brd_pieceCount[pce]++; // Darabszam novelese
		SetBitBoard(sq, pce, currentPlayer);
	}
	function DELETE_PCE(pce, sq, currentPlayer) {
		CHESS_BOARD[sq] = 0; // Babu torlese
		brd_pieceCount[pce]--; // Darabszam csokkentese
		var lastPceSquare = brd_pieceList[(pce << 4) | brd_pieceCount[pce]];
		brd_pieceIndex[lastPceSquare] = brd_pieceIndex[sq];
		brd_pieceList[(pce << 4) | brd_pieceIndex[lastPceSquare]] = lastPceSquare;
		brd_pieceList[(pce << 4) | brd_pieceCount[pce]] = EMPTY; // Ures
		brd_Material[currentPlayer] -= PieceValue[pce];
		ClearBitBoard(sq, pce, currentPlayer);
	}
	function BIT_MOVE(from, to, captured, promoted, castled) {
		return (from | (to << 6) | (captured << 12) | (promoted << 13) | (castled << 17)); // Lepes: 18 bit
	}
	/*
	0000 0000 0000 0011 1111 -> Ahonnan lepunk (m & 0x3F)
	0000 0000 1111 1100 0000 -> Ahova lepunk ((m >> 6) & 0x3F)
	0000 0001 0000 0000 0000 -> Leutes jelzes (m & CAPTURE_MASK)
	0001 1110 0000 0000 0000 -> Gyalog bevaltas ((m >> 13) & 0xF)
	0010 0000 0000 0000 0000 -> Sancolas jelzes (m & CASTLED_MASK)
	-----------------------------------------------------------------
	0001 1111 0000 0000 0000 -> Utes vagy Bevaltas (m & TACTICAL_MASK)
	0011 1111 0000 0000 0000 -> Utes, Bevaltas, Sanc (m & DANGER_MASK)
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
			pawnKeyHigh	: brd_pawnKeyHigh,
			hashKeyLow	: brd_hashKeyLow,
			pawnKeyLow	: brd_pawnKeyLow,
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
				EN_PASSANT = to-8; // Hack: Koztes tarolo
				HASH_PCE(WHITE_PAWN, EN_PASSANT);
				DELETE_PCE(WHITE_PAWN, EN_PASSANT, WHITE);
			}
			else // Feher
			{
				EN_PASSANT = to+8; // Hack: Koztes tarolo
				HASH_PCE(BLACK_PAWN, EN_PASSANT);
				DELETE_PCE(BLACK_PAWN, EN_PASSANT, BLACK);
			}
		}
		else if (move & CASTLED_MASK) // Sancolaskor Bastya mozgatasa
		{
			switch (to) {
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
			brd_fiftyMove = 0; // 50 lepes nullazasa

			if (Math.abs(from - to) === 16) // En Passant mentese
			{
				EN_PASSANT = (to + (currentPlayer ? -8 : 8));
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
		brd_pawnKeyLow = MOVE_HISTORY[moveCount].pawnKeyLow;
		brd_hashKeyHigh = MOVE_HISTORY[moveCount].hashKeyHigh;
		brd_pawnKeyHigh = MOVE_HISTORY[moveCount].pawnKeyHigh;
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
			currentPlayer ? ADDING_PCE(BLACK_PAWN, (EN_PASSANT + 8), BLACK) // Fekete
			              : ADDING_PCE(WHITE_PAWN, (EN_PASSANT - 8), WHITE); // Feher
		}
		else if (move & CASTLED_MASK) // Sancolas torlesekor a Bastya mozgatasa
		{
			switch (to) {
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
			DELETE_PCE(PROMOTED_PIECE, from, currentPlayer);
			ADDING_PCE((currentPlayer | PAWN), from, currentPlayer);
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function S(mg, eg) { return (mg << 16) + eg; }

	function EG_SC(sc) { return (sc << 16) >> 16; }

	function MG_SC(sc) { return (sc + 0x8000) >> 16; }

	function isMate(Score) { return Score > ISMATE || Score < -ISMATE; }

	function isCheck(Side) { return isSquareUnderAttack(brd_pieceList[(Side | KING) << 4], Side); }


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function isSquareUnderAttack(target, us) {

		var bb, from, them = us^8;

		// Gyalog tamadas
		if (us === BLACK ? DefendedByWPawn(target) : DefendedByBPawn(target)) {
			return 1;
		}

		// Huszar tamadas
		bb = PceAttacks(KNIGHT, target);
		if (bb.Low & BitBoard[(them|KNIGHT) << 1 | LOW]
		|| bb.High & BitBoard[(them|KNIGHT) << 1 | HIGH]) {
			return 1;
		}

		// Kiraly tamadas
		bb = PceAttacks(KING, target);
		if (bb.Low & BitBoard[(them|KING) << 1 | LOW]
		|| bb.High & BitBoard[(them|KING) << 1 | HIGH]) {
			return 1;
		}

		// Futo, Bastya, Vezer
		var xPiecesBB = GetAllPce();
		var b = { Low : 0, High : 0 };

		// Futo & Vezer tamadas
		bb = PceAttacks(BISHOP, target);
		b.Low  |= bb.Low  & (BitBoard[(them|BISHOP) << 1 | LOW]  | BitBoard[(them|QUEEN) << 1 | LOW]);
		b.High |= bb.High & (BitBoard[(them|BISHOP) << 1 | HIGH] | BitBoard[(them|QUEEN) << 1 | HIGH]);

		// Bastya & Vezer tamadas
		bb = PceAttacks(ROOK, target);
		b.Low  |= bb.Low  & (BitBoard[(them|ROOK) << 1 | LOW]  | BitBoard[(them|QUEEN) << 1 | LOW]);
		b.High |= bb.High & (BitBoard[(them|ROOK) << 1 | HIGH] | BitBoard[(them|QUEEN) << 1 | HIGH]);

		for (bb = b.Low; bb != 0; bb = restBit(bb)) {
			from = firstBitLow(bb);
			if (LineIsEmpty(from, target, xPiecesBB) == 0) return 1;
		}
		for (bb = b.High; bb != 0; bb = restBit(bb)) {
			from = firstBitHigh(bb);
			if (LineIsEmpty(from, target, xPiecesBB) == 0) return 1;
		}

		return NOT_IN_CHECK;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function givesCheck(move) {

		var to = TOSQ(move);
		var from = FROMSQ(move);
		var us = CHESS_BOARD[from] & 0x8;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var PCE = PROMOTED(move) !== 0 ? PROMOTED(move) & 0x07 : CHESS_BOARD[from] & 0x07;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Gyalog Sakk..?
		if (PCE === PAWN)
		{
			var attack = us ? NeighbourMask[to+8] & BitBoard[WHITE_KING << 1 | HighSQMask[to+8]]
			                : NeighbourMask[to-8] & BitBoard[BLACK_KING << 1 | HighSQMask[to-8]];

			if (attack) return 1;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var bb, them = us^8;
		var xPiecesBB = GetAllPce();
		var King = brd_pieceList[(them | KING) << 4];

		// Babu mozgatasa
		HighSQMask[from] ? xPiecesBB.High ^= SetMask[from] : xPiecesBB.Low ^= SetMask[from];
		HighSQMask[to]   ? xPiecesBB.High |= SetMask[to]   : xPiecesBB.Low |= SetMask[to];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Sancolas
		if (move & CASTLED_MASK)
		{
			switch (to) {
				case SQUARES.C1: var RookFrom = SQUARES.A1, RookTo = SQUARES.D1; break;
				case SQUARES.C8: var RookFrom = SQUARES.A8, RookTo = SQUARES.D8; break;
				case SQUARES.G1: var RookFrom = SQUARES.H1, RookTo = SQUARES.F1; break;
				case SQUARES.G8: var RookFrom = SQUARES.H8, RookTo = SQUARES.F8; break;
				default: break;
			}

			// Bastya mozgatasa
			us === BLACK ? xPiecesBB.Low  = (xPiecesBB.Low  ^ SetMask[RookFrom]) | SetMask[RookTo]
			             : xPiecesBB.High = (xPiecesBB.High ^ SetMask[RookFrom]) | SetMask[RookTo];

			// Hack: Bastya tamadas!
			PCE = ROOK; to = RookTo;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Direkt Sakk..?
		if (PCE !== PAWN)
		{
			bb = PceAttacks(PCE, to);
			if (bb.Low & BitBoard[(them|KING) << 1 | LOW]
			|| bb.High & BitBoard[(them|KING) << 1 | HIGH])
			{
				if (LineIsEmpty(to, King, xPiecesBB) == 0) return 1;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var Beyond = Behind(King, from); // Babu mogott megnyilo mezok!

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// En Passant
		if (PCE === PAWN && CHESS_BOARD[to] == 0 && (move & CAPTURE_MASK))
		{
			var epSq = us === BLACK ? to-8 : to+8;

			// Ellenfel torlese
			HighSQMask[epSq] ? xPiecesBB.High ^= SetMask[epSq] : xPiecesBB.Low ^= SetMask[epSq];

			// Mogotte megnyilo mezok!
			Beyond.Low  |= BehindBBMask[BetweenBBidx(King, epSq, LOW)];
			Beyond.High |= BehindBBMask[BetweenBBidx(King, epSq, HIGH)];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Felfedezett Sakk..?
		if (Beyond.Low | Beyond.High)
		{
			var b = { Low : 0, High : 0 };

			// Futo & Vezer tamadas
			bb = PceAttacks(BISHOP, King);
			b.Low  |= bb.Low  & (BitBoard[(us|BISHOP) << 1 | LOW]  | BitBoard[(us|QUEEN) << 1 | LOW]);
			b.High |= bb.High & (BitBoard[(us|BISHOP) << 1 | HIGH] | BitBoard[(us|QUEEN) << 1 | HIGH]);

			// Bastya & Vezer tamadas
			bb = PceAttacks(ROOK, King);
			b.Low  |= bb.Low  & (BitBoard[(us|ROOK) << 1 | LOW]  | BitBoard[(us|QUEEN) << 1 | LOW]);
			b.High |= bb.High & (BitBoard[(us|ROOK) << 1 | HIGH] | BitBoard[(us|QUEEN) << 1 | HIGH]);

			for (bb = b.Low & Beyond.Low; bb != 0; bb = restBit(bb)) {
				from = firstBitLow(bb);
				if (LineIsEmpty(from, King, xPiecesBB) == 0) return 1;
			}
			for (bb = b.High & Beyond.High; bb != 0; bb = restBit(bb)) {
				from = firstBitHigh(bb);
				if (LineIsEmpty(from, King, xPiecesBB) == 0) return 1;
			}
		}

		return NOT_IN_CHECK;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function isLegal(move) {

		var to = TOSQ(move);
		var from = FROMSQ(move);
		var bb, us = currentPlayer;
		var them = currentPlayer^8;
		var PCE = CHESS_BOARD[from] & 0x07;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Kiraly lepett
		if (PCE === KING)
		{
			if (CHESS_BOARD[to]) ClearBitBoard(to, CHESS_BOARD[to], them);
			ClearBitBoard(from, (us|KING), us);

			var attack = isSquareUnderAttack(to, us);

			SetBitBoard(from, (us|KING), us);
			if (CHESS_BOARD[to]) SetBitBoard(to, CHESS_BOARD[to], them);

			return !attack; // Negalt!
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var xPiecesBB = GetAllPce();
		var King = brd_pieceList[(us | KING) << 4];

		// Babu mozgatasa
		HighSQMask[from] ? xPiecesBB.High ^= SetMask[from] : xPiecesBB.Low ^= SetMask[from];
		HighSQMask[to]   ? xPiecesBB.High |= SetMask[to]   : xPiecesBB.Low |= SetMask[to];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var Beyond = Behind(King, from); // Babu mogott megnyilo mezok!

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// En Passant
		if (PCE === PAWN && CHESS_BOARD[to] == 0 && (move & CAPTURE_MASK))
		{
			var epSq = us === BLACK ? to-8 : to+8;

			// Ellenfel torlese
			HighSQMask[epSq] ? xPiecesBB.High ^= SetMask[epSq] : xPiecesBB.Low ^= SetMask[epSq];

			// Mogotte megnyilo mezok!
			Beyond.Low  |= BehindBBMask[BetweenBBidx(King, epSq, LOW)];
			Beyond.High |= BehindBBMask[BetweenBBidx(King, epSq, HIGH)];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Felfedezett Sakk..?
		if (Beyond.Low | Beyond.High)
		{
			var b = { Low : 0, High : 0 };

			// Futo & Vezer tamadas
			bb = PceAttacks(BISHOP, King);
			b.Low  |= bb.Low  & (BitBoard[(them|BISHOP) << 1 | LOW]  | BitBoard[(them|QUEEN) << 1 | LOW]);
			b.High |= bb.High & (BitBoard[(them|BISHOP) << 1 | HIGH] | BitBoard[(them|QUEEN) << 1 | HIGH]);

			// Bastya & Vezer tamadas
			bb = PceAttacks(ROOK, King);
			b.Low  |= bb.Low  & (BitBoard[(them|ROOK) << 1 | LOW]  | BitBoard[(them|QUEEN) << 1 | LOW]);
			b.High |= bb.High & (BitBoard[(them|ROOK) << 1 | HIGH] | BitBoard[(them|QUEEN) << 1 | HIGH]);

			for (bb = b.Low & Beyond.Low; bb != 0; bb = restBit(bb)) {
				from = firstBitLow(bb);
				if (LineIsEmpty(from, King, xPiecesBB) == 0 && from != to) return false;
			}
			for (bb = b.High & Beyond.High; bb != 0; bb = restBit(bb)) {
				from = firstBitHigh(bb);
				if (LineIsEmpty(from, King, xPiecesBB) == 0 && from != to) return false;
			}
		}

		return true;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function Evaluation() {

		var bb           = 0; // bb
		var mob          = 0; // Mob
		var Rank         = 0; // Sor
		var PCE          = 0; // Babu
		var File         = 0; // Oszlop
		var Phase        = 24; // Fazis
		var Draw         = 1; // Dontetlen
		var threats      = 0; // Fenyegetes
		var pieceIdx     = 0; // Babu index
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
	//							  DONTETLEN
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

		var king = 0;
		var pawns = 0;
		var rooks = 0;
		var safety = 0;
		var queens = 0;
		var knights = 0;
		var bishops = 0;
		var posScore = 0;
		var mobScore = 0;

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var xPiecesBB = GetAllPce();
		var wPassedPawn = new Array();
		var bPassedPawn = new Array();
		var wAttacks = { Low : 0, High : 0 }; wPawnAttacks(wAttacks);
		var bAttacks = { Low : 0, High : 0 }; bPawnAttacks(bAttacks);

		var hash = brd_PawnTable[brd_pawnKeyLow & PAWNMASK];

		if (hash != null && hash.pawnLockKey == brd_pawnKeyHigh) {

			pawns       = hash.score;
			wPassedPawn = hash.wPassed;
			bPassedPawn = hash.bPassed;

		} else {

			pawns = EvalPawns(wPassedPawn, bPassedPawn); // Pont atvetele!

			brd_PawnTable[brd_pawnKeyLow & PAWNMASK] = { // max 144 byte
				score       : pawns,       //    8 byte
				wPassed     : wPassedPawn, // n* 8 byte
				bPassed     : bPassedPawn, // n* 8 byte
				pawnLockKey : brd_pawnKeyHigh // 8 byte
			};
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Vezer, Tisztek ellenorzese
		var wBigPieces = (wNumKnights || wNumBishops || wNumRooks || wNumQueens);
		var bBigPieces = (bNumKnights || bNumBishops || bNumRooks || bNumQueens);

	// Gyalog ellenorzes
		var wPawnHome = BitBoard[wPawnHigh] & RankBBMask[RANKS.RANK_2]; // wPawn on 2th
		var bPawnHome = BitBoard[bPawnLow]  & RankBBMask[RANKS.RANK_7]; // bPawn on 7th

	// Biztonsagos mobilitas:    ~(usPawn | usKing | themPawnAttack)
		var wPawnSafe = { Low  : ~(BitBoard[wPawnLow]  | BitBoard[wKingLow]  | bAttacks.Low),
		                  High : ~(BitBoard[wPawnHigh] | BitBoard[wKingHigh] | bAttacks.High) };
		var bPawnSafe = { Low  : ~(BitBoard[bPawnLow]  | BitBoard[bKingLow]  | wAttacks.Low),
		                  High : ~(BitBoard[bPawnHigh] | BitBoard[bKingHigh] | wAttacks.High) };

	// Tamadasi erok
		var wCanAttack = wNumQueens && (wNumKnights || wNumBishops || wNumRooks || wNumQueens >= 2);
		var bCanAttack = bNumQueens && (bNumKnights || bNumBishops || bNumRooks || bNumQueens >= 2);

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	//							  BABUK ERTEKELESE
	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Kiraly
		var wKing = brd_pieceList[WHITE_KING << 4];
		var wKingRank = TableRanks[wKing]; // Kiraly sora
		var wKingFile = TableFiles[wKing]; // Kiraly oszlopa
		var WKZ = PceAttacks(KING, wKing); // Kiraly tamadas
		var wKingAttacks = { Low : WKZ.Low, High : WKZ.High };
		KingZone(WKZ, wKingRank, wKingFile); // 3x3-as gyuru..
		posScore += KingPst[wKing];

	// Fekete Kiraly
		var bKing = brd_pieceList[BLACK_KING << 4];
		var bKingRank = TableRanks[bKing]; // Kiraly sora
		var bKingFile = TableFiles[bKing]; // Kiraly oszlopa
		var BKZ = PceAttacks(KING, bKing); // Kiraly tamadas
		var bKingAttacks = { Low : BKZ.Low, High : BKZ.High };
		KingZone(BKZ, bKingRank, bKingFile); // 3x3-as gyuru..
		posScore -= KingPst[TableMirror[bKing]];

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Gyalog fenyegetes
		threats += PawnCapture(wAttacks, BLACK);
		threats -= PawnCapture(bAttacks, WHITE);

	// Kiraly fenyegetes
		threats += CaptureScore(wKingAttacks, wPawnSafe, KING, BLACK);
		threats -= CaptureScore(bKingAttacks, bPawnSafe, KING, WHITE);

	// Kiraly zonak
		var SafeWKZ = { Low : WKZ.Low & bPawnSafe.Low, High : WKZ.High & bPawnSafe.High };
		var SafeBKZ = { Low : BKZ.Low & wPawnSafe.Low, High : BKZ.High & wPawnSafe.High };

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Vezer
		pieceIdx = WHITE_QUEEN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Rank = TableRanks[PCE];

			if (Rank == RANKS.RANK_7 && (bPawnHome || bKingRank == RANKS.RANK_8)) { // 7. sorban
				queens += QueenOn7th;
			}

			// BitBoard
			bb = AttacksFrom(QUEEN, PCE, xPiecesBB);

			// Tamadasok
			wAttacks.Low  |= bb.Low;
			wAttacks.High |= bb.High;

			// Mobilitas
			mob  = PopCount(wPawnSafe.Low  & bb.Low);
			mob += PopCount(wPawnSafe.High & bb.High);

			// Fenyegetes
			threats += CaptureScore(bb, wPawnSafe, QUEEN, BLACK);

			// Kiraly tamadas
			if ((bb.Low & SafeBKZ.Low) | (bb.High & SafeBKZ.High)) {
				wAttackCount++;
				wAttackPower += PopCount(bb.Low  & SafeBKZ.Low);
				wAttackPower += PopCount(bb.High & SafeBKZ.High);
			}

			Phase -= 4;
			mobScore += QueenMob[mob];
			posScore += QueenPst[PCE];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Vezer
		pieceIdx = BLACK_QUEEN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Rank = TableRanks[PCE];

			if (Rank == RANKS.RANK_2 && (wPawnHome || wKingRank == RANKS.RANK_1)) { // 7. sorban
				queens -= QueenOn7th;
			}

			// BitBoard
			bb = AttacksFrom(QUEEN, PCE, xPiecesBB);

			// Tamadasok
			bAttacks.Low  |= bb.Low;
			bAttacks.High |= bb.High;

			// Mobilitas
			mob  = PopCount(bPawnSafe.Low  & bb.Low);
			mob += PopCount(bPawnSafe.High & bb.High);

			// Fenyegetes
			threats -= CaptureScore(bb, bPawnSafe, QUEEN, WHITE);

			// Kiraly tamadas
			if ((bb.Low & SafeWKZ.Low) | (bb.High & SafeWKZ.High)) {
				bAttackCount++;
				bAttackPower += PopCount(bb.Low  & SafeWKZ.Low);
				bAttackPower += PopCount(bb.High & SafeWKZ.High);
			}

			Phase -= 4;
			mobScore -= QueenMob[mob];
			posScore -= QueenPst[TableMirror[PCE]];

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

			if (Rank == RANKS.RANK_7 && (bPawnHome || bKingRank == RANKS.RANK_8)) { // 7. sorban
				rooks += RookOn7th;
			}

			// BitBoard
			bb = AttacksFrom(ROOK, PCE, xPiecesBB);

			// Tamadasok
			wAttacks.Low  |= bb.Low;
			wAttacks.High |= bb.High;

			// Mobilitas
			mob  = PopCount(wPawnSafe.Low  & bb.Low);
			mob += PopCount(wPawnSafe.High & bb.High);

			// Fenyegetes
			threats += CaptureScore(bb, wPawnSafe, ROOK, BLACK);

			// Kiraly tamadas
			if ((bb.Low & SafeBKZ.Low) | (bb.High & SafeBKZ.High)) {
				wAttackCount++;
				wAttackPower += PopCount(bb.Low  & SafeBKZ.Low);
				wAttackPower += PopCount(bb.High & SafeBKZ.High);
			}

			Phase -= 2;
			mobScore += RookMob[mob];
			posScore += RookPst[PCE];

			if (IsOpenFile(File, WHITE) == 0) { // Felig nyitott oszlop

				if (IsOpenFile(File, BLACK) == 0) { // Teljesen nyitott
					rooks += RookFullOpen;
				} else {
					rooks += RookHalfOpen;
				}

			} else if (mob <= 3 && Rank <= RANKS.RANK_2) { // Sarokba szorult..?

				if (wKingFile < FILES.FILE_E ?
				   (castleRights & CASTLEBIT.WQ) == 0 && File <= wKingFile
				 : (castleRights & CASTLEBIT.WK) == 0 && File >= wKingFile) {
					rooks -= BlockedRook;
				}
			}

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Bastya
		pieceIdx = BLACK_ROOK << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			if (Rank == RANKS.RANK_2 && (wPawnHome || wKingRank == RANKS.RANK_1)) { // 7. sorban
				rooks -= RookOn7th;
			}

			// BitBoard
			bb = AttacksFrom(ROOK, PCE, xPiecesBB);

			// Tamadasok
			bAttacks.Low  |= bb.Low;
			bAttacks.High |= bb.High;

			// Mobilitas
			mob  = PopCount(bPawnSafe.Low  & bb.Low);
			mob += PopCount(bPawnSafe.High & bb.High);

			// Fenyegetes
			threats -= CaptureScore(bb, bPawnSafe, ROOK, WHITE);

			// Kiraly tamadas
			if ((bb.Low & SafeWKZ.Low) | (bb.High & SafeWKZ.High)) {
				bAttackCount++;
				bAttackPower += PopCount(bb.Low  & SafeWKZ.Low);
				bAttackPower += PopCount(bb.High & SafeWKZ.High);
			}

			Phase -= 2;
			mobScore -= RookMob[mob];
			posScore -= RookPst[TableMirror[PCE]];

			if (IsOpenFile(File, BLACK) == 0) { // Felig nyitott oszlop

				if (IsOpenFile(File, WHITE) == 0) { // Teljesen nyitott
					rooks -= RookFullOpen;
				} else {
					rooks -= RookHalfOpen;
				}

			} else if (mob <= 3 && Rank >= RANKS.RANK_7) { // Sarokba szorult..?

				if (bKingFile < FILES.FILE_E ?
				   (castleRights & CASTLEBIT.BQ) == 0 && File <= bKingFile
				 : (castleRights & CASTLEBIT.BK) == 0 && File >= bKingFile) {
					rooks += BlockedRook;
				}
			}

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Futo
		pieceIdx = WHITE_BISHOP << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			// BitBoard
			bb = AttacksFrom(BISHOP, PCE, xPiecesBB);

			// Tamadasok
			wAttacks.Low  |= bb.Low;
			wAttacks.High |= bb.High;

			// Mobilitas
			mob  = PopCount(wPawnSafe.Low  & bb.Low);
			mob += PopCount(wPawnSafe.High & bb.High);

			// Fenyegetes
			threats += CaptureScore(bb, wPawnSafe, BISHOP, BLACK);

			// Kiraly tamadas
			if ((bb.Low & SafeBKZ.Low) | (bb.High & SafeBKZ.High)) {
				wAttackCount++;
				wAttackPower += PopCount(bb.Low  & SafeBKZ.Low);
				wAttackPower += PopCount(bb.High & SafeBKZ.High);
			}

			Phase -= 1;
			mobScore += BishopMob[mob];
			posScore += BishopPst[PCE];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Futo
		pieceIdx = BLACK_BISHOP << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			// BitBoard
			bb = AttacksFrom(BISHOP, PCE, xPiecesBB);

			// Tamadasok
			bAttacks.Low  |= bb.Low;
			bAttacks.High |= bb.High;

			// Mobilitas
			mob  = PopCount(bPawnSafe.Low  & bb.Low);
			mob += PopCount(bPawnSafe.High & bb.High);

			// Fenyegetes
			threats -= CaptureScore(bb, bPawnSafe, BISHOP, WHITE);

			// Kiraly tamadas
			if ((bb.Low & SafeWKZ.Low) | (bb.High & SafeWKZ.High)) {
				bAttackCount++;
				bAttackPower += PopCount(bb.Low  & SafeWKZ.Low);
				bAttackPower += PopCount(bb.High & SafeWKZ.High);
			}

			Phase -= 1;
			mobScore -= BishopMob[mob];
			posScore -= BishopPst[TableMirror[PCE]];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Huszar
		pieceIdx = WHITE_KNIGHT << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			// BitBoard
			bb = PceAttacks(KNIGHT, PCE);

			// Tamadasok
			wAttacks.Low  |= bb.Low;
			wAttacks.High |= bb.High;

			// Mobilitas
			mob  = PopCount(wPawnSafe.Low  & bb.Low);
			mob += PopCount(wPawnSafe.High & bb.High);

			// Fenyegetes
			threats += CaptureScore(bb, wPawnSafe, KNIGHT, BLACK);

			// Kiraly tamadas
			if ((bb.Low & SafeBKZ.Low) | (bb.High & SafeBKZ.High)) {
				wAttackCount++;
				wAttackPower += PopCount(bb.Low  & SafeBKZ.Low);
				wAttackPower += PopCount(bb.High & SafeBKZ.High);
			}

			Phase -= 1;
			mobScore += KnightMob[mob];
			posScore += KnightPst[PCE];

			var outpost = KnightOutpost[PCE]; // Huszar Orszem

			if (outpost && DefendedByBPawn(PCE) == 0) { // Nincs fenyegetes
				knights += outpost * PopCount(DefendedByWPawn(PCE));
			}

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// Fekete Huszar
		pieceIdx = BLACK_KNIGHT << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			// BitBoard
			bb = PceAttacks(KNIGHT, PCE);

			// Tamadasok
			bAttacks.Low  |= bb.Low;
			bAttacks.High |= bb.High;

			// Mobilitas
			mob  = PopCount(bPawnSafe.Low  & bb.Low);
			mob += PopCount(bPawnSafe.High & bb.High);

			// Fenyegetes
			threats -= CaptureScore(bb, bPawnSafe, KNIGHT, WHITE);

			// Kiraly tamadas
			if ((bb.Low & SafeWKZ.Low) | (bb.High & SafeWKZ.High)) {
				bAttackCount++;
				bAttackPower += PopCount(bb.Low  & SafeWKZ.Low);
				bAttackPower += PopCount(bb.High & SafeWKZ.High);
			}

			Phase -= 1;
			mobScore -= KnightMob[mob];
			posScore -= KnightPst[TableMirror[PCE]];

			var outpost = KnightOutpost[TableMirror[PCE]]; // Huszar Orszem

			if (outpost && DefendedByWPawn(PCE) == 0) { // Nincs fenyegetes
				knights -= outpost * PopCount(DefendedByBPawn(PCE));
			}

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Telt Gyalog
		for (var idx = 0; idx < wPassedPawn.length; idx++)
		{
			PCE = wPassedPawn[idx];
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			pawns += PassedPawnBase[Rank]; // Alap Pont

			if (Rank >= RANKS.RANK_4) {

				pawns += PassedDistanceOwn [DISTANCE[wKing][PCE-8]][Rank]; // Kiraly Tavolsag Sajat
				pawns += PassedDistanceThem[DISTANCE[bKing][PCE-8]][Rank]; // Kiraly Tavolsag Ellenfel

				if (!bBigPieces && UnstoppablePawn(wKing, bKing, xPiecesBB, PCE, WHITE, File-1)) { // Megallithatatlan

					pawns += 900 * (Rank - RANKS.RANK_3) / 5;

				} else if (CHESS_BOARD[PCE-8] == 0) { // Szabad Telt Gyalog

					var unsafe = (bKingAttacks.Low & ~(wKingAttacks.Low | wAttacks.Low)) | bAttacks.Low;
					var front  = { High : WOpenFileMask[BitFixHigh[PCE]], Low : WOpenFileMask[PCE] };
					var rear   = { Low  : BOpenFileMask[BitFixLow[PCE]], High : BOpenFileMask[PCE] };

					if (FreePawn(unsafe, front.Low, rear, xPiecesBB, PCE, BLACK, LOW)) { // Szabad
						pawns += PassedFullFree[Rank];
					}
						pawns += PassedHalfFree[Rank];
				}
			}

			pawns |= 0; // Kerekites
		}

	// Fekete Telt Gyalog
		for (var idx = 0; idx < bPassedPawn.length; idx++)
		{
			PCE = bPassedPawn[idx];
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			pawns -= PassedPawnBase[9-Rank]; // Alap Pont Kozepjatek

			if (Rank <= RANKS.RANK_5) {

				pawns -= PassedDistanceOwn [DISTANCE[bKing][PCE+8]][9-Rank]; // Kiraly Tavolsag Sajat
				pawns -= PassedDistanceThem[DISTANCE[wKing][PCE+8]][9-Rank]; // Kiraly Tavolsag Ellenfel

				if (!wBigPieces && UnstoppablePawn(bKing, wKing, xPiecesBB, PCE, BLACK, File+55)) { // Megallithatatlan

					pawns -= 900 * (RANKS.RANK_6 - Rank) / 5;

				} else if (CHESS_BOARD[PCE+8] == 0) { // Szabad Telt Gyalog

					var unsafe = (wKingAttacks.High & ~(bKingAttacks.High | bAttacks.High)) | wAttacks.High;
					var front  = { Low  : BOpenFileMask[BitFixLow[PCE]], High : BOpenFileMask[PCE] };
					var rear   = { High : WOpenFileMask[BitFixHigh[PCE]], Low : WOpenFileMask[PCE] };

					if (FreePawn(unsafe, front.High, rear, xPiecesBB, PCE, WHITE, HIGH)) { // Szabad
						pawns -= PassedFullFree[9-Rank];
					}
						pawns -= PassedHalfFree[9-Rank];
				}
			}

			pawns |= 0; // Kerekites
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (wCanAttack)
		{
			if (wAttackCount > 4) wAttackCount = 4; // Max 4 tamado

			safety += KingSafetyMull[wAttackCount] * wAttackPower;

			if (bKingRank >= RANKS.RANK_6) { // Pawn shield

				var shield_zone = BKZ.Low & ~(BKZ.Low << 16);

				for (bb = BitBoard[bPawnLow] & shield_zone; bb != 0; bb = restBit(bb)) {

					PCE = firstBitLow(bb);

					if ((WOpenFileMask[PCE] & BitBoard[bPawnLow] & shield_zone) == 0) {

						Rank = TableRanks[PCE];
						File = TableFiles[PCE];

						if (File > FILES.FILE_D) File = 9 - File;

						king -= KingShield[File][9-Rank];
					}
				}
			}
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (bCanAttack)
		{
			if (bAttackCount > 4) bAttackCount = 4; // Max 4 tamado

			safety -= KingSafetyMull[bAttackCount] * bAttackPower;

			if (wKingRank <= RANKS.RANK_3) { // Pawn shield

				var shield_zone = WKZ.High & ~(WKZ.High >>> 16);

				for (bb = BitBoard[wPawnHigh] & shield_zone; bb != 0; bb = restBit(bb)) {

					PCE = firstBitHigh(bb);

					if ((BOpenFileMask[PCE] & BitBoard[wPawnHigh] & shield_zone) == 0) {

						Rank = TableRanks[PCE];
						File = TableFiles[PCE];

						if (File > FILES.FILE_D) File = 9 - File;

						king += KingShield[File][Rank];
					}
				}
			}
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (wNumBishops >= 2) bishops += BishopPair;
		if (bNumBishops >= 2) bishops -= BishopPair;

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var tempo = currentPlayer === WHITE ? TempoBonus : -TempoBonus;

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var material = brd_Material[WHITE] - brd_Material[BLACK] + posScore;

		var Score = material;

		Score += mobScore;
		Score += threats;
		Score += safety;
		Score += tempo;
		Score += pawns;
		Score += knights;
		Score += bishops;
		Score += rooks;
		Score += queens;
		Score += king;

		if (Phase < 0) { // Minden babu a fedelzeten = 0
			Phase = 0;
		}

		Phase = (Phase << 8) / 24 + 0.5 | 0; // Jatek fazis

		// Linearis interpolacio kezdo es vegjatek kozott..

		Score = ((MG_SC(Score) * (256 - Phase)) + (EG_SC(Score) * Phase)) >> 8;

		Score = Score / Draw | 0; // Ketes dontetlennel nem 0-at adunk vissza!

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (ShowEvalForUI === true) {
			return '\n'
			+' Eval term |       MG       |       EG       |\n'
			+'-----------|----------------|----------------|\n'
			+' tempo     |'+evalStr(tempo)               +'|\n'
			+' pawns     |'+evalStr(pawns)               +'|\n'
			+' knights   |'+evalStr(knights)             +'|\n'
			+' bishops   |'+evalStr(bishops)             +'|\n'
			+' rooks     |'+evalStr(rooks)               +'|\n'
			+' queens    |'+evalStr(queens)              +'|\n'
			+' king      |'+evalStr(king)                +'|\n'
			+' safety    |'+evalStr(safety)              +'|\n'
			+' threats   |'+evalStr(threats)             +'|\n'
			+' mobility  |'+evalStr(mobScore)            +'|\n'
			+' material  |'+evalStr(material)            +'|\n'
			+'-----------|----------------|----------------|\n'
			+' Total Eval: '+(Score / 100).toFixed(2);
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		return currentPlayer === WHITE ? Score : -Score;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function UnstoppablePawn(usKing, themKing, xPiecesBB, sq, us, promSq) {

		var front = us ? { Low  : BOpenFileMask[BitFixLow[sq]], High : BOpenFileMask[sq] }
		               : { High : WOpenFileMask[BitFixHigh[sq]], Low : WOpenFileMask[sq] };

		if ((xPiecesBB.Low & front.Low) | (xPiecesBB.High & front.High)) return false; // blocked

		if (DISTANCE[usKing][sq] <= 1 && DISTANCE[usKing][promSq] <= 1) return true; // king controls promotion path

		if (DISTANCE[sq][promSq] < DISTANCE[themKing][promSq] + ((currentPlayer == us)|0) - 1) return true; // unstoppable

		return false;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function FreePawn(unsafe, front, rear, xPiecesBB, sq, them, bit) {

		if (front & (unsafe | BitBoard[them << 1 | bit])) return false; // unsafe or blocked!

		// major attackers from behind..?
		rear.Low  &= BitBoard[(them|ROOK) << 1 | LOW]  | BitBoard[(them|QUEEN) << 1 | LOW];
		rear.High &= BitBoard[(them|ROOK) << 1 | HIGH] | BitBoard[(them|QUEEN) << 1 | HIGH];

		for (var bb = rear.Low;  bb != 0; bb = restBit(bb)) if (LineIsEmpty(firstBitLow(bb),  sq, xPiecesBB) == 0) return false;
		for (var bb = rear.High; bb != 0; bb = restBit(bb)) if (LineIsEmpty(firstBitHigh(bb), sq, xPiecesBB) == 0) return false;

		return true;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function CaptureScore(attacks, pawnSafe, pce, them) {

		var weak = { Low  : attacks.Low  & BitBoard[them << 1 | LOW]  & ~BitBoard[(them|PAWN) << 1 | LOW],
		             High : attacks.High & BitBoard[them << 1 | HIGH] & ~BitBoard[(them|PAWN) << 1 | HIGH] };

		if ((weak.Low | weak.High) == 0) return 0; // no threats!

		if (pce >= ROOK) {
			weak.Low  &= pawnSafe.Low  & ~BitBoard[(them|pce) << 1 | LOW]; // Not equal and not defended by pawn..
			weak.High &= pawnSafe.High & ~BitBoard[(them|pce) << 1 | HIGH];

			if (pce == ROOK) {
				weak.Low  |= attacks.Low  & BitBoard[(them|QUEEN) << 1 | LOW]; // ..or Queen attacked by Rook!
				weak.High |= attacks.High & BitBoard[(them|QUEEN) << 1 | HIGH];
			}
		}

		var sc = 0;
		for (var bb = weak.Low;  bb != 0; bb = restBit(bb)) sc += ThreatScore[pce][CHESS_BOARD[firstBitLow(bb)]  & 0x07];
		for (var bb = weak.High; bb != 0; bb = restBit(bb)) sc += ThreatScore[pce][CHESS_BOARD[firstBitHigh(bb)] & 0x07];

		return sc;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function PawnCapture(attacks, them) {

		var weak = { Low  : attacks.Low  & BitBoard[them << 1 | LOW]  & ~BitBoard[(them|PAWN) << 1 | LOW],
		             High : attacks.High & BitBoard[them << 1 | HIGH] & ~BitBoard[(them|PAWN) << 1 | HIGH] };

		var sc = 0;
		for (var bb = weak.Low;  bb != 0; bb = restBit(bb)) sc += ThreatScore[PAWN][CHESS_BOARD[firstBitLow(bb)]  & 0x07];
		for (var bb = weak.High; bb != 0; bb = restBit(bb)) sc += ThreatScore[PAWN][CHESS_BOARD[firstBitHigh(bb)] & 0x07];

		return sc;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function EvalPawns(wPassedPawn, bPassedPawn) {

		var PCE   = 0;
		var Score = 0;

		var pieceIdx = WHITE_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			var Open = 0; // Nyitott
			var Rank = TableRanks[PCE];
			var File = TableFiles[PCE];

			if (BlackOpenFile(PCE) != 0) { // Dupla Gyalog
				Score += PawnDoubled;
			}

			if (WhiteOpenFile(PCE) == 0 && WhiteMostPawn(PCE) == 0) { // Legelso Gyalog + Nyitott
				Open = 1;
			}

			if (IsolatedPawn(PCE, WHITE) == 0) { // Elkulonitett Gyalog
				Score += PawnIsolated + PawnIsolatedOpen * Open;
			} else if (WhiteBackwardPawn(PCE) == 0 && WhiteBackwardControl(PCE, Rank)) { // Hatrahagyott Gyalog
				Score += PawnBackward + PawnBackwardOpen * Open;
			}

			if (Open) {
				if (WhitePassedPawn(PCE) == 0) { // Telt Gyalog

					wPassedPawn[wPassedPawn.length] = PCE;

				} else if (WhiteCandidatePawn(PCE)) { // Jelolt Gyalog

					Score += CandidatePawn[Rank];
				}
			}

			Score += PawnPst[PCE];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var pieceIdx = BLACK_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			var Open = 0; // Nyitott
			var Rank = TableRanks[PCE];
			var File = TableFiles[PCE];

			if (WhiteOpenFile(PCE) != 0) { // Dupla Gyalog
				Score -= PawnDoubled;
			}

			if (BlackOpenFile(PCE) == 0 && BlackMostPawn(PCE) == 0) { // Legelso Gyalog + Nyitott
				Open = 1;
			}

			if (IsolatedPawn(PCE, BLACK) == 0) { // Elkulonitett Gyalog
				Score -= PawnIsolated + PawnIsolatedOpen * Open;
			} else if (BlackBackwardPawn(PCE) == 0 && BlackBackwardControl(PCE, Rank)) { // Hatrahagyott Gyalog
				Score -= PawnBackward + PawnBackwardOpen * Open;
			}

			if (Open) {
				if (BlackPassedPawn(PCE) == 0) { // Telt Gyalog

					bPassedPawn[bPassedPawn.length] = PCE;

				} else if (BlackCandidatePawn(PCE)) { // Jelolt Gyalog

					Score -= CandidatePawn[9-Rank];
				}
			}

			Score -= PawnPst[TableMirror[PCE]];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

		return Score;
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

		var us = fromPiece & 0x8; // Mi
		var them = us^8; // Ellenfel

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Ellenfel Gyalog Tamadas
		if (us === BLACK ? DefendedByWPawn(to) : DefendedByBPawn(to)) {
			return false;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var bb, pieceType;
		var SeePieces = GetAllPce(); // Osszes Babu
		var attackers = { Low : 0, High : 0 }; // Tamadok
		var captureDeficit = fromValue - toValue; // Deficit

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		SeeRemovePiece(from, attackers, SeePieces); // Babu torlese

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Huszar, Futo, Bastya, Vezer Tamadasok
		// Ha az ellenfel letud utni, es kisebb a nyereseg,
		// mint a tamado babu erteke, akkor nem folytatjuk!
		for (pieceType = KNIGHT; pieceType <= QUEEN; pieceType++)
		{
			SeeAddAttacks(to, pieceType, attackers, SeePieces);

			if (captureDeficit > SeeValue[pieceType]
			&& (attackers.Low  & BitBoard[(them|pieceType) << 1 | LOW]
			 || attackers.High & BitBoard[(them|pieceType) << 1 | HIGH])) {
				return false;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
		// Ezen a ponton biztos, hogy rossz az utes, DE az ellenfel meg nem tudott gyozni.
		// El kell dontetni, hogy gyoztes vagy egyenlo merteku allast kitudunk-e harcolni!
		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Sajat Gyalog Vedelem
		if (us === BLACK ? DefendedByBPawn(to) : DefendedByWPawn(to)) {
			return true;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Kiraly tamadasok hozzadasa
		SeeAddAttacks(to, KING, attackers, SeePieces);

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
			var capturingPieceValue = -1;
			var capturingPieceIndex = -1;

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// A ellenfel legkevesbe ertekes babuja, aki tamadni tudja a mezot
			for (pieceType = KNIGHT; pieceType <= KING; pieceType++)
			{
				if (bb = attackers.Low  & BitBoard[(them|pieceType) << 1 | LOW]) {
					capturingPieceIndex = firstBitLow(bb);
					capturingPieceValue = SeeValue[pieceType];
					break;
				}
				if (bb = attackers.High & BitBoard[(them|pieceType) << 1 | HIGH]) {
					capturingPieceIndex = firstBitHigh(bb);
					capturingPieceValue = SeeValue[pieceType];
					break;
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

			SeeRemovePiece(capturingPieceIndex, attackers, SeePieces);

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Rontgen tamadasok hozzadasa
			SeeAddXrayAttack(to, capturingPieceIndex, attackers, SeePieces);

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Mi fogunk tamadni
			capturingPieceValue = -1;
			capturingPieceIndex = -1;

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// A legkevesbe ertekes babunk, aki tamadni tudja a mezot
			for (pieceType = KNIGHT; pieceType <= KING; pieceType++)
			{
				if (bb = attackers.Low  & BitBoard[(us|pieceType) << 1 | LOW]) {
					capturingPieceIndex = firstBitLow(bb);
					capturingPieceValue = SeeValue[pieceType];
					break;
				}
				if (bb = attackers.High & BitBoard[(us|pieceType) << 1 | HIGH]) {
					capturingPieceIndex = firstBitHigh(bb);
					capturingPieceValue = SeeValue[pieceType];
					break;
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

			SeeRemovePiece(capturingPieceIndex, attackers, SeePieces);

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			// Rontgen tamadasok hozzadasa
			SeeAddXrayAttack(to, capturingPieceIndex, attackers, SeePieces);
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function SeeRemovePiece(sq, attackBB, seePiece) {
		if (HighSQMask[sq]) {
			seePiece.High &= ClearMask[sq];
			attackBB.High &= ClearMask[sq];
		} else {
			seePiece.Low &= ClearMask[sq];
			attackBB.Low &= ClearMask[sq];
		}
	}

	function SeeAddXrayAttack(target, lastAttacker, attackBB, SeePieces) {
		var bb, from;
		var behind = Behind(target, lastAttacker); // Utolso tamado mogotti mezok!

		// Az elso akadaly nelkuli tamado mentese utan kilepunk, ezzel idot nyerunk. ;-)
		// Ha nincs mogotte mezo (Huszar & Sarkok), akkor a for ciklusok nem indulnak el.

		// Futo & Vezer Tamadas
		var attacks = PceAttacks(BISHOP, target);
		attacks.Low  &= BitBoard[wBishopLow]  | BitBoard[bBishopLow]  | BitBoard[wQueenLow]  | BitBoard[bQueenLow];
		attacks.High &= BitBoard[wBishopHigh] | BitBoard[bBishopHigh] | BitBoard[wQueenHigh] | BitBoard[bQueenHigh];

		for (bb = attacks.Low & behind.Low & SeePieces.Low; bb != 0; bb = restBit(bb)) {
			from = firstBitLow(bb);
			if (LineIsEmpty(from, target, SeePieces) == 0) { attackBB.Low |= SetMask[from]; return; }
		}
		for (bb = attacks.High & behind.High & SeePieces.High; bb != 0; bb = restBit(bb)) {
			from = firstBitHigh(bb);
			if (LineIsEmpty(from, target, SeePieces) == 0) { attackBB.High |= SetMask[from]; return; }
		}

		// Bastya & Vezer Tamadas
		attacks = PceAttacks(ROOK, target);
		attacks.Low  &= BitBoard[wRookLow]  | BitBoard[bRookLow]  | BitBoard[wQueenLow]  | BitBoard[bQueenLow];
		attacks.High &= BitBoard[wRookHigh] | BitBoard[bRookHigh] | BitBoard[wQueenHigh] | BitBoard[bQueenHigh];

		for (bb = attacks.Low & behind.Low & SeePieces.Low; bb != 0; bb = restBit(bb)) {
			from = firstBitLow(bb);
			if (LineIsEmpty(from, target, SeePieces) == 0) { attackBB.Low |= SetMask[from]; return; }
		}
		for (bb = attacks.High & behind.High & SeePieces.High; bb != 0; bb = restBit(bb)) {
			from = firstBitHigh(bb);
			if (LineIsEmpty(from, target, SeePieces) == 0) { attackBB.High |= SetMask[from]; return; }
		}
	}

	function SeeAddAttacks(target, Piece, attackBB, SeePieces) {
		var bb, from;
		var attacks = PceAttacks(Piece, target);
		attacks.Low  &= BitBoard[Piece << 1 | LOW]  | BitBoard[(BLACK|Piece) << 1 | LOW];
		attacks.High &= BitBoard[Piece << 1 | HIGH] | BitBoard[(BLACK|Piece) << 1 | HIGH];

		for (bb = attacks.Low & SeePieces.Low; bb != 0; bb = restBit(bb)) {
			from = firstBitLow(bb);
			if (LineIsEmpty(from, target, SeePieces) == 0) { attackBB.Low |= SetMask[from]; }
		}
		for (bb = attacks.High & SeePieces.High; bb != 0; bb = restBit(bb)) {
			from = firstBitHigh(bb);
			if (LineIsEmpty(from, target, SeePieces) == 0) { attackBB.High |= SetMask[from]; }
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function GenerateAllMoves(capturesOnly, useSee) {

		var pieceType = 0; // Akivel lepunk
		var pieceIdx  = 0; // Babu indexeles
		var from      = 0; // Ahonnan lepunk
		var next      = 0; // Ahova lepunk
		var Score     = 0; // Lepes pont
		var Move      = 0; // Lepes bit
		var bb        = 0; // BitBoard

		brd_moveStart[boardPly + 1] = brd_moveStart[boardPly]; // Hack

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var xPiecesBB = GetAllPce();
		var inc = currentPlayer ? 8 : -8;
		var enemy = AllPceByColor(currentPlayer^8);
		var StartRank   = currentPlayer ? RANKS.RANK_7 : RANKS.RANK_2;
		var PromoteRank = currentPlayer ? RANKS.RANK_2 : RANKS.RANK_7;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Gyalog lepesek
		pieceIdx = (currentPlayer|PAWN) << 4;
		from = brd_pieceList[pieceIdx++];
		while (from != EMPTY)
		{
			next = from + inc; // Elore lepes

			if (capturesOnly === false) // Ures mezok
			{
				if (CHESS_BOARD[next] == 0) // Ures mezo
				{
					if (TableRanks[from] == PromoteRank) // Gyalog bevaltas
					{
						AddQuietMove(from, next, (currentPlayer|QUEEN), 0);
						AddQuietMove(from, next, (currentPlayer|ROOK),  0);
						AddQuietMove(from, next, (currentPlayer|BISHOP), 0);
						AddQuietMove(from, next, (currentPlayer|KNIGHT), 0);
					} else {
						AddQuietMove(from, next, 0, 0); // Sima lepes

						if (TableRanks[from] == StartRank && CHESS_BOARD[next + inc] == 0) // Dupla lepes
						{
							AddQuietMove(from, next + inc, 0, 0);
						}
					}
				}
			} else if (CHESS_BOARD[next] == 0 && TableRanks[from] == PromoteRank) { // Vezer Promocio (Quiescence)

				AddQuietMove(from, next, (currentPlayer|QUEEN), 0);
			}

			for (bb = NeighbourMask[next]; bb != 0; bb = restBit(bb)) // Tamadasok
			{
				next = HighSQMask[next] ? firstBitHigh(bb) : firstBitLow(bb); // from [+-] 7/9

				if (CHESS_BOARD[next] && (CHESS_BOARD[next] & 0x8) !== currentPlayer) // Ellenfel
				{
					Score = 1000005 + (100 * MvvLvaScores[CHESS_BOARD[next]]); // Pontszam

					if (TableRanks[from] == PromoteRank) // Gyalog bevaltas
					{
						AddCaptureMove(BIT_MOVE(from, next, 1, (currentPlayer|QUEEN), 0), Score);
						AddCaptureMove(BIT_MOVE(from, next, 1, (currentPlayer|ROOK),  0), Score);
						AddCaptureMove(BIT_MOVE(from, next, 1, (currentPlayer|BISHOP), 0), Score);
						AddCaptureMove(BIT_MOVE(from, next, 1, (currentPlayer|KNIGHT), 0), Score);
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

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (capturesOnly === false) // Sancolas: indulast es erkezest mashol ellenorizzuk!
		{
			if (currentPlayer === WHITE) // Feher oldal
			{
				if (castleRights & CASTLEBIT.WK) { // Kiraly oldal
					if (CHESS_BOARD[SQUARES.F1] == 0 && CHESS_BOARD[SQUARES.G1] == 0) {
						if (!isSquareUnderAttack(SQUARES.F1, WHITE)) {
							AddQuietMove(SQUARES.E1, SQUARES.G1, 0, 1);
						}
					}
				}
				if (castleRights & CASTLEBIT.WQ) { // Vezer oldal
					if (CHESS_BOARD[SQUARES.D1] == 0 && CHESS_BOARD[SQUARES.C1] == 0 && CHESS_BOARD[SQUARES.B1] == 0) {
						if (!isSquareUnderAttack(SQUARES.D1, WHITE)) {
							AddQuietMove(SQUARES.E1, SQUARES.C1, 0, 1);
						}
					}
				}

			} else { // Fekete oldal

				if (castleRights & CASTLEBIT.BK) { // Kiraly oldal
					if (CHESS_BOARD[SQUARES.F8] == 0 && CHESS_BOARD[SQUARES.G8] == 0) {
						if (!isSquareUnderAttack(SQUARES.F8, BLACK)) {
							AddQuietMove(SQUARES.E8, SQUARES.G8, 0, 1);
						}
					}
				}
				if (castleRights & CASTLEBIT.BQ) { // Vezer oldal
					if (CHESS_BOARD[SQUARES.D8] == 0 && CHESS_BOARD[SQUARES.C8] == 0 && CHESS_BOARD[SQUARES.B8] == 0) {
						if (!isSquareUnderAttack(SQUARES.D8, BLACK)) {
							AddQuietMove(SQUARES.E8, SQUARES.C8, 0, 1);
						}
					}
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Huszar, Futo, Bastya, Vezer, Kiraly
		for (pieceType = KNIGHT; pieceType <= KING; pieceType++)
		{
			pieceIdx = (currentPlayer | pieceType) << 4;
			from = brd_pieceList[pieceIdx++];
			while (from != EMPTY)
			{
				var attacks = AttacksFrom(pieceType, from, xPiecesBB);

				for (bb = attacks.Low & enemy.Low; bb != 0; bb = restBit(bb)) // Tamadas
				{
					next = firstBitLow(bb); Move = BIT_MOVE(from, next, 1, 0, 0);

					if (useSee && !See(Move))
					Score =     106 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam
					else
					Score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam

					AddCaptureMove(Move, Score);
				}
				for (bb = attacks.High & enemy.High; bb != 0; bb = restBit(bb)) // Tamadas
				{
					next = firstBitHigh(bb); Move = BIT_MOVE(from, next, 1, 0, 0);

					if (useSee && !See(Move))
					Score =     106 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam
					else
					Score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam

					AddCaptureMove(Move, Score);
				}

				if (capturesOnly === false) // Ures mezok
				{
					for (bb = attacks.Low & ~xPiecesBB.Low; bb != 0; bb = restBit(bb)) {
						next = firstBitLow(bb);
						AddQuietMove(from, next, 0, 0);
					}
					for (bb = attacks.High & ~xPiecesBB.High; bb != 0; bb = restBit(bb)) {
						next = firstBitHigh(bb);
						AddQuietMove(from, next, 0, 0);
					}
				}

				from = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
			}
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function GenerateEvasions() {

		var bb     = 0; // BitBoard
		var Score  = 0; // Lepes pont
		var next   = 0; // Ahova lepunk
		var from   = 0; // Ahonnan lepunk
		var b      = { Low : 0, High : 0 };
		var checks = { Low : 0, High : 0 };
		var unsafe = { Low : 0, High : 0 };

		brd_moveStart[boardPly + 1] = brd_moveStart[boardPly]; // Hack

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var them = currentPlayer^8;
		var xPiecesBB = GetAllPce();
		var friendsBB = AllPceByColor(currentPlayer);
		var King = brd_pieceList[(currentPlayer|KING) << 4];
		var front = currentPlayer === BLACK ? King + 8 : King - 8;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Gyalog tamadas
		HighSQMask[front] ? checks.High |= NeighbourMask[front] & BitBoard[(them|PAWN) << 1 | HIGH]
		                  : checks.Low  |= NeighbourMask[front] & BitBoard[(them|PAWN) << 1 | LOW];

		// Huszar tamadas
		bb = PceAttacks(KNIGHT, King);
		checks.Low  |= bb.Low  & BitBoard[(them|KNIGHT) << 1 | LOW];
		checks.High |= bb.High & BitBoard[(them|KNIGHT) << 1 | HIGH];

		// Futo & Vezer tamadas
		bb = PceAttacks(BISHOP, King);
		b.Low  |= bb.Low  & (BitBoard[(them|BISHOP) << 1 | LOW]  | BitBoard[(them|QUEEN) << 1 | LOW]);
		b.High |= bb.High & (BitBoard[(them|BISHOP) << 1 | HIGH] | BitBoard[(them|QUEEN) << 1 | HIGH]);

		// Bastya & Vezer tamadas
		bb = PceAttacks(ROOK, King);
		b.Low  |= bb.Low  & (BitBoard[(them|ROOK) << 1 | LOW]  | BitBoard[(them|QUEEN) << 1 | LOW]);
		b.High |= bb.High & (BitBoard[(them|ROOK) << 1 | HIGH] | BitBoard[(them|QUEEN) << 1 | HIGH]);

		for (bb = b.Low; bb != 0; bb = restBit(bb)) {
			from = firstBitLow(bb);
			if (LineIsEmpty(from, King, xPiecesBB) == 0) {
				checks.Low  |= SetMask[from];
				unsafe.Low  |= BetweenBBMask[BetweenBBidx(from, King, LOW)]  | BehindBBMask[BetweenBBidx(from, King, LOW)];
				unsafe.High |= BetweenBBMask[BetweenBBidx(from, King, HIGH)] | BehindBBMask[BetweenBBidx(from, King, HIGH)];
			}
		}
		for (bb = b.High; bb != 0; bb = restBit(bb)) {
			from = firstBitHigh(bb);
			if (LineIsEmpty(from, King, xPiecesBB) == 0) {
				checks.High |= SetMask[from];
				unsafe.Low  |= BetweenBBMask[BetweenBBidx(from, King, LOW)]  | BehindBBMask[BetweenBBidx(from, King, LOW)];
				unsafe.High |= BetweenBBMask[BetweenBBidx(from, King, HIGH)] | BehindBBMask[BetweenBBidx(from, King, HIGH)];
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Kiraly lepesei
		var attacks = PceAttacks(KING, King);
		for (bb = attacks.Low & ~unsafe.Low & ~friendsBB.Low; bb != 0; bb = restBit(bb)) {

			if (CHESS_BOARD[next = firstBitLow(bb)] != 0) // Ellenfel
			{
				Score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[KING]); // Pontszam

				AddCaptureMove(BIT_MOVE(King, next, 1, 0, 0), Score);
			} else {
				AddQuietMove(King, next, 0, 0); // Ures mezo
			}
		}
		for (bb = attacks.High & ~unsafe.High & ~friendsBB.High; bb != 0; bb = restBit(bb)) {

			if (CHESS_BOARD[next = firstBitHigh(bb)] != 0) // Ellenfel
			{
				Score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[KING]); // Pontszam

				AddCaptureMove(BIT_MOVE(King, next, 1, 0, 0), Score);
			} else {
				AddQuietMove(King, next, 0, 0); // Ures mezo
			}
		}

		if ((PopCount(checks.Low) + PopCount(checks.High)) > 1) return; // Dupla Sakknal csak a Kiraly lephet :(

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var checkSQ = checks.Low ? firstBitLow(checks.Low) : firstBitHigh(checks.High); // Tamado mezo!

		var target = { // Kiraly es az egyetlen tamado kozotti mezok + tamado!
		Low  : BetweenBBMask[BetweenBBidx(checkSQ, King, LOW)]  | checks.Low,
		High : BetweenBBMask[BetweenBBidx(checkSQ, King, HIGH)] | checks.High };

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Gyalog lepesek
		var inc = currentPlayer ? 8 : -8;
		var StartRank   = currentPlayer ? RANKS.RANK_7 : RANKS.RANK_2;
		var PromoteRank = currentPlayer ? RANKS.RANK_2 : RANKS.RANK_7;

		var pieceIdx = (currentPlayer|PAWN) << 4;
		from = brd_pieceList[pieceIdx++];
		while (from != EMPTY)
		{
			next = from + inc; // Elore lepes

			if (CHESS_BOARD[next] == 0) // Ures mezo
			{
				bb = HighSQMask[next] ? target.High : target.Low;

				if (bb & SetMask[next]) // Blokkolas
				{
					if (TableRanks[from] == PromoteRank) // Gyalog bevaltas
					{
						AddQuietMove(from, next, (currentPlayer|QUEEN), 0);
						AddQuietMove(from, next, (currentPlayer|ROOK),  0);
						AddQuietMove(from, next, (currentPlayer|BISHOP), 0);
						AddQuietMove(from, next, (currentPlayer|KNIGHT), 0);
					} else {
						AddQuietMove(from, next, 0, 0); // Sima lepes
					}
				}
				// Blokkolas dupla lepessel
				if ((bb & SetMask[next + inc]) && TableRanks[from] == StartRank && CHESS_BOARD[next + inc] == 0)
				{
					AddQuietMove(from, next + inc, 0, 0);
				}
			}

			for (bb = NeighbourMask[next]; bb != 0; bb = restBit(bb)) // Tamadasok
			{
				next = HighSQMask[next] ? firstBitHigh(bb) : firstBitLow(bb); // from [+-] 7/9

				if (next == checkSQ) // Sakkado babu tamadasa
				{
					Score = 1000005 + (100 * MvvLvaScores[CHESS_BOARD[next]]); // Pontszam

					if (TableRanks[from] == PromoteRank) // Gyalog bevaltas
					{
						AddCaptureMove(BIT_MOVE(from, next, 1, (currentPlayer|QUEEN), 0), Score);
						AddCaptureMove(BIT_MOVE(from, next, 1, (currentPlayer|ROOK),  0), Score);
						AddCaptureMove(BIT_MOVE(from, next, 1, (currentPlayer|BISHOP), 0), Score);
						AddCaptureMove(BIT_MOVE(from, next, 1, (currentPlayer|KNIGHT), 0), Score);
					} else {
						AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), Score); // Nincs gyalogbevaltas
					}
				} else if (EN_PASSANT != 0 && EN_PASSANT == next && (EN_PASSANT - inc) == checkSQ) { // En Passant

					Score = 1000105; // En Passant Pontszam

					AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), Score);
				}
			}

			from = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Huszar, Futo, Bastya, Vezer (Kiralyt nem nezzuk ujra!)
		for (var pieceType = KNIGHT; pieceType <= QUEEN; pieceType++)
		{
			pieceIdx = (currentPlayer | pieceType) << 4;
			from = brd_pieceList[pieceIdx++];
			while (from != EMPTY)
			{
				var attacks = AttacksFrom(pieceType, from, xPiecesBB);

				for (bb = attacks.Low & target.Low; bb != 0; bb = restBit(bb)) // Tamadas & Blokkolas
				{
					next = firstBitLow(bb);

					if (next == checkSQ) // Sakkado babu tamadasa
					{
						Score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam

						AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), Score);
					} else {
						AddQuietMove(from, next, 0, 0); // Blokkolas
					}
				}
				for (bb = attacks.High & target.High; bb != 0; bb = restBit(bb)) // Tamadas & Blokkolas
				{
					next = firstBitHigh(bb);

					if (next == checkSQ) // Sakkado babu tamadasa
					{
						Score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam

						AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), Score);
					} else {
						AddQuietMove(from, next, 0, 0); // Blokkolas
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
		for (var index = moveNum; index < brd_moveStart[boardPly + 1]; index++) {
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
		var currentTime = Date.now() - startTime;
		if (currDepth >= 2 && currentTime >= minSearchTime) {
			if (!ScoreDrop || currentTime >= maxSearchTime) {
				timeStop = 1;
			}
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function Quiescence(alpha, beta, depth, inCheck, pv) {

		if ((nodes & 2047) == 0) { // Ido ellenorzese
			CheckUp();
		}

		nodes++; // Csomopontok novelese

		pv[0] = NOMOVE; // Hack: Pv torlese

		if (IsRepetition()) { // Lepesismetles
			return 0;
		}

		if (boardPly >= maxDepth) { // Melyseg limit
			return Evaluation();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var BestScore = -INFINITE;

		if (depth == DEPTH_ZERO) { // Atultetesi tabla

			var hashData = ProbeHash();

			if (hashData != NOMOVE) {

				BestScore = inCheck ? -INFINITE : hashData.eval;

				var value = hashData.score;

				if (value > ISMATE) {
					value -= boardPly;
				} else if (value < -ISMATE) {
					value += boardPly;
				}

				if (hashData.flags == FLAG_ALPHA && value <= alpha) return value;
				if (hashData.flags == FLAG_BETA  && value >= beta)  return value;
				if (hashData.flags == FLAG_EXACT) return value;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (!inCheck && BestScore == -INFINITE) { // Ertekeles
			BestScore = Evaluation();
		}

		if (!inCheck && BestScore >= beta) { // Vagas
			return BestScore;
		}

		if (!inCheck && BestScore > alpha) { // Update alpha
			alpha = BestScore;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var is_pv = (beta != alpha + 1);
		var newPv = new Array(maxDepth);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var Score = -INFINITE; // Pont nullazas
		var Check = NOT_IN_CHECK; // Sakk lepes
		var capturedPCE = NOMOVE; // Leutott babu
		var currentMove = NOMOVE; // Aktualis lepes
		var DeltaMargin = BestScore + 100; // Delta Margo
		inCheck ? GenerateEvasions() : GenerateAllMoves(true, false);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; index++)
		{
			PickNextMove(index);

			currentMove = brd_moveList[index];
			capturedPCE = CHESS_BOARD[TOSQ(currentMove)];

			Check = givesCheck(currentMove);

			if (!inCheck && !Check && !PROMOTED(currentMove) && (capturedPCE & 0x07) !== QUEEN) // Delta metszes
			{
				var FutileValue = DeltaMargin + DeltaValue[capturedPCE ? capturedPCE : PAWN]; // En Passant..?

				if (FutileValue <= alpha) {
					if (FutileValue > BestScore) {
						BestScore = FutileValue;
					}
					continue;
				}
			}

			if (!inCheck && !See(currentMove)) { // Rossz utes
				continue;
			}

			if (!isLegal(currentMove)) { // Ervenytelen lepes
				continue;
			}

			makeMove(currentMove); // Lepes ervenyesitese

			Score = -Quiescence(-beta, -alpha, depth-1, Check, newPv);

			unMakeMove(); // Lepes visszavonasa

			if (timeStop == 1) { // Ido vagas
				return 0;
			}

			if (Score > BestScore) {
				BestScore = Score;
				if (Score > alpha) {
					if (is_pv) {
						BuildPv(pv, newPv, currentMove);
					}
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


	function AlphaBeta(alpha, beta, depth, nullMove, inCheck, pv) {

		if (depth <= DEPTH_ZERO) { // Melyseg eleresekor kiertekeles
			return Quiescence(alpha, beta, DEPTH_ZERO, inCheck, pv);
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if ((nodes & 2047) == 0) { // Ido ellenorzese
			CheckUp();
		}

		nodes++; // Csomopontok novelese

		pv[0] = NOMOVE; // Hack: Pv torlese

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
		var staticEval = -INFINITE;
		var is_pv = (beta != alpha + 1);
		var newPv = new Array(maxDepth);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var hashData = ProbeHash(); // Atultetesi tabla
		var hashMove = hashData != NOMOVE ? hashData.move : NOMOVE;

		if (!is_pv && hashData != NOMOVE) {

			staticEval = hashData.eval;

			if (hashData.depth >= depth) {

				var value = hashData.score;

				if (value > ISMATE) {
					value -= boardPly;
				} else if (value < -ISMATE) {
					value += boardPly;
				}

				if (hashData.flags == FLAG_ALPHA && value <= alpha) return value;
				if (hashData.flags == FLAG_BETA  && value >= beta)  return value;
				if (hashData.flags == FLAG_EXACT) return value;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (!is_pv && !inCheck
		&& (brd_pieceCount[currentPlayer | KNIGHT] != 0
		 || brd_pieceCount[currentPlayer | BISHOP] != 0
		 || brd_pieceCount[currentPlayer | ROOK]   != 0
		 || brd_pieceCount[currentPlayer | QUEEN]  != 0)) { // Metszheto csomopont

			if (staticEval == -INFINITE && (nullMove || depth <= 4)) { // Futility depth
				staticEval = Evaluation();
			}

			pruneNode = true;
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

				Score = depth <= 4 ? -Quiescence(-beta, -beta+1, DEPTH_ZERO, NOT_IN_CHECK, newPv)
				                   :  -AlphaBeta(-beta, -beta+1, depth-4, 0, NOT_IN_CHECK, newPv);

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
					Score = Quiescence(threshold-1, threshold, DEPTH_ZERO, NOT_IN_CHECK, newPv);
					if (Score < threshold) return Score;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (is_pv && boardPly != 0 && depth >= 4 && hashMove == NOMOVE) { // Belso iterativ melyites /IID/
			Score = AlphaBeta(alpha, beta, depth-2, 0, inCheck, newPv);
			if (Score > alpha) hashMove = newPv[0];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		Score = -INFINITE; // Pont nullazas
		var E = 0; // Kiterjesztes valtozo
		var R = 0; // LMR Dinamikus valtozo
		var LegalMove = 0; // Ervenyes lepes
		var moveScore = 0; // Lepes pontszama
		var OldAlpha = alpha; // Alpha mentese
		var BestMove = NOMOVE; // Legjobb lepes
		var dangerous = false; // Veszelyes..??
		var Check = NOT_IN_CHECK; // Sakk lepes
		var currentMove = NOMOVE; // Aktualis lepes
		var BestScore = -INFINITE; // Legjobb pontszam
		var PlayedMoves = new Array(); // Lepesek tomb
		var FutileValue = staticEval + depth * 100; // Futile ertek
		inCheck ? GenerateEvasions() : GenerateAllMoves(false, true);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (hashMove != NOMOVE) { // Atultetesi tablabol lepes
			for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; index++)
			{
				if (brd_moveList[index] == hashMove) { // Elore soroljuk
					brd_moveScores[index] = 2000000;
					break;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; index++)
		{
			PickNextMove(index);

			currentMove = brd_moveList[index];
			moveScore = brd_moveScores[index];
			Check = givesCheck(currentMove);

			dangerous = !LegalMove || inCheck || Check || moveScore >= 800000 || (currentMove & DANGER_MASK) || PawnPush(currentMove);

			if (!dangerous && depth <= 2 && pruneNode && !isMate(BestScore) && LegalMove > depth*5) { // Late Move Pruning
				continue;
			}

			if (!dangerous && depth <= 4 && pruneNode && !isMate(BestScore) && FutileValue < alpha) { // Futility Pruning
				continue;
			}

			if (!isLegal(currentMove)) { // Ervenytelen lepes
				continue;
			}

			makeMove(currentMove); // Lepes ervenyesitese

			E = 0; // "E" nullazasa
			R = 0; // "R" nullazasa

			if (inCheck && (is_pv || depth < 5)) { // Sakk kiterjesztes
				E = 1;
			}

			if (!dangerous && depth >= 3 && LegalMove >= 3) // Late Move Reduction
			{
				R = is_pv ? 0.00 + Math.log(depth) * Math.log(Math.min(LegalMove, 63)) / 3.00 | 0
				          : 0.33 + Math.log(depth) * Math.log(Math.min(LegalMove, 63)) / 2.25 | 0;
			}

			if ((is_pv && LegalMove != 0) || R != 0) {
				Score = -AlphaBeta(-alpha-1, -alpha, depth+E-R-1, 1, Check, newPv); // PVS-LMR
				if (Score > alpha) {
					Score = -AlphaBeta(-beta, -alpha, depth+E-1, 1, Check, newPv); // Full
				}
			} else {
				Score = -AlphaBeta(-beta, -alpha, depth+E-1, 1, Check, newPv); // Full
			}

			PlayedMoves[LegalMove++] = currentMove; // Ervenyes lepesek

			unMakeMove(); // Lepes visszavonasa

			if (timeStop == 1) { // Ido vagas
				return 0;
			}

			if (Score > BestScore) {

				BestScore = Score;

				if (is_pv && (LegalMove == 1 || Score > alpha)) {

					BuildPv(pv, newPv, currentMove);

					if (boardPly == 0) {
						UpdatePv(currentMove, Score, depth, alpha, beta, pv);
					}
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

						StoreHash(currentMove, Score, staticEval, FLAG_BETA, depth);

						return Score;
					}
					alpha = Score;
					BestMove = currentMove;
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
			StoreHash(BestMove, BestScore, staticEval, FLAG_EXACT, depth);
		} else {
			StoreHash(BestMove, BestScore, staticEval, FLAG_ALPHA, depth);
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
		hashDate = 0; // Hash ido tag nullazas
		hashUsed = 0; // Hash hasznalat nullazas
		InitEvalMasks(); // Bitmaszk inicializalas
		brd_PawnTable = null; // Hash tabla urites
		brd_PawnTable = new Array(PAWNENTRIES);
		hash_move     = new Uint32Array(HASHENTRIES);
		hash_date     = new Uint16Array(HASHENTRIES);
		hash_eval     = new Int16Array (HASHENTRIES);
		hash_lock     = new Int32Array (HASHENTRIES);
		hash_score    = new Int16Array (HASHENTRIES);
		hash_flags    = new Uint8Array (HASHENTRIES);
		hash_depth    = new Uint8Array (HASHENTRIES);
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function ClearForSearch() {

		nodes = 0; boardPly = 0; bestMove = 0; timeStop = 0;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var i = 0; i < maxDepth; i++) { // Gyilkosok
			searchKillers[i] = [0, 0];
		}

		for (var i = 0; i < 15; i++) { // Elozmeny tabla
			historyTable[i] = new Array(64);
			for (var j = 0; j < 64; j++) {
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
		ScoreDrop = 0;
		hashDate++;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (UI_HOST == HOST_TANKY && maxSearchDepth > 0) { // Also szint
			maxDepth = maxSearchDepth;
		} else {
			maxDepth = 64;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var inCheck = isCheck(currentPlayer); // Sakk..?

		inCheck ? GenerateEvasions() : GenerateAllMoves(false, false);

		for (var index = brd_moveStart[0]; index < brd_moveStart[1]; index++)
		{
			if (!isLegal(brd_moveList[index])) { // Ervenytelen lepes
				continue;
			}

			countMove++; // Lepesek szamolasa
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var pv = new Array(maxDepth + 1);

		startTime = Date.now(); // Kezdo ido!

		if (UI_HOST == HOST_TANKY) postMessage(['StartedTime', startTime]); // Kuldes!

		search :

		for (currDepth = 1; currDepth <= maxSearchDepth; currDepth++) { // Iterativ melyites

			if (countMove == 1 && currDepth > 5 && bestMove) break; // Egy ervenyes lepes

			for (var margin = (currDepth >= 4 ? 10 : INFINITE); ; margin *= 2) { // ablak

				alpha = Math.max(Score - margin, -INFINITE);
				beta  = Math.min(Score + margin,  INFINITE);

				Score = AlphaBeta(alpha, beta, currDepth, 1, inCheck, pv);

				if (timeStop == 1) break search; // Lejart az ido

				if (isMate(Score)) break; // Matt pontszam

				if (Score > alpha && Score < beta) break;
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


	function UpdatePv(Move, Score, depth, alpha, beta, pv) {

		var flags = FLAG_NONE;
		if (Score > alpha) flags |= FLAG_BETA;
		if (Score < beta)  flags |= FLAG_ALPHA;

		ScoreDrop = depth > 1 && (flags == FLAG_ALPHA || bestMove.score - 30 >= Score);

		bestMove = { move : Move, score : Score, depth : depth };

		if (UI_HOST == HOST_TANKY) // TanKy UI
		{
			postMessage(['SearchInfo', bestMove]); // Info kuldes

			/*var time = (Date.now() - startTime); // Keresesi ido

			var pvLine = ''; // Pv
			for (var index = 0; pv[index] != NOMOVE; index++) {
				pvLine += ' '+FormatMove(pv[index]);
			}

			if (flags ==  FLAG_BETA) depth += '+';
			if (flags == FLAG_ALPHA) depth += '-';

			console.log('Depth: '+depth+ ' Score: '+Score+' Nodes: '+nodes+' Time: '+time+' Pv:'+pvLine);*/
		}
		else // WebWorker, Node.js, JSUCI
		{
			var time = (Date.now() - startTime); // Keresesi ido

			var pvLine = ''; // Pv
			for (var index = 0; pv[index] != NOMOVE; index++) {
				pvLine += ' '+FormatMove(pv[index]);
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


	function BuildPv(pv, newPv, move) {
		pv[0] = move;
		for (var i = 0; (pv[i+1] = newPv[i]); i++);
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


	var uci_options = { 'Hash' : '32' };
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
					    minSearchTime  = maxSearchTime * 1; // Hack: Early exit!
					var maxSearchDepth = getInt('depth'   , 0, tokens); // Depth

						if (maxSearchTime == 0)
						{
							var movesToGo = getInt('movestogo', 30, tokens);

							if (currentPlayer == WHITE) {
								var Inc  = getInt('winc' , 0, tokens);
								var Time = getInt('wtime', 0, tokens);
							} else {
								var Inc  = getInt('binc' , 0, tokens);
								var Time = getInt('btime', 0, tokens);
							}

							Time = Time - Math.min(1000, Time / 10);

							var total = Time + Inc * (movesToGo - 1);

							maxSearchTime = Math.min(total * 0.5, Time) | 0;

							minSearchTime = Math.min(total / movesToGo, Time) | 0;
						}

						if (maxSearchDepth > 0) { // Fix melysegnel max 1 ora!
							minSearchTime = 1000 * 3600;
						}

						if (maxSearchTime < minSearchTime) { // Max >= Min!
							maxSearchTime = minSearchTime;
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
						sendMessage('option name Hash type spin default 32 min 1 max 256');
						sendMessage('uciok');

					break;

				// ############################################################################################

					case 'setoption':

						var key = getStr('name', '', tokens);
						var val = getStr('value', '', tokens);

						if (key == 'Hash' && val != uci_options[key] && val >= 1) {

							if (restBit(val) !== 0) break; // Hash must be power of 2

							HASHENTRIES = (val << 20) / 16;
							HASHMASK = HASHENTRIES - 4;
							InitEnginSearch();

							uci_options[key] = val;

							sendMessage('info string Hash changed to '+val+' MB');
						}

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

					case 'eval':

						ShowEvalForUI = true;

						sendMessage('info string '+Evaluation());

						ShowEvalForUI = false;

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


	function evalStr(sc) {
		var mg = (MG_SC(sc) / 100).toFixed(2).toString();
		var eg = (EG_SC(sc) / 100).toFixed(2).toString();
		for (var i = (16 - mg.length) / 2; i > 0; i--) mg = ' '+mg+' ';
		for (var i = (16 - eg.length) / 2; i > 0; i--) eg = ' '+eg+' ';
		return mg.substr(0, 16)+'|'+eg.substr(0, 16);
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
			msg += ['', '', 'n', 'b', 'r', 'q', ''][PROMOTED(Move) & 0x07];
		}

		return msg;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function GetMoveFromString(moveString) {

		GenerateAllMoves(false, false);

		for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; index++) {
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

	function getStr(key, def, tokens) {

		for (var index = 0; index < tokens.length; index++)
			if (tokens[index] == key)
				if (index < tokens.length - 1)
					return tokens[index+1];

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

		for (var pce = 0; pce < 15; pce++) { // Babuk hasKey (En Passant: 0)
			for (var sq = 0; sq < 64; sq++) {
				PieceKeysLow [(pce << 6) | sq] = RAND_32();
				PieceKeysHigh[(pce << 6) | sq] = RAND_32();
			}
		}

		for (var index = 0; index < 16; index++) { // Sancolas hashKey
			CastleKeysLow [index] = RAND_32();
			CastleKeysHigh[index] = RAND_32();
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// Babuk inicializalasa
	function InitPieceList() {

		brd_Material[0] = 0; // Feher anyag
		brd_Material[8] = 0; // Fekete anyag

		for (var pce = 0; pce < 15; pce++) { // BLACK_KING: 14

			brd_pieceCount[pce] = 0; // Darabszam nullazasa

			for (var num = 0; num < 16; num++) { // Max 15 db azonos lehet (9 Vezer)
				brd_pieceList[(pce << 4) | num] = EMPTY; // Mezo nullazas (64. mezo)
			}
		}

		for (var pce = 0; pce < 15; pce++) { // BitBoard nullazasa
			BitBoard[pce << 1 | LOW]  = 0;
			BitBoard[pce << 1 | HIGH] = 0;
		}

		for (var sq = 0; sq < 64; sq++)
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
		brd_pawnKeyLow  = 0; // pawnKey Low
		brd_pawnKeyHigh = 0; // pawnKey High

		for (var sq = 0; sq < 64; sq++) { // Babuk 
			if (CHESS_BOARD[sq] != 0) {
				brd_hashKeyLow  ^= PieceKeysLow [(CHESS_BOARD[sq] << 6) | sq];
				brd_hashKeyHigh ^= PieceKeysHigh[(CHESS_BOARD[sq] << 6) | sq];
			}
			if ((CHESS_BOARD[sq] & 0x07) == PAWN) { // Gyalog Key
				brd_pawnKeyLow  ^= PieceKeysLow [(CHESS_BOARD[sq] << 6) | sq];
				brd_pawnKeyHigh ^= PieceKeysHigh[(CHESS_BOARD[sq] << 6) | sq];
			}
		}

		if (currentPlayer == WHITE) { // Aki lephet
			brd_hashKeyLow  ^= SideKeyLow;
			brd_hashKeyHigh ^= SideKeyHigh;
		}

		if (EN_PASSANT != 0) { // En Passant
			brd_hashKeyLow  ^= PieceKeysLow [EN_PASSANT];
			brd_hashKeyHigh ^= PieceKeysHigh[EN_PASSANT];
		}

		brd_hashKeyLow  ^= CastleKeysLow [castleRights]; // Sancolas
		brd_hashKeyHigh ^= CastleKeysHigh[castleRights]; // Sancolas
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	// CHESS_BOARD -> FEN
	function boardToFEN() {

		var piece, emptySquares = 0, FEN = '';

		for (var index = 0; index < 64; index++) {
			var n = CHESS_BOARD[index];
			if ((n & 0x07) === KING) { // king
				piece = 'K';
			} else if ((n & 0x07) === QUEEN) { // queen
				piece = 'Q';
			} else if ((n & 0x07) === ROOK) { // rook
				piece = 'R';
			} else if ((n & 0x07) === BISHOP) { // bishop
				piece = 'B';
			} else if ((n & 0x07) === KNIGHT) { // knight
				piece = 'N';
			} else if ((n & 0x07) === PAWN) { // pawn
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

		currentPlayer = Fen[1] === 'w' ? WHITE : BLACK; // Kezdo!

		castleRights = 0; // Sancolas nullazas!

		for (index = 0; index < Fen[2].length; index++) { // Sancolasok
			switch (Fen[2][index]) {
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
	 11,  15,  15,  15,   3,  15,  15,   7,
	 15,  15,  15,  15,  15,  15,  15,  15,
	 15,  15,  15,  15,  15,  15,  15,  15,
	 15,  15,  15,  15,  15,  15,  15,  15,
	 15,  15,  15,  15,  15,  15,  15,  15,
	 15,  15,  15,  15,  15,  15,  15,  15,
	 15,  15,  15,  15,  15,  15,  15,  15,
	 14,  15,  15,  15,  12,  15,  15,  13
	];

	// Tukor tabla
	var TableMirror = [
	 56,  57,  58,  59,  60,  61,  62,  63,
	 48,  49,  50,  51,  52,  53,  54,  55,
	 40,  41,  42,  43,  44,  45,  46,  47,
	 32,  33,  34,  35,  36,  37,  38,  39,
	 24,  25,  26,  27,  28,  29,  30,  31,
	 16,  17,  18,  19,  20,  21,  22,  23,
	  8,   9,  10,  11,  12,  13,  14,  15,
	  0,   1,   2,   3,   4,   5,   6,   7
	];

	// Oszlop tabla
	var TableFiles = [
	  1,   2,   3,   4,   5,   6,   7,   8,
	  1,   2,   3,   4,   5,   6,   7,   8,
	  1,   2,   3,   4,   5,   6,   7,   8,
	  1,   2,   3,   4,   5,   6,   7,   8,
	  1,   2,   3,   4,   5,   6,   7,   8,
	  1,   2,   3,   4,   5,   6,   7,   8,
	  1,   2,   3,   4,   5,   6,   7,   8,
	  1,   2,   3,   4,   5,   6,   7,   8
	];

	// Sor tabla
	var TableRanks = [
	  8,   8,   8,   8,   8,   8,   8,   8,
	  7,   7,   7,   7,   7,   7,   7,   7,
	  6,   6,   6,   6,   6,   6,   6,   6,
	  5,   5,   5,   5,   5,   5,   5,   5,
	  4,   4,   4,   4,   4,   4,   4,   4,
	  3,   3,   3,   3,   3,   3,   3,   3,
	  2,   2,   2,   2,   2,   2,   2,   2,
	  1,   1,   1,   1,   1,   1,   1,   1
	];

	// Huszar "orszem"
	var KnightOutpost = [
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0),
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0),
	S(  0,   0), S(  0,   0), S(  4,   0), S(  5,   0), S(  5,   0), S(  4,   0), S(  0,   0), S(  0,   0),
	S(  0,   0), S(  2,   0), S(  5,   0), S( 10,   0), S( 10,   0), S(  5,   0), S(  2,   0), S(  0,   0),
	S(  0,   0), S(  2,   0), S(  5,   0), S( 10,   0), S( 10,   0), S(  5,   0), S(  2,   0), S(  0,   0),
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0),
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0),
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0)
	];

	var PawnPst = [
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0),
	S( -6,   6), S( -4,  -4), S(  4, -14), S( 17, -12), S( 17, -12), S(  4, -14), S( -4,  -4), S( -6,   6),
	S(  7,  18), S( 17,  16), S( 32,   7), S( 22,   0), S( 22,   0), S( 32,   7), S( 17,  16), S(  7,  18),
	S(-10,  11), S(  3,   5), S(  4,  -1), S( 21, -10), S( 21, -10), S(  4,  -1), S(  3,   5), S(-10,  11),
	S(-16,   3), S(-15,   0), S(  7,  -7), S( 22, -13), S( 22, -13), S(  7,  -7), S(-15,   0), S(-16,   3),
	S(-13,  -4), S( -4,  -7), S(  4,  -5), S(  9,  -2), S(  9,  -2), S(  4,  -5), S( -4,  -7), S(-13,  -4),
	S(-19,  -1), S(  2,  -5), S(-11,   9), S(  0,   5), S(  0,   5), S(-11,   9), S(  2,  -5), S(-19,  -1),
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0)
	];

	var KnightPst = [
	S(-161,-43), S(-62, -48), S(-64, -23), S(-16, -29), S(-16, -29), S(-64, -23), S(-62, -48), S(-161,-43),
	S(-63, -33), S(-41, -15), S( -3, -23), S(-14, -10), S(-14, -10), S( -3, -23), S(-41, -15), S(-63, -33),
	S(-21, -35), S( 18, -25), S( 14,  -3), S( 17,  -2), S( 17,  -2), S( 14,  -3), S( 18, -25), S(-21, -35),
	S(  3, -22), S(  6,  -4), S( 13,   8), S(  9,  15), S(  9,  15), S( 13,   8), S(  6,  -4), S(  3, -22),
	S(-10, -16), S( 12, -14), S( 11,   3), S(  9,   9), S(  9,   9), S( 11,   3), S( 12, -14), S(-10, -16),
	S(-17, -25), S( -2, -21), S(  6, -16), S( 10,  -2), S( 10,  -2), S(  6, -16), S( -2, -21), S(-17, -25),
	S(-22, -40), S(-22, -23), S( -3, -27), S( -1, -15), S( -1, -15), S( -3, -27), S(-22, -23), S(-22, -40),
	S(-50, -38), S(-22, -38), S(-30, -25), S(-18, -18), S(-18, -18), S(-30, -25), S(-22, -38), S(-50, -38)
	];

	var BishopPst = [
	S(-33, -16), S(-13, -16), S(-42, -11), S(-38,  -8), S(-38,  -8), S(-42, -11), S(-13, -16), S(-33, -16),
	S(-43,  -6), S(-23,  -1), S(-25,   1), S(-20,  -7), S(-20,  -7), S(-25,   1), S(-23,  -1), S(-43,  -6),
	S(  0,  -7), S( 11,  -7), S( 14,  -1), S( -6,  -2), S( -6,  -2), S( 14,  -1), S( 11,  -7), S(  0,  -7),
	S(-12,  -5), S(-12,   1), S(  5,   3), S( 13,   8), S( 13,   8), S(  5,   3), S(-12,   1), S(-12,  -5),
	S( -7, -11), S(  1,  -8), S( -5,   5), S( 20,   3), S( 20,   3), S( -5,   5), S(  1,  -8), S( -7, -11),
	S( -9,  -7), S(  6,  -7), S( 12,  -2), S(  4,   6), S(  4,   6), S( 12,  -2), S(  6,  -7), S( -9,  -7),
	S( -5, -15), S( 18, -15), S(  9, -10), S(  0,  -2), S(  0,  -2), S(  9, -10), S( 18, -15), S( -5, -15),
	S(-23, -12), S( -6, -10), S( -7,  -7), S( -6,  -6), S( -6,  -6), S( -7,  -7), S( -6, -10), S(-23, -12)
	];

	var RookPst = [
	S( -7,  18), S(  4,  14), S(-10,  19), S(  6,  15), S(  6,  15), S(-10,  19), S(  4,  14), S( -7,  18),
	S(-10,   8), S( -9,   9), S(  4,   6), S(  6,   1), S(  6,   1), S(  4,   6), S( -9,   9), S(-10,   8),
	S( -9,  13), S(  9,  16), S(  5,  14), S( -2,  15), S( -2,  15), S(  5,  14), S(  9,  16), S( -9,  13),
	S(-17,  17), S( -8,  13), S(  5,  18), S(  5,  11), S(  5,  11), S(  5,  18), S( -8,  13), S(-17,  17),
	S(-25,  11), S( -3,  10), S(-14,  13), S(  0,   6), S(  0,   6), S(-14,  13), S( -3,  10), S(-25,  11),
	S(-26,   3), S( -9,   5), S( -7,  -1), S( -4,  -1), S( -4,  -1), S( -7,  -1), S( -9,   5), S(-26,   3),
	S(-27,   1), S( -3,  -7), S( -5,  -3), S(  4,  -4), S(  4,  -4), S( -5,  -3), S( -3,  -7), S(-27,   1),
	S( -7,  -9), S( -3,  -5), S( -4,   1), S(  8,  -7), S(  8,  -7), S( -4,   1), S( -3,  -5), S( -7,  -9)
	];

	var QueenPst = [
	S( -9, -18), S(  0,  -7), S(  4,   3), S(  7,   2), S(  7,   2), S(  4,   3), S(  0,  -7), S( -9, -18),
	S( -1, -22), S(-27,  -9), S( -9,   2), S(-10,  19), S(-10,  19), S( -9,   2), S(-27,  -9), S( -1, -22),
	S(  9, -17), S(  2,   0), S(  0,   8), S( -9,  28), S( -9,  28), S(  0,   8), S(  2,   0), S(  9, -17),
	S(-13,  11), S(-15,  25), S(-11,  14), S(-23,  31), S(-23,  31), S(-11,  14), S(-15,  25), S(-13,  11),
	S( -7,  -2), S( -7,  16), S( -7,  11), S(-10,  24), S(-10,  24), S( -7,  11), S( -7,  16), S( -7,  -2),
	S(-11,  -3), S(  5, -13), S( -6,   8), S( -4,   4), S( -4,   4), S( -6,   8), S(  5, -13), S(-11,  -3),
	S(-15, -23), S( -1, -29), S( 12, -23), S(  8, -11), S(  8, -11), S( 12, -23), S( -1, -29), S(-15, -23),
	S( -9, -36), S( -6, -34), S( -3, -27), S(  8, -26), S(  8, -26), S( -3, -27), S( -6, -34), S( -9, -36)
	];

	var KingPst = [
	S(-48, -77), S( 10, -42), S(-20, -21), S(-66, -35), S(-66, -35), S(-20, -21), S( 10, -42), S(-48, -77),
	S(-13, -26), S( -8, -13), S(-23,   4), S(-39,   3), S(-39,   3), S(-23,   4), S( -8, -13), S(-13, -26),
	S(  0, -16), S( 12,   7), S( -3,  17), S(-50,  10), S(-50,  10), S( -3,  17), S( 12,   7), S(  0, -16),
	S(-28, -16), S( -7,   9), S(-27,  15), S(-55,  16), S(-55,  16), S(-27,  15), S( -7,   9), S(-28, -16),
	S(-26, -24), S(-11,  -7), S(-29,   9), S(-55,  15), S(-55,  15), S(-29,   9), S(-11,  -7), S(-26, -24),
	S( 11, -28), S( 18, -10), S( -5,  -1), S(-28,   6), S(-28,   6), S( -5,  -1), S( 18, -10), S( 11, -28),
	S( 44, -38), S( 38, -22), S(  4, -10), S(-12,  -5), S(-12,  -5), S(  4, -10), S( 38, -22), S( 44, -38),
	S( 46, -73), S( 54, -47), S( 20, -35), S( 25, -42), S( 25, -42), S( 20, -35), S( 54, -47), S( 46, -73)
	];

	// Extra
	var BishopPair  = S( 46,  39);
	var TempoBonus  = S( 33,  25);
	var BlockedRook = S( 47,  -8);

	// File & Rank
	var RookOn7th    = S( -1,  26);
	var QueenOn7th   = S(-15,  19);
	var RookHalfOpen = S(  6,  15);
	var RookFullOpen = S( 27,   4);

	// Pawn Evals
	var PawnDoubled      = S( -5,  -6);
	var PawnIsolated     = S(-14, -12);
	var PawnIsolatedOpen = S(-13,  -4);
	var PawnBackward     = S( -7,  -7);
	var PawnBackwardOpen = S(-16,  -1);

	// Material
	var DeltaValue = [ 0, 100, 343, 340, 518, 1005, 20000, 0, 0, 100, 343, 340, 518, 1005, 20000 ];

	var PieceValue = [ 0, S( 81,  84), S(343, 314), S(340, 322), S(480, 518), S(1005, 1005), S(20000, 20000),
	                0, 0, S( 81,  84), S(343, 314), S(340, 322), S(480, 518), S(1005, 1005), S(20000, 20000) ];

	// King Safety
	var KingShield = new Array(5);
	KingShield[0] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0) ];
	KingShield[1] = [ S(  0,   0), S(  0,   0), S(  9,   0), S( 17,   0), S(  5,   0) ];
	KingShield[2] = [ S(  0,   0), S(  0,   0), S( 29,   0), S( 27,   0), S(  9,   0) ];
	KingShield[3] = [ S(  0,   0), S(  0,   0), S( 34,   0), S(  0,   0), S(-13,   0) ];
	KingShield[4] = [ S(  0,   0), S(  0,   0), S(  9,   0), S(  7,   0), S(-42,   0) ];

	var KingSafetyMull = [ S(  0,   0), S(  8,   0), S( 21,   0), S( 34,   0), S( 45,   0) ];

	// Threats
	var ThreatScore = new Array(7);
	ThreatScore[0] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0) ];
	ThreatScore[1] = [ S(  0,   0), S(  0,   0), S( 65,  23), S( 63,  46), S( 82,  10), S( 70,  12), S(  0,   0) ];
	ThreatScore[2] = [ S(  0,   0), S(  0,   0), S(  0,   0), S( 35,  28), S( 64,  11), S( 55,  -9), S(  0,   0) ];
	ThreatScore[3] = [ S(  0,   0), S(  0,   0), S( 18,  24), S(  0,   0), S( 50,  21), S( 68,  53), S(  0,   0) ];
	ThreatScore[4] = [ S(  0,   0), S(  0,   0), S( 21,  23), S( 23,  31), S(  0,   0), S( 82,  23), S(  0,   0) ];
	ThreatScore[5] = [ S(  0,   0), S(  0,   0), S(  5,  21), S(  3,  21), S( -2,  20), S(  0,   0), S(  0,   0) ];
	ThreatScore[6] = [ S(  0,   0), S(  0,   0), S( 11,  29), S( 16,  29), S(  0,  32), S(  0,   0), S(  0,   0) ];

	// Passed Pawn
	var CandidatePawn  = [ S(  0,   0), S(  0,   0), S(  5,  -6), S(  3,   5), S(  4,  12), S(  5,  18), S( 14, 112), S( 55, 110) ];
	var PassedPawnBase = [ S(  0,   0), S(  0,   0), S( 10,  20), S( 10,  20), S( 11,  29), S( 26,  43), S( 43,  66), S( 77, 105) ];
	var PassedHalfFree = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( -1,   4), S(  5,   6), S( 14,  14), S( 22,  33) ];
	var PassedFullFree = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-23,  17), S( -9,  32), S( 40,  85), S( 61, 135) ];

	var PassedDistanceOwn = new Array(7);
	PassedDistanceOwn[0] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  6,  30), S( 37,  62), S( 31,  91), S( 52, 105) ];
	PassedDistanceOwn[1] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( 17,  24), S( 36,  45), S( 52,  76), S( 45,  62) ];
	PassedDistanceOwn[2] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  7,   9), S( 19,  15), S( 20,  16), S( 32,  37) ];
	PassedDistanceOwn[3] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( -8,  -2), S( -2,  -6), S( 12, -15), S( 18,  -7) ];
	PassedDistanceOwn[4] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-11, -14), S( -5, -21), S( -9, -31), S( -1, -35) ];
	PassedDistanceOwn[5] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-15, -13), S(-11, -25), S( -9, -38), S( -5, -40) ];
	PassedDistanceOwn[6] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  9, -11), S(  9, -26), S( -8, -34), S(  4, -49) ];
	PassedDistanceOwn[7] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-11,  -5), S(  1, -25), S( 19, -34), S(  5, -49) ];

	var PassedDistanceThem = new Array(7);
	PassedDistanceThem[0] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-16, -28), S(  5, -32), S(  9, -52), S(  1, -64) ];
	PassedDistanceThem[1] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( -2,  -9), S( 14, -21), S( 14, -40), S(  9, -58) ];
	PassedDistanceThem[2] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( 16,  -7), S( 11, -12), S( 18, -20), S( 14, -15) ];
	PassedDistanceThem[3] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( -5,   3), S(-13,  19), S(-15,  49), S( 13,  83) ];
	PassedDistanceThem[4] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-18,  16), S( -9,  40), S(-20,  80), S( -3, 111) ];
	PassedDistanceThem[5] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-13,  25), S(-11,  52), S(-11,  84), S( 12, 112) ];
	PassedDistanceThem[6] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( -2,  28), S( -1,  55), S( -4,  85), S(  3, 121) ];
	PassedDistanceThem[7] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-16,  26), S( -6,  52), S( -7,  79), S(-21, 109) ];

	// Mobility
	var KnightMob = [ S(-24, -83), S(-16, -38), S( -6, -19), S( -5,  -6), S(  5,  -5), S( 10,   5), S( 16,   2), S( 21,   2), S( 33,  -6) ];
	var BishopMob = [ S(-42, -54), S(-31, -49), S(-14, -29), S(-11, -13), S( -3,  -4), S(  4,   0), S(  7,   5), S(  8,   6), S( 11,  10), S( 11,   9), S( 15,   4), S( 32,   5), S( 17,  13), S( 31,   6) ];
	var RookMob   = [ S(-42, -87), S(-18, -51), S(-13, -29), S(-13, -15), S(-13,  -9), S( -9,   0), S( -6,   6), S(  0,   9), S(  3,  11), S(  9,  14), S(  9,  19), S( 14,  21), S( 18,  21), S( 17,  22), S( 16,  23) ];
	var QueenMob  = [ S(-199, -26), S(-16, -157), S(-22, -98), S(-21, -50), S(-19, -67), S(-18, -56), S(-11, -52), S( -8, -44), S( -5, -26), S( -2, -20), S( -2, -10), S(  1,  -5), S(  3,  -2), S(  5,   5), S(  7,   7), S(  6,  14), S(  5,  20), S(  8,  15), S( 13,  24), S( 19,  25), S( 22,  26), S( 22,  31), S( 31,  25), S( 29,  31), S( 30,  26), S( 23,  25), S(  7,  22), S( 27,  22) ];
