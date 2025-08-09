/*
 tomitankChess 5.1 Copyright (C) 2017-2021 Tamas Kuzmics - tomitank
 Mail: tanky.hu@gmail.com
 Date: 2021.08.08.

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
var VERSION         = '5.1';
var Nodes           = 0; // Csomopont
var HashUsed        = 0; // Hash szam
var BoardPly        = 0; // Reteg szam
var MaxDepth        = 64; // Max melyseg
var TimeStop        = 0; // Ido vagas be
var HashDate        = 0; // Hash ido tag
var BestMove        = 0; // A legjobb lepes
var CurrDepth       = 0; // Aktualis melyseg
var MoveCount       = 0; // Osszes lepesszam
var StartTime       = 0; // Kereses kezdo ido
var ScoreDrop       = 0; // Csokkeno pontszam
var SideKeyLow      = 0; // Oldal hashKey also
var SideKeyHigh     = 0; // Oldal hashKey felso
var CastleRights    = 0; // Sancolasok 4 biten!
var MinSearchTime   = 0; // Min keresesi ido (ms)
var MaxSearchTime   = 0; // Max keresesi ido (ms)
var CurrentPlayer   = 0; // Aki lephet (Feher: 0)
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
var SearchKillers   = new Array(MaxDepth); // Gyilkos lepesek
var brd_moveList    = new Array(MaxDepth * 256); // Lepes lista
var brd_moveScores  = new Array(MaxDepth * 256); // Lepes ertek
var brd_moveStart   = new Array(MaxDepth + 1); // Tomb hatarolo
var PieceKeysHigh   = new Array(16 * 64); // Babu hashKey felso
var PieceKeysLow    = new Array(16 * 64); // Babu hashKey also
var CastleKeysHigh  = new Array(16); // Sancolas hashKey felso
var CastleKeysLow   = new Array(16); // Sancolas hashKey also
var HistoryTable    = new Array(15); // Elozmeny tabla
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
var FLAG_UPPER      = 2; // Hash zaszlo 2
var FLAG_LOWER      = 1; // Hash zaszlo 1
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
var ISMATE          = INFINITE - MaxDepth * 2; // Matt
var PAWNENTRIES     = (1  << 12) /  1; // Gyalog hash max ~1 MB
var PAWNMASK        = PAWNENTRIES - 1; // Gyalog hash maszk, csak ketto hatvanya lehet
var HASHENTRIES     = (32 << 20) / 16; // Hashtabla merete 32 MB / 1 Hash merete (16 byte)
var HASHMASK        = HASHENTRIES - 4; // Hashtabla maszk, csak ketto hatvanya lehet & MASK
var CASTLEBIT       = { WQ : 1, WK : 2, BQ : 4, BK : 8, W : 3, B : 12 }; // Sanc-ellenorzes
var MvvLvaScores    = [ 0, 1, 2, 3, 4, 5, 6, 0, 0, 1, 2, 3, 4, 5, 6 ]; // Mvv-Lva Babuk erteke
var SeeValue        = [ 0, 100, 325, 325, 500, 975, 20000, 0, 0, 100, 325, 325, 500, 975, 20000 ];
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

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

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

				NeighbourMask[from] |= SetMask[from - 1];
				IsolatedMask [from] |= FileBBMask[TableFiles[from] - 1];

				for (sq = from + 7; sq < 64; sq += 8) {
					BlackPassedMask[from] |= SetMask[sq];
				}

				for (sq = from - 9; sq >= 0; sq -= 8) {
					WhitePassedMask[from] |= SetMask[sq];
				}
			}

			if (TableFiles[from] != FILES.FILE_H) {

				NeighbourMask[from] |= SetMask[from + 1];
				IsolatedMask [from] |= FileBBMask[TableFiles[from] + 1];

				for (sq = from + 9; sq < 64; sq += 8) {
					BlackPassedMask[from] |= SetMask[sq];
				}

				for (sq = from - 7; sq >= 0; sq -= 8) {
					WhitePassedMask[from] |= SetMask[sq];
				}
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

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

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

	function DefendedByPawn(sq, sd) {
		return sd === WHITE ? DefendedByWPawn(sq) : DefendedByBPawn(sq);
	}

	function DefendedByBPawn(sq) {
		sq = Math.max(sq - 8,  0);
		return (NeighbourMask[sq] & BitBoard[BLACK_PAWN << 1 | HighSQMask[sq]]);
	}

	function DefendedByWPawn(sq) {
		sq = Math.min(sq + 8, 63);
		return (NeighbourMask[sq] & BitBoard[WHITE_PAWN << 1 | HighSQMask[sq]]);
	}

	function DirectNeighborPawn(sq, sd) {
		return (NeighbourMask[sq] & BitBoard[(sd | PAWN) << 1 | HighSQMask[sq]]);
	}

	function PawnControlled(sq, sd, xd) {
		return PopCount(DefendedByPawn(sq, sd)) >= PopCount(DefendedByPawn(sq, xd));
	}

	function PawnSafeSquare(sq, sd, xd) {
	//	return (CHESS_BOARD[sq] & 0x07) !== PAWN && PawnControlled(sq, sd, xd);
		return (CHESS_BOARD[sq] & 0x07) !== PAWN && DefendedByPawn(sq, xd) == 0;
	}

	function WeakPawn(sq, rank, file, us, them) {

		var inc = us ? 8 : -8;
		var usPawn = us | PAWN;
		var Rank_2 = us ? RANKS.RANK_7 : RANKS.RANK_2;
		var Rank_5 = us ? RANKS.RANK_4 : RANKS.RANK_5;

		// Hatrahagyott Gyalog..?

		var s1 = sq + inc; // Elottunk 1. mezo
		var s2 = s1 + inc; // Elottunk 2. mezo

		if (DirectNeighborPawn(s1, us)
		&& PawnSafeSquare(s1, us, them)) {
			return false;
		}

		if (rank == Rank_2
		&& DirectNeighborPawn(s2, us)
		&& PawnSafeSquare(s1, us, them)
		&& PawnSafeSquare(s2, us, them)) {
			return false;
		}

		// Eloretolt Gyalog..?

		if (file != FILES.FILE_A) { // Bal oldali vedo

			var s0 = sq -   1; // Bal oldal
			var s1 = s0 - inc; // Balra lent 1. mezo
			var s2 = s1 - inc; // Balra lent 2. mezo
			var s3 = s2 - inc; // Balra lent 3. mezo

			if (CHESS_BOARD[s2] === usPawn
			&& PawnSafeSquare(s1, us, them)) {
				return false;
			}

			if (rank == Rank_5
			&& CHESS_BOARD[s3] === usPawn
			&& PawnSafeSquare(s1, us, them)
			&& PawnSafeSquare(s2, us, them)) {
				return false;
			}
		}

		if (file != FILES.FILE_H) { // Jobb oldali vedo

			var s0 = sq +   1; // Jobb oldal
			var s1 = s0 - inc; // Jobbra lent 1. mezo
			var s2 = s1 - inc; // Jobbra lent 2. mezo
			var s3 = s2 - inc; // Jobbra lent 3. mezo

			if (CHESS_BOARD[s2] === usPawn
			&& PawnSafeSquare(s1, us, them)) {
				return false;
			}

			if (rank == Rank_5
			&& CHESS_BOARD[s3] === usPawn
			&& PawnSafeSquare(s1, us, them)
			&& PawnSafeSquare(s2, us, them)) {
				return false;
			}
		}

		return true;
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
		return (CurrentPlayer ? (BitBoard[bPawnHigh] & RankBBMask[RANKS.RANK_2]) : (BitBoard[wPawnLow] & RankBBMask[RANKS.RANK_7]));
	}

	function PawnPush(Move) {
		return (CHESS_BOARD[FROMSQ(Move)] & 0x07) == PAWN && (CurrentPlayer ? (TableRanks[TOSQ(Move)] <= RANKS.RANK_3 && BlackPassedPawn(TOSQ(Move)) == 0)
		                                                                    : (TableRanks[TOSQ(Move)] >= RANKS.RANK_6 && WhitePassedPawn(TOSQ(Move)) == 0));
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

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

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function validateMove(from, to, side) { // for TanKy UI

		var forceMove = CurrentPlayer != side;
		var fromPiece = CHESS_BOARD[from];
		var toPiece   = CHESS_BOARD[to];

		if (!fromPiece) { // Moving an empty square?
			return false;
		}

		if ((fromPiece & 0x8) ^ side) { // Not your turn!
			return false;
		}

		if (!forceMove && toPiece && (toPiece & 0x8) == side) { // Cannot attack one of your own!
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
		if (pieceType === KING && Math.abs(from - to) === 2) {
			castling = 1;
		}

	// Create move..
		var Move = BIT_MOVE(from, to, capture, promote, castling);

	// Legal move..?
		if (!forceMove)
		{
			for (var index = brd_moveStart[0]; index < brd_moveStart[1]; index++) {
				if (brd_moveList[index] == Move) {
					return isLegal(Move);
				}
			}
			return false;
		}
		else if (castling === 1)
		{
			return side === WHITE ? (to == SQUARES.G1 && CastleRights & CASTLEBIT.WK) || (to == SQUARES.C1 && CastleRights & CASTLEBIT.WQ)
			                      : (to == SQUARES.G8 && CastleRights & CASTLEBIT.BK) || (to == SQUARES.C8 && CastleRights & CASTLEBIT.BQ);
		}
		else if (pieceType === PAWN)
		{
			var attacks = { Low : 0, High : 0 };
			var inc = side ? 8 : -8, next = from + inc;

			HighSQMask[next] ? attacks.High = SetMask[next] | NeighbourMask[next]
			                 : attacks.Low  = SetMask[next] | NeighbourMask[next];

			if (TableRanks[from] == (side ? RANKS.RANK_7 : RANKS.RANK_2))
			{
				HighSQMask[next + inc] ? attacks.High |= SetMask[next + inc]
				                       : attacks.Low  |= SetMask[next + inc];
			}
		}
		else
		{
			var attacks = PceAttacks(pieceType, from);
		}

		return HighSQMask[to] ? (attacks.High & SetMask[to]) != 0 : (attacks.Low & SetMask[to]) != 0;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function StoreHash(move, score, _eval, flags, depth) { // Hash mentes

		var index = brd_hashKeyLow & HASHMASK;

		var oldest = -1;
		var update =  0;

		for (var entry = index; entry < index + 4; entry++) {

			if (hash_lock[entry] == brd_hashKeyHigh) {

				if (hash_depth[entry] <= depth) {
					if (move == NOMOVE) {
						move = hash_move[entry];
					}
					update = entry;
					break;
				}

				if (hash_move[entry] == NOMOVE && move != NOMOVE) { // update!
					hash_move[entry] = move;
				}

				hash_date[entry] = HashDate; // update age of deeper entry!

				return;
			}

			var age = (HashDate - hash_date[entry]) * 65 + 65 - hash_depth[entry];
			if (oldest < age) {
				oldest = age;
				update = entry;
			}
		}

		if (hash_lock[update] == 0) { // new
			HashUsed++;
		}

		if (score > ISMATE) {
			score += BoardPly;
		} else if (score < -ISMATE) {
			score -= BoardPly;
		}

		hash_move [update] = move;
		hash_eval [update] = _eval;
		hash_score[update] = score;
		hash_flags[update] = flags;
		hash_depth[update] = depth;
		hash_date [update] = HashDate;
		hash_lock [update] = brd_hashKeyHigh;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

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

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function IsRepetition() { // Lepesismetles + 50 lepesszabaly

		if (brd_fiftyMove >= 100) { // TODO: mate?
			return true;
		}

		for (var index = 4; index <= brd_fiftyMove; index += 2) {
			if (MOVE_HISTORY[MoveCount-index].hashKeyLow  == brd_hashKeyLow
			 && MOVE_HISTORY[MoveCount-index].hashKeyHigh == brd_hashKeyHigh) {
				return true;
			}
		}

		return false;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

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
		brd_hashKeyLow  ^= CastleKeysLow [CastleRights];
		brd_hashKeyHigh ^= CastleKeysHigh[CastleRights];
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

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function makeMove(move) {

		var to = TOSQ(move);
		var from = FROMSQ(move);
		var MOVED_PIECE = CHESS_BOARD[from];
		var PROMOTED_PIECE = PROMOTED(move);
		var CAPTURED_PIECE = CHESS_BOARD[to];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		MOVE_HISTORY[MoveCount] = { // Lepeselozmeny mentese
			NN_HIDDEN_L	: NN_HIDDEN_LAYER.slice(0), // copy!
			capturedPCE	: CAPTURED_PIECE,
			hashKeyHigh	: brd_hashKeyHigh,
			pawnKeyHigh	: brd_pawnKeyHigh,
			hashKeyLow	: brd_hashKeyLow,
			pawnKeyLow	: brd_pawnKeyLow,
			fiftyMove	: brd_fiftyMove,
			castleBIT	: CastleRights,
			epSquare	: EN_PASSANT,
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
			DELETE_PCE(CAPTURED_PIECE, to, (CurrentPlayer^8));
			DELETE_NN_PCE(CAPTURED_PIECE, to, (CurrentPlayer^8));
		}
		else if (move & CAPTURE_MASK) // En Passant Lepes
		{
			if (CurrentPlayer) // Fekete
			{
				EN_PASSANT = to-8; // Hack: Koztes tarolo
				HASH_PCE(WHITE_PAWN, EN_PASSANT);
				DELETE_PCE(WHITE_PAWN, EN_PASSANT, WHITE);
				DELETE_NN_PCE(WHITE_PAWN, EN_PASSANT, WHITE);
			}
			else // Feher
			{
				EN_PASSANT = to+8; // Hack: Koztes tarolo
				HASH_PCE(BLACK_PAWN, EN_PASSANT);
				DELETE_PCE(BLACK_PAWN, EN_PASSANT, BLACK);
				DELETE_NN_PCE(BLACK_PAWN, EN_PASSANT, BLACK);
			}
		}
		else if (move & CASTLED_MASK) // Sancolaskor Bastya mozgatasa
		{
			switch (to) {
				case SQUARES.C1:
					HASH_PCE(WHITE_ROOK, SQUARES.A1);
					HASH_PCE(WHITE_ROOK, SQUARES.D1);
					MOVE_PCE(WHITE_ROOK, SQUARES.A1, SQUARES.D1);
					MOVE_NN_PCE(WHITE_ROOK, SQUARES.A1, SQUARES.D1);
				break;
				case SQUARES.C8:
					HASH_PCE(BLACK_ROOK, SQUARES.A8);
					HASH_PCE(BLACK_ROOK, SQUARES.D8);
					MOVE_PCE(BLACK_ROOK, SQUARES.A8, SQUARES.D8);
					MOVE_NN_PCE(BLACK_ROOK, SQUARES.A8, SQUARES.D8);
				break;
				case SQUARES.G1:
					HASH_PCE(WHITE_ROOK, SQUARES.H1);
					HASH_PCE(WHITE_ROOK, SQUARES.F1);
					MOVE_PCE(WHITE_ROOK, SQUARES.H1, SQUARES.F1);
					MOVE_NN_PCE(WHITE_ROOK, SQUARES.H1, SQUARES.F1);
				break;
				case SQUARES.G8:
					HASH_PCE(BLACK_ROOK, SQUARES.H8);
					HASH_PCE(BLACK_ROOK, SQUARES.F8);
					MOVE_PCE(BLACK_ROOK, SQUARES.H8, SQUARES.F8);
					MOVE_NN_PCE(BLACK_ROOK, SQUARES.H8, SQUARES.F8);
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
				EN_PASSANT = (to + (CurrentPlayer ? -8 : 8));
				HASH_EP(); // En Passant hashKey
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		MOVE_NN_PCE(MOVED_PIECE, from, to); // Babu mozgatasa
		MOVE_PCE(MOVED_PIECE, from, to);
		HASH_PCE(MOVED_PIECE, from);
		HASH_PCE(MOVED_PIECE, to);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (PROMOTED_PIECE != 0) // Gyalog bevaltasa
		{
			HASH_PCE(MOVED_PIECE, to);
			HASH_PCE(PROMOTED_PIECE, to);
			DELETE_PCE(MOVED_PIECE, to, CurrentPlayer);
			ADDING_PCE(PROMOTED_PIECE, to, CurrentPlayer);
			DELETE_NN_PCE(MOVED_PIECE, to, CurrentPlayer);
			ADDING_NN_PCE(PROMOTED_PIECE, to, CurrentPlayer);
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		HASH_CA(); // Sancolas hashKey

		CastleRights &= CastlePerm[from] & CastlePerm[to]; // Sancolas

		HASH_CA(); // Sancolas hashKey

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		CurrentPlayer ^= 8; // Ember valtas
		HASH_SIDE(); // Aki lephet hashKey
		MoveCount++; // Lepes szamlalo
		BoardPly++; // Melyseg szamlalo
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function unMakeMove() {

		MoveCount--; // Lepes szamlalo
		BoardPly--; // Melyseg szamlalo

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var move = MOVE_HISTORY[MoveCount].move;
		EN_PASSANT = MOVE_HISTORY[MoveCount].epSquare;
		CastleRights = MOVE_HISTORY[MoveCount].castleBIT;
		brd_fiftyMove = MOVE_HISTORY[MoveCount].fiftyMove;
		brd_hashKeyLow = MOVE_HISTORY[MoveCount].hashKeyLow;
		brd_pawnKeyLow = MOVE_HISTORY[MoveCount].pawnKeyLow;
		brd_hashKeyHigh = MOVE_HISTORY[MoveCount].hashKeyHigh;
		brd_pawnKeyHigh = MOVE_HISTORY[MoveCount].pawnKeyHigh;
		NN_HIDDEN_LAYER = MOVE_HISTORY[MoveCount].NN_HIDDEN_L;
		var CAPTURED_PIECE = MOVE_HISTORY[MoveCount].capturedPCE;

		var to = TOSQ(move);
		var from = FROMSQ(move);
		var MOVED_PCE = CHESS_BOARD[to];
		var PROMOTED_PIECE = PROMOTED(move);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		MOVE_PCE(MOVED_PCE, to, from); // Babu mozgatasa (to->from)

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (CAPTURED_PIECE) // Leutott babu visszavonasa
		{
			ADDING_PCE(CAPTURED_PIECE, to, CurrentPlayer);
		}
		else if (move & CAPTURE_MASK) // En Passant Lepes visszavonasa
		{
			CurrentPlayer ? ADDING_PCE(BLACK_PAWN, (EN_PASSANT + 8), BLACK) // Fekete
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

		CurrentPlayer ^= 8; // Ember valtas

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (PROMOTED_PIECE != 0) // Gyalog bevaltasanak visszavonasa
		{
			DELETE_PCE(PROMOTED_PIECE, from, CurrentPlayer);
			ADDING_PCE((CurrentPlayer | PAWN), from, CurrentPlayer);
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function makeNullMove() {

		MOVE_HISTORY[MoveCount++] = {
			hashKeyHigh	: brd_hashKeyHigh,
			hashKeyLow	: brd_hashKeyLow,
			fiftyMove	: brd_fiftyMove,
			epSquare	: EN_PASSANT
		};

		if (EN_PASSANT != 0) HASH_EP();

		CurrentPlayer ^= 8;
		brd_fiftyMove = 0;
		EN_PASSANT = 0;
		HASH_SIDE();
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function unMakeNullMove() {

		MoveCount--;

		CurrentPlayer ^= 8;

		EN_PASSANT = MOVE_HISTORY[MoveCount].epSquare;
		brd_fiftyMove = MOVE_HISTORY[MoveCount].fiftyMove;
		brd_hashKeyLow = MOVE_HISTORY[MoveCount].hashKeyLow;
		brd_hashKeyHigh = MOVE_HISTORY[MoveCount].hashKeyHigh;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function S(mg, eg) { return (mg << 16) + eg; }

	function EG_SC(sc) { return (sc << 16) >> 16; }

	function MG_SC(sc) { return (sc + 0x8000) >> 16; }

	function isMate(score) { return score > ISMATE || score < -ISMATE; }

	function isCheck(Side) { return isSquareUnderAttack(brd_pieceList[(Side | KING) << 4], Side); }

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

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

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

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
		var bb, us = CurrentPlayer;
		var them = CurrentPlayer^8;
		var PCE = CHESS_BOARD[from] & 0x07;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Kiraly lepett
		if (PCE === KING)
		{
			ClearBitBoard(from, (us|KING), us);

			var attack = isSquareUnderAttack(to, us);

			SetBitBoard(from, (us|KING), us);

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
	//						         DONTETLEN
	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (wNumPawns == 0 && bNumPawns == 0) { // Nincs Gyalog
			if (wNumQueens == 0 && bNumQueens == 0) { // Nincs Vezer
				if (wNumRooks == 0 && bNumRooks == 0) { // Nincs Bastya
					if (wNumBishops == 0 && bNumBishops == 0) { // Nincs Futo
						if (wNumKnights < 3 && bNumKnights < 3) { // K(Ns) vs K(Ns)
							return 0;
						}
					} else if (wNumKnights == 0 && bNumKnights == 0) { // K(Bs) vs K(Bs)
						if (Math.abs(wNumBishops - bNumBishops) < 2) { // Max B diff < 2
							return 0;
						}
					} else if ((wNumKnights  < 3 && wNumBishops == 0)
						    || (wNumKnights == 0 && wNumBishops == 1)) { // K(Ns|B) vs K(Ns|B)
						if ((bNumKnights  < 3 && bNumBishops == 0)
						 || (bNumKnights == 0 && bNumBishops == 1)) {
							return 0;
						 }
					}
				} else if (wNumRooks == 1 && bNumRooks == 1) { // KR(N|B) vs KR(N|B)
					if (wNumKnights + wNumBishops == 0
					 && bNumKnights + bNumBishops == 0) { // KR vs KR
						return 0;
					}
					if (wNumKnights + wNumBishops < 2
					 && bNumKnights + bNumBishops < 2) { // +(N|B) vs +(N|B)
						Draw = 10;
					}
				} else if (wNumRooks == 1 && bNumRooks == 0) { // KR vs KNs|Bs
					if (wNumKnights + wNumBishops == 0
					&& (bNumKnights + bNumBishops == 1
					 || bNumKnights + bNumBishops == 2)) {
						Draw = 4;
					}
				} else if (wNumRooks == 0 && bNumRooks == 1) { // KNs|Bs vs KR
					if (bNumKnights + bNumBishops == 0
					&& (wNumKnights + wNumBishops == 1
					 || wNumKnights + wNumBishops == 2)) {
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
		var threats = 0;
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
	//						           BABUK ERTEKELESE
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
				   (CastleRights & CASTLEBIT.WQ) == 0 && File <= wKingFile
				 : (CastleRights & CASTLEBIT.WK) == 0 && File >= wKingFile) {
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
				   (CastleRights & CASTLEBIT.BQ) == 0 && File <= bKingFile
				 : (CastleRights & CASTLEBIT.BK) == 0 && File >= bKingFile) {
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
		}

	// Fekete Telt Gyalog
		for (var idx = 0; idx < bPassedPawn.length; idx++)
		{
			PCE = bPassedPawn[idx];
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			pawns -= PassedPawnBase[9-Rank]; // Alap Pont

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
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (wCanAttack)
		{
			if (wAttackCount > 4) wAttackCount = 4; // Max 4 tamado

			safety += KingSafetyMull[wAttackCount] * wAttackPower;

			if (bKingRank >= RANKS.RANK_6) { // Pawn shield

				var shield_zone = (BKZ.Low | (BKZ.Low >>> 8)) & ~(BKZ.Low << 16);

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

				var shield_zone = (WKZ.High | (WKZ.High << 8)) & ~(WKZ.High >>> 16);

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

		var tempo = CurrentPlayer === WHITE ? TempoBonus : -TempoBonus;

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var material = brd_Material[WHITE] - brd_Material[BLACK] + posScore;

		var nn_eval = ChessNNEval();

		var score = material;

		score += mobScore;
		score += threats;
		score += safety;
		score += tempo;
		score += pawns;
		score += knights;
		score += bishops;
		score += rooks;
		score += queens;
		score += king;

		if (Phase < 0) { // Minden babu a fedelzeten = 0
			Phase = 0;
		}

		Phase = (Phase << 8) / 24 + 0.5 | 0; // Jatek fazis

		// Linearis interpolacio kezdo es vegjatek kozott..

		score = ((MG_SC(score) * (256 - Phase)) + (EG_SC(score) * Phase)) >> 8;

		score = (score + nn_eval) / Draw | 0; // Ketes dontetlennel nem 0-at adunk vissza!

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
			+' Total Eval: '+(score / 100).toFixed(2);
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		return CurrentPlayer === WHITE ? score : -score;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function UnstoppablePawn(usKing, themKing, xPiecesBB, sq, us, promSq) {

		var front = us ? { Low  : BOpenFileMask[BitFixLow[sq]], High : BOpenFileMask[sq] }
		               : { High : WOpenFileMask[BitFixHigh[sq]], Low : WOpenFileMask[sq] };

		if ((xPiecesBB.Low & front.Low) | (xPiecesBB.High & front.High)) return false; // blocked!

		if (DISTANCE[usKing][sq] <= 1 && DISTANCE[usKing][promSq] <= 1) return true; // king controls promotion path

		if (DISTANCE[sq][promSq] < DISTANCE[themKing][promSq] + ((CurrentPlayer == us)|0) - 1) return true; // unstoppable

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
		var score = 0;

		var pieceIdx = WHITE_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			var Rank = TableRanks[PCE];
			var File = TableFiles[PCE];

			var Open = WhiteOpenFile(PCE) == 0 && WhiteMostPawn(PCE) == 0; // Legelso + Nyitott

			if (DirectNeighborPawn(PCE, WHITE) || DefendedByWPawn(PCE)) { // Eros Gyalog

				score += Open ? PawnConnectedOpen[Rank] : PawnConnected[Rank];

			} else {

				if (BlackOpenFile(PCE) != 0) { // Dupla Gyalog

					score += Open ? PawnDoubledOpen[Rank] : PawnDoubled[Rank];
				}

				if (IsolatedPawn(PCE, WHITE) == 0) { // Elkulonitett Gyalog

					score += Open ? PawnIsolatedOpen[Rank] : PawnIsolated[Rank];

				} else if (WeakPawn(PCE, Rank, File, WHITE, BLACK)) { // Gyenge Gyalog

					score += Open ? PawnBackwardOpen[Rank] : PawnBackward[Rank];
				}
			}

			if (Open && WhitePassedPawn(PCE) == 0) { // Telt Gyalog

				wPassedPawn[wPassedPawn.length] = PCE;
			}

			score += PawnPst[PCE];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var pieceIdx = BLACK_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			var Rank = TableRanks[PCE];
			var File = TableFiles[PCE];

			var Open = BlackOpenFile(PCE) == 0 && BlackMostPawn(PCE) == 0; // Legelso + Nyitott

			if (DirectNeighborPawn(PCE, BLACK) || DefendedByBPawn(PCE)) { // Eros Gyalog

				score -= Open ? PawnConnectedOpen[9-Rank] : PawnConnected[9-Rank];

			} else {

				if (WhiteOpenFile(PCE) != 0) { // Dupla Gyalog

					score -= Open ? PawnDoubledOpen[9-Rank] : PawnDoubled[9-Rank];
				}

				if (IsolatedPawn(PCE, BLACK) == 0) { // Elkulonitett Gyalog

					score -= Open ? PawnIsolatedOpen[9-Rank] : PawnIsolated[9-Rank];

				} else if (WeakPawn(PCE, Rank, File, BLACK, WHITE)) { // Gyenge Gyalog

					score -= Open ? PawnBackwardOpen[9-Rank] : PawnBackward[9-Rank];
				}
			}

			if (Open && BlackPassedPawn(PCE) == 0) { // Telt Gyalog

				bPassedPawn[bPassedPawn.length] = PCE;
			}

			score -= PawnPst[TableMirror[PCE]];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

		return score;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function See(move, threshold) {

		var to = TOSQ(move);
		var from = FROMSQ(move);
		var fromPiece = CHESS_BOARD[from];
		var fromValue = SeeValue[fromPiece];
		var toValue = SeeValue[CHESS_BOARD[to]];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (PROMOTED(move) != 0 // Bevaltas
		|| (fromPiece & 0x07) == KING // Kiraly -> isLegal..?
		|| (move & CAPTURE_MASK && !toValue)) { // En passant
			return true;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		threshold = threshold || 0; // Hack: alap hatarertek!

		var seeValue = toValue - threshold; // Ha van hatarertek!

		if (seeValue < 0) { // A hatarertek miatt alapbol vesztes!
			return false;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		seeValue -= fromValue; // Ha szabadon leutne az ellenfel..

		if (seeValue >= 0) { // ..es igy is nyertes pozicioban vagyunk!
			return true;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var bb, pieceType, King;
		var them = CurrentPlayer;
		var Side = CurrentPlayer^8;
		var SeePieces = GetAllPce();
		var remaining = { Low : 0, High : 0 };
		var provisory = { Low : 0, High : 0 };
		var attackers = { Low : 0, High : 0 };

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		HighSQMask[from] ? SeePieces.High ^= SetMask[from] // Tamado torlese
		                 : SeePieces.Low  ^= SetMask[from];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		SeeAddAllAttacks(to, attackers, SeePieces); // Osszes tamadas betoltese..

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (; ; )
		{
			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			King = brd_pieceList[(Side|KING) << 4]; // Kiraly pozicioja..

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			remaining.Low  = attackers.Low  & SeePieces.Low; // Aktualizalas..
			remaining.High = attackers.High & SeePieces.High;

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			from = EMPTY; // Hack: tamado babu mezejenek nullazasa..

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			while (from == EMPTY) // A ellenfel legkevesbe ertekes babuja..
			{
				provisory.Low  = SeePieces.Low; // Hack: SeePieces megorzese..
				provisory.High = SeePieces.High;

				for (pieceType = PAWN; pieceType <= KING; pieceType++)
				{
					if (bb = remaining.Low & BitBoard[(Side|pieceType) << 1 | LOW]) {
						from = firstBitLow(bb);
						remaining.Low ^= SetMask[from];
						provisory.Low ^= SetMask[from];
						break;
					}
					if (bb = remaining.High & BitBoard[(Side|pieceType) << 1 | HIGH]) {
						from = firstBitHigh(bb);
						remaining.High ^= SetMask[from];
						provisory.High ^= SetMask[from];
						break;
					}
				}

				if (from == EMPTY) { // Nincs tobb tamado!
					break;
				}

				var Beyond = Behind(King, from); // Babu mogott megnyilo mezok!

				if (Beyond.Low | Beyond.High) // Felfedezett Sakk..?
				{
					var b = { Low : 0, High : 0 };

					if (TableRanks[from] == TableRanks[King] || TableFiles[from] == TableFiles[King]) {
						bb = PceAttacks(ROOK, King);
						b.Low  |= bb.Low  & (BitBoard[(them|ROOK) << 1 | LOW]  | BitBoard[(them|QUEEN) << 1 | LOW]);
						b.High |= bb.High & (BitBoard[(them|ROOK) << 1 | HIGH] | BitBoard[(them|QUEEN) << 1 | HIGH]);
					} else {
						bb = PceAttacks(BISHOP, King);
						b.Low  |= bb.Low  & (BitBoard[(them|BISHOP) << 1 | LOW]  | BitBoard[(them|QUEEN) << 1 | LOW]);
						b.High |= bb.High & (BitBoard[(them|BISHOP) << 1 | HIGH] | BitBoard[(them|QUEEN) << 1 | HIGH]);
					}

					for (bb = b.Low & Beyond.Low & provisory.Low; bb != 0 && from != EMPTY; bb = restBit(bb))
					{
						if (LineIsEmpty(firstBitLow(bb), King, provisory) == 0) from = EMPTY;
					}
					for (bb = b.High & Beyond.High & provisory.High; bb != 0 && from != EMPTY; bb = restBit(bb))
					{
						if (LineIsEmpty(firstBitHigh(bb), King, provisory) == 0) from = EMPTY;
					}
				}
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (from == EMPTY) { // Nincs tobb tamado!
				break;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			Side ^= BLACK; // Oldal csere -> ellenfel kovetkezik..
			them ^= BLACK;

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			seeValue = -seeValue - 1 - SeeValue[pieceType]; // Negamax..

			if (seeValue >= 0) { // Ha leutne az ellenfel, de igy is nyerunk!
				break;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			HighSQMask[from] ? SeePieces.High ^= SetMask[from] // Tamado torlese
			                 : SeePieces.Low  ^= SetMask[from];

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			SeeAddSliderAttacks(to, attackers, SeePieces, pieceType); // Mogotte
		}

		return CurrentPlayer != Side; // curr != side -> true
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function SeeAddAllAttacks(target, attackBB, Pieces) {

		SeeAddSliderAttacks(target, attackBB, Pieces, QUEEN); // slider attacks..

		var attacks = PceAttacks(KING, target);
		attackBB.Low  |= attacks.Low  & (BitBoard[wKingLow]  | BitBoard[bKingLow]);
		attackBB.High |= attacks.High & (BitBoard[wKingHigh] | BitBoard[bKingHigh]);

		var attacks = PceAttacks(KNIGHT, target);
		attackBB.Low  |= attacks.Low  & (BitBoard[wKnightLow]  | BitBoard[bKnightLow]);
		attackBB.High |= attacks.High & (BitBoard[wKnightHigh] | BitBoard[bKnightHigh]);

		target+8 > 31 ? attackBB.High |= DefendedByWPawn(target) : attackBB.Low |= DefendedByWPawn(target);
		target-8 > 31 ? attackBB.High |= DefendedByBPawn(target) : attackBB.Low |= DefendedByBPawn(target);
	}

	function SeeAddSliderAttacks(target, attackBB, Pieces, lastAttacker) {

		if (lastAttacker == ROOK || lastAttacker == QUEEN) {
			var attacks = AttacksFrom(ROOK, target, Pieces);
			attackBB.Low  |= attacks.Low  & (BitBoard[wRookLow]  | BitBoard[bRookLow]  | BitBoard[wQueenLow]  | BitBoard[bQueenLow]);
			attackBB.High |= attacks.High & (BitBoard[wRookHigh] | BitBoard[bRookHigh] | BitBoard[wQueenHigh] | BitBoard[bQueenHigh]);
		}

		if (lastAttacker == PAWN || lastAttacker == BISHOP || lastAttacker == QUEEN) {
			var attacks = AttacksFrom(BISHOP, target, Pieces);
			attackBB.Low  |= attacks.Low  & (BitBoard[wBishopLow]  | BitBoard[bBishopLow]  | BitBoard[wQueenLow]  | BitBoard[bQueenLow]);
			attackBB.High |= attacks.High & (BitBoard[wBishopHigh] | BitBoard[bBishopHigh] | BitBoard[wQueenHigh] | BitBoard[bQueenHigh]);
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function GenerateAllMoves(capturesOnly, useSee) {

		var pieceType = 0; // Akivel lepunk
		var pieceIdx  = 0; // Babu indexeles
		var from      = 0; // Ahonnan lepunk
		var next      = 0; // Ahova lepunk
		var score     = 0; // Lepes pont
		var Move      = 0; // Lepes bit
		var bb        = 0; // BitBoard

		brd_moveStart[BoardPly + 1] = brd_moveStart[BoardPly]; // Hack

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var xPiecesBB = GetAllPce();
		var inc = CurrentPlayer ? 8 : -8;
		var enemy = AllPceByColor(CurrentPlayer^8);
		var StartRank   = CurrentPlayer ? RANKS.RANK_7 : RANKS.RANK_2;
		var PromoteRank = CurrentPlayer ? RANKS.RANK_2 : RANKS.RANK_7;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Gyalog lepesek
		pieceIdx = (CurrentPlayer|PAWN) << 4;
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
						AddQuietMove(from, next, (CurrentPlayer|QUEEN), 0);
						AddQuietMove(from, next, (CurrentPlayer|ROOK),  0);
						AddQuietMove(from, next, (CurrentPlayer|BISHOP), 0);
						AddQuietMove(from, next, (CurrentPlayer|KNIGHT), 0);
					} else {
						AddQuietMove(from, next, 0, 0); // Sima lepes

						if (TableRanks[from] == StartRank && CHESS_BOARD[next + inc] == 0) // Dupla lepes
						{
							AddQuietMove(from, next + inc, 0, 0);
						}
					}
				}
			} else if (CHESS_BOARD[next] == 0 && TableRanks[from] == PromoteRank) { // Vezer Promocio (Quiescence)

				AddQuietMove(from, next, (CurrentPlayer|QUEEN), 0);
			}

			for (bb = NeighbourMask[next]; bb != 0; bb = restBit(bb)) // Tamadasok
			{
				next = HighSQMask[next] ? firstBitHigh(bb) : firstBitLow(bb); // from [+-] 7/9

				if (CHESS_BOARD[next] && (CHESS_BOARD[next] & 0x8) !== CurrentPlayer) // Ellenfel
				{
					score = 1000005 + (100 * MvvLvaScores[CHESS_BOARD[next]]); // Pontszam

					if (TableRanks[from] == PromoteRank) // Gyalog bevaltas
					{
						AddCaptureMove(BIT_MOVE(from, next, 1, (CurrentPlayer|QUEEN), 0), score);
						AddCaptureMove(BIT_MOVE(from, next, 1, (CurrentPlayer|ROOK),  0), score);
						AddCaptureMove(BIT_MOVE(from, next, 1, (CurrentPlayer|BISHOP), 0), score);
						AddCaptureMove(BIT_MOVE(from, next, 1, (CurrentPlayer|KNIGHT), 0), score);
					} else {
						AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), score); // Nincs gyalogbevaltas
					}
				} else if (CHESS_BOARD[next] == 0 && EN_PASSANT != 0 && EN_PASSANT == next) { // En Passant

					score = 1000105; // En Passant Pontszam

					AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), score);
				}
			}

			from = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (capturesOnly === false) // Sancolas: indulast es erkezest mashol ellenorizzuk!
		{
			if (CurrentPlayer === WHITE) // Feher oldal
			{
				if (CastleRights & CASTLEBIT.WK) { // Kiraly oldal
					if (CHESS_BOARD[SQUARES.F1] == 0 && CHESS_BOARD[SQUARES.G1] == 0) {
						if (!isSquareUnderAttack(SQUARES.F1, WHITE)) {
							AddQuietMove(SQUARES.E1, SQUARES.G1, 0, 1);
						}
					}
				}
				if (CastleRights & CASTLEBIT.WQ) { // Vezer oldal
					if (CHESS_BOARD[SQUARES.D1] == 0 && CHESS_BOARD[SQUARES.C1] == 0 && CHESS_BOARD[SQUARES.B1] == 0) {
						if (!isSquareUnderAttack(SQUARES.D1, WHITE)) {
							AddQuietMove(SQUARES.E1, SQUARES.C1, 0, 1);
						}
					}
				}

			} else { // Fekete oldal

				if (CastleRights & CASTLEBIT.BK) { // Kiraly oldal
					if (CHESS_BOARD[SQUARES.F8] == 0 && CHESS_BOARD[SQUARES.G8] == 0) {
						if (!isSquareUnderAttack(SQUARES.F8, BLACK)) {
							AddQuietMove(SQUARES.E8, SQUARES.G8, 0, 1);
						}
					}
				}
				if (CastleRights & CASTLEBIT.BQ) { // Vezer oldal
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
			pieceIdx = (CurrentPlayer | pieceType) << 4;
			from = brd_pieceList[pieceIdx++];
			while (from != EMPTY)
			{
				var attacks = AttacksFrom(pieceType, from, xPiecesBB);

				for (bb = attacks.Low & enemy.Low; bb != 0; bb = restBit(bb)) // Tamadas
				{
					next = firstBitLow(bb); Move = BIT_MOVE(from, next, 1, 0, 0);

					if (useSee && !See(Move))
					score =     106 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam
					else
					score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam

					AddCaptureMove(Move, score);
				}
				for (bb = attacks.High & enemy.High; bb != 0; bb = restBit(bb)) // Tamadas
				{
					next = firstBitHigh(bb); Move = BIT_MOVE(from, next, 1, 0, 0);

					if (useSee && !See(Move))
					score =     106 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam
					else
					score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam

					AddCaptureMove(Move, score);
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
		var score  = 0; // Lepes pont
		var next   = 0; // Ahova lepunk
		var from   = 0; // Ahonnan lepunk
		var b      = { Low : 0, High : 0 };
		var checks = { Low : 0, High : 0 };
		var unsafe = { Low : 0, High : 0 };

		brd_moveStart[BoardPly + 1] = brd_moveStart[BoardPly]; // Hack

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var them = CurrentPlayer^8;
		var xPiecesBB = GetAllPce();
		var friendsBB = AllPceByColor(CurrentPlayer);
		var King = brd_pieceList[(CurrentPlayer|KING) << 4];
		var front = CurrentPlayer === BLACK ? King + 8 : King - 8;

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
				score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[KING]); // Pontszam

				AddCaptureMove(BIT_MOVE(King, next, 1, 0, 0), score);
			} else {
				AddQuietMove(King, next, 0, 0); // Ures mezo
			}
		}
		for (bb = attacks.High & ~unsafe.High & ~friendsBB.High; bb != 0; bb = restBit(bb)) {

			if (CHESS_BOARD[next = firstBitHigh(bb)] != 0) // Ellenfel
			{
				score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[KING]); // Pontszam

				AddCaptureMove(BIT_MOVE(King, next, 1, 0, 0), score);
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
		var inc = CurrentPlayer ? 8 : -8;
		var StartRank   = CurrentPlayer ? RANKS.RANK_7 : RANKS.RANK_2;
		var PromoteRank = CurrentPlayer ? RANKS.RANK_2 : RANKS.RANK_7;

		var pieceIdx = (CurrentPlayer|PAWN) << 4;
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
						AddQuietMove(from, next, (CurrentPlayer|QUEEN), 0);
						AddQuietMove(from, next, (CurrentPlayer|ROOK),  0);
						AddQuietMove(from, next, (CurrentPlayer|BISHOP), 0);
						AddQuietMove(from, next, (CurrentPlayer|KNIGHT), 0);
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
					score = 1000005 + (100 * MvvLvaScores[CHESS_BOARD[next]]); // Pontszam

					if (TableRanks[from] == PromoteRank) // Gyalog bevaltas
					{
						AddCaptureMove(BIT_MOVE(from, next, 1, (CurrentPlayer|QUEEN), 0), score);
						AddCaptureMove(BIT_MOVE(from, next, 1, (CurrentPlayer|ROOK),  0), score);
						AddCaptureMove(BIT_MOVE(from, next, 1, (CurrentPlayer|BISHOP), 0), score);
						AddCaptureMove(BIT_MOVE(from, next, 1, (CurrentPlayer|KNIGHT), 0), score);
					} else {
						AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), score); // Nincs gyalogbevaltas
					}
				} else if (EN_PASSANT != 0 && EN_PASSANT == next && (EN_PASSANT - inc) == checkSQ) { // En Passant

					score = 1000105; // En Passant Pontszam

					AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), score);
				}
			}

			from = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Huszar, Futo, Bastya, Vezer (Kiralyt nem nezzuk ujra!)
		for (var pieceType = KNIGHT; pieceType <= QUEEN; pieceType++)
		{
			pieceIdx = (CurrentPlayer | pieceType) << 4;
			from = brd_pieceList[pieceIdx++];
			while (from != EMPTY)
			{
				var attacks = AttacksFrom(pieceType, from, xPiecesBB);

				for (bb = attacks.Low & target.Low; bb != 0; bb = restBit(bb)) // Tamadas & Blokkolas
				{
					next = firstBitLow(bb);

					if (next == checkSQ) // Sakkado babu tamadasa
					{
						score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam

						AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), score);
					} else {
						AddQuietMove(from, next, 0, 0); // Blokkolas
					}
				}
				for (bb = attacks.High & target.High; bb != 0; bb = restBit(bb)) // Tamadas & Blokkolas
				{
					next = firstBitHigh(bb);

					if (next == checkSQ) // Sakkado babu tamadasa
					{
						score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[pieceType]); // Pontszam

						AddCaptureMove(BIT_MOVE(from, next, 1, 0, 0), score);
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
			var score = 950000 + prom;
		} else if (SearchKillers[BoardPly][0] == Move) { // Gyilkos lepes 1.
			var score = 900000;
		} else if (SearchKillers[BoardPly][1] == Move) { // Gyilkos lepes 2.
			var score = 800000;
		} else {
			var score = 1000 + HistoryTable[CHESS_BOARD[from]][to]; // Elozmeny tabla alapjan
		}

		brd_moveList[brd_moveStart[BoardPly + 1]] = Move;
		brd_moveScores[brd_moveStart[BoardPly + 1]++] = score;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function AddCaptureMove(Move, score) {
		brd_moveList[brd_moveStart[BoardPly + 1]] = Move;
		brd_moveScores[brd_moveStart[BoardPly + 1]++] = score;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function PickNextMove(moveNum) {

		var bestNum = moveNum;
		for (var index = moveNum; index < brd_moveStart[BoardPly + 1]; index++) {
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
		var currentTime = Date.now() - StartTime;
		if (CurrDepth >= 2 && currentTime >= MinSearchTime) {
			if (!ScoreDrop || currentTime >= MaxSearchTime) {
				TimeStop = 1;
			}
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function Quiescence(alpha, beta, depth, inCheck, pv) {

		if ((Nodes & 2047) == 0) { // Ido ellenorzese
			CheckUp();
		}

		Nodes++; // Csomopontok novelese

		pv[0] = NOMOVE; // Hack: Pv torlese

		if (IsRepetition()) { // Lepesismetles
			return 0;
		}

		if (BoardPly >= MaxDepth) { // Melyseg limit
			return Evaluation();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var bestScore  = -INFINITE;
		var staticEval = -INFINITE;

		if (inCheck || depth == DEPTH_ZERO) { // Atultetesi tabla

			var hashData = ProbeHash();

			if (hashData != NOMOVE) {

				staticEval = hashData.eval;
				var value = hashData.score;

				if (value > ISMATE) {
					value -= BoardPly;
				} else if (value < -ISMATE) {
					value += BoardPly;
				}

				if (hashData.flags == FLAG_UPPER && value <= alpha) return value;
				if (hashData.flags == FLAG_LOWER && value >= beta)  return value;
				if (hashData.flags == FLAG_EXACT) return value;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (!inCheck) {

			if ((bestScore = staticEval) == -INFINITE) { // Ertekeles
				staticEval = bestScore = Evaluation();
			}

			if (bestScore >= beta) { // Biztos vagas
				return bestScore;
			}

			if (bestScore > alpha) { // Friss alpha
				alpha = bestScore;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var is_pv = (beta != alpha + 1);
		var newPv = new Array(MaxDepth);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var oldAlpha = alpha; // Alpha mentese
		var bestMove = NOMOVE; // Legjobb lepes
		var score = -INFINITE; // Pont nullazas
		var check = NOT_IN_CHECK; // Sakk lepes
		var capturedPCE = NOMOVE; // Leutott babu
		var currentMove = NOMOVE; // Aktualis lepes
		var deltaMargin = bestScore + 100; // Delta Margo
		inCheck ? GenerateEvasions() : GenerateAllMoves(true, false);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var index = brd_moveStart[BoardPly]; index < brd_moveStart[BoardPly + 1]; index++)
		{
			PickNextMove(index);

			currentMove = brd_moveList[index];
			check       = givesCheck(currentMove);
			capturedPCE = CHESS_BOARD[TOSQ(currentMove)];

			if (!inCheck && !check && !PROMOTED(currentMove) && (capturedPCE & 0x07) !== QUEEN) // Delta metszes
			{
				var futileValue = deltaMargin + DeltaValue[capturedPCE ? capturedPCE : PAWN]; // En Passant..?

				if (futileValue <= alpha) {
					if (bestScore < futileValue) {
						bestScore = futileValue;
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

			score = -Quiescence(-beta, -alpha, depth-1, check, newPv);

			unMakeMove(); // Lepes visszavonasa

			if (TimeStop == 1) { // Ido vagas
				return 0;
			}

			if (score > bestScore) {
				bestScore = score;
				if (score > alpha) {
					if (is_pv) {
						BuildPv(pv, newPv, currentMove);
					}
					if (score >= beta) {
						if (inCheck || depth == DEPTH_ZERO) {
							StoreHash(currentMove, bestScore, staticEval, FLAG_LOWER, DEPTH_ZERO);
						}
						return score;
					}
					alpha = score;
					bestMove = currentMove;
				}
			}
		}

		if (inCheck && score == -INFINITE) { // Matt
			return -INFINITE + BoardPly;
		}

		if (inCheck || depth == DEPTH_ZERO) {
			StoreHash(bestMove, bestScore, staticEval, (alpha != oldAlpha ? FLAG_EXACT : FLAG_UPPER), DEPTH_ZERO);
		}

		return bestScore;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function AlphaBeta(alpha, beta, depth, nullMove, inCheck, pv) {

		if (depth <= DEPTH_ZERO) { // Melyseg eleresekor kiertekeles
			return Quiescence(alpha, beta, DEPTH_ZERO, inCheck, pv);
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if ((Nodes & 2047) == 0) { // Ido ellenorzese
			CheckUp();
		}

		Nodes++; // Csomopontok novelese

		pv[0] = NOMOVE; // Hack: Pv torlese

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (BoardPly != 0) { // Gyermek csomopont

			if (IsRepetition()) { // Lepesismetles
				return 0;
			}

			if (BoardPly >= MaxDepth) { // Melyseg limit
				return Evaluation();
			}

			var mate_value = INFINITE - BoardPly; // Matt-tavolsag metszes
			if (alpha < -mate_value) alpha = -mate_value;
			if (beta > mate_value - 1) beta = mate_value - 1;
			if (alpha >= beta) {
				return alpha;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var pruneNode = false;
		var score = -INFINITE;
		var staticEval = -INFINITE;
		var is_pv = (beta != alpha + 1);
		var newPv = new Array(MaxDepth);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var hashData = ProbeHash(); // Atultetesi tabla
		var hashMove = hashData != NOMOVE ? hashData.move : NOMOVE;

		if (hashData != NOMOVE) {

			staticEval = hashData.eval;

			if (!is_pv && hashData.depth >= depth) {

				var value = hashData.score;

				if (value > ISMATE) {
					value -= BoardPly;
				} else if (value < -ISMATE) {
					value += BoardPly;
				}

				if (hashData.flags == FLAG_UPPER && value <= alpha) return value;
				if (hashData.flags == FLAG_LOWER && value >= beta)  return value;
				if (hashData.flags == FLAG_EXACT) return value;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (!is_pv && !inCheck
		&& (brd_pieceCount[CurrentPlayer | KNIGHT] != 0
		 || brd_pieceCount[CurrentPlayer | BISHOP] != 0
		 || brd_pieceCount[CurrentPlayer | ROOK]   != 0
		 || brd_pieceCount[CurrentPlayer | QUEEN]  != 0)) { // Metszheto csomopont

			if (staticEval == -INFINITE && (nullMove || depth <= 4)) { // Futility depth
				staticEval = Evaluation();
			}

			pruneNode = true;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (pruneNode && nullMove && !isMate(beta)) // Metszesek
		{
			if (depth <= 3 && (score = staticEval - 100 * depth) >= beta && PawnOnSeventh() == 0) { // Beta
				return score;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (depth >= 2 && staticEval >= beta) // Null lepes
			{
				makeNullMove();

				score = -AlphaBeta(-beta, -beta+1, depth-4, 0, NOT_IN_CHECK, newPv);

				unMakeNullMove();

				if (TimeStop == 1) { // Ido vagas
					return 0;
				}

				if (score >= beta && !isMate(score)) {
					return score;
				}
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (depth <= 1 && hashMove == NOMOVE && staticEval + 300 < beta && PawnOnSeventh() == 0) { // Razor
				score = Quiescence(alpha, beta, DEPTH_ZERO, NOT_IN_CHECK, newPv);
				if (score < beta) {
					return score;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (is_pv && BoardPly != 0 && depth >= 4 && hashMove == NOMOVE) { // Belso iterativ melyites /IID/
			score = AlphaBeta(alpha, beta, depth-2, 0, inCheck, newPv);
			if (score > alpha) hashMove = newPv[0];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		score = -INFINITE; // Pont nullazas
		var E = 0; // Kiterjesztes valtozo
		var R = 0; // LMR Dinamikus valtozo
		var legalMove = 0; // Ervenyes lepes
		var moveScore = 0; // Lepes pontszama
		var oldAlpha = alpha; // Alpha mentese
		var bestMove = NOMOVE; // Legjobb lepes
		var dangerous = false; // Veszelyes..??
		var check = NOT_IN_CHECK; // Sakk lepes
		var currentMove = NOMOVE; // Aktualis lepes
		var bestScore = -INFINITE; // Legjobb pontszam
		var playedMoves = new Array(); // Lepesek tomb
		var futileValue = staticEval + depth * 100; // Futile ertek
		inCheck ? GenerateEvasions() : GenerateAllMoves(false, true);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (hashMove != NOMOVE) { // Atultetesi tablabol lepes
			for (var index = brd_moveStart[BoardPly]; index < brd_moveStart[BoardPly + 1]; index++)
			{
				if (brd_moveList[index] == hashMove) { // Elore soroljuk
					brd_moveScores[index] = 2000000;
					break;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var index = brd_moveStart[BoardPly]; index < brd_moveStart[BoardPly + 1]; index++)
		{
			PickNextMove(index);

			currentMove = brd_moveList[index];
			moveScore = brd_moveScores[index];
			check   = givesCheck(currentMove);

			dangerous = inCheck || check || moveScore >= 800000 || (currentMove & DANGER_MASK) || PawnPush(currentMove);

			if (!dangerous && depth <= 2 && pruneNode && !isMate(bestScore) && legalMove > depth*5) { // Late Move Pruning
				continue;
			}

			if (!dangerous && depth <= 4 && pruneNode && !isMate(bestScore) && futileValue < alpha) { // Futility Pruning
				continue;
			}

			if (!dangerous && pruneNode && !isMate(bestScore) && !See(currentMove, -15 * depth * depth)) { // See Pruning
				continue;
			}

			if (pruneNode && moveScore < 1000 && !isMate(bestScore) && !See(currentMove, -100 * depth)) { // Bad Captures
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

			if (!dangerous && depth >= 3 && legalMove >= 3) // Late Move Reduction
			{
				R = is_pv ? Math.min(Math.log(depth) * Math.log(legalMove) * 0.33 | 0, depth-2)
				          : Math.min(Math.log(depth) * Math.log(legalMove) * 0.66 | 0, depth-2);
			}

			if ((is_pv && legalMove != 0) || R != 0) {
				score = -AlphaBeta(-alpha-1, -alpha, depth+E-R-1, 1, check, newPv); // PVS-LMR
				if (score > alpha) {
					score = -AlphaBeta(-beta, -alpha, depth+E-1, 1, check, newPv); // Full
				}
			} else {
				score = -AlphaBeta(-beta, -alpha, depth+E-1, 1, check, newPv); // Full
			}

			playedMoves[legalMove++] = currentMove; // Ervenyes lepesek

			unMakeMove(); // Lepes visszavonasa

			if (TimeStop == 1) { // Ido vagas
				return 0;
			}

			if (score > bestScore) {

				bestScore = score;

				if (is_pv && (legalMove == 1 || score > alpha)) {

					BuildPv(pv, newPv, currentMove);

					if (BoardPly == 0) {
						UpdatePv(currentMove, score, depth, alpha, beta, pv);
					}
				}

				if (score > alpha) {
					if (score >= beta) {
						if (!inCheck && (currentMove & TACTICAL_MASK) == 0) { // Update Killers & History
							if (SearchKillers[BoardPly][0] != currentMove) {
								SearchKillers[BoardPly][1] = SearchKillers[BoardPly][0];
								SearchKillers[BoardPly][0] = currentMove;
							}
							HistoryGood(currentMove);

							for (var h = 0; h < legalMove-1; h++) {
								HistoryBad(playedMoves[h]);
							}
						}
						StoreHash(currentMove, bestScore, staticEval, FLAG_LOWER, depth);
						return score;
					}
					alpha = score;
					bestMove = currentMove;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (legalMove == 0) {
			return inCheck ? -INFINITE + BoardPly : 0; // Matt : patt
		}

		StoreHash(bestMove, bestScore, staticEval, (alpha != oldAlpha ? FLAG_EXACT : FLAG_UPPER), depth);

		return bestScore;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function HistoryGood(move) {
		var hist = HistoryTable[CHESS_BOARD[FROMSQ(move)]][TOSQ(move)];
		HistoryTable[CHESS_BOARD[FROMSQ(move)]][TOSQ(move)] += (2048 - hist) >> 5;
	}

	function HistoryBad(move) {
		if ((move & TACTICAL_MASK) == 0) {
			var hist = HistoryTable[CHESS_BOARD[FROMSQ(move)]][TOSQ(move)];
			HistoryTable[CHESS_BOARD[FROMSQ(move)]][TOSQ(move)] -= hist >> 5;
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function InitEnginSearch() {
		HashDate = 0; // Hash ido tag nullazas
		HashUsed = 0; // Hash hasznalat nullazas
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

		Nodes = 0; BoardPly = 0; BestMove = 0; TimeStop = 0;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var i = 0; i < MaxDepth; i++) { // Gyilkosok
			SearchKillers[i] = [0, 0];
		}

		for (var i = 0; i < 15; i++) { // Elozmeny tabla
			HistoryTable[i] = new Array(64);
			for (var j = 0; j < 64; j++) {
				HistoryTable[i][j] = 1024;
			}
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function ClearForNewGame() {
		MoveCount = 0;
		brd_fiftyMove = 0;
		MOVE_HISTORY = new Array();
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function SearchPosition(maxSearchDepth) {

		ClearForSearch(); // Nullazas

		var alpha = -INFINITE;
		var beta = INFINITE;
		var countMove = 0;
		var score = 0;
		ScoreDrop = 0;
		HashDate++;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (UI_HOST == HOST_TANKY && maxSearchDepth > 0) { // Also szint
			MaxDepth = maxSearchDepth;
		} else {
			MaxDepth = 64;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var inCheck = isCheck(CurrentPlayer); // Sakk..?

		inCheck ? GenerateEvasions() : GenerateAllMoves(false, false);

		for (var index = brd_moveStart[0]; index < brd_moveStart[1]; index++)
		{
			if (!isLegal(brd_moveList[index])) { // Ervenytelen lepes
				continue;
			}

			countMove++; // Lepesek szamolasa
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var pv = new Array(MaxDepth + 1);

		StartTime = Date.now(); // Kezdo ido!

		if (UI_HOST == HOST_TANKY) postMessage(['StartedTime', StartTime]); // Kuldes!

		search :

		for (CurrDepth = 1; CurrDepth <= maxSearchDepth; CurrDepth++) { // Iterativ melyites

			if (countMove == 1 && CurrDepth > 5 && BestMove) break; // Egy ervenyes lepes

			for (var margin = (CurrDepth >= 4 ? 10 : INFINITE); ; margin *= 2) { // ablak

				alpha = Math.max(score - margin, -INFINITE);
				beta  = Math.min(score + margin,  INFINITE);

				score = AlphaBeta(alpha, beta, CurrDepth, 1, inCheck, pv);

				if (TimeStop == 1) break search; // Lejart az ido

				if (isMate(score)) break; // Matt pontszam

				if (score > alpha && score < beta) break;
			}
		}

		if (UI_HOST == HOST_TANKY) {
			postMessage(['BestMove', BestMove]); // TanKy UI
		} else {
			sendMessage('bestmove '+FormatMove(BestMove.move));
			sendMessage('info hashfull '+Math.round((1000*HashUsed) / HASHENTRIES));
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function UpdatePv(Move, score, depth, alpha, beta, pv) {

		var flags = FLAG_NONE;
		if (score > alpha) flags |= FLAG_LOWER;
		if (score < beta)  flags |= FLAG_UPPER;

		ScoreDrop = depth > 1 && (flags == FLAG_UPPER || BestMove.score - 30 >= score);

		BestMove = { move : Move, score : score, depth : depth };

		if (UI_HOST == HOST_TANKY) // TanKy UI
		{
			postMessage(['SearchInfo', BestMove]); // Info kuldes

			/*var time = (Date.now() - StartTime); // Keresesi ido

			var pvLine = ''; // Pv
			for (var index = 0; pv[index] != NOMOVE; index++) {
				pvLine += ' '+FormatMove(pv[index]);
			}

			if (flags == FLAG_LOWER) depth += '+';
			if (flags == FLAG_UPPER) depth += '-';

			console.log('depth: '+depth+ ' score: '+score+' nodes: '+Nodes+' time: '+time+' pv:'+pvLine);*/
		}
		else // Worker, Node.js, JSUCI
		{
			var time = (Date.now() - StartTime); // Keresesi ido

			var pvLine = ''; // Pv
			for (var index = 0; pv[index] != NOMOVE; index++) {
				pvLine += ' '+FormatMove(pv[index]);
			}

			if (score < -ISMATE) {
				score = 'mate '+((-INFINITE - score) / 2); // -Matt
			} else if (score > ISMATE) {
				score = 'mate '+((INFINITE - score + 1) / 2); // +Matt
			} else {
				score = 'cp '+score;
			}

			if (flags == FLAG_LOWER) score += ' lowerbound';
			if (flags == FLAG_UPPER) score += ' upperbound';

			sendMessage('info depth '+depth+' score '+score+' nodes '+Nodes+' time '+time+' pv'+pvLine);
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
		} else if (UI_HOST != HOST_WEB) { // Worker, JSUCI
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

	if (typeof WorkerGlobalScope != 'undefined') { // Worker

		UI_HOST = HOST_WORKER;

	} else if (typeof process != 'undefined') { // Node.js

		UI_HOST = HOST_NODEJS;
		var nodefs = require('fs');
		process.stdin.setEncoding('utf8');
		process.stdin.on('data', function(data) {
			onMessage({ data: data });
		});
		process.stdin.on('end', function() {
			process.exit();
		});

	} else if (typeof lastMessage != 'undefined') { // JSUCI

		UI_HOST = HOST_JSUCI;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	var uci_options = { 'Hash': '32' };

	var onMessage = function(command) {

		if (command !== null && command.data !== undefined)
		{
			if (command.data.constructor === Array && command.data[0] == 'HashKeys') // TanKy UI
			{
				UI_HOST = HOST_TANKY;
				SideKeyLow = command.data[1];
				SideKeyHigh = command.data[2];
				PieceKeysLow = command.data[3];
				PieceKeysHigh = command.data[4];
				CastleKeysLow = command.data[5];
				CastleKeysHigh = command.data[6];
				return;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			var tokens  = [];
			var message = '';
			var msgList = command.data.toString().split('\n');

			for (var msgNum = 0; msgNum < msgList.length; msgNum++)
			{
				message = msgList[msgNum].replace(/(\r\n|\n|\r)/gm,'');
				message = message.trim();
				message = message.replace(/\s+/g,' ');
				tokens  = message.split(' ');
				command = tokens[0];

				if (!command) continue;

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
						if (SideKeyLow == 0 && UI_HOST != HOST_TANKY) InitHashKeys();
						onMessage({ data: 'position startpos' }); // Start position..

					break;

				// ############################################################################################

					case 'position':

						if (SideKeyLow == 0) { // Nincs HashKey
							if (UI_HOST == HOST_TANKY)
							return postMessage(['debug', 'No HashKey! Inditsd ujra a jatekot!']); // TanKy UI
							else
							return sendMessage('info string First send a "u" command for New Game!');
						}

						ClearForNewGame(); // Valtozok nullazasa

						START_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -';

						var arr = getArr('fen', 'moves', tokens); // FEN parameterek

						if (arr.lo > 0) {
							if (arr.lo <= arr.hi) START_FEN  =     tokens[arr.lo]; arr.lo++; // CHESS_BOARD
							if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo]; arr.lo++; // CurrentPlayer
							if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo]; arr.lo++; // CastleRights
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
								BoardPly = 0; // Hack!
							}
						}

					break;

				// ############################################################################################

					case 'go':

					    MaxSearchTime  = getInt('movetime', 0, tokens); // Time!
					    MinSearchTime  = MaxSearchTime * 1; // Hack: Early exit!
					var maxSearchDepth = getInt('depth'   , 0, tokens); // Depth

						if (MaxSearchTime == 0)
						{
							var movesToGo = getInt('movestogo', 30, tokens);

							if (CurrentPlayer == WHITE) {
								var Inc  = getInt('winc' , 0, tokens);
								var Time = getInt('wtime', 0, tokens);
							} else {
								var Inc  = getInt('binc' , 0, tokens);
								var Time = getInt('btime', 0, tokens);
							}

							Time = Time - Math.min(1000, Time / 10);

							var total = Time + Inc * (movesToGo - 1);

							MaxSearchTime = Math.min(total * 0.5, Time) | 0;

							MinSearchTime = Math.min(total / movesToGo, Time) | 0;
						}

						if (maxSearchDepth > 0) { // Fix melysegnel max 1 ora!
							MinSearchTime = 1000 * 3600;
						}

						if (MaxSearchTime < MinSearchTime) { // Max >= Min!
							MaxSearchTime = MinSearchTime;
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
						}

					break;

				// ############################################################################################

					default:

						sendMessage(command+': unknown command!');

					break;
				}
			}
		}
	};

	// Hack: in Node.js the onmessage is undefined in 'use strict' mode, but "var onmessage" is crashed in IE
	// So we declare the on[M]essage function and if we have onmessage (in browsers) then we update with it..

	if (typeof self != 'undefined') {
		self.onmessage = onMessage;
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
		msg += Letters[TableFiles  [to]-1]+''+TableRanks  [to]; // Ahova

		if (PROMOTED(Move) != 0) { // Promocio
			msg += ['', '', 'n', 'b', 'r', 'q', ''][PROMOTED(Move) & 0x07];
		}

		return msg;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function GetMoveFromString(moveString) {

		GenerateAllMoves(false, false);

		for (var index = brd_moveStart[BoardPly]; index < brd_moveStart[BoardPly + 1]; index++) {
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

		SideKeyLow  = RAND_32(); // Oldal
		SideKeyHigh = RAND_32(); // Oldal

		for (var pce = 0; pce <= BLACK_KING; pce++) { // Babuk (En Passant: 0)
			for (var sq = 0; sq < 64; sq++) {
				PieceKeysLow [(pce << 6) | sq] = RAND_32();
				PieceKeysHigh[(pce << 6) | sq] = RAND_32();
			}
		}

		for (var index = 0; index < 16; index++) { // Sancolas
			CastleKeysLow [index] = RAND_32();
			CastleKeysHigh[index] = RAND_32();
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Babuk inicializalasa
	function InitPieceList() {

		brd_Material[0] = 0; // Feher anyag
		brd_Material[8] = 0; // Fekete anyag

		for (var pce = 0; pce <= BLACK_KING; pce++) {

			brd_pieceCount[pce] = 0; // Darabszam nullazas

			BitBoard[pce << 1 | LOW]  = 0; // BitBoard nullazas
			BitBoard[pce << 1 | HIGH] = 0;

			for (var num = 0; num < 16; num++) { // Max 15 db azonos lehet (9 Vezer)
				brd_pieceList[(pce << 4) | num] = EMPTY; // Mezo nullazas (64. mezo)
			}
		}

		for (var sq = 0; sq < 64; sq++) {

			brd_pieceIndex[sq] = 0; // Mezo index nullazas

			if (CHESS_BOARD[sq] != 0)
			{
				var piece = CHESS_BOARD[sq];
				var color = CHESS_BOARD[sq] & 0x8;

				ADDING_PCE(piece, sq, color); // Babu mentese!
				ADDING_NN_PCE(piece, sq, color); // Hozzaadas!
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
				if ((CHESS_BOARD[sq] & 0x07) === PAWN) { // Gyalog
					brd_pawnKeyLow  ^= PieceKeysLow [(CHESS_BOARD[sq] << 6) | sq];
					brd_pawnKeyHigh ^= PieceKeysHigh[(CHESS_BOARD[sq] << 6) | sq];
				}
			}
		}

		if (CurrentPlayer === WHITE) { // Aki lephet
			brd_hashKeyLow  ^= SideKeyLow;
			brd_hashKeyHigh ^= SideKeyHigh;
		}

		if (EN_PASSANT != 0) { // En Passant
			brd_hashKeyLow  ^= PieceKeysLow [EN_PASSANT];
			brd_hashKeyHigh ^= PieceKeysHigh[EN_PASSANT];
		}

		brd_hashKeyLow  ^= CastleKeysLow [CastleRights]; // Sancolas
		brd_hashKeyHigh ^= CastleKeysHigh[CastleRights]; // Sancolas
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
		FEN += CurrentPlayer === WHITE ? 'w' : 'b';

		if (CastleRights == 0) { // Nincs sancolas
			FEN += ' -';
		} else {
			FEN += ' '; // Szokoz hozzadasa
			if (CastleRights & CASTLEBIT.WK) FEN += 'K'; // White King side
			if (CastleRights & CASTLEBIT.WQ) FEN += 'Q'; // White Queen side
			if (CastleRights & CASTLEBIT.BK) FEN += 'k'; // Black King side
			if (CastleRights & CASTLEBIT.BQ) FEN += 'q'; // Black Queen side
		}

		if (EN_PASSANT == 0) { // Nincs En Passant
			FEN += ' -';
		} else {
			FEN += ' '+(Letters[TableFiles[EN_PASSANT]-1]+''+TableRanks[EN_PASSANT]);
		}

		FEN += ' '+brd_fiftyMove; // 50 lepes
		FEN += ' '+(1 + (MoveCount - (CurrentPlayer === BLACK)) / 2); // Lepespar

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

		CurrentPlayer = Fen[1] === 'w' ? WHITE : BLACK; // Kezdo!

		CastleRights = 0; // Sancolas nullazas!

		for (index = 0; index < Fen[2].length; index++) { // Sancolasok
			switch (Fen[2][index]) {
				case 'K': CastleRights |= CASTLEBIT.WK; break; // White King side
				case 'Q': CastleRights |= CASTLEBIT.WQ; break; // White Queen side
				case 'k': CastleRights |= CASTLEBIT.BK; break; // Black King side
				case 'q': CastleRights |= CASTLEBIT.BQ; break; // Black Queen side
				default: break;
			}
		}

		if (Fen[3] == '-') { // Nincs En Passant
			EN_PASSANT = 0;
		} else {
			EN_PASSANT = parseInt(SQUARES[Fen[3].toUpperCase()]);
		}

		brd_fiftyMove = Fen[4] != null ? Fen[4] : 0; // 50 lepes

		InitChessNN(); // Halozat inicializalasa
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
	S( -8,   8), S( -1,  -2), S(  5, -13), S( 19,  -9), S( 19,  -9), S(  5, -13), S( -1,  -2), S( -8,   8),
	S(  3,  15), S(  7,  11), S( 24,   2), S( 19,  -5), S( 19,  -5), S( 24,   2), S(  7,  11), S(  3,  15),
	S( -9,  13), S(  2,   4), S(  2,  -2), S( 21, -11), S( 21, -11), S(  2,  -2), S(  2,   4), S( -9,  13),
	S(-18,   3), S(-17,   0), S(  4,  -8), S( 14, -13), S( 14, -13), S(  4,  -8), S(-17,   0), S(-18,   3),
	S(-13,  -3), S( -5,  -5), S(  4,  -3), S(  8,  -1), S(  8,  -1), S(  4,  -3), S( -5,  -5), S(-13,  -3),
	S(-17,  -1), S(  5,  -3), S( -7,  10), S(  3,   6), S(  3,   6), S( -7,  10), S(  5,  -3), S(-17,  -1),
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0)
	];

	var KnightPst = [
	S(-161,-43), S(-62, -49), S(-63, -23), S(-15, -29), S(-15, -29), S(-63, -23), S(-62, -49), S(-161,-43),
	S(-63, -33), S(-39, -15), S( -3, -23), S(-11, -10), S(-11, -10), S( -3, -23), S(-39, -15), S(-63, -33),
	S(-23, -35), S( 19, -25), S( 16,  -3), S( 17,  -1), S( 17,  -1), S( 16,  -3), S( 19, -25), S(-23, -35),
	S(  3, -22), S(  6,  -5), S( 14,   8), S( 10,  15), S( 10,  15), S( 14,   8), S(  6,  -5), S(  3, -22),
	S(-10, -16), S( 12, -14), S( 11,   4), S( 10,   9), S( 10,   9), S( 11,   4), S( 12, -14), S(-10, -16),
	S(-18, -25), S( -1, -22), S(  6, -16), S( 11,  -2), S( 11,  -2), S(  6, -16), S( -1, -22), S(-18, -25),
	S(-21, -40), S(-21, -24), S( -4, -26), S( -1, -15), S( -1, -15), S( -4, -26), S(-21, -24), S(-21, -40),
	S(-49, -38), S(-22, -38), S(-30, -24), S(-18, -19), S(-18, -19), S(-30, -24), S(-22, -38), S(-49, -38)
	];

	var BishopPst = [
	S(-31, -16), S(-14, -15), S(-43, -11), S(-37,  -7), S(-37,  -7), S(-43, -11), S(-14, -15), S(-31, -16),
	S(-43,  -5), S(-22,  -1), S(-25,   1), S(-21,  -6), S(-21,  -6), S(-25,   1), S(-22,  -1), S(-43,  -5),
	S(  1,  -7), S( 11,  -6), S( 16,  -2), S( -5,  -1), S( -5,  -1), S( 16,  -2), S( 11,  -6), S(  1,  -7),
	S(-11,  -6), S(-11,   1), S(  5,   3), S( 13,   8), S( 13,   8), S(  5,   3), S(-11,   1), S(-11,  -6),
	S( -6, -11), S(  0,  -8), S( -4,   5), S( 20,   4), S( 20,   4), S( -4,   5), S(  0,  -8), S( -6, -11),
	S(-10,  -7), S(  8,  -7), S( 12,  -1), S(  5,   6), S(  5,   6), S( 12,  -1), S(  8,  -7), S(-10,  -7),
	S( -5, -15), S( 18, -16), S(  9, -11), S(  0,  -3), S(  0,  -3), S(  9, -11), S( 18, -16), S( -5, -15),
	S(-22, -13), S( -6, -10), S( -8,  -7), S( -7,  -6), S( -7,  -6), S( -8,  -7), S( -6, -10), S(-22, -13)
	];

	var RookPst = [
	S( -6,  18), S(  4,  14), S(-10,  19), S(  6,  15), S(  6,  15), S(-10,  19), S(  4,  14), S( -6,  18),
	S(-11,   8), S( -8,   8), S(  3,   6), S(  6,   1), S(  6,   1), S(  3,   6), S( -8,   8), S(-11,   8),
	S( -8,  13), S( 10,  16), S(  4,  14), S( -1,  15), S( -1,  15), S(  4,  14), S( 10,  16), S( -8,  13),
	S(-16,  16), S( -8,  13), S(  6,  18), S(  6,  11), S(  6,  11), S(  6,  18), S( -8,  13), S(-16,  16),
	S(-24,  11), S( -3,  10), S(-13,  13), S(  0,   7), S(  0,   7), S(-13,  13), S( -3,  10), S(-24,  11),
	S(-25,   2), S( -9,   5), S( -6,  -1), S( -4,  -1), S( -4,  -1), S( -6,  -1), S( -9,   5), S(-25,   2),
	S(-27,   1), S( -4,  -7), S( -5,  -3), S(  4,  -5), S(  4,  -5), S( -5,  -3), S( -4,  -7), S(-27,   1),
	S( -7,  -9), S( -3,  -5), S( -4,   1), S(  8,  -7), S(  8,  -7), S( -4,   1), S( -3,  -5), S( -7,  -9)
	];

	var QueenPst = [
	S( -8, -18), S(  0,  -7), S(  4,   2), S(  8,   2), S(  8,   2), S(  4,   2), S(  0,  -7), S( -8, -18),
	S( -1, -22), S(-26,  -8), S( -9,   2), S(-10,  19), S(-10,  19), S( -9,   2), S(-26,  -8), S( -1, -22),
	S(  9, -17), S(  1,   0), S(  1,   9), S( -9,  28), S( -9,  28), S(  1,   9), S(  1,   0), S(  9, -17),
	S(-13,  11), S(-14,  26), S(-10,  13), S(-21,  32), S(-21,  32), S(-10,  13), S(-14,  26), S(-13,  11),
	S( -8,  -1), S( -7,  15), S( -7,  11), S( -9,  24), S( -9,  24), S( -7,  11), S( -7,  15), S( -8,  -1),
	S(-12,  -4), S(  5, -12), S( -6,   8), S( -4,   4), S( -4,   4), S( -6,   8), S(  5, -12), S(-12,  -4),
	S(-15, -24), S( -2, -29), S( 12, -22), S(  8, -10), S(  8, -10), S( 12, -22), S( -2, -29), S(-15, -24),
	S( -8, -37), S( -7, -34), S( -4, -27), S(  7, -26), S(  7, -26), S( -4, -27), S( -7, -34), S( -8, -37)
	];

	var KingPst = [
	S(-48, -76), S( 10, -41), S(-19, -20), S(-64, -34), S(-64, -34), S(-19, -20), S( 10, -41), S(-48, -76),
	S(-13, -26), S( -8, -13), S(-23,   5), S(-37,   3), S(-37,   3), S(-23,   5), S( -8, -13), S(-13, -26),
	S(  1, -16), S( 14,   8), S( -3,  17), S(-49,  10), S(-49,  10), S( -3,  17), S( 14,   8), S(  1, -16),
	S(-27, -15), S( -7,   9), S(-26,  15), S(-55,  16), S(-55,  16), S(-26,  15), S( -7,   9), S(-27, -15),
	S(-27, -24), S(-12,  -7), S(-29,   9), S(-56,  15), S(-56,  15), S(-29,   9), S(-12,  -7), S(-27, -24),
	S( 10, -28), S( 17, -10), S( -7,  -1), S(-31,   7), S(-31,   7), S( -7,  -1), S( 17, -10), S( 10, -28),
	S( 43, -38), S( 38, -23), S(  5, -11), S(-13,  -5), S(-13,  -5), S(  5, -11), S( 38, -23), S( 43, -38),
	S( 47, -73), S( 55, -47), S( 22, -35), S( 24, -42), S( 24, -42), S( 22, -35), S( 55, -47), S( 47, -73)
	];

	// Extra
	var BishopPair  = S( 48,  38);
	var TempoBonus  = S( 33,  25);
	var BlockedRook = S( 47,  -7);

	// File & Rank
	var RookOn7th    = S(  0,  27);
	var QueenOn7th   = S(-15,  19);
	var RookHalfOpen = S(  6,  14);
	var RookFullOpen = S( 27,   4);

	// King Safety
	var KingShield = new Array(5);
	KingShield[0] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0) ];
	KingShield[1] = [ S(  0,   0), S(  0,   0), S( 15,   0), S( 21,   0), S( 16,   0) ];
	KingShield[2] = [ S(  0,   0), S(  0,   0), S( 30,   0), S( 26,   0), S(  1,   0) ];
	KingShield[3] = [ S(  0,   0), S(  0,   0), S( 34,   0), S( -1,   0), S(  2,   0) ];
	KingShield[4] = [ S(  0,   0), S(  0,   0), S( 12,   0), S(  8,   0), S( 10,   0) ];

	var KingSafetyMull = [ S(  0,   0), S(  8,   0), S( 21,   0), S( 34,   0), S( 45,   0) ];

	// Material
	var DeltaValue = [ 0, 100, 343, 341, 518, 1005, 20000, 0, 0, 100, 343, 341, 518, 1005, 20000 ];

	var PieceValue = [ 0, S( 80,  87), S(343, 314), S(341, 322), S(481, 518), S(1005, 1005), S(20000, 20000),
	                0, 0, S( 80,  87), S(343, 314), S(341, 322), S(481, 518), S(1005, 1005), S(20000, 20000) ];

	// Threats
	var ThreatScore = new Array(7);
	ThreatScore[0] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0) ];
	ThreatScore[1] = [ S(  0,   0), S(  0,   0), S( 67,  22), S( 64,  45), S( 83,  10), S( 70,  14), S(  0,   0) ];
	ThreatScore[2] = [ S(  0,   0), S(  0,   0), S(  0,   0), S( 35,  27), S( 64,  12), S( 54,  -9), S(  0,   0) ];
	ThreatScore[3] = [ S(  0,   0), S(  0,   0), S( 18,  24), S(  0,   0), S( 50,  21), S( 68,  52), S(  0,   0) ];
	ThreatScore[4] = [ S(  0,   0), S(  0,   0), S( 21,  23), S( 23,  31), S(  0,   0), S( 82,  22), S(  0,   0) ];
	ThreatScore[5] = [ S(  0,   0), S(  0,   0), S(  6,  20), S(  3,  20), S( -2,  20), S(  0,   0), S(  0,   0) ];
	ThreatScore[6] = [ S(  0,   0), S(  0,   0), S( 10,  29), S( 17,  29), S(  0,  32), S(  0,   0), S(  0,   0) ];

	// Passed Pawn
	var PassedPawnBase = [ S(  0,   0), S(  0,   0), S( 10,  20), S( 10,  20), S(  9,  27), S( 23,  41), S( 43,  67), S( 78, 107) ];
	var PassedHalfFree = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( -2,   3), S(  4,   5), S( 13,  14), S( 21,  34) ];
	var PassedFullFree = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-23,  17), S( -9,  33), S( 41,  87), S( 62, 137) ];

	var PassedDistanceOwn = new Array(7);
	PassedDistanceOwn[0] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  6,  27), S( 36,  59), S( 34,  93), S( 56, 107) ];
	PassedDistanceOwn[1] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( 17,  23), S( 36,  44), S( 53,  77), S( 49,  65) ];
	PassedDistanceOwn[2] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  5,   8), S( 17,  13), S( 19,  16), S( 34,  39) ];
	PassedDistanceOwn[3] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( -9,  -4), S( -7,  -8), S( 10, -16), S( 18,  -5) ];
	PassedDistanceOwn[4] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-12, -16), S( -8, -22), S(-10, -30), S( -2, -33) ];
	PassedDistanceOwn[5] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-17, -14), S(-12, -26), S( -9, -36), S( -5, -38) ];
	PassedDistanceOwn[6] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  9, -13), S(  5, -26), S( -7, -32), S(  5, -47) ];
	PassedDistanceOwn[7] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-13,  -6), S( -3, -26), S( 17, -32), S(  7, -46) ];

	var PassedDistanceThem = new Array(7);
	PassedDistanceThem[0] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-18, -30), S(  2, -35), S(  9, -54), S(  2, -64) ];
	PassedDistanceThem[1] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( -4, -11), S( 12, -23), S( 15, -42), S(  9, -59) ];
	PassedDistanceThem[2] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( 14,  -9), S(  8, -13), S( 18, -18), S( 15, -12) ];
	PassedDistanceThem[3] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( -6,   2), S(-16,  18), S(-15,  50), S( 15,  85) ];
	PassedDistanceThem[4] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-18,  15), S(-12,  39), S(-19,  82), S( -2, 113) ];
	PassedDistanceThem[5] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-14,  23), S(-13,  50), S(-11,  86), S( 13, 115) ];
	PassedDistanceThem[6] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S( -2,  26), S( -3,  54), S( -6,  86), S(  3, 124) ];
	PassedDistanceThem[7] = [ S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(-17,  24), S( -8,  50), S( -8,  80), S(-23, 111) ];

	// Pawn Evals
	var PawnDoubled       = [ S(  0,   0), S(  0,   0), S(-10, -20), S(-19, -11), S( -4, -15), S(-12, -11), S( 23, -16), S(-10, -20) ];
	var PawnDoubledOpen   = [ S(  0,   0), S(  0,   0), S(-10, -20), S( -4, -25), S(  6, -19), S( -3,  -7), S(  3,  -3), S(  8,  -2) ];
	var PawnIsolated      = [ S(  0,   0), S(  0,   0), S(-10,  -9), S(-13, -12), S( -6, -13), S( -6, -17), S( -2, -10), S(-10, -20) ];
	var PawnIsolatedOpen  = [ S(  0,   0), S(  0,   0), S(-25, -16), S(-28, -18), S(-25, -14), S(-13, -19), S( -6, -26), S(-18, -33) ];
	var PawnBackward      = [ S(  0,   0), S(  0,   0), S( -6,  -4), S( -3, -10), S(-11, -15), S( -7, -17), S(  0,  -6), S( -8, -10) ];
	var PawnBackwardOpen  = [ S(  0,   0), S(  0,   0), S(-16, -14), S(-25, -11), S(-23,  -6), S( -8,  -8), S( -8, -18), S(-19, -20) ];
	var PawnConnected     = [ S(  0,   0), S(  0,   0), S(  2,  -2), S(  6,  -1), S( 10,  -4), S( 15,   2), S( 21,  40), S(  0,   0) ];
	var PawnConnectedOpen = [ S(  0,   0), S(  0,   0), S(  2, -10), S(  7,  -5), S( 14,   4), S( 20,  17), S( 34,  44), S( 66,  45) ];

	// Mobility
	var KnightMob = [ S(-27, -83), S(-16, -38), S( -6, -18), S( -4,  -6), S(  5,  -5), S( 10,   5), S( 16,   2), S( 22,   2), S( 33,  -6) ];
	var BishopMob = [ S(-42, -53), S(-30, -48), S(-14, -28), S(-11, -13), S( -3,  -4), S(  4,   1), S(  7,   5), S(  8,   6), S( 11,  10), S( 11,   9), S( 15,   3), S( 33,   5), S( 17,  12), S( 31,   6) ];
	var RookMob   = [ S(-42, -88), S(-19, -50), S(-13, -27), S(-13, -15), S(-12,  -8), S( -8,   0), S( -6,   6), S(  0,   9), S(  3,  11), S(  9,  14), S(  9,  19), S( 14,  21), S( 18,  20), S( 18,  22), S( 16,  23) ];
	var QueenMob  = [ S(-200, -26), S(-19, -166), S(-22, -104), S(-19, -54), S(-18, -63), S(-17, -53), S(-11, -51), S( -7, -43), S( -5, -24), S( -2, -20), S( -2,  -9), S(  0,  -5), S(  2,  -2), S(  5,   5), S(  7,   7), S(  5,  14), S(  5,  19), S(  8,  15), S( 13,  24), S( 20,  24), S( 22,  25), S( 22,  31), S( 32,  24), S( 28,  31), S( 29,  26), S( 23,  24), S(  5,  21), S( 27,  22) ];

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
// Chess Neural Network by Tamas Kuzmics
// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	var INPUT_NEURONS     = 768;
	var HIDDEN_NEURONS    = 16;
	var OUTPUT_NEURONS    = 1;
	var NN_HIDDEN_LAYER   = new Array(HIDDEN_NEURONS);
	var NN_OUTPUT_LAYER   = new Array(OUTPUT_NEURONS);
	var NN_HIDDEN_BIASES  = new Array(HIDDEN_NEURONS);
	var NN_OUTPUT_BIASES  = new Array(OUTPUT_NEURONS);
	var NN_HIDDEN_WEIGHTS = new Array(HIDDEN_NEURONS * INPUT_NEURONS);
	var NN_OUTPUT_WEIGHTS = new Array(OUTPUT_NEURONS * HIDDEN_NEURONS);

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	setTimeout(function() {
		for (var neuron = 0; neuron < HIDDEN_NEURONS; neuron++) {
			NN_HIDDEN_BIASES[neuron] = CHESS_NN.biases[0][neuron];
			for (var input_neuron = 0; input_neuron < INPUT_NEURONS; input_neuron++) {
				NN_HIDDEN_WEIGHTS[neuron * INPUT_NEURONS + input_neuron] = CHESS_NN.weights[0][neuron][input_neuron];
			}
		}
		for (var neuron = 0; neuron < OUTPUT_NEURONS; neuron++) {
			NN_OUTPUT_BIASES[neuron] = CHESS_NN.biases[1][neuron];
			for (var input_neuron = 0; input_neuron < HIDDEN_NEURONS; input_neuron++) {
				NN_OUTPUT_WEIGHTS[neuron * HIDDEN_NEURONS + input_neuron] = CHESS_NN.weights[1][neuron][input_neuron];
			}
		}
		CHESS_NN = null; // remove from memory!
	}, 0);

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function CHESS_NN_IDX(piece, sq, side) {
		return sq + 64 * (piece - 1) + 384 * (side == BLACK);
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function ADDING_NN_PCE(pce, sq, side) {
		var input_neuron = CHESS_NN_IDX((pce & 0x07), sq, side);
		for (var neuron = 0; neuron < HIDDEN_NEURONS; neuron++) {
			NN_HIDDEN_LAYER[neuron] += NN_HIDDEN_WEIGHTS[neuron * INPUT_NEURONS + input_neuron];
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function DELETE_NN_PCE(pce, sq, side) {
		var input_neuron = CHESS_NN_IDX((pce & 0x07), sq, side);
		for (var neuron = 0; neuron < HIDDEN_NEURONS; neuron++) {
			NN_HIDDEN_LAYER[neuron] -= NN_HIDDEN_WEIGHTS[neuron * INPUT_NEURONS + input_neuron];
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function MOVE_NN_PCE(pce, from, to) { // assume that the current player moved
		ADDING_NN_PCE(pce, to, CurrentPlayer);
		DELETE_NN_PCE(pce, from, CurrentPlayer);
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function InitChessNN() {
		NN_HIDDEN_LAYER = NN_HIDDEN_BIASES.slice(0); // biases
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function ChessNNEval() {
		for (var neuron = 0; neuron < OUTPUT_NEURONS; neuron++) {
			NN_OUTPUT_LAYER[neuron] = NN_OUTPUT_BIASES[neuron]; // biases
			for (var input_neuron = 0; input_neuron < HIDDEN_NEURONS; input_neuron++) {
				if (NN_HIDDEN_LAYER[input_neuron] > 0) { // ReLU -> hidden layer activation
					NN_OUTPUT_LAYER[neuron] += NN_HIDDEN_LAYER[input_neuron] * NN_OUTPUT_WEIGHTS[neuron * HIDDEN_NEURONS + input_neuron];
				}
			}
		}
		return NN_OUTPUT_LAYER[0];
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	var CHESS_NN = {
		weights: [
			[
				[ 0.023456925259728846, 0.03510350219072219, -0.01870934282177904, 0.028516613396281365, 0.025610071899253586, 0.01062138810047145, 0.03196573471177646, -0.013044709295628308, -0.6337221816422621, -0.6213561458889103, 2.8512116605003954, 0.06881784692071914, 4.384391592959272, 0.268966029714588, 0.2950901237774475, -0.8488816234882239, -1.5970526175783923, 1.6632324528181868, 1.1722567517370628, 1.7463294374523881, 2.5451132101785183, 2.952667650262479, 0.5304090012627648, -0.7594670116280522, 0.10210849322313911, -0.2135673847501434, -0.25404542837541544, 0.9404972534407803, 1.0161704995764886, 1.4416271417474693, -0.24680043192026072, -0.26109654514422503, 0.78508926575759, -0.5933360579925048, -0.16356776558629169, 0.13643801018595564, -0.09068073785678897, -0.37102003151726826, -0.6228789914336844, 0.3362567801125888, 0.3553531516462452, -0.37581360631777555, 0.7295629091259429, -0.31909066279262216, -1.681269109908557, -1.3459980657770794, -3.532041093279227, -0.19015318214278318, 0.6607192228392567, -0.434903970778236, 0.9843435119855523, -1.7840456788309542, -1.552164055184543, -3.3885145147071647, -3.1845650631637774, -0.2363722700335478, 0.009646782722384221, -0.007289830447961625, 0.014857155137734997, -0.01732003157983705, -0.011929698112431886, -0.030290685707770035, -0.03062472393736775, -0.020617607882694393, -3.090115597275307, 0.5939753152997087, 1.679809717738612, -1.2755403911083851, 2.74267900976831, 0.23941838971815618, 4.394548397912572, 1.782361799174485, 1.8231407515316245, -1.34603930939962, 1.9138020928163253, 2.2055843349486293, 2.091889343980664, -1.8883977393170421, 0.6246914869416108, 0.5911388816767887, 0.5708900902343368, 1.0681064825481965, 1.9129125800416897, 0.8322327808858859, 2.0484390930950793, 0.8813299477467536, 0.6729711214183925, 1.2916562238843152, 1.8767239642363582, 0.852176547702964, -0.15232537850437305, 2.2502743713889815, 0.2764527575645026, 1.3151094294483012, 1.91461592897466, 3.199358634431567, -1.2495202343004461, 1.4523554345005774, 0.4338077112847379, 0.07819915274163274, 0.31243100519043443, 1.0149525948092828, 2.120188761916604, 1.827382848598052, -0.27075378995280425, -1.818879838625557, -0.028808670132537233, -0.08731478765498146, 1.1821175489748583, 0.3298482842296664, 1.418620107778804, 1.8624632754941912, -0.8264542903762906, -0.6201959688533226, -0.6419629646499463, -0.4156316681015093, -0.4015170410791209, 1.2992878332928177, -0.39982356747375575, 0.9581264781909479, -2.960458245323931, -1.510202948029461, -1.753597513425383, 0.37400184656915475, 0.12420783351771825, 0.9209989094747075, 0.2649367389187658, 1.8427160996924183, -2.3788621702534156, 0.8717803168799679, 2.729458774085041, 1.0301336823052818, -5.156373383065928, 0.5655363264264194, 0.010721463040452208, -3.9179511687132353, -1.4622844386318796, -0.2531319747417507, 0.7715464441644312, 0.5885594661422521, -0.06412351006615509, 1.9347231725949787, -1.2144225519094989, 1.4300975908056937, -0.3904072907846731, 1.196228346866957, -0.2779184850799586, 1.4528087305109216, 1.2788825731852218, 2.6968174463193133, 0.4680824166057463, 0.44846301607527805, 0.5177741298799868, 0.9321142863839262, 1.1958572733246797, 1.5812992942419046, 1.6361339508697665, 1.2410958850432512, 1.7382303189754034, 0.43759335571947683, 0.21379293635584193, 1.8198922104064246, 0.47747626702091, 0.05535974312301808, 0.012426658406797155, 1.6024156157952314, 0.5853189915425394, 2.5136154965287973, 1.8973764399558024, 0.8411832839183989, 1.4401492572233976, 1.323161509180669, 0.9638609721452459, -0.32621060433501614, 1.035746067435447, -0.19244073556331967, 0.1324812921570788, 1.0762554632274048, 0.43557477881101214, 1.4342505826868628, -0.15104474430522685, -0.7665079457142108, -0.4523336298489972, 3.5702948006289708, 1.0436372382861063, 1.5288862905804557, 1.0535143568847853, -1.018573199924146, 0.05922830865117738, -1.2908848157702704, -0.2513167287299465, 1.215553136616071, 3.6056206801251123, 0.6680556863676096, 1.8577624838963958, 0.4198444405824092, 2.354234222974374, 3.5102692095701413, 2.835430922133761, 2.1400366764911785, 2.2004586931819254, 0.5607320949783986, 1.191224433224379, 0.9956192565153824, 1.905529221115038, 0.859126457993368, 1.6938417124000817, 1.4773406193263499, 2.104085859782179, 0.6268444054876436, -0.382026316017159, 2.5698637317909045, 2.099651864555664, 1.2885170477718382, 2.6491214144184383, 3.3163528905181554, 1.6204972876748727, 1.3753156943876503, 1.4666285194360265, 1.673813898070924, 1.4390451508244286, 2.0090337527637954, 3.393310829662436, 2.111458608445787, 0.44409977449460447, 0.4738115919407572, -0.46151499059118306, 1.16357043276502, 2.332835770758855, 1.9753748094967394, 4.053344716625007, 2.167029556860156, -1.9534339952114093, 0.08397039933390879, -0.28378428577831105, 0.9387215361173603, 1.408455047945327, 1.1320050806014246, 3.690733859073084, 4.339524403960525, -1.635307456384526, -0.47915920935779477, -0.0776982542959757, -0.007860550068733846, 0.29165772766315357, 2.499713673131964, 4.291753156118997, 0.6366273107398674, -0.04844657844653227, -0.2937978772507979, 0.3755196078068811, 0.9970738760756599, 1.3463212555753181, 2.543299245486722, 4.348314263430727, 2.1109727148246833, -1.0320430164306762, -1.3894017754117773, -0.737333215267799, -0.8546223639989889, -2.026214420806961, -1.2027736946804042, -0.4363798762162568, 4.024932165852502, 2.0850637120656708, 1.6242897099939781, 0.7209112103056698, 0.9448107254512441, -0.6910174271319347, -2.0853332972390928, 3.7380656888032786, 3.918573722333398, 1.2249319813580053, 1.63860315932062, 1.6794505849496473, 1.2748690335638568, 1.7663361312179304, 3.639856679549519, 3.899078723895623, 5.1640381292452915, 3.097732071417202, -2.730630251616433, 0.9843307475320757, 1.8696835290540736, 2.4394186830514752, 3.0810183733465917, 4.585576668800051, 4.757404746177993, -0.2955894228216099, 1.4016135901106412, 0.6872168855544508, 1.7742540218600278, 2.7192587884803503, 3.4193547704356186, 3.1904711213889434, 4.144637995827736, -0.1638829215244488, -0.035494906706603296, 0.8960533266513974, 1.999783910373308, 1.0966655275504265, 2.5933626997394765, 3.6115072357133537, 5.316295550287094, -0.26733279317225644, 1.2655061192052122, 0.9508738850165085, 1.4620859738841412, 1.113281340256617, 2.5830435860606005, 3.2662157304576294, 4.862129330387024, 2.6061012238224404, 1.1840939580429959, 2.0892684793727594, 1.0012468868961348, 1.291724468324887, 3.0013682901833594, 3.539173069781236, 1.4389228301939565, -2.7019963739728303, 0.7964839745431673, -1.8986317331833449, -1.1821870050250733, 1.5643703652684227, -3.0425484858066127, -4.001467214698161, 0.09113629017370936, 2.1663382003544305, 0.8890353441847901, 0.3481555072796692, -0.03044783377570803, 0.8450320502325313, -0.5092626728410445, -1.3987639486349515, 1.0480001090164157, 1.8904764723082128, 1.003008921301519, 1.9438144880939412, -0.1764363771863389, -1.1985656400449276, -2.0054411456457975, -3.6162137517922814, -1.9231680341031276, 2.4054009425359735, 1.2680576352975323, 1.296731659003129, 0.6625791301268424, -0.676372920811352, -0.38517294982254285, -3.6958174136053445, -1.760952647005701, 2.4174300589664863, -0.23937481483954112, 0.7779399627903063, 2.304058224686741, -0.007227980161972446, -1.5970642829793191, -1.9391839239972508, -1.2231540667337242, -0.20143697065179184, 1.3198113492513808, -0.14463794887114503, -0.7362888502439066, -2.5336890361426, -0.62968640251335, -1.87312256983219, -0.9553821604699511, -1.139035931612396, -1.5956588140087373, 0.20677208431317887, -2.099574585917676, -1.484869072962508, -1.6117422207204732, -3.4556621213252123, -1.512023283890905, 0.06144263148698152, 0.07215126914430588, -0.35205291469177424, -2.1719080047670127, -1.3216223396933673, -1.5865175144359684, -1.9136926798131808, 1.0419992565782823, 0.027425821190462878, -0.03465850875967062, 0.022236664175880147, 0.023675238357713353, -0.02616795371238558, 0.012239935694801668, -0.030173522082649208, 0.014479946962723107, 1.3526456754006757, 1.949408436579831, 0.6841602398793593, 1.3686996196602792, 1.3229169157466618, 0.4272590866972259, -1.6972336600449198, -4.2051149890347075, 1.4762532961112422, 1.607610603501498, 0.6674515427646887, 0.12763430473520432, -0.050764497124907854, -0.5039108970587046, -2.110301757099391, -2.0742765501622564, 1.5117556693331673, 1.6606656201358583, 1.1893811255198166, -0.09335094390309243, 0.023090658333565165, -2.3180472666934717, -2.4517652242659898, -1.3861164182018924, 1.2850106298790311, 1.9757099201698285, 2.2439568329760813, 0.9845256489873927, -0.5417039529267286, -1.8415803566908417, -1.7223832199845173, -0.06460379431834358, 1.8833424241899324, 1.3567135706228117, 2.8720514159594766, 0.12333231887460631, 0.39850189821377774, -3.2482445826519535, -0.9179203409418697, 0.7524744981310169, -2.6696241381326797, 4.20557804050652, -2.4967700687748877, 1.5343552126553992, -1.1525555383336197, -3.18658081048061, 0.3752316607480765, 1.3589961775558657, 0.011761584219365833, 0.009210594546869053, 0.03232074575641513, 0.005917922881232569, 0.0034417104421859343, -0.02605164849623214, -0.02625447165374644, -0.027194447675893525, 1.1582484226612004, 1.175703509515102, 1.0773707139978264, -0.04121373733877459, 0.3433440358752217, -0.5143805060091945, 0.39350672521030844, -1.3031224715373229, 2.42588923909743, 2.0234086522253505, 1.205919401288091, 1.060520532304315, 0.30541586170831503, -0.29951026417813476, -0.23987924680788872, 0.49839825701024326, 1.2486762296037426, 1.8623207750677533, 0.942954556419299, 0.1926313910599546, -0.7235907040279291, 0.2154810117187677, -0.5405272907417158, -0.8764726918139065, 0.3713340579364931, 1.4865857506098474, 0.36881483730247444, 0.8094357025248208, -1.2820940369397862, -2.7847225684355803, 1.1990935026958078, -1.0638254764521704, 1.1602488893714251, 1.4033772366668003, 0.8331761377106546, 0.5164317421104929, -1.696042256578703, -1.054175615987549, -0.09720896846957142, 1.3519072999358894, 2.034328019023147, 1.2464836034402818, 1.2553819322785724, 1.4332255093149753, -1.2283591541947676, -0.03194960611779391, 2.9928419162410864, 0.8855492567345785, -1.0973789374093377, -0.038788940687398826, 1.0967980473659897, 2.321176998205521, -2.871798643544039, 0.8821077585770233, -2.0880380836204075, -1.7733975816617256, -0.2353619792975624, 0.38902090349980223, 0.7286790517219504, -2.9305533046461143, -1.1757444650741318, -1.87241360252564, 0.001459969193528751, 2.437878204514774, -3.1027950766917707, -0.23316463310832425, -0.04384771716748929, -0.578682742996113, -1.567220057304122, -0.46472233006262154, -0.47957808416549974, -2.4914967004004143, 0.5747594751631914, -0.5195262396745595, 0.964506211997268, -0.4280065745832447, -0.0872116541790945, -1.5100386452681211, -0.9785986068972794, -0.9410504250867268, 0.5820447048534453, 0.0345143868911148, -0.7719110812524561, -0.21412292891421203, -1.0059633816427138, -0.9476137971195799, -1.1849758825493482, -1.1971241848407546, 0.438911482662864, 0.38248844825427114, 0.39652558000464755, -0.8703847132743727, -1.9160064111384865, -2.4956082873632845, -1.856331332472196, -0.8710119767610437, 0.8032529539085945, -0.4237484606500083, -1.1816130692426239, -0.6526070166662151, -2.7994789563432043, -2.270314658141923, -1.1444366188439015, -0.1005624682848816, 1.5920130625588353, -2.758574787720527, -1.8891942638400094, -2.0673239589939247, -0.6720680311838928, -0.2573630095864348, -0.462402881100896, 0.2622069246838569, -0.0645857550466717, -2.396832241691919, -1.4138719367634123, -0.6706425530115624, -1.8687740867921538, -0.9436680394975883, -0.28184519793379353, -1.4481503189630753, 1.3985327146770405, -1.4997483775281544, 0.6955033692020228, -2.532429156462863, -0.797903672479457, 1.922016150046528, -1.222398150131945, -1.083829201953409, 2.1793589091101073, 2.0662190070459783, 1.653216599693528, 1.6507634989000222, 1.2171544834910173, 1.279351471410645, -0.34913126254377763, -0.3195717856399983, 2.5937922108571736, 0.7845238727592322, 0.5317630446780878, 0.8671553185609874, 0.7148559702025639, 0.32212116079618075, -0.3916627555839902, -1.7648016623807932, 1.1043242792766017, -0.03095080663560972, -0.09492878412889723, 0.7156871786316441, -0.7643812230401184, -0.051620478512855665, -0.4264836373700611, -0.764764596478983, 1.2509617313724384, 1.993228832434406, 1.3951976627087102, 1.0936270032528124, 0.15756213518606021, 0.23785708961725213, -0.8504826464928003, -1.7576380051195806, 0.9466019998556329, 0.9275887668878405, 0.8054181696000036, 0.22781109670080266, -1.1832623374997333, -0.7646549910053068, -0.7791895047947783, -2.084043165774993, 0.11772722785702076, 0.7853462149648194, 0.7813417372573823, -0.29588052861751446, -0.47557306738103144, -0.1845350080691958, 0.28828160693314736, -0.12988326391335644, -0.3284461508168734, 0.523191300663164, 0.6124039411456662, 0.3437486683147099, -0.9435745755281009, -0.48907028502156613, -0.526712313732638, -1.5650528720649677, 0.378051622274363, -0.7922666683453906, -0.25652707277245707, -1.1724533140819842, 0.6436335242950911, 0.9426378360169989, -0.26228425819038814, 2.134004769899903, 0.4190077935683887, 1.9975433822503017, 1.4643341584742686, 1.1321881186449059, 0.2332334870570166, 0.5368585786806872, 0.659624766420755, -1.4532975394508294, 1.191955379761907, 1.5636976863294736, 1.4814407867020503, 1.069507251251375, 0.8911035277884605, 1.124926598848814, 0.4251698234113935, 2.192692158652768, 1.416133079123686, 1.472678906144579, 0.5789969537602231, 0.45657496439888007, 0.628414261310242, 1.5550364567448511, 0.9721392269410633, 1.9374086981167384, 1.2140978560101365, 0.39300204873447075, 0.7956821954838312, 1.313839584475162, 0.2346074236197264, 0.9232157465092259, 0.9217503445869217, 1.9229041263068392, -1.1529913716789475, -0.48551700227622413, -0.8168920486258341, 0.8859835680201661, 0.6346644409230839, 0.025725448126517964, 0.3424135111525451, 2.2403722080162187, 1.878422299916924, 0.5373137259340833, 0.10941074592849326, -0.4506721594363596, 0.22694405737046144, 0.35354182297610703, -3.5251354185668977, 2.038985614417588, 0.11525414686793678, 1.0655308011190208, -0.7112811261276106, 0.6029991560888421, 0.6781589341847201, -1.2092382032769506, 1.688430109640246, 1.3390921755504084, -0.2332646627446521, 0.4659946669850797, -0.09314445133040236, -0.7614593847073793, -2.812072206388775, 0.8464307483141901, 1.0038410262687507, -4.024445171890774, -9.944605536781806, -8.60017648949083, -5.956266043091743, -3.1281367943558473, -1.3476808926231851, 0.5679463645768259, 0.399894168931945, -0.6522176423298532, -10.056615345282268, -5.8892211718846195, -3.804438048225105, -1.3102651144735729, -0.6213576337988281, 0.5158498822259756, 0.3801399675612191, 0.13288979005517196, -3.1174046890736444, -5.256710758489706, -5.196841249186044, -2.3813210023893014, -1.813385137181067, -0.749924494547546, 1.0391545165121607, 0.5962507043897516, -3.0519454775569725, -5.453549227764136, -4.267150754636527, -2.3238434068310285, -1.745094879463321, -2.1823789395338036, -0.3554671604374523, 2.4237442701465577, -5.715056820560521, -3.665270995513553, -3.179143660994532, 0.30735845187904415, -1.1757314353771726, 1.3804747188754705, 1.5456516460230114, 2.7551962628028916, -4.314172950575475, -2.2349232295277073, -2.325494884035562, -2.7537773134815065, -3.0213219412351022, 2.28582491068414, 3.7795501830119242, 3.9127365133325065, 0.09496808811760298, -2.5165398781386874, -1.154037209958446, -4.974203010406754, -2.7902818877614046, 2.8007177915063357, 3.358461952414528, 4.139987420408031, -1.5321699763002632, -2.7666483361577976, -0.5712203024920066, -0.26599198716685807, -3.1746619995867422, -3.2814436051369458, -5.38450754369308, 0.17125446714230808 ],
				[ 0.0064877422336603145, -0.007567190863740631, -0.016278906470359875, 0.019946340185579704, 0.013687920065272804, -0.003524649077691379, -0.023033040546114558, -0.025689715390245386, 1.1437551698578325, -0.15988225084437888, 1.2934998391923975, 0.52792734764706, -1.3131979431833407, -3.727376780076591, -5.015348958053323, -2.7163746642539883, 0.7260341661374491, -0.13544292151207513, 0.6105252714994911, 0.5271076495576801, -0.2724141788727006, 0.8808002385511126, -0.1717658429069673, -0.0978311420260004, 0.26760263836143855, 0.33794744334479654, 0.8856229860089654, 1.0659059627070677, 0.8451261787636628, -0.04894943871735928, -0.2911992182591596, -0.49697628392703386, -0.051164545476008516, 0.6992972068160087, 0.550049273572771, 0.4381622707231437, 0.5567652167757079, 0.06376556824223147, 0.2309516749457139, -0.33927051718791845, -0.22463035996318512, -0.48133200109220603, 0.3394550258797287, -0.7775834661245591, -0.211963623906186, -0.10692805318737353, 0.03433984643831632, -0.5378905845805985, -0.005635112949476085, -0.0753905580671419, -0.3424886919576753, -0.3884755695239584, -0.8157691388185133, 0.1644319298388558, -0.3905579172644408, -0.643354430263773, 0.020956009652247497, 0.03017328255008999, -0.01014310513730974, 0.03424304059780459, -0.010094087666632997, 0.0011357318002971446, 0.006956784688427283, -0.021383298246754792, 0.23497402466290448, -1.6137720904107113, -2.3108300611037333, -2.6043498484088836, -2.0496100237993, -1.2537497670370368, 0.035475125720520674, -1.588526488028422, -1.412409736463256, -0.6677850804665977, -0.9516768876340088, -1.1298233875046781, -0.3813441534290796, -1.2860358428693672, 0.3799620107130483, 1.574409941514146, -1.3292976309239541, -2.493409664332967, -1.8561471285969922, -2.0202303477301995, -2.0176438254458975, -1.7733033501790836, -1.9227090690621624, -0.7980702174081715, -2.112499768575448, -1.8366471290674744, -1.511094302418244, -2.036009108160009, -2.306186890912613, -2.505098924929145, -2.131502904722295, -1.1117628656224323, -2.005830398747412, -1.9621603525334534, -2.492802332489743, -2.234969899187143, -2.126932935982357, -2.1787639137975883, -1.6306920941521188, -1.602860521549216, -1.5934752203347506, -2.321553796382045, -2.5283993034624745, -2.077761154981059, -2.1722993192651647, -2.2075157573708766, -1.9559531741169782, -1.3071462950061394, -2.816499258094491, -0.8980242784445558, -2.2316935520242356, -1.9249406945505383, -1.8041094747239133, -1.8262993937687027, -0.7345461949632834, -1.890173694555567, -0.9606241046577662, -1.6304692263192124, -1.050869101916304, -0.6255990505712125, -1.157921538741687, -1.1113879266246498, -1.7810832471422315, -1.2986419532907068, -3.8978588558535003, -3.9226483255860143, -2.203280594406777, -3.0079820476152417, -3.160055241383698, -3.573547395993378, -2.22618150781534, -3.65395681408671, -1.5249892771036087, -2.4344715378867248, -2.405426223365885, -3.3618796107700173, -2.7322980009717757, -2.376360726802696, -2.7341240419163624, -1.2046826567537385, -1.3921685175771354, -2.1578820436202104, -1.662293171922658, -2.315098340822544, -1.5496820954309294, -2.964236395260967, -2.5038233455914414, -1.6450025072193766, -1.6299367634169122, -1.8837927098846483, -2.181549316574239, -2.107348623496383, -2.1016966806172293, -1.7100031409911853, -2.3604080822952387, -1.877613778447628, -0.9967308580064598, -1.9082713026637879, -1.0182524019715, -2.208784169974912, -1.7846245807662073, -2.023927422778564, -1.9699610753363754, -2.419378783349281, -2.0092380211351464, -1.1301922014498205, -1.5773470289318732, -1.5687770183408813, -1.631835670026521, -1.2020515383120396, -1.5532038819957847, -2.131407910621132, -1.3580026337518025, -1.0778345835148482, -1.521430360869739, -1.8369012922051613, -1.8858905366662282, -1.4934997391061058, -1.4309454650185105, -0.4418745628290295, -0.8137825735049387, -1.2360200440679494, -0.8140751707943846, -1.4400944169702041, -0.7929073588601094, -1.509543415373414, -0.8330588832343211, -0.9916026593612757, -2.447442238202274, -2.317347523887277, -2.97865795193919, -2.9796363315769576, -3.104977708377495, -2.497395291760515, -2.6876817132482, -2.415490760408639, -1.6746060711622677, -2.091949157399539, -2.140374995581026, -3.2005183817110443, -2.4284159667484375, -1.7681679054271378, -1.0924144803759852, -1.3153764741603906, -2.255542161879986, -1.7080528623016178, -2.1851933113891717, -2.2785879311676998, -1.7146401119689105, -2.2971188399389924, -1.4172444797400687, -1.4080441254538951, -1.469834369964083, -1.3990557116177094, -1.632804423664653, -1.5403069625601822, -1.6404858627231633, -1.8246467483309032, -1.0666458144203161, -1.0880189574134878, -1.6948339262295362, -1.585369384802588, -1.9796687453771544, -1.2068797648467313, -1.3668673043052975, -1.8219317111439088, -1.0461919526422732, -0.8522418405636712, -1.8560807252687341, -1.6762508577031054, -1.637586653636984, -1.5151595172691057, -1.0383565977079734, -1.605245865258839, -0.985626002375812, -0.6104747311466104, -1.2185244140726619, -1.159800564823244, -0.8411276349196665, -0.8665560329406246, -1.3274130998266709, -1.2814202296575177, -1.451490362482899, -1.8807229492046045, -2.0944825913835294, -1.6324754603455205, -1.631771209382129, -2.0793027562175257, -2.336537503037008, -2.142093910549535, -1.7242627083705662, -2.4183547218322823, -5.564937752506835, -6.974535283760833, -7.449565760829738, -7.199358769740287, -6.781423468876658, -7.535250032904991, -8.717058430304757, -8.077131928032093, -3.224621591537178, -4.107902303133874, -3.45321589689754, -7.062907598953885, -7.0384981146159955, -6.005241211426689, -4.027503173919696, -6.3428927450767425, -3.131208444682751, -3.5827733129034494, -4.348762346433016, -4.574512647909649, -7.869113503174717, -5.921167966823748, -5.084247542993024, -5.569381512768376, -2.328845661860635, -2.9031291814678255, -4.374568974376074, -4.037312179392867, -3.6042951320403347, -5.359110035347788, -4.255605566543048, -4.0293236946356, -0.8200876816670277, -2.1581156249830387, -2.565179918746485, -5.0576128747538585, -2.9193157270184344, -3.6751021636651937, -4.840479980514783, -4.186223265422004, -1.3940427495455348, -1.775221195957308, -1.9320951282191072, -2.2950375133472747, -1.8995322720674268, -3.4089258719455766, -2.8369580825901126, -1.3380940227130835, -2.1058466364786574, -2.4747158865964893, -1.5301445794363968, -2.592379036040071, -2.823270771288122, -1.3480138183133028, -2.576644770886049, -0.6913711622912156, -1.7501044040270626, -0.7883145129469566, -0.874354262001725, -2.479169059668633, -1.39981977537648, -1.0149629665061664, -0.16802751201245056, -0.6487112829517739, 4.006272649509345, 1.7655281872703388, 1.3625211635165952, -4.42898865758288, -1.050075355155218, -3.7048873479127327, -3.5082030181969186, 0.3471474184445136, -0.2028952900398222, -2.0211202485191135, -2.7519602317674874, -1.3639334989451175, -4.83695851569074, -0.4038872932614525, 0.13176680878490213, 0.20076196907561936, -2.3897502437332383, -2.050983730778387, -4.910001066325608, -2.6962328754093234, -3.795722448719371, -2.7658865740024154, -2.019414076561405, -0.43864548303135303, -2.0077234035885283, -3.543671610168828, -1.514209363328775, -1.9088998354643918, -1.6513558434152915, -2.128732401949797, -2.004535814136428, -0.7175948392868922, 0.05982648084095679, -0.9748337159622772, -1.069160170968352, -1.287040078663634, -0.9665903090752517, -1.089324394728773, -1.130088407159029, -0.6549677055746419, -0.9541672732623098, -0.6296184256709275, -0.476321518543488, -0.35299084629661903, -0.5695173072276994, -0.3630546094996638, -0.3985642320569429, -0.6002183147638576, -1.4663356701506667, -0.7911426495558689, -0.3436263273719277, -0.544340461292107, -0.07820199583836035, -0.25411116434879166, 0.001808472541590279, -0.22485973340325247, -1.0951754931435425, -0.623015956163759, -1.3070683911431615, -1.2451037982829176, -0.19990506877771042, -0.3883459155492351, -0.3670334466894503, 0.254071624705902, -0.024389091846623044, 0.025206416082589826, -0.035888686849057175, -0.03537517837412062, -0.005584128742362127, -0.0041080377558776054, 0.02624864828401107, -0.011326566467191622, 1.5810182989726191, 1.503114782760371, 1.154661162964544, 1.965222118819156, 1.3833129712627206, 1.2586997018346124, 1.3024046737800665, 1.1238793761758887, 1.378985050447681, 1.9454764631939991, 1.4203873704051708, 1.767513731687849, 1.1068766472719005, 1.634671073692401, 1.1009682529968654, 0.959643052816025, 1.80586985591638, 2.213877976362161, 2.220535481445984, 1.9734027483548968, 2.2331948473892815, 1.398018895255761, 1.6968607686668002, 1.3581522601226381, 1.9053227031118531, 2.5485284264350354, 2.5610336616133953, 2.608839349852435, 2.353308575264699, 2.3409895379772347, 2.486162376492494, 1.6343877381884768, 2.6862427020210506, 3.1075328214421694, 2.9505945631576815, 3.1300380752268993, 2.738713088607603, 2.151837955747378, 2.206859323570031, 1.7187465182133428, 2.485666417667156, 2.5706833970398493, 3.294349179804241, 3.1815388631151738, 0.9874440940747254, 2.2456736205371617, 3.098898964012628, 2.1218301015270535, 0.0015165323725040048, 0.029007587657220453, 0.01522597948713278, -0.02823968831228752, 0.00043469796658451604, -0.03259172202839468, 0.02399364838676689, -0.007660089661353089, 0.01829293704719538, 0.09398722392503027, 1.5101243446251227, -0.1273826820183461, 1.5380476072220672, 0.5736969032996979, -1.2936243594890349, -1.8098541815565736, 1.1606629102428219, 1.4110631815432242, 1.7422593734343836, 0.7145975290804081, 0.8139399947422056, 1.6885475172975473, 0.9199842523250575, 1.4681312631889718, 0.1134488634335593, 1.553047578087533, 1.5310542874410111, 2.1974471662143915, 2.104961764058724, 0.9652238801654536, 0.9352799985028665, 0.07934954629028312, 1.1294275190270975, 2.49777581061784, 3.2029929876174537, 2.1110045210451616, 2.0770953524168583, 1.8519266019292595, 2.418189750222736, 1.3842908391167577, 2.52308238623531, 1.4672954556434021, 2.7921463447424784, 2.216293958233051, 2.460894937936472, 3.183588308845348, 2.7190582487147865, 2.489215269000577, 3.0553721049835567, 3.8565148466748904, 2.665275061073458, 2.9956481762269895, 2.7031827482596493, 2.292880247183693, 2.0885528136042857, 2.252264794151547, 1.7801074951818077, 2.4431801799969826, 2.372093878364931, 2.3252981288401138, 3.348120836665605, 1.9475793240399528, 2.920387214194085, 0.6468332899201865, 0.5684518818287376, 2.4912169034552587, 2.3154868284398953, 2.935274506524395, 1.5634465689392494, 2.8724684496357633, 1.2794404270521018, 1.0701284956387058, 0.10038458671958092, -1.1930187422185379, 0.3687362423816335, -0.8998150663617374, 1.3454622844913968, -1.1895864091345054, -0.2408288244643971, -0.5026110168793365, -0.18044651190539054, 0.8753224603626738, 0.026404596712114738, 1.0160097430233925, -0.5214152392617174, 1.051494262048668, -1.220463807713666, -0.6919658645880071, 0.746887158618606, 0.33062395936008115, 1.096627179953786, 0.27691063698047513, 1.5938763232645, 0.8335037690643485, 0.25894871975765377, 0.82067651968683, 0.7485154104422156, 2.150644109044107, 1.0784524896437433, 1.3623210149720664, 1.3286318954319258, 1.9512191416954088, 0.9375674029053354, 0.49027989282199125, 1.4897916561530515, 0.8515021718627422, 1.9724824920107935, 0.7427176400028301, 1.3902046137190025, 0.7756448880762998, 1.2877853977433196, 1.3593166132800352, 1.1336281411850877, 1.5338718569472005, 1.3139606552982577, 1.3976570581526826, 0.9802846053430722, 0.8334952205641982, 0.6142946568296471, 1.6151137321443927, 0.4697919488447613, 0.5900591167481901, 0.9175930489511133, -0.010407892008617012, 0.9563040331475736, 0.4721495568410705, 1.200002273617427, 0.863720225733123, 0.1266876543456928, 1.528551205635511, -0.5242636153727188, 1.2471645051079872, 0.24973259039133722, 1.046793182259244, -0.6978572704244398, 2.180084570459008, 0.8231481663115058, 1.368749845554573, 0.6023875057969689, 0.864462567384926, 0.47953233500992304, 0.2880866859500566, 1.2316379544577378, 1.0710181478129919, 1.7869663697586082, 1.6582138744384187, 1.1318030086804212, 1.7225752119063058, 0.6684280659739756, 0.9189620897465703, 0.4157787674940418, 1.8395525598347406, 1.6031856789078627, 2.407358761887781, 2.2312151733254892, 2.3625438832170107, 2.12783439263912, 1.5272095562029913, 0.7637487156909202, 2.2091870065299686, 1.5251161444469548, 2.7373929710018357, 2.9578491442911927, 2.987045063403682, 2.102180440641198, 2.068527750216223, 2.4207013700486213, 2.4836700941180725, 2.557024385170452, 2.924781173537414, 2.646459977548037, 2.6869471624683636, 2.897388019673896, 2.9469553088432474, 2.635177182947348, 2.75959260134155, 2.993651137441986, 3.4721507847796147, 2.9561695352108166, 2.7556609700672845, 2.704222513620336, 3.1601071130113487, 3.4411714039978327, 3.1652612500133532, 3.4392950527265325, 3.817023380966437, 2.868553502940051, 2.7226719861742743, 2.9766375302266046, 3.301597084197081, 3.4141550676274233, 2.9649133313810676, 2.4570378941495874, 2.560394485489519, 2.5849382119346833, 2.431105907089374, 2.327489582005763, 2.77126327245721, 2.3303276226027374, 1.9888287402948845, -0.9371847975577731, 1.0092582991279393, 0.33783758577989526, -0.6437243282280549, -0.5203114032697277, 0.005569789068131868, -0.28850064605867476, 0.86969663721631, 0.2511806434174259, -0.18764380722628968, -0.3397475744602511, 0.029919951343699215, -0.20163705076546815, -1.6701524757917334, 0.16103185987360263, 1.214866651075487, 0.7765726953662079, 0.03562127379060921, 0.12002489243081847, 0.37704746284403307, -0.05979550213226526, -0.14712622283720467, 0.15520028288899207, 0.9837207392860141, 0.9916367734320928, 1.1461074749110023, 1.333103367365781, 1.7178873830773018, 0.7669339535205407, 0.10744333927526936, 0.9074483051007787, 0.9479106375193412, 0.02362546723511708, 0.782146609259391, 1.4735479818323236, 1.6941853733380516, 1.8242914537743131, 0.9553997821817756, 0.6365935988836481, 0.14740834299324157, 1.0817028663207269, 1.427892992981629, -0.12266815541925283, 1.7811898715934489, 1.814605480259935, 0.9855398472459466, 0.7363432373243184, 0.6445108544893112, -0.5480405546860144, 1.866184496526248, 1.2213522349185943, 1.8907411198086634, 2.5640381563227677, 2.1877318190032633, 3.848610580094774, 2.69987156291178, 1.02988709469707, 1.3301865352762108, 1.1096111444614407, 1.1210048490507796, 0.11751014436540429, 0.884856184453929, 2.227013226597811, 3.214850806803615, -1.9333265755585862, -0.791856949348018, -0.5412528763162545, 0.1907363966755072, -0.9134660177982439, -0.7258032886672883, -2.3906481581884154, -3.060450600791431, 0.05037351330520932, -0.19227651410945215, -0.14054953597108955, 0.8552628307678858, -0.15080750875635485, -0.7849347085389702, -1.6049586656381867, -1.7009872001085606, -0.12358246293073867, 0.22228944552499494, 0.2689493359071083, 0.8142775338997192, 0.04090730134411964, -0.30531126848923545, -0.9934578704357846, -1.080199453123224, 1.030669406560499, 0.6303277772993914, 0.4990674793129169, 0.5961709742112886, 0.3099981225538919, -0.39481464474721795, -0.4253550132842304, -0.9981784821052915, 1.7043085154504831, 0.6944574748738234, 0.9453201482969216, 0.40201910953553754, 0.6272538424519595, -0.13735681065206495, -0.1656174130481142, -0.5434999545745874, 0.23126013360627287, 1.2844124008061684, 0.35196000805996097, 0.5671253560907376, 0.6235140087589386, 0.14248903209844158, 0.32363132718765425, -0.4715769595694235, 0.3746068589356292, 1.5913694718781053, 0.5418672513357443, 0.18855113703632184, -0.4017072122896189, 0.27591192181877283, 0.25601248986794173, -0.8327033259939628, 0.7208824490838186, -0.6342470673768656, 0.06146362583600086, 0.4857075140566327, 0.909658539089971, 1.02487438763949, -0.4349002669097122, -1.4788013682721193 ],
				[ -0.00046947287270719077, 0.016946269746727957, -0.004986481369743249, -0.02829644276936685, -0.035066696020963926, 0.03329098527071458, -0.0029726293099194227, 0.031251705204518844, 2.5064089653766586, 1.114621874713505, -0.3985678700101943, 2.0546492805367635, 1.0905745377617762, -0.9514592976033365, -2.6790214214485544, -3.427992895822942, 2.0174069463297184, 0.39952482450848514, 1.2419178439539362, 0.5341455030744611, 0.10849829997198676, 2.1566341746193554, 1.0306575455688662, 1.9872871154979803, 2.183426103136125, 1.8541753838216837, 2.362162550417298, 1.9041870039965423, 2.6891989986716336, 0.3470353077104601, 0.5296109808753564, 0.5096640609179567, 1.7820867107812508, 2.228037876511733, 1.319619717729891, 2.472304159448551, 0.8216404250140983, 2.007444457698296, 2.7989539565247936, 1.379784338074701, 1.943613444725007, 0.7323905185064402, 2.344474232256518, 0.315340070229555, 1.4404946746956753, 1.340083004878929, 2.7981294633058895, 0.7541986669370885, 1.3068356675338655, 0.8857580689476822, 0.566042593630611, 1.6002199669050834, 0.38280700724398853, 2.0025829655897476, 1.4735554912231026, 2.1659432763942776, 0.006019343344151778, 0.024327923715687226, 0.0049948450802259695, -0.02819098600101825, -0.008392434086195721, 0.009944490126200401, -0.006201632284911194, 0.006035735778584003, -2.871046036647713, 1.6066302881621823, -0.6487992560688999, 1.3192901657466427, 1.8307424678671607, 1.848868293995203, 1.0067269140520592, 2.1906929682443725, 3.087827826694883, 1.157538846915758, 0.028847613057911527, 0.09804496936513601, -0.2229044229916019, -0.6581676724047884, -1.2772270625572966, 0.5557217008045119, 1.7736368057755658, 2.558681075424132, 1.839876128537553, 1.1817790324343498, 0.4203654168276967, -0.467078275145914, -1.6176244271358926, 1.3117011847718358, 3.278297228743686, 1.9707237854729556, 2.3226487568901764, 1.1088149422179978, -0.285813231793942, -0.0746399891108228, -0.5942034627724151, 1.4255758368273221, 3.1666049910862903, 1.9714924359554795, -0.6484540543682954, 1.0053600090642503, 1.1703363342081736, -0.38560209188212646, 0.22204781414546573, 0.75924278611176, 1.2517384224503136, 2.2069168496984646, 1.2495761366235403, 1.3083810553582986, 2.146891109713818, 0.056511755854163535, 1.8498515895946228, 1.5975315651974529, 2.310824496197197, 2.3078977015799382, 1.2816902099735181, 0.5143078483494812, 2.481569608933803, 2.5557307810450967, 2.7244386944169046, 1.873673719788083, 2.51652576000198, 2.448804384912807, 1.57608208280395, 3.108562085836642, 1.7564774370815077, 3.9973267934223116, 0.858312073566158, 3.5561562387305745, -0.6346566606014159, -0.7344163077655388, -2.279832162157831, -3.6547728560398314, 0.5498866020143117, -2.0030923533031664, 0.1355660644663522, -3.069275842643872, -0.10395386179549182, -2.2792922861877143, 1.0700963049665126, 1.5046319619015929, -2.011749366142015, -0.44904025146318544, -5.900834083959724, 0.8392483828749777, -1.8754684413450093, -1.4431331022715534, 1.3603886519938724, -1.4167176981147929, 1.5203533259184778, -3.8891543698787787, -2.197154084711578, -3.078979374409185, -1.246104053538815, 2.8756055955980044, -0.06739745096731103, 1.5289236409657154, -2.5077011627238788, -0.21611042492440183, -1.1990276265235578, -0.04463413502753972, 0.12368791961031037, -1.3491244400193034, 0.34986534830713995, -1.6577471889649884, -0.6422737443288474, -2.010886454857928, -1.0858802449410871, -0.38222942084451234, 0.360326771148265, 1.4091756427083484, -1.9962641529896996, 0.8436073031076186, -0.4620647882618862, 0.7331614609563724, 0.11436934299578667, 0.673944600362194, 1.0761909460737868, -0.919385194449859, 2.3490846310212525, -1.0936889752916699, 2.0859723286811938, 0.18523573571200788, 1.5145262147586611, 1.8505203348651516, 2.779785656285614, 3.170509045263915, -0.9386929917024941, 0.9670101015403062, -0.23421977167362712, 1.8536320104931743, 0.05790593325675185, 1.5482703916225524, 0.24368950393990058, 0.4989774111781159, -0.713960034650037, -0.6477631790845932, 0.04048330835015745, 0.5508680123852528, 0.5823746003462783, -0.059020857550062464, 1.5652125900032534, 0.448529382350907, 0.7571860799747129, 0.5913322418527291, 0.23552585264332285, 0.302447924883811, 0.10618419453202003, 2.0131507590829365, 2.086546133285137, 1.352984634487034, 1.74857847618588, 2.2852146217180738, 2.228362129751009, 2.4425643014303517, 1.7777484890210886, 0.8930233431015445, 2.3027485435327217, 1.7058299963025174, 0.7339549413277993, 1.1741739817429417, 1.8380105279599432, 0.6375207793133575, 1.328713467397286, 0.8916147034790167, 1.290501850199066, 0.8823199232394202, 1.8650078309401459, 1.5265044033177229, 0.99491937419789, -0.23169759117165317, 0.46579970562092776, 1.722368425468071, 1.4418273720915473, 1.7387692695521744, 2.2105819761764463, 1.0934998805688743, 2.305524862016225, 0.054326561077630155, 0.8978323533356879, 1.0575805035423533, 0.4778638825160214, 1.3814482581087595, 2.432231421902021, 1.2895250426258864, 0.9517868937711426, 0.45581396241944494, -0.12894429624998127, 1.3575650494572074, 0.9973502251313897, 1.56495838412664, 1.6098053451431797, 0.7942854045936587, 0.9372906324446408, 0.3215499726694795, -0.40654387880324216, 0.298588773201554, -4.703707876381913, -2.1531754750174903, -0.36563146225791177, -1.750595514479016, -2.058142248599646, -3.2481827754149997, -0.22242631734492993, 0.40394229023933453, -0.0762644240978732, -3.7943416319549654, -0.21784461835466792, -1.1455856895692538, -4.472522020084664, -2.6084470599988636, 1.890502896866027, -0.11379653450147134, -1.6353916040926015, 0.7036040869570179, -2.118797126596742, -0.45421569149222585, -2.651778758762171, -0.9355991898120571, 1.1917562604274394, -3.760641647291755, 0.12926115201030544, -0.26453266216097243, 0.08499970649787081, 0.328480384261424, -1.4545682818448573, -1.7359692968629814, -1.3633916549498184, 0.19860974783410362, 0.2798044757712951, 2.783282713950234, 2.4799193878630987, 1.805340095776988, -0.445045563845309, -1.1631248434890171, -0.7816285312215863, 0.10241664173452734, 1.475905554034403, 2.3530963670053886, 0.4628631736894613, 2.6854608450198225, 1.279927333013286, -2.1423365549664326, -2.0688113430850557, -2.654337910553424, 0.8117575984067091, 1.3727163200479766, 1.9606321773830535, 1.034827149159076, 1.1413234147971743, -0.1586852962654402, 1.2997506388968865, -1.4090521638810178, 3.8292018596674096, 1.8801615662128501, 2.2405291058954964, 0.5863699295304552, 0.8534722128534218, 1.3306319910997733, -0.6880643946426667, -0.768146154779356, -1.7127213747179815, 3.3976653070168195, 3.3420385854600023, 2.1928490460038783, 0.8439464936244863, -0.3993796835113068, 2.0121345597309097, 2.860026402746197, 3.6364361398818077, 2.8327891231841202, 3.0278785900324388, 1.1986190448684197, 2.4119432853266076, -0.7799250599462854, 2.791883810818414, 0.617846390294768, 3.7943400172965758, 3.984190077141224, 4.068294808172719, 2.1882476602810903, 1.5186272548911084, 0.8969360207188126, -0.8053605763919819, 0.5479916314786182, 4.088465345238007, 3.029089614655707, 3.739201236665199, 0.6880503209431648, 0.9750768994071822, -0.1520229752815061, 0.39777022550533586, -0.332809144927114, 2.5582124328183586, 2.086433016179514, 0.41533133738568473, 1.5849557402345091, -1.0731481259513056, -0.9122933408921922, -2.3165696658002735, 0.5132777081397341, 1.2462949619422883, 1.117216059379749, 1.5052895298148927, 1.830450835511192, -0.006923347630808074, -1.2003451474995042, -0.4054345899774233, -1.9728535079307232, -1.4552166846382433, -0.3325605500895624, 0.4992849756025538, 1.4342844549975473, 0.973339925109396, -0.0941025989279037, -2.21771951401063, -2.7001360582493836, -2.2078819610000053, -3.046239587763133, -0.1836365987240929, -2.803970524359466, -0.9745238735116779, -1.2315289920944252, -2.2571014525247834, -3.9653956621855264, -0.013785738552805207, -0.032009516164556384, -0.006414878989870884, -0.02427412488985959, 0.00022861175999296367, 0.005969421194318767, -0.0015212842904517446, 0.029665526675002128, -1.0257689611837704, 1.4676061074795212, 0.504548176706334, 1.5633318105451075, -0.10449302774616455, -0.3533542324276068, -0.764268522461393, -0.8658887451732459, 0.22563596507050368, 1.2750150019994704, 0.9899450224887254, 0.2051393790312968, -0.7240048325407742, -0.42500990940909733, -0.7526794995920083, -0.21400362526186043, -0.2067030431548231, 0.5642443928763582, -0.2869485410486574, 0.45996890270764595, -0.5499309055986744, -1.4467673761254685, -2.0670630321097314, -1.0726847625232916, -0.18209223872877267, -0.28018163524770223, -0.33181123348626707, -0.9322611908926579, -1.0951793945605013, -3.6009597180384088, -0.5784466695165768, -1.8571858069844458, 1.5367514396731106, 0.1535055942666094, 2.4738215100052923, -2.2654975101346952, -1.0044604231369036, -2.154914956183125, -3.913877417576497, -2.7218635615304616, -5.15431474878396, -3.3422063187567925, -6.560891318169195, -5.3441613687868745, -8.687859342387984, -0.01799635708204894, 1.196243543833513, -2.7016703241362827, 0.028759844852083605, -0.00572367815505842, 0.018117687194803007, 0.03544039335577653, -0.020688344679783477, -0.020903940236365496, -0.00732807957675528, -0.01781393604370576, -1.3420831816487309, -2.6751017600545777, -2.237087195018258, -3.797962081531506, -2.0804043483204606, -2.723005045674575, -2.9112513209011492, -1.3780496985380901, -2.7807501802251373, -3.273949984808182, 0.19653164500855017, -1.50873304055617, -0.6960353403499402, -1.1629147063375804, -3.033386397942795, -3.034754126010684, -0.7612344421841327, -1.049971720271038, 0.8546825899809184, -2.243775495606381, 0.11126232682429607, -0.7932898147497971, -0.4620294296464146, -2.6354861422018456, -3.3307508542147524, -1.7879229829031797, 0.10344246189319227, -1.0644467037297418, -0.2442468707879251, 0.6109316779755107, -0.41983544459707145, 0.19780380419359334, -2.040981293862803, -1.5537439113898912, -1.900963183152301, -0.26954244119334836, 0.004610532254769195, 0.1748146273917644, 0.598548849564733, -1.0523105236249939, -1.7880812756241569, 2.5790299746444174, -0.9323990473073047, -0.06157494881799308, 0.8614839648335457, -2.654804932112874, 1.7323062288918603, -3.2423595297404457, -3.8505995687257815, -0.8965433855863603, 0.17727850555231964, -2.838133678614433, 0.670972302121858, 1.3149691437543314, 0.439034652130304, -3.598066383642873, -0.9355419909720126, -3.5313803811574505, -0.9092821226971267, -0.09195334984759095, -1.4350733457706908, 2.9434977739182133, 0.008918442035936874, -1.6820872626637045, -1.6941380135385138, -1.1897352046334184, -2.0381603355300757, -1.6108491055223375, -0.3674151746353714, -2.148733280762235, -1.1428917226569855, -3.183408271997279, -1.5913864693198774, -0.5718360654586188, -1.253745006832956, -0.3902718035749804, 0.3870489840558812, -1.1097680071066343, -0.15643423490690336, -3.1402418189961376, -2.0810959537245926, -0.35593865123465374, -0.5965069257088506, -0.11073856091891116, 0.16288476187521383, -0.24444684687547238, -1.7394558910033786, -1.7091878476657272, -2.280976615913101, -1.9665925662563162, -2.633305802692576, -1.1358061255324587, 0.2079727055166654, -0.8729754897070348, -1.2050615632852595, -2.423163854882728, -1.2617478651399676, -2.4523956517405114, -1.9740355672161654, -0.7467659407223534, -1.655154178799245, -1.4495834289262972, -1.6669760500157482, 0.41028349686998145, 0.1844957178163627, -1.376000042574347, -1.6423557747852984, -2.290129758032313, -1.7778134864101172, -2.0713388757604516, -3.5211784937830326, -0.10850286595816529, 0.12075894411287545, 0.24318426757758155, -1.9012002760326538, -1.5818803568785624, -3.3182848394889892, -3.2482927716480416, -2.1415727872400514, -1.6357590126898653, 0.39542420599477457, 0.12727058856577114, -1.5795822497334382, -3.9507660841235532, -2.6251200775435213, -1.3534777583887398, -2.1754248726627865, -2.4074251150956862, -1.019710510605719, -0.6553618351253531, -1.03984319850998, -0.6459151214367467, -0.9605909623780533, -0.6568442523899141, -1.2242306818189825, -2.1017307264698983, -0.6798256745442595, -1.5135274377631565, -0.7353046491409221, -0.7110807267156243, -1.2093378276042952, -0.6848829890564113, -0.839124439965682, -2.1150970991772278, -0.2258040273053696, -0.2590989225629414, 1.0436394496271115, 0.2573963774982877, 1.014251180085208, 0.06016858376312083, -0.5427758817203517, -1.0187149863768759, -1.4669869334996846, -0.30822321216721604, -1.7094156492382988, -0.16121287167407336, -0.3451561305561196, 0.7953057970968179, 0.3074520714486953, -1.2943881151331842, -1.820599151559678, -3.3951316824044064, -0.8707381525246692, -1.2346690195133405, -0.44540332077880646, -0.8746755644147581, -0.9220587559508382, -0.6537370440877098, -0.8709869703115587, -1.9964786486756985, -0.7661835466587702, -1.395659553393625, -0.5211385425782971, 0.7365263812494335, -1.0185648798856386, 0.194913914961731, -0.15529052600868762, -0.5197200695595406, -0.9804531015541796, -1.4152446801387057, 0.2601485650965484, -0.873201892540635, -0.35671725014263306, 0.3980958087564117, -1.540039821012578, -2.0481456840867325, 0.13173822017385045, -1.1654986551229871, -1.62483987693907, -0.7659670503009522, -0.4741164680815578, -1.630301087418302, -2.696073990567618, -1.8241588125821078, -2.037866673382286, -1.0822235599849466, -3.5048909452925896, -0.2166338564704213, -2.407143981862219, -3.721656984964243, -2.446454179863629, -2.2166354110289093, -1.629401355871467, -1.4273429125027657, -2.005992103239913, -2.1337701384867236, -3.8859094396679823, -3.011547698217138, -1.6708684677134005, -1.0085915866362816, -2.7140422162218174, -1.4915447968362119, -2.3543116277695275, -2.661715530831759, -1.700526238982624, -0.40305720681894736, -1.205860631842686, -0.47774132863164753, -1.7948042221374734, -4.303188124703687, -2.0590875104790514, -1.4490607035812364, -2.608326051412173, -0.43426280858680694, -2.073722534541028, -2.797130972120811, -1.264376821268181, -2.843429639638459, -2.058437414984356, -0.5519860663390334, 0.01226983649496402, -1.3969326119964864, -1.8342162782677005, -0.07445289800487885, -1.6224656030174618, -0.34186509431843837, -2.089670955870985, -1.4158487678039042, -2.0048380847656997, 1.6299482197154471, -2.05242009372909, -1.728134868717335, -2.366626860405024, -1.3493708496445393, 2.538189851845356, -6.935125292924104, -3.278711206815431, -1.8571089362699909, -3.2914232437428343, -2.2712507577017376, -4.294561806251137, -2.5594972707504615, 0.428458705681926, -3.2841161592920836, -7.784698689455935, -5.790153647564584, -2.3577833271938475, -3.5053955579343787, -3.498040064151372, -2.2935429859994145, -1.23981039599231, -1.4060421375399583, -0.20477076359961938, -1.0621134517074657, -0.8789624354007889, -0.8876276718885291, -0.7845517196741941, 0.18743001480531257, -0.9080811853288641, -0.5032722894989083, -0.5575898616439852, -0.0739358563280569, -1.259663739338968, 0.37551909490462937, 0.993543012722252, -0.12346992319808112, 0.6284532501721054, -0.22777867962539528, 0.014958781200369298, -0.8359460744816324, -1.6567037045232809, -2.2955132600810426, -2.775424262416182, -1.3029118089656178, 0.15722070453841452, -0.4198411496768582, -0.40869835849803005, 0.47456389524493087, -0.5646061709276345, -4.588340763360116, -5.385345654435219, -1.3620013353236256, -1.2434895332580276, -1.7490734664271679, -1.1497224685480885, -0.2489841468350919, -2.138081783650871, -1.6824569596216519, -0.6073566689752722, 0.6487197701828828, 0.14801516508826565, -2.546399400009018, -3.2028927241570964, -1.0726641544588165, -0.7525689974931852, -2.549327278306521, -1.9626894784828963, 1.1176815611386064, -0.7716110516767685, 0.3017265335536815, -0.5193922111360445, -4.077318540599844, -2.7543021990336256, -3.778768853594506, -1.1888844165334027, -0.7445526424105424, 0.325055966419148, 2.3907507040144704, -1.965357489197926, 0.9472112652497497 ],
				[ -0.029506627412498786, 0.00015118748802666818, 0.018557319868461056, -0.017307154159852435, 0.0005625691751042262, 0.01398084953446244, -0.024685486008114946, 0.005897946435870431, -2.3849550276458142, -2.1416184367714535, -0.996737142505063, -3.146691575357208, -2.953236874081015, -4.259739391519179, -2.7477832755426723, -4.7280426191224745, -0.5964377507997081, -0.48627507057866426, -0.5852655537449827, -1.3917265223734059, -1.614931610172322, -2.126646115382571, -0.023936561566050136, 0.19531588671928904, 0.11802876240448174, -0.279893207904063, 1.1414772468861552, -1.1883196759308647, -1.112570829046248, -3.1356517591706714, 0.8670651205005059, 0.36794252188463034, -0.8959669181093608, 0.662300144815277, -0.9155518268928735, 1.1343006400955762, -1.1554416446346056, 0.16480836545331298, 0.03131206910044059, 1.1209477875874183, -0.12547415099834205, -0.4415639675760544, 0.7888973604346778, -0.9730824398798019, -0.06136463311077642, 0.4667588073085614, 0.8028983299305331, 0.19763781377690806, 0.4245103223197877, -0.1759340926988638, -1.3949254694230562, -1.4140579584437938, 0.36685352253901626, 1.2903169866799713, 0.052719349411575, 0.7096206203381988, -0.026295447403179892, -0.0272871852051859, 0.014249610419118895, 0.01783824203272777, -0.013682090752986542, 0.010600656527875223, 0.021457744361729043, -0.029552774884486255, -0.3065681893772456, 1.8148964590546788, 1.8687879212656757, -0.35294634496749316, -0.8575293283642879, 1.0002219852333307, 0.15935376721848046, -1.5560872386997688, 0.04890591483688235, -0.47819454339458733, -1.4316064618250364, 0.450536888362119, 0.4146956042765549, -0.47856016120879624, -0.09872396027249783, 2.8314406932908707, 1.1720034121816605, 1.1283395654684591, -1.557627565419691, -1.094984237596377, -1.5239290586787346, -1.9158033148495994, 0.1461576701058163, 1.2977694150486863, -0.4810311130121364, -0.7552796073929058, -0.21075665814504121, -0.22623978599734235, -0.3016987169035354, -0.6094645706425416, 0.2938001215272716, 1.8589990077467418, -1.402819448093492, 1.0034533483427146, -1.658398665685658, -0.11359934805579053, -0.7385124126041708, 0.9643818200665627, 0.8322958014828812, 0.36631752238223486, -0.23253870784259267, -0.44679489063685995, 0.7719823100393264, 0.8454818658223764, 0.031197981319904984, -0.280308170303637, 1.9868487004895188, -0.5279248652021779, 0.22174834114656886, -2.1571685434211116, -0.029990626120140453, 0.050946255981504894, 0.7025457579700064, -0.40129367465829163, 0.912415911523583, 0.18503605475243023, -0.4392748918975446, -2.1186200955527843, 2.646010343290355, 2.808128478657742, 0.9751406547792872, 1.0380666031379437, -0.2103560402562633, -3.4677291861769786, 4.242272321002176, 0.9564194711202927, 3.0447439364652857, 1.2380270599809282, 2.8633503743513478, -0.03395447899831122, 1.2514019153983673, 0.953778913967814, -3.1301648641519573, 2.751842621304325, -0.6667423857573527, 1.2233396717308633, -0.7065441918140037, 0.7555841516985509, 1.813998690730549, -0.7675514459569898, 1.9422147651030894, -0.4422566533265834, 2.028606089060208, -0.38763966893911517, 1.529825229453277, -1.158554195768462, 2.4921179471871087, 0.01614991132741567, -2.1454757142666825, -0.2675616064070622, -1.3683199373853892, 0.9781408428343802, -1.16885904061522, 1.3951344866180104, 0.9531984974080906, 2.419479242733348, 2.38765321785657, -1.0110232720529106, 1.1659029770291691, 0.9952170870511957, 1.2689334280655995, -0.12326980437496583, 2.30150965591702, 1.0609068335645946, -3.879424604616404, 2.874125766721267, -1.5261338745038913, 2.0953083787172524, -0.39645595854565857, 3.0542751431571378, -1.0452830847787657, 1.2347113451616554, 3.1932203418701155, -3.7983757499938906, 1.329272647052382, -0.8880210406190937, 2.7441668998822166, -0.36628790949095236, 3.9895941038279923, 0.3608110686263617, -0.35421281831195867, 3.0063205372405473, -1.239488587280922, 2.7961913663569637, 0.5709016557181614, 3.0212818537891173, 1.4479116771837945, -2.128378592511065, 0.07639581836507446, 0.3614590287092786, 0.1718822389028393, 0.7833983316095061, 1.0929805735408664, 2.079526883654047, 0.5155943326656246, 1.04394050828743, 0.19370381983466264, -0.6279938469049263, -0.2492679819497301, -1.2300011173585785, 0.5323255117089258, -0.3153679287574031, -0.159195094926274, -0.0507795007698412, -0.4560661934987355, -1.1169899162352381, -1.702238590526451, 0.12881555952425858, -0.5311111471104758, 0.6934071332532112, -0.02212925558318264, 1.9923947722096629, 1.2292931059369996, -0.39166866718884047, 0.8198640705019687, 1.274604822853683, 1.3826190924879946, 0.4555823179610482, 1.2144431565223488, 1.6368109161779827, 0.8981696042439805, 0.7965317423461403, 1.1004115903821834, 2.4275308051471667, 2.6422557670243303, 2.5586149078120344, 0.8982275457036191, 2.267904441888169, 2.1013008154692767, 2.9914692265481495, 1.6729739214200934, 1.3632410473214034, 1.326026832495582, 1.4597030065155128, 0.5837338270187312, 0.7783153278259023, 2.4245426781728763, 3.3245908963029844, 1.9151504755628, 2.088290244442173, 1.8615003994654706, 0.2659739814499529, 2.38760289734926, -1.155023180618679, 1.5792386064728874, 2.3412811529626576, 1.5493005689014798, 1.5908315083776257, 0.8873490824172203, 0.6934354789466569, -0.6536283553722224, -1.3895460009616853, 2.3202406872632984, 1.170857337421294, -2.3084889387933822, -0.39651990287375344, 1.9661753454058457, -0.31421190240663094, 0.580137789258093, -0.20730953677925715, -0.14530955055153857, -0.9080708441358503, -0.1829075664082253, 0.5031315353381182, 1.027447081751118, -0.6814363635859876, -0.6742081587609454, 1.4989141864653632, 1.7039276221295996, -0.036903134152614536, 0.4530925899147992, 0.7882699474441416, -0.30115981311043905, 3.4910704930551626, 2.4743409319699343, 3.4163343578944634, 1.609997506237425, -0.10000623140545925, -0.20543626288263273, -0.48562302244880196, 0.032367419625265306, 0.7156932750810912, 1.2896576803924102, 2.5483140238207356, 1.7385766143316195, 0.013181655057007424, 0.7002379889860846, 0.310802902445567, 1.7386100948170342, 1.236273924985977, 1.919903062824876, 2.377494695265583, 1.0983660605343335, 1.1785918337919588, -0.2759057590382052, 1.8744809778896354, 1.496597413956098, 2.361728537591018, 2.867515460961262, 0.3739354157451686, 1.9033623507889843, 1.8270155110866317, 0.04051041671095541, 0.4663572025306184, 1.7660043014815252, 0.66978251614915, -0.3621823369316312, -0.10337722738610357, 1.2435673998313712, 2.5833648881864932, 0.6768553143860547, 0.7202596366305529, -0.5070839190329822, 0.8436822792558885, 0.008846460945560105, 0.7000850694888978, -1.7960931702845078, -5.266130842230312, -3.0105418781507653, -1.487520487990406, -1.7317006819489666, 0.6046529420741202, -2.580756367436339, 2.2294143072657913, -6.5427060353121, -7.540597664446257, -7.2717882775625196, -4.832111597020019, -5.659310806682412, -0.8163808420109029, 1.0002893772042512, 0.29779526223013053, -7.001397290497147, -6.026393478437879, -10.03992128264349, -5.575823175772258, -2.2576081632518643, -0.570709873561117, -0.17393192838134297, 0.5009032947089785, -1.25787715066844, -5.572516418373742, -5.298835081758072, -4.135350422587913, -1.2339237008853288, 0.04606872170745881, 0.8099034725683165, 1.79447235822711, -5.786180649248794, -5.5271408532977615, -3.1788824417854924, -0.9869388049390058, -1.7774383107495773, 0.4423986317752303, 1.8430732143317718, 2.622801958852027, -7.113229920101005, -3.6257072021026118, -3.1437655611277924, -0.7333565224912701, -0.9288069929261148, 0.7647004982923246, 1.8789613595729995, 2.50248301116482, -4.129084437687841, -3.22374343603269, -0.8971394381836678, -0.9813004325279036, 0.4630007212571803, 0.8631914824822293, 1.9699990217952046, 2.079308698398083, -3.419766919599065, -6.041011784564463, -0.5645776213296844, -0.3653501301932446, 0.20225114275802444, 2.5847687776155284, 1.88234648628604, 1.839100269833651, -0.014335308457174505, -0.012338301304110375, -0.00886407875349281, 0.027023899619211478, 0.02722181653684993, -0.004098785398601772, -0.023586721482378146, -0.03283255995891077, -1.451924146122413, -0.7956012750203221, -1.7155421977233252, -1.4398090339123688, -1.4212518726655594, 0.028416171434241765, 0.9919126956182717, 1.0832756410808877, -1.59698860234001, -2.41216035438924, -3.228644887248655, -1.2338724083984765, -1.7634005943883704, 0.3752576985997443, -0.6194487504746785, 0.8577179462369867, -2.256829697436504, -1.9595057309294401, -1.8423861302734672, -1.9115751815869246, -0.49943042277272764, -0.5927237217588252, 1.4315695121574952, 1.810914183030865, -2.4748365459518853, -1.708649054934543, -1.223255994106205, 0.33584392201387414, -0.05396043912122829, 1.8563370232455743, 3.256110928008107, 3.667593496975714, -3.4647905550013975, -2.274914771948247, 0.27057749141953, -0.4016574258226062, 1.8168224820677232, 1.9838723194621395, 3.975141096166075, 2.911691278459864, -1.0262532807672695, 2.448690994143895, -2.8363676468497334, 2.756692479304059, -0.17067114867870434, 1.4903951123615464, 3.2441868593379017, 7.1585945540299205, -0.0037584827759752524, -0.01747060570902668, 0.0007011478879762657, 0.004005960769990212, 0.008032950131526564, 0.002638537146797679, 0.012173374255466298, 0.006915063421236595, -3.659404554368143, 1.3283573783258626, 1.2053710060686886, -0.25972127281869495, -1.893679326969922, -1.493177550087094, 0.4501256570786935, -1.2232646178711009, -0.3657734170690408, 1.658667004207737, -0.09491944698387797, 0.03857181811559868, -0.8740572344309189, -0.07326697017969912, -2.8300073736230877, 0.3080565797761238, 1.5862133921049435, 0.6371642607469733, 0.389882872119142, 1.011079942867755, -0.06837895576770481, -0.9507993187372958, -0.9711611508125723, -2.5943769978491815, 0.48247138997653577, 0.6357025090646573, 1.0385961460306081, 0.8289644182294981, 0.17747213735161677, -2.114429516442715, 0.6571269326192617, -0.7781997805939983, 0.5368293840450433, 1.7803008977649988, 0.8338361451242681, 0.6926417033489921, 0.03649256223973343, -0.44285969133656217, -0.8537516136169307, -1.6335275890328422, 0.19281005057288797, 0.8220673517765574, 0.4903363946829464, -1.052302605312063, -0.2577686690274608, -5.043684379103932, -4.011292712429217, -1.8586704290317855, -4.287842462531973, 0.9812802194737037, -0.8323320247325856, -0.6612157007265956, -0.09307428815281704, 0.042291778030866096, 0.2838468301894303, -1.0738438934569636, -0.3886474602360468, -0.7926350086740337, 1.4020126828314838, -2.07396535567639, -2.8315865723584865, -2.7571168920019953, -1.5282980697697068, 2.968202256992221, -1.4993503570946327, -0.5329628289115642, -2.0514619140562202, -1.2578904531380999, -3.2213846637437347, -0.16474176365662838, -1.0329917781386442, 0.9867985822975599, -2.494379741278201, -2.558174954653467, -1.3301861020935024, -1.720189141260461, -0.4390991257010006, -2.33016860043199, -1.012099098916832, -0.8190488875825249, -1.2483652516597339, -2.4740290830331486, -3.527826389865459, -0.23556846070560045, -0.9310987994962734, -0.06926344669831645, -1.155810431664332, -0.5666682260643392, -0.723626580998321, -1.5982967332757085, -1.26787354159176, -1.832605346282877, -0.7286894910662906, -1.1387581969934173, -1.6590574955020019, 0.32218857214632907, -1.6124723440435365, -0.15686136159011954, -0.7200177470227783, 0.20595319119603467, -1.3550192874357987, -1.9471268711522094, -1.8105494747710578, -0.876437337389441, -1.1744172839410685, -1.506279331683907, 0.21761368335068143, -2.3486369142115757, -2.9199226900861937, -6.329344521553554, -6.477092391398786, -2.0241931542695784, -2.4565068369091674, -0.2655283221428136, -0.9621063263416005, -3.331811634544859, -2.163717800423056, -4.414945424225264, -2.7301247819697885, -0.7052722961814581, -0.8056053500909679, -1.573846114705804, -2.311632326934397, -0.44995267658670557, -2.6161971409318636, -2.5546061622144474, 0.6757053109932323, -0.9382315476004373, -1.6637043736154915, -1.805431392841595, -1.4731019142762416, -1.4098004334011789, -1.255190696712519, -1.9132258354830185, 0.3639286453455539, -0.10330204063566835, -1.5286720871197443, -1.7314404209620136, -1.1810665932526085, -1.71245249332978, -1.8488235483833355, -1.1277995485814878, -0.960055462098308, -0.8878655065653753, -2.0108834832822855, -1.253037626010009, -1.401137837829554, -1.0912048661879832, -1.1273233916709346, -0.42027499724970513, -1.7594049696862974, -0.608943473934387, -2.448171194789426, -2.160094500286077, -1.7283908668211392, -1.256271668565804, -0.7013253911132095, -1.9528346931313145, -0.6608827668466359, -0.16457484468860828, -2.0277096593033663, -0.9645079553306136, -0.33826960937130623, -0.9022516765642292, 1.1961938144559616, -1.030111752823706, -0.8139924612802346, -1.5721336233640455, -1.1204236773646117, -0.1405665523111037, 0.08569738488752811, -0.37838377876706825, 0.038927698766678405, -0.8064218388821881, -1.1946077136841549, -0.5798580032427283, -1.0513884590812972, 0.6099495183903227, 0.1421055515513564, -1.8188374574854875, 0.2095070798976065, -0.0011809658465850989, -2.5603163783973018, -1.7273848930618279, -1.3042536781342384, -3.5632964764914705, -3.0893769444161334, -2.6743486504156877, -2.335399457898503, -0.29293985372290493, -0.9399321821941868, -1.653941594214188, -1.3041160724969074, -0.27452350705766076, -0.5617461275234338, -1.5514439882112816, -0.7573305843198018, -0.49015716176727675, -1.6244696497821243, -3.7811450618983264, 0.2066037655581633, 1.1049144179389494, -1.0251986378372038, 0.37644147724120985, -1.6770448989236597, -1.8209459948418196, -0.4053821550693052, -3.2783117789321556, 0.4642013349451308, -1.0262336229554987, 0.9917147931272992, -0.7639678475047307, -0.29955572673662295, -0.6166968584741247, -1.1507242231087649, -2.997002072207115, -0.2688197982971724, -0.497517885068741, -0.29195742503929356, -1.5122062435890031, -1.6884682875587935, -0.7674032607636683, -1.7284662634673527, -3.507659230587028, 0.37556833232596953, 0.11105530454365442, -0.9761573214227564, -2.883971104284842, -0.8479249110684856, -5.119584524037647, -2.7216055217638604, -4.849152967310777, -0.6687970666903611, -0.6961429282094044, 1.7019578130881752, 0.5401841570515526, -1.3377815528695771, -3.815652644023476, -3.329706130742753, -2.2184783669052024, -0.4853485065858508, -0.141850666234679, -2.5960962371320933, -1.6000945520287049, -1.1034135003030217, -4.337072976102183, -2.1524238999378196, -5.533946263776863, -1.3641121629731845, -0.7439180626321278, -1.6670351887548163, -2.081060037762921, -1.3341548808017512, -8.275106782508491, 0.19627561752841707, -3.107195034652109, 1.36505776480467, 0.38728035562993546, 0.7309688734138022, -0.672727797141948, -0.8242416026530553, -1.4392531804949114, -1.1409302674416177, -1.463217146172463, -0.05140396760352841, 0.7698697107142823, 0.6601115202176581, 0.8563141599863466, 0.23616509726288532, -1.0955685516837945, -1.876476121765754, -1.0367727998774012, 0.47876937663357844, 2.131653000769625, 1.2064602769072796, 1.4905497983314633, 1.45036968600401, -0.6479898302017985, -0.1770521021042671, -0.7608305363121959, 0.6657852985015456, -0.035348854679086356, 2.2354991357918585, 1.0946196834878905, 2.229524704202283, 0.8782325659180878, 1.4305801670941374, 0.006632950985398619, 1.5278346211952027, 1.565828217902216, 2.91751673041195, 5.503640172935525, 2.352220190636259, 2.4492854423412975, 2.0495907724237985, -0.3290520442993547, 1.4429920414762645, 1.7023955784676366, 4.044176326565458, 3.853358257723576, 1.577256540823807, -0.10227551234716135, 0.9449975698916064, 1.011631577004722, 1.52309417615006, 3.543696373217951, 3.1423304469346025, 2.928099522962288, 0.5998579624319774, -0.32991708962152533, -4.76064462951196, 1.720764646083454, 4.801205001378236, 1.9037717879981437, -1.284721853971813, 0.7259851667895371, 2.1094424177179603, -1.7126219130389346, -1.6149687322976285, 0.1987182030159339 ],
				[ -0.0092380607403008, -0.010446926853578998, 0.015770447492315244, 0.028600391715132498, -0.019658961989771077, -0.0033952904702547965, -0.0037740684930840027, -0.021346333216928255, 3.2205005383546688, 5.147567364770551, -1.731991526323744, 3.8746190228492488, 2.9369455830239617, 5.210005820782384, 1.9521863722102577, 2.313347732919307, -0.4693653773858074, -1.0129737821793832, 3.1451472108823775, 2.566636336376649, 1.8504169038238147, 1.4162505751696286, 3.584262614986407, 2.0016018164176885, -2.8269411532166435, -0.6702025459568164, 0.6862017798375059, -3.600332910987313, 0.49977590656739584, 0.48408029513759937, 2.135477979296705, 2.717205667854347, -0.9445084082726372, -2.193640134994775, -0.5104524810233346, -0.9210071602120602, 0.17445024698336456, -0.9209368852934374, 1.694778149368425, 1.9600902166198735, -0.544076107658707, -0.4211783116816557, -1.3531840066481495, 0.49410825394157276, -1.667464284615769, -0.6662922691230213, -0.9961226668176842, 0.24514101649770198, -0.8291296583328142, -0.5145957122762839, -1.4874878713457458, 0.5443368849490424, -0.9024976716216766, 0.3172029077085819, -0.44658024604849733, 1.1257917715740144, -0.028564368935247844, 0.0060494925319498905, 0.01888681793286487, 0.014835869942758352, -0.014699132199996329, 0.035811556510218175, 0.027310832823153282, -0.01723030042284697, 3.063094104536768, 1.0634714394394005, 1.0313652421470492, -2.4627305182642494, -2.2412462472791095, -3.176146100417861, -3.000591283011941, 0.7501537515495375, 0.28534379260814047, 0.2316800469016368, -2.316220482174513, -0.06378497146917655, 1.4605106657276818, -2.3352173642220713, 1.4590498699645111, -3.4931300399599814, 0.8301292173124439, 1.5431071532746736, 0.9559380348914541, 0.7461171865154662, 0.19265796492647483, -4.009079918061915, -3.1214777000110008, -1.3643395263660862, -0.5249854826118597, 1.2282897072650572, 0.896727542160622, -0.5842612561216468, 1.4489845726235622, -1.0803999513561386, -0.06827702068011424, -1.6171424435366288, 1.0878723243731028, 1.7415345234002717, 1.5611154619700427, 0.3655904430487542, -0.27889327979645256, -0.9062358609522081, -1.5135016558501087, 0.1513773224748508, -1.0032734461202228, 0.7566486446616119, -0.15655871824295364, 0.9700937350007923, -0.8100505108786168, -1.547705917020368, -0.8178181370464118, -1.024071630876321, -1.3463268909919994, -1.0855196885248077, 0.29328184875910296, -0.5617376906422665, -0.7074892542013915, -1.2817020569215845, -2.49504498383248, -3.3424648047139773, -1.3669993756362704, -0.5444050813729041, -0.5925948850950153, -1.7303460163512934, -1.503533925502171, -2.3246881721374035, -1.0602384553688686, -0.0066616218771230265, -1.9711895247400064, -1.2640273196527272, -1.435778788494677, -4.777475145502559, -1.1513056711465053, -3.8530664664154295, -0.043099531322120695, -1.8208209964526565, -0.5869937166168979, -0.5592006692987578, -2.032085054341872, -0.31849840636307275, -2.5775725021125084, -0.32311377837415606, -2.807295128070875, -0.056139545239981, -0.592307124597405, -2.0982041134982112, -1.4353389172981414, -3.0063192169792643, -0.6630956592719665, -6.0911546785978485, -0.9298663156763192, -1.4010509945438834, -1.8298878644053225, -0.43422456535844306, 0.2425445923156402, 0.915925272394814, -0.11670323800154443, -0.38712228192948045, -1.3363985718547602, -1.2442597977856102, -1.8523410193932834, -0.3626544614580083, -1.4358777060147894, -1.508755889826605, -0.35948392704241, -0.029502239173997146, -0.8768568671181898, -0.30384329906692187, -1.7166516524711914, -1.7209325501788497, -2.119988471534591, -0.34036083412533535, -1.3952767425191424, -0.4654995120946517, -2.41755232437028, -2.0015022332187917, -1.126264223922536, -1.0098416350988269, -0.09998204238107977, -1.6687610312034995, -0.8234993450825283, -3.4612130377974557, -2.4946241131572386, -3.0123382809683075, -0.6219275393047654, -0.24815346592568102, -1.985876386307793, -0.5078165863942661, -2.7115718344205226, -1.9214983741874634, -3.858030007861475, -3.0834755974677366, -3.0005011446584957, -2.8469106953373893, -2.4766279880180995, -3.1666666442444806, -2.7098143566032515, -2.56711173446136, -3.05311864028583, -3.1026257776910002, 0.5349271721478809, -0.009940488800624803, -1.3477268879171704, -1.5774552840554188, -0.9362016220506372, -0.8582704493766032, -1.2563498509679683, -0.33309301978261885, -2.4204293756224198, -1.3408944316266413, -0.8696085413935417, -0.7706141391187213, -1.7212717691024726, -0.05699361814729308, -0.3842418691854976, -4.564409307463983, -2.3569535059080495, -3.3207483728411775, -1.0058513216914975, -2.3737631091203526, -0.4312286132109012, -0.7594407844300386, -2.3015888422873196, -0.951927381481938, -2.1731359928285543, -3.408580283900269, -1.1293491379604739, -1.2215254569951306, -1.1167630492827763, -0.8525005239834627, -2.0767184758620214, -3.3891951841878103, -2.248226081956235, -0.6828037378481332, -0.8740788720220133, -2.193579753123301, -2.0782450669487305, -1.9132365138711203, -2.748229784375423, -0.4150627201917084, -0.9463895301071812, -2.098030948200575, -1.001939569750138, -1.4991783065518491, -2.0338229181111536, -1.8146987249567037, 0.1578707318105605, -1.204749367759424, -1.7115729674577653, -1.5229055843483323, -1.7918158929399128, -1.3774370811692318, -2.101145285600489, -1.763914456980755, -0.8851040677009917, -2.6653199222155073, -2.174857488708476, -3.3903919999356815, -3.3684851092058747, -2.9062400434844595, -4.134781513205782, -4.879344406710727, -2.988045726870755, -4.7601680385267064, -3.2398164898967092, -1.51193720814423, -1.582239856154145, -1.4510735113066018, -0.8343158904943055, -4.798823977523597, -4.889949996831896, -7.650481739913529, -1.8512462920793862, -0.7024553464641355, -1.9261210360274277, -2.9290929198399493, -0.3055632412705858, -2.063969627837708, -5.066842520519455, -4.373519913284427, -0.42084401654787085, -0.24953333227562188, -0.6155479886493582, -1.741293705098393, -0.9616500270238718, -4.0444516409068605, -5.211334717283309, -4.255713263380996, 0.35995385509221584, 0.2651818851048144, -0.13058416437545783, -0.5165440369858898, -2.3469551683465113, -3.7568328705800424, -3.8370158346732297, -4.409503978342146, -1.0848580686964566, -1.7641343716227966, -1.597136805781356, 0.32992697841218627, -1.548911172556984, -2.2444726673413427, -1.159527844146242, -1.456497487986393, -0.38769711780157956, -1.489401388995249, -1.7843257543248496, -1.0210419566831304, -2.1217003162894605, -1.6746285457750285, -2.023297278781384, -0.9429389775353411, -0.9231430068699416, -1.4835127609138774, -1.1627203358629012, -1.0186378254888224, -2.6140475499694307, -0.5606125304521418, -1.550601728745209, -2.524598796068198, 5.022269694137664, 0.39706634599696206, 2.367786063807715, -0.5874566211194195, -1.1432633291181569, -3.443098958043688, -1.340804742048997, -0.42693292288890883, 0.3249557836762289, 0.986462150662104, 2.675220188754844, 3.4892574335132513, 2.93990843984298, -1.5760909733530508, -5.95751172889752, 1.0089679294249376, 0.47019974775870205, 1.6497038400768416, 4.066750253799844, 2.8479965280025183, 1.8757835782457524, -2.5520279992390327, -4.476478096741593, 0.5354271075947572, 2.8728334522132086, -0.3491129683510361, 2.3099547925796884, 2.020212382703457, 1.4585840769468115, 2.7566253026799203, 0.9316662182189186, 0.8448815455329478, -0.4774707230202689, 0.2375000519295496, 0.786445301820791, 3.147775498258592, 0.5226896506481812, 1.2539598620710977, 1.1495041524722502, 0.8601342292235591, 1.3678879891601161, 0.39743565824833643, 1.6915405350647026, 1.7217859534834146, 0.986125770458147, 0.6372541062881869, 1.9860091286187258, 0.43506998282159254, -1.6392678685729152, -0.13900812430119802, 0.3374660574417866, 2.701571983625506, 0.5228253237939454, 0.16387981965080403, -0.4871957282394775, 0.14158038183635013, -2.712687360240596, -5.36713359116605, -3.3287194481198377, 0.06490759236303709, -0.15744249812109662, -0.8704785111926198, -0.4941432175659309, 0.7086960347907998, -0.018052850310132183, 0.005981029025818596, -0.028073505254907368, 0.012543367438845127, -0.005775566579244081, 0.0028173772022269117, 0.03496667721401322, 0.020194108758448077, 1.3961704145579121, 1.3363258714206931, -1.0075280946783949, 0.9729128990625184, 0.8186259879668645, 2.2939085808969044, 1.8777874499378764, 0.054639916676664395, 0.09651728848051247, 0.7233346191400095, -0.2949106406398791, -1.8901695861933896, 0.4286124152149425, 1.798533210110155, 1.5131975466840974, 0.9383983918258613, -0.10303048570065676, -0.9054315575163919, -0.16988827320457306, -0.29938423437010925, 0.2950671042016437, -0.641121607888991, 0.9582117055929111, 0.710249795501052, 0.6959045337708022, -1.6602194426410972, -2.9346268758280036, 0.1580964937651277, -1.8254055151811344, -1.1701679635894093, 0.5469867451669307, 0.4711507427518357, 1.0679364368276902, -3.4839247334307513, -3.011480897144441, -1.629278481186161, -2.940156280391443, -2.8893469032042125, -1.2943320076689473, -1.0636423341046097, -2.3867065367997253, -3.540342826365807, -2.0371214526922414, -2.6613230220450586, -4.245201957162002, -5.043715915148791, 0.1725909365221071, -3.6314597638838033, -0.02510895121191547, -0.011876713715683797, -0.003230433376673293, -0.0034249717804139294, -0.002411561498867119, 0.00925995040546974, 0.00008471992400808597, 0.027640367622744057, -1.3251303338132692, 1.7485983464095496, 0.5380140231457631, 2.3805765237745917, 1.0202674460767165, 2.908515807648808, -0.19319142667473646, 0.9820770818127088, 2.8082025780001723, 3.3017027059436206, -0.8443342938365819, 0.34366471212516925, 0.1708127742782548, 1.6172395079218174, 1.1726991914736622, 1.0284832918959919, -0.6305045565441766, 0.5476802928927879, 1.7195878670473788, -0.4554630470734972, 0.46829483753115814, -1.3218417069464592, 1.8444623621472778, 0.503947732723824, 0.6075042823148944, -2.1312546606735356, -1.1263972906874162, 0.16376012459645925, 1.0830675869562798, 0.9047061045325506, 1.07047410013324, -0.15827521727352362, -0.4923213791410834, 1.538565859558951, -1.580749225311377, -0.25956046116097786, -1.6666497924378232, 0.3169401164295985, -1.3155099742621086, 2.6838230896985698, -0.754282523829264, 1.7226320759319973, -0.9307114502982896, -1.3263807026848693, -1.7025797120193877, -0.009180272477792724, -1.4449372751725098, -0.19712066018223737, -1.1384114859332528, 2.350263189233505, -0.23320770565352303, 0.2743440713481139, 0.44333008612084573, 1.9157182913598079, 0.8414550618482576, 1.2222612838907798, 1.8954291342524512, 0.180137903309614, 2.7318440116136276, 1.0280087475720554, -0.8260352083238028, 1.3564930081916176, 0.7462626983591686, 0.19002379566338432, 5.328996741697524, 1.773306826138203, 1.3061003183552717, 2.0878916482251255, 0.35470351460088095, 0.4124820359542184, 0.8165662722625068, 0.22278692510854142, 0.7522238740128491, 1.7163703291550376, 0.6335863704692812, 0.15015995142232721, -0.25555083384297894, 1.7100161683237245, 0.7572029947782536, 0.962673767830013, 1.7380024963983156, -0.11484348747463033, 1.523714817092374, -1.1707040041921195, 2.091870919685965, -0.15945490972355383, 0.9651727411530331, 1.4726940471416736, -0.03241013224499151, 0.08693026729289059, -0.19973678628445746, 0.9316614325197421, -0.7795521616775104, 1.8936766928617783, 0.6992198296763015, 1.9324605170561446, 0.5112199938431657, -0.3656500517468422, -1.2257970180892028, 0.6793718472861418, -2.36362778026619, -0.6430016801835138, 0.8025006216595177, 1.4054854546383833, 0.17562234383471506, 1.8329123463584427, 0.009936860139097718, 0.2333390869445679, -0.2881298522423498, -0.15282897900169046, 0.052633736473875085, 0.2221319733832633, -0.13441524305911387, 1.826601250451012, -0.2968912488559726, 1.703188812101057, 1.3350025686144213, -0.5470513792220032, 0.9423832221424796, 0.1820876820687434, 1.8198208368953628, 0.7323529577382376, 1.8118959828364603, 2.39590213656036, 0.07672563378731508, 2.0143850286271117, 4.731607622959866, 3.01445034670792, 0.9435944596021396, -0.1875362773942966, -0.24703875995953142, 1.4021084128813264, 0.05900560965525051, 0.5083502590638704, -2.443405813396752, -0.5851605085125418, -0.20121240217283332, 1.7693550077510192, 0.2995447892550651, 3.204599034538634, 1.1820422892045137, 3.0463349016576076, -0.7399294168904923, -1.6359782850906954, 1.19962294409818, 1.0038158982860539, 1.3349641148554185, 2.2543981742127257, 1.9936891769516918, 2.4615510282832207, 1.2045014032360022, -0.24571368433841828, 0.9606974622076775, 1.5078749853476252, 0.8894625208249094, 1.016558535578136, 2.3573410068638623, 3.387667171250313, 2.6234825617388458, 4.389750022537261, 0.8017379858521883, 1.576095865391435, 0.43392302781517594, 3.1000170372538407, 2.0822236912428846, 2.1616026391300505, 1.848198619686277, 3.853234995077554, 2.1842442467250462, -0.2621978263148504, 0.39471755914044937, 0.1503521708557227, 0.048664933817975826, 3.196360145218818, 1.4251905876190454, 2.9711867216054233, -0.7682689808630898, 0.27974742115376267, -0.43366548689359447, 0.8376831928341416, 1.3305694677525683, 0.5044566388535117, -0.4810389460879825, -0.12719535618726333, 2.434542229300529, 1.7948079593166855, 0.850960002837049, -1.2431644797246477, 0.9854553910981052, 3.4352690583814254, 1.6629912491286822, 2.820630343364766, 3.0993866527398213, 1.638191721017764, 1.6580919741900602, 0.5512940711478301, 1.4447265029452043, 0.33423076563614396, -2.3802285700905332, -0.7251765363297381, 0.4569132360560552, 2.8994816828624463, 0.03318806281429138, 2.5854267444153582, 1.0657235425471052, 0.16778688069877576, 0.24108169547639083, 0.6983062985792201, 1.156559794705972, 1.7047015045605902, 2.2332859644427887, 1.4921784560771785, 0.9816422968480766, 0.15607191668020404, 1.3159927362166681, 2.0036585845469377, -0.6582435331974071, 0.12768141192607538, 0.12322240324891848, 1.337265801173455, 1.1157311613489829, -0.3945167125124847, 1.7958333762680911, 1.556313773988677, -0.2697671056030309, -0.2888700624245416, -1.2635474114729597, -0.06252879129804957, -0.41125294348689834, 0.6750514784258193, 1.5035267798043686, 2.3664332548266, -2.3018697663002756, -1.7339131634359302, -4.308625609894536, -0.4487469180460246, 0.10459224978948471, 1.3470132656601803, 2.115605662757203, 2.0512898741137175, -1.0452278323603572, -0.058858122264472, -1.067956068599337, 0.29332235606326224, 1.6049584915150124, 1.5529744193308805, -0.0036079422274136776, 3.9421173292914355, 0.8993001606531847, 2.948910380960674, 1.007436882632385, 1.3438372628983122, 1.4214168427801288, 1.9679983925380036, 2.9816043626673507, 1.9520850803969938, -4.7751965983210045, -0.8869897956778862, 2.837464878504775, -0.7530074619100331, 2.098006910366492, 2.6569931662113926, 1.1307853527602854, 0.1809323204040639, -4.14985124040186, -3.682862501967, -0.4725528121741794, -2.7794597211662317, 0.3622130333036481, 2.544444651726441, 1.7795335042858158, 1.959959982219369, -5.408949707916458, -2.2519159085906617, -2.217074484367905, -1.253970265145325, 0.1129752121672951, 0.2590181270056163, 0.8480599856838904, 1.410081568687783, -1.3659015465818753, -7.460068043700738, -2.9101971856383333, -1.495637477903872, -1.35197239733093, 0.37305541420619337, 2.1504562131293308, 2.2787927970903845, -3.6780145184836877, -3.308013944971948, -2.7312149216169734, 0.19209378068867833, -2.757788183520365, -0.04772800916555936, 0.2344578843878486, 0.4509823940419662, -4.632105146743149, -4.938925748893592, -2.105431685947383, -5.061261151935495, -2.4555445576164967, -0.6329350302245041, -0.2239404409767081, -1.2942734327461345, -0.4772799933042458, -8.165051625840665, -6.533505501396023, -4.125404670733742, -6.287517329356782, -1.5464927831698736, 1.335322623895652, -0.7524427189906137, 0.47797605807870003, -5.26269487949411, -2.679440617386033, 0.08934585073912993, 0.14271772074870176, -0.7092383710218741, 0.08528725284187706, 0.6831203091891244 ],
				[ 0.009786152911185474, -0.005177662445619877, 0.017338248265233037, -0.02546387715829263, 0.02206436619398411, -0.0033254422064168477, 0.035743115511764074, -0.035288953133341114, 3.242504577351998, 4.064475242777977, 1.213572721162689, 3.2967934102608174, 1.6173707075186257, 0.5295360827452311, -0.8531792174537652, 1.0701979410001417, 1.4259035564521265, 2.783374624731659, 1.8910958303973249, 2.417570293873973, 1.6803946516488693, 1.4283727703714642, 1.020455601935494, 1.2301434981702437, 0.7081169338523267, 1.3350875460902591, 1.963754125296804, 1.0021641166095094, 0.6777944113094952, 1.6274511239064697, -0.3006749675322348, -0.23102079410081852, 1.1811442842665936, 0.5772414158232022, -0.44743510784565155, 0.28913814640637103, 1.032337576215882, 0.04929733437105562, 1.6496671305036743, 1.2425468086893225, -0.6554897282957173, -2.766240647967605, -1.5029730731055508, -0.8856003570148395, 0.33881189092173275, 1.2564620708779197, 0.18597302138476246, 1.5526736455517216, -1.2680508542877642, -2.4739654136910634, -2.275739884844704, 0.6037623995101731, -1.1744745850321074, 0.3438434022945149, 1.5920560178596506, 0.3568926969803816, 0.03536058471360829, 0.009362125864920485, -0.014718548820180605, 0.03429407752147331, 0.007675353225823724, 0.016208514955469475, 0.004964067058584173, 0.027502042245984716, 3.109811263232994, -0.5882219549183565, 0.1583966960412678, 2.4304056933713993, 1.536105781071237, -0.5965950050255913, 1.2760035641962, 1.1702335588202804, 2.5508266412120255, 0.28380257916360374, 1.7557086655347633, 2.278494721550009, -0.6525089170372947, 0.8533267415671002, -0.6050575754021335, 1.0678474624503147, 2.189205596204064, 0.7659070484517099, 1.989268831808766, 1.0556316428446575, -0.8378150117441502, -0.8416878743817402, -1.1948844854220286, -2.437787272628569, 2.460888265519422, 2.4864423972792875, 1.6431185968243676, 0.7365876124903841, 1.0268516053516432, -0.1748780150144597, 0.3781006566778765, 0.10433061559671467, 0.2502984508672949, -0.8907038257662326, 0.55079886838947, 0.6811164044380558, 0.756165249823032, 0.44779587985671415, -4.130017303162028, -1.7639240089068988, -0.6780220619836583, 1.4987228702297806, -0.7997572367050146, 0.17554246603447324, -0.28707389594967025, -0.24014002128688955, -1.7650596366949427, 0.19387375507313362, -0.20749491946619592, 1.1146837362092208, -2.2368923409039487, -0.5676554178080526, -0.9738803362629598, 0.21657391457474204, -0.34813611771864345, -1.0440676870886163, 2.2346322048523715, -0.7418644553497615, 0.6489305549196557, -0.20965754594949088, 0.34851392804829256, 0.7786286718635244, 0.8899544165407286, 0.3691985318669408, 1.7707105318745935, -0.003197581584189651, 0.055463349571538076, -3.2737361836293415, -0.4297976994663633, -0.2987402331239893, 1.4325017284820627, -0.27248417772779415, 0.8325321491697264, -0.385302848444613, 0.7263938611627622, -2.7210733481389253, -1.8645604515430347, -4.0170363849571675, -3.846383308509973, -0.4839392662685324, 1.2407364151063476, 1.1053794352164183, 0.5673246224738168, 1.2049995976731553, -0.5647176337168981, -1.259629019565876, -0.7553197520864362, -0.03759008675568587, -0.11412703730213376, 2.8948246622922373, 2.113755568275743, 1.1529161964416368, 1.0611090466530149, -0.2124880084292897, -0.4885504840821851, 0.33662944381953613, 1.7669858775022944, 0.4554513219991873, -0.5094839989418304, 0.17129227424718513, 1.4185759089671226, 1.294410171157164, 0.8862475312148693, 0.856380106684141, 1.4048446154342522, -2.3588258592830096, -0.9659697632585534, 0.5260844177705655, 1.122362837453992, -0.3455030516899536, 2.0478293807003896, 1.43230291404176, 1.0113990397238366, -1.8512041815681735, -1.8715253407757955, 0.5377658418900592, -0.37243142480363056, 2.7955953931685396, -0.009286426020726669, 2.292326815584273, 0.000013832947995707405, -0.8897589507998643, -1.5724916304100158, -3.0187399861103126, 0.7673871105152715, 1.397152272631167, 2.0433892392852866, -0.28672701273333995, 0.8124774255861977, 1.841770058293703, 1.2375178047711097, -0.9231761886418686, 0.9324271889237231, -1.3858939352606052, 1.702475885475974, 3.449328969535238, 0.8861676198721825, 1.0641419181414558, 1.7257506860672334, 0.4977757934883584, 2.810172401824059, -0.6055322538028233, 1.345030897730598, 0.46632344117009566, 1.2908768147241467, 1.0727537299702723, 1.3246474211779287, 2.4581764375918413, 2.90009712461827, 0.6433120915625237, 1.344356081008115, 1.2527350957333372, 1.400811505230728, 2.398479417564257, 0.6425763683519246, 1.6232220796846009, 1.799908353157641, 0.8542134947612153, 1.7329207086692642, 2.4282012049634996, 0.7911902404764294, 1.8951612531505049, 0.32105475377931153, 1.4566672650497139, 1.2719960793905745, 0.6701920148023157, -1.5510372063105948, -1.8809327158131088, 0.44096915930996644, 1.933702837560849, 1.8518395526296558, -0.7694669618759497, 0.8902454292421813, 0.10992080978796333, -0.4137022032522111, -0.7876751905762054, 1.0912014313817113, 2.284439789749878, 1.116784522741019, 1.7285857092569632, -0.7871979806871404, 1.63800537060724, 0.5918753303903573, -2.7599333056291053, 1.7927357123811327, 2.5392684128467127, 2.7443540340843726, 1.5281720071168687, 1.2327584922097368, 1.6459782421165023, 1.1768425268831195, -0.5513157181753261, 0.19768475079032968, 0.7820631759729919, 0.5681066933287342, -1.8999536537255282, -1.3765338532005675, 2.3543118620321684, -0.9316831218784881, -1.4370029442434056, 2.7144243820545237, 0.5466952833514004, 1.46644010091122, 1.1397195748347775, -0.25825149506097167, -0.4362865820904785, 1.7713237210560784, -0.47006318708278505, 1.6905137363885314, 0.693054501862638, 1.9088630663881714, 1.0032234693033153, 1.0872480368440753, -0.3494106041174535, -1.1810370301747222, -1.7015851618563675, 2.3774246746637018, 3.2443793110018087, 2.7848179036234595, 0.004545554081503016, 2.2281323360098746, -0.5957749175398136, -3.4726083104672862, -2.1690490638021935, 2.93170806290648, 2.453910554951097, 0.6128216278280718, 1.620164573755932, 0.6586264488679607, -1.3645334427382985, 1.2554095653725266, -1.5381794218079987, 2.8486765141447075, 2.636635769061794, 0.9082980613857425, 0.9864570841480065, 0.5346118899139326, -0.17998886964659602, 1.167242161268538, -2.1181139941885756, 3.4026929009412097, 1.5847911119794633, 1.7290415053866546, 0.6352775608113739, 0.9338683067696419, 2.0257283697440256, 0.708665151853208, -1.679701390710676, 0.21747764739743158, -0.06916885778952425, 1.3044169627604378, 1.6542272354682668, 2.8013449821995033, 1.8494410465169997, -0.37980428375481073, 0.7544761207482213, -3.330225914951442, 0.9909711564513765, 0.5570191510176108, 0.7942621431254204, -2.0909263978407204, 0.6775677250754083, 0.9901520497816131, 3.586663727476349, -3.3698801735332156, -2.4890279894533474, -2.861822053007776, -4.009330607014098, -4.415668150979951, 2.031663588781418, 0.7151660411810743, 1.4812871415302198, -5.315605082018546, -5.880780486232328, -2.9297139679669204, -0.7147827198253861, 0.39863006709947757, 0.533375803923381, 1.7973927075463736, 3.0273133537900754, -3.487412276586227, -2.119807397931753, -3.4849371343104787, -1.351286427517556, -0.09541144605888809, 2.691258418938079, 2.5203659694007507, 1.9401418786724784, -2.9033376125152435, -0.540090513912727, -0.626300036146666, -1.0996888257321586, 0.3906861958959972, -1.2826364377700898, -1.1580797409464432, -2.1257214461662914, -2.4158917899672585, 0.4045473212996979, -3.0179315558576203, -1.490169550929702, -1.9710565115526708, -3.109558685140227, -2.8106364757786624, -4.577604163815066, 1.0735647697797273, -5.554991250609306, 0.3645175596555342, -3.898565273169293, -2.1154210030649563, -1.950904169829311, -1.6798431787675976, -0.38303368110602765, -2.755603755809999, -6.5895237846508286, -8.473010015818646, -3.744923224470552, -1.4977046743620857, -1.6340177803188238, 0.7355846536900487, 1.7510962845344207, -0.011169700562192467, -0.00909713437759, -0.006493903529753885, -0.03383138162714042, 0.0035769416099688933, 0.0038448794613443237, 0.010428508524116895, -0.007913788423507498, -2.251173519791554, -2.668610381540424, -1.1287784056961108, -1.2467003372879515, 0.48784799577887333, -1.7340236406853797, 0.13097333929733546, 1.666606927628381, -1.9192582628880122, -3.00530074147326, -2.0592302324348566, -0.7449764347740658, 0.8267422597599804, 0.11825446805284859, 1.5174952036020217, 1.4866340811603775, -1.9197057152148458, -3.2693258463503643, -2.2986214779322136, 0.3634725389063003, 1.266073954470388, 0.751575628835089, 1.3441043775804604, 0.9716049859606055, -1.3541943604658537, -2.164731816740655, -2.3253792498762387, 0.09530943931190591, 0.6194439822081101, -0.6621620031595249, -0.09853182400955544, 0.02612183720306301, -0.3144144736241924, -2.14989039718479, -2.7727481998979937, 0.26792824370329443, -2.0194828987566145, -3.463191150786155, 0.04295318948781089, 1.3409868879838558, -4.008524087434057, -5.741077774059163, -5.915318924685505, 0.9739845661548259, -3.687860568237834, 0.38826837181384005, 0.14713859582713937, 0.7839312628128277, -0.022994428514340016, 0.02633187569266908, -0.029995892798576118, 0.03448527946775074, 0.011003633357093763, -0.000987717738321819, 0.002519670206655688, 0.007628725260142742, 1.6941645463888744, -1.7603612816729879, -0.5698824259639705, -0.8990072574994061, 1.6089313527610725, -1.2078567564880751, 1.4052589902404005, -3.7275048366175634, -1.0581710218319977, -0.23314715877461953, 0.6446953578878858, -0.2857849297308821, 1.3241588170123912, 0.38525121007321533, -0.07430688420065351, 1.0747456758154625, 0.309895261513194, -1.894429235418116, 0.06892776554475716, 0.585180814244453, 0.8721743705725313, -0.052874147925107286, 0.005378440821795586, 2.7544591777888865, -3.926105775322959, -1.0116404384203457, -1.8452943573361988, -0.7402218737390096, -0.6998265493503094, 1.712816413151077, -0.09560969199472, -0.029480464087807794, 1.0662807052689374, -1.7206693217123916, -2.0244069194089414, -1.7813676188444372, -0.2542427258178903, 1.328405839920023, 0.03702934257030085, 0.8168844327101521, 1.0910073849771735, -1.4543824679370334, -1.5551255281583067, 1.047830276177623, -0.5631152313615923, 3.1589731363094304, 2.149655743736278, 0.6153892230487812, -1.550785244932327, -0.501217898897959, -1.6021841515217319, 0.9377686290137546, 0.9647871569740291, 0.14848636973607934, 0.060412101604820176, 0.4469653999268275, -1.6177826420274501, 1.951102905671943, 1.931922604355339, -1.6284189419128283, -0.3511941067356034, -2.0162594916199166, -1.6863394398198563, 3.4474464664672904, -1.8247858363656357, -3.5395185156541453, -0.6339360190735819, -6.145753383479637, 0.17826762555634293, -0.26141310193274225, 1.0612351204999753, -1.034841430578901, -3.9029308382510193, -0.7092443752039468, -2.070227734640056, -0.6366632716616484, -0.9264767368458896, 0.28446938739544697, 1.3791223933187482, 2.3075184377859665, -0.6062174627636217, -2.374851982913783, -0.1600145576371542, -2.1041597002319627, -0.1366446467894708, -1.1193910175370907, 2.13877521649939, -0.07384142911615967, -2.5077244981610005, -0.5257882938561724, -3.029440967133316, -0.8864669510527193, 0.34981560631516073, 0.9094484317833058, 0.6232666189633659, -0.22649499702027795, -1.3110975365659308, -3.1954888456257198, -0.5073561278975779, -1.843410919237662, -1.3506101711942704, -3.8365758914004777, -0.5694770596728203, -0.09571014638190077, -1.988164320249171, -0.08117607291748001, -1.5620761376994325, -1.4846360936609988, -4.401468393186494, -1.0245368899072769, -3.9428295447433412, 0.3276930388117053, -2.306709129981849, -1.4117112963908622, -2.6093527952408446, -2.1994731417850293, -1.5531591004010648, -2.679218301286615, -3.5159690347371977, -2.250780063367571, 0.024302280788341755, -0.4996348592037556, -4.856971189394442, -4.3606009818697204, -2.904932904307359, -5.276339679799153, -3.8688867738170627, -4.998399673692248, -0.2998891058538263, 0.3926411060844288, -0.17775081688523217, 0.11404787320459772, 0.18270447026841283, -0.3877083882365874, 0.11374649038818278, 1.2395387751094502, 0.9243261340835273, 1.2798011090821935, -0.6314855292508402, 0.6316404263067289, 0.7450831820772171, -0.004185008261097403, 1.330229367100235, 0.6481669986731765, -1.249966598450075, 0.27650822490676563, -0.2564492647942629, -0.3298665957630369, 0.5925302663818801, -1.4344063391519148, -0.2697511714371925, 0.4244739156174564, -0.5880259276909631, 1.0036858910490547, -0.2784452387834542, -1.279580623060234, 0.07528640297729286, 1.0352243149749871, 1.9541977368447028, 1.0360945354166748, -0.6806540103515362, -1.6009890469365302, -2.5355837891737503, -1.5659927769499078, -1.0272933441233838, -0.27993727059139034, 1.2792098513734105, 0.4972815483276929, -1.0119996938338323, -0.0058609012418214205, -0.629645274620474, -0.6603523139687273, -1.4350379050510467, -0.8698197372124276, 0.5305046646190886, 0.18490076852646556, -1.5343835854512662, -0.8150572458634249, -0.11631591433703799, -1.565975355623062, -0.5388941255431248, -1.8181651672377526, -0.3093950298149522, -0.7067693214385403, -1.0474998804681164, -0.5713811305435342, -1.3033180763438676, -1.182914543774558, -1.561866857451762, 0.3939039859170767, -2.599799692251526, -2.6271024282132402, -0.20295298774428014, -0.00812445510780747, -1.1089691108100173, -0.778336208013206, -0.22743954216099782, 1.479496090490263, -1.529401284029537, 0.575693780429904, -0.3651434304041205, 0.20028292072213955, 0.4754062267904909, -0.13497352421257722, 0.9950033927772295, 0.13480189931982323, -0.6633938995023881, -1.0735100727620368, 1.1331708817693813, -0.2692072506869978, -0.47440249762824, -0.08132768204783335, 1.465489995667863, -1.0093836835332397, 1.318798173496829, -0.006262511868100308, 0.4478683974103435, -0.048669221696649306, 0.5179340185995978, -0.9309302383292875, 0.14415251926573816, 0.5954580369703191, -0.9610312211524519, -1.7334313323644912, -1.0875984276116026, -0.7430337186601896, 0.13235091876510446, 0.6681564603683029, 1.0003427361506385, -1.284139752102255, -0.15534716172870547, 1.046676561954582, -0.11191448377821125, -0.5271483567432964, -1.4022814296593822, -1.0120847552433705, -1.4182585213219685, -1.1504118017287508, -3.4780632351915073, -0.8827961711761058, 1.1432134205299236, 0.8248538088063198, -1.6575553338772155, -0.22678016073301321, 0.8004658147122848, -6.036554540836624, -2.6916942124573273, -0.06401512905235697, -0.40530343301354177, 1.441452469965327, -3.0407905479508837, 0.07915403590242383, -1.379143601278839, -4.026909953570857, -0.6475050140750248, -3.2183845988802866, 4.248660063044617, 3.7617957089090943, 4.230192084569618, 2.3915369476609567, 0.6322099604948349, -1.1741822448547816, -1.1372563533926026, -2.231910108677107, 0.9743140048403075, 1.883450328057393, 1.6365173516231069, 0.615519048477312, -1.954350128130461, -2.8724574835986503, -2.414317290417498, -3.528199863714237, 2.142964029195656, 2.0233586305407565, -0.053892426335653824, -0.7661288643814524, -3.847904868952641, -3.5810104000792986, -3.931926264008421, -4.3751781360918995, 3.792535684868713, 1.3014241142282033, -3.604653638670987, 0.7751657649436159, -5.19234460533069, -4.332539826958286, -5.995409699322764, -1.6441407241139554, 3.672503379135794, 4.023421169047717, 1.1504377461274398, -0.46472447736397243, -2.7667546201203375, -5.655288150985479, -2.6274588389812457, -1.7998535416559076, 2.1362364305090824, 3.142948295698886, 3.792926997864692, 0.30473829583487666, -3.003381656570926, -4.104179018797315, -5.723807338068068, -2.3194852830965527, 2.8584734356348984, 3.268239826672547, 1.9681423303700722, -0.6837889510163391, 0.828065427041831, 0.8796881700671186, 0.22366939809993264, -0.6966904033380983, 3.8628562458366313, -0.43149972989559165, 2.9111816524981746, 1.162739562712409, -3.2921816706035654, 2.390789173286056, -2.7500011439456014, 3.3655769142563416 ],
				[ 0.0004304486945203792, -0.0001053520912901102, -0.00368457799698994, 0.0188190857415736, 0.02020980022867632, 0.009779106235928241, 0.018227501448530498, 0.0016686776025343023, 1.6104171553687914, 2.54636719288753, 2.1294299491393547, 2.8449456975488805, 1.0757880025202555, 1.3954383611190562, 2.864554243357397, 1.1544416593344733, 2.252961644994098, 2.100238680011143, 3.169539545353427, 2.413669916165078, 2.704462740275754, 1.6062181181082715, 1.9358281774256667, 1.5091952440831877, 1.7987344627469586, 2.163699858931152, 1.9641324964017672, 2.4057186951973826, 1.887254183601151, 1.6191827302057427, 1.6758088317057271, 1.2569665460192276, 1.5732648969762164, 1.8460652304669776, 1.8526680525357446, 1.8912109605135714, 2.5630520064291153, 1.1892979525655003, 1.4702939622455238, 1.6198063678415202, 1.3244794043408663, 1.6050449579241444, 1.4087434108146732, 1.216554707575674, 1.092916517817817, 1.0397647554370446, 0.9817724855245152, 1.3731635469941545, 1.2347052800044722, 1.7586414920318665, 1.276686334076912, 0.9484472179477017, 1.7457012561841136, 1.0153659498757188, 1.1622516691666762, 0.8329616992210538, 0.010088063310979598, 0.006574889295401188, 0.024876390785205642, 0.01750555611080172, -0.00583324608319895, -0.026583020316004263, -0.014311040238488223, 0.021788307373931087, 1.5865353969501184, 2.1890314384351615, 3.2702213476207995, 1.2594754649350839, 1.1690018750899849, 2.802481980494531, 2.3747619188789963, 1.2584486345524677, 0.7223280239526227, 2.106868328842543, 2.39757923286254, 2.048122632100409, 1.7598523909005386, 1.1202806330738693, 2.8302475926407626, 1.6198427755048335, 2.7641944229787474, 2.9845877728900523, 2.1497661930323244, 2.5989757658180834, 2.1952523416321963, 2.0567490815633165, 3.2179688069054713, 1.9902980175367293, 1.3131871094757228, 2.3177183563683332, 2.3594724249006713, 1.4132683688000156, 1.8904990971286062, 1.9259306868595316, 1.868873655775284, 1.515048554453885, 1.1468779491451178, 1.8699931382451398, 1.9472802293082683, 1.591943813668313, 1.7644806143050007, 1.617794593082369, 2.141941532848179, 0.6406626504532541, 0.9055236602742185, 1.445846266120411, 1.7281054391266684, 1.5199137744181674, 1.9345657602107214, 0.8875086285061683, 1.332792044031024, 0.5957744788022407, 0.7587288329800425, 1.8196419442098053, 1.2287396300295779, 1.257723518415284, 1.4350460172486514, 1.1279748268164271, 0.9841250749208469, 0.49278108093015305, -0.825347218744136, 0.266957757112973, 0.8818503889136496, 1.1619091665810997, 1.2264516384626745, -0.08674621633158806, 1.2281075902695229, -0.03727277068424356, -1.568618732172342, 0.588859084576604, 0.670640777876552, 1.2632474888916352, 0.5001955845135712, 1.495322416989675, -0.5293409494356852, 0.41726903356134204, 2.0539549843428446, 0.6812062937479301, 0.538915631503949, -0.31296938212306946, 1.8531833287017017, 1.058969478882412, 2.157392488479206, 1.423120324140714, 1.3373457086196392, 1.456165828787542, 0.7459054104553474, 1.3706697875020804, 0.33870858552847155, 1.5218699353800973, 1.1390658246622691, 2.392360528789078, 2.265871229540349, 0.08592960133024721, 2.1243738300167125, 1.4208416150241656, 1.789218128387611, 1.2536779268784715, 1.535641121023059, 0.8925138051381304, 0.9664402336872319, 2.4386311533093483, 1.3290341877280818, 1.8277406548171333, 1.225652931466778, 1.799191555546763, 0.8237252741087744, 1.9382827618982674, 1.702411867751699, 1.0175270374274625, 2.194968039699557, 0.7159696389338305, 1.744690369330701, 0.8593828850526324, 1.013791797719392, -0.2353793524833179, 0.14054315370855325, 1.2773386967178488, 0.39184955307182584, 1.34869171553586, 0.05098369499179669, 0.6405611761681687, -0.663391528505378, 0.6193210179495134, 0.5283589871075509, -0.1312973714800848, 1.4510235849042992, 0.6961763675314548, 1.3168478412894922, -0.28507149107540125, -0.447212697979757, -1.0746516154434431, 2.6531462334589393, 2.9197453710536485, 2.35014558328798, 2.3091031861419493, 2.9755987419899528, 2.027087377613894, 2.39423358043583, 2.0725225450129563, 3.3962098822130384, 3.4219235208896492, 2.8923513048944463, 2.974830242124784, 3.6054924726071325, 3.1942332718434, 3.616853532023057, 2.8833687828122323, 3.102150749050233, 2.7377303696060866, 2.918797323839668, 2.2366750434480784, 2.854798656480269, 2.977043357969358, 3.3303725959658084, 2.9345482197894133, 3.1624343806443345, 2.75722410877744, 2.840717012996669, 2.7095592928122114, 2.3433138259236688, 2.6072429378485285, 1.8409596168646862, 2.820567905151133, 2.3817329177601647, 2.7151141001112347, 2.596169617710434, 2.522744938777805, 2.41853987352571, 2.797055189653528, 2.6152439595168993, 2.4993152684604834, 1.5915487768666907, 2.6497528266140646, 2.7889263758318172, 2.2884534168870685, 1.855049537203092, 1.7308837394105452, 1.1617458494450097, 2.087608818039029, 2.5743836713059474, 2.456667267402931, 2.4216117025339723, 2.3323675503144763, 1.7113436822813806, 1.0474680074965759, 1.3179573822291408, 1.2692796865120344, 1.5170528780050447, 1.6919399206454366, 1.7743370393557012, 1.5295785435218456, 1.0783668886246973, 0.7478569199917496, 1.3988263356048634, 0.8883190717270185, 0.9840696637622718, -0.5240138240218924, 1.000731937528331, 0.6454967507534537, -0.5600377183686661, -0.04583573297991289, 1.336211963060721, -0.17962734056226787, -1.741584885033668, 0.8324540573062513, 0.14763286220797087, -0.17661741146208515, 0.4806747912692789, 2.0653047817149117, 0.9793620004931178, 0.5347076104737493, 1.8826331374544862, 1.11202001311574, 0.9354128668182172, 1.0566190372527797, 1.4831938829833529, 1.4728166926155812, 0.39348119549450505, -0.4353503833669297, 0.4862326491789882, 0.8355028181065111, 2.173501045429118, 1.2837915126767188, 0.2825904091200018, -0.09578691285993858, -1.2446131027015026, -0.4141472499644381, 1.9026171809797507, 1.3136332791135472, 1.060545664144702, 0.1894382825656881, 1.0910319088563467, 0.184810466263376, 0.22063484509934836, -0.28650065251470963, 1.7292214064627298, 0.16189882471577258, 0.13157378111505547, 0.5547961349991732, 0.13740369442963846, -0.5640847083136068, -1.9156252461371333, 0.10793561472412841, -0.9271418511938323, -1.1808375510444762, 0.0024047408652688993, 0.11934881145213333, 0.2635170549823811, 0.4780465401754334, -0.9606939479459458, 0.06439507229961493, 0.22835670392166157, 0.711881945403531, 0.21454629185448457, -0.6300166374459524, -0.18899700503416042, 0.4004410398316818, -0.002366379112488798, 1.1411621167694137, 0.11428344044271598, 0.3345893597493798, 0.62078152258537, -1.1269993032005932, 0.9189738233250004, -1.8518715094544853, -1.3498927131070253, -0.2670841974561151, -1.2047195459425843, 1.0771315201195324, -0.5234961114883689, -0.023442720279928074, -0.3611708279655313, -0.8532139627839468, 1.6455435421288382, -0.4281283915524438, 0.020934732748397775, 0.10461934228640464, 0.4726679630276772, 0.07563016999613546, 0.17621991982648758, -0.1673050390519469, 0.5561033407778567, -0.4475453752384625, 0.19264672109647263, 0.19051806767553253, 0.136848462563718, 0.49414385509512454, -0.07044441445743935, 0.4085628590427661, -0.0848740849124295, 0.05931399212457415, 0.7405561252305347, 0.443234222807607, 0.11279960015059737, 0.03232063029866543, 0.3923299089069048, -0.11875962944468607, -0.1884385003490426, -0.3830596285532318, -0.4051566774405431, -0.35993741522025585, 0.4759394027019136, 0.13628704091825913, 0.1822367990856356, -0.2889059947621622, -0.8224122541034248, -0.7872833773338312, -0.9934303045774572, 0.13396702970847882, 0.1779482636176492, 0.22185242237844566, 0.03406911916623003, -0.1643846443320819, -1.1222377961121652, -1.3687698111941609, -1.6150020404911003, -0.5622651055759056, -0.5760276046529119, 0.2594557399861934, -0.6757500627083461, -0.5534916795828488, -1.2047878399463492, -1.60263467776795, 0.0031641535643375726, -0.012009838616216566, -0.006908190076068752, 0.002272812966128515, -0.015674904612103524, -0.02527237664461785, -0.026120178745462134, -0.026930428793267312, -0.4255795578896292, -0.8607234425478671, -0.9366093096782208, -0.12941370372160643, -0.9650045403328763, 0.30672456566467954, -0.10027982389890647, -0.581551564529581, -0.37803688561578996, -0.5054338808724999, -0.5045463366702764, -0.6244063454778469, -0.2713339926718942, 0.15472314205298537, -0.12316947201828944, -0.7929891758570666, 0.2251651159772506, -0.090583335446856, -0.031186516553940787, -0.1758796184755848, -0.07758955623631254, -0.03225152425213686, 0.33643323045694296, -0.5715254021738193, 0.4179845326207586, -0.05871556282249153, 0.7202467853177604, 0.16549298020755893, 0.30007722610626836, 0.6036709276861915, -0.1889642596786931, -0.30100786886223174, 0.29612902464726837, 0.4062054346257179, 0.4228921954248852, 0.7374671669109213, 0.1847450252482283, 1.1832553216751416, -0.3896827753328148, -0.8831241361251467, 3.483632637364068, -0.21310851496394032, 1.767684893736051, 0.8424519091429975, -1.7617423427138876, -0.25965466296573814, -1.7817921484340609, -2.2277864480692933, -0.019213638013807054, -0.027423299807199, -0.03073882243230232, 0.007969910495883938, -0.006169637629843124, -0.026577025615478755, -0.024505119148851003, -0.005218647363516467, -0.8806733561947145, -1.3685721068833023, -2.130859808941242, -1.5467040797439024, -0.8256889708310727, -0.7322241108596876, -1.911770789054511, 0.8602944449475189, -2.190791142830212, -1.9494753452391231, -1.4669796765109564, -2.1580201254359213, -1.6841186667770358, -0.9293632624971014, -0.7513626845898436, -1.467564358802165, -2.4454952919451847, -2.478272160621887, -2.2550614789762022, -1.4781067081405868, -2.0386649176988585, -1.9738146562998504, -1.8905174540553744, -0.9111847034952752, -1.4440166451209748, -1.529557550757808, -1.698719969431701, -1.8035978676585942, -2.0708530967300094, -2.195672729045301, -1.7569197818455895, -1.5276118526492568, -1.3199595068196512, -2.0396127780275126, -1.4962447159389718, -1.7434097105148036, -2.1445007288905105, -1.2240980231443368, -2.005363113704992, -0.5534921109988785, -0.8020110253940341, -1.5375150421482842, -1.4850983541145224, -1.9051333689318148, -2.1612427983731632, -1.1616614455468304, -2.6596677491547434, -2.216179863307392, -0.5554873582031339, -0.61401329909809, -1.3957486455447852, -1.7512405614167532, -1.154026272013077, -0.9559296726914883, -1.6404530519518248, 1.3307807447637832, -2.6887581529466456, -2.5537919500585624, -1.688742320377753, -0.4493387387217041, -2.281308110252693, -2.316856078022279, -1.8346601403178555, -1.973920795618742, -0.04936543011150352, -2.6401424396517803, -1.7270998507660074, -1.9575371027931783, -1.092298487268962, -1.6335237518986365, -0.697764129132357, -1.6482208215334113, -1.816384828002355, -1.9584250491537318, -2.1468671939714277, -2.2841010012770755, -2.261193172472154, -0.7580971037626527, -1.4774197721879534, 0.13672874556708167, -2.139977354698616, -2.4744345669436485, -2.100288003225815, -2.164858622768937, -1.493930066816602, -1.9035995507676369, -1.485046999611186, -1.0940661365197566, -2.014572126892207, -1.2296345250573244, -2.31666909772878, -1.9670143646298681, -2.5026391210935675, -1.3768077543047537, -1.8945696657120312, -2.5973146442952757, -1.6952501165442186, -1.5729000654063332, -2.1477959427589064, -2.2126125120479645, -2.470951224181036, -2.38008640919253, -2.236735865760005, -2.1107583762785973, -2.3065819954635334, -1.8195093029788523, -2.3148107843695827, -2.028331039319896, -2.595870600929756, -2.889064310357738, -2.821799573336195, -2.5601162365668224, -2.0974714204380507, -2.8233617581836, -1.9205447669185538, -3.1067648223601005, -3.253784507882114, -2.84965884994164, -2.539179457802158, -2.233020419575248, -4.06552645388463, -3.1198231058287678, -3.1978747528361517, -2.804874570560702, -3.2710643108957047, -3.1014571810091285, -3.4634594364775357, -1.9457356226328335, -2.920759048330109, -2.257148859126933, -2.3551376900019414, -2.493402173699262, -2.709335906332424, -2.775911766068073, -1.7803767156603212, -2.7958586212598586, -1.7937222559287058, -2.2242127261054145, -2.14406795116132, -1.8352091130640928, -2.053071633764536, -1.4795920923840362, -1.8025747987121272, -1.186024986657672, -1.9175539015680698, -2.119174172189509, -2.4652952212835544, -2.0373803556523185, -1.817965480158119, -1.8549025033070363, -1.5299404116138944, -1.2763913502509185, -2.164513028275832, -2.26657899114308, -1.9752492288727395, -1.80143634629779, -2.125184439942903, -2.214122316570587, -1.2382687582435183, -1.864917225824032, -1.935816496843416, -1.8841823297633855, -2.010186913578261, -2.064373616236356, -2.3234554057844403, -1.5621488729583954, -1.7129081146271097, -1.6855987046820784, -2.4242727188435804, -1.8471073368014468, -2.42500127169949, -2.3680672547025217, -2.429597809854309, -1.9620547380853448, -1.7462097609588108, -2.535785972456022, -2.610687719758025, -2.1648223669920474, -2.6970315066354136, -2.615251169417247, -2.7705464448872936, -2.8346718363307084, -2.3420880548802123, -2.305953378576643, -2.1752131307433995, -2.41549761414539, -2.874190623349573, -2.9771796641243893, -2.9529488576382725, -2.7490511115565237, -2.6293190304372556, -2.2899686374102184, -1.8378084542765314, -1.2728430615503261, -1.4126886046760228, -3.0074377704435182, -2.947029918489439, -2.1797125100606722, -0.7105500312857879, -2.256125634503475, -1.8960232764008829, -2.1062776888449335, -1.9183326962610951, -2.4669255274810795, -2.6183776982156393, -2.26491246535985, -0.7159380716510021, -0.17236673137820405, -1.9912901550282165, -2.63449686886981, -2.5867558289824193, -1.9142567747965433, -2.5953510154691326, -2.9339534559687874, -2.072078724905927, -0.9785448906420473, -2.306788772224837, -1.9124781230291812, -2.9221201485703197, -2.98217084929627, -4.116648888889484, -4.236820783264399, -3.0319999874051224, -4.731459995277857, -1.9774912384632934, -2.751079908598555, -4.110722245380841, -5.902557851960665, -6.0607993119419845, -6.783907328997875, -6.954528227979464, -8.54334648080543, -4.178612577601484, -6.443086336642386, -5.434011492272115, -5.306474186573221, -7.859616178626297, -8.946913902192263, -6.619790709735585, -8.59317233897886, -6.636871709344679, -6.394495758643113, -5.514037434064424, -8.0823356477354, -9.44108319477654, -7.516024344709149, -4.828878175045285, -8.683191845671455, -6.6046925605085915, -6.017970261261648, -7.466496871665372, -8.319015216315009, -8.93201977934609, -6.747725762492027, -5.912399365526131, -8.017764539300897, -0.5482255201513928, -0.1264555175265083, -0.35028061367002633, -0.4593609676634534, -0.005707302102168323, -0.22089617967879976, -0.38907682942488747, 0.29913672723507345, 0.1403625051223494, -0.8174065144754576, 0.3611023526592186, -0.27993057447137526, -0.1970255875083131, -0.3482490651264383, -0.3446780577565841, -0.14030469922967906, -0.8314966405886873, -0.42536632888511466, -0.30221900301407434, -0.20260416306702272, -0.3505288980195708, -0.6982797712609816, -0.6808320590352782, -0.3248081534188339, 0.3714354773856843, -0.5051138534832246, -0.6910764190188159, -0.6567099614554684, -0.7772925722204536, -0.9628075583029836, -0.3415719798062078, -0.5674479412515183, -0.10748882669236713, -2.140917183561021, -0.9435343347045635, -1.4780350098123252, -1.6301963928191159, -1.5642377565604053, -0.7927260428391981, -0.6133903444736858, -3.979150733414564, -0.055925555732416796, -1.28943172833254, -1.3695286760323147, -2.601305954616051, -1.7940819948909714, -2.708969071268607, -1.2143483907241779, 1.5977689274024374, -1.3681101539173124, -0.6804501208384186, -2.4175393853926135, -1.8691477378459138, -1.5914196806782743, -0.8400659000022297, -0.135292863853659, 2.5187962572427156, 0.7095326857189106, -1.5647069748401012, -3.3800872804270536, -0.5977176309108759, 1.4859394754239443, 1.0221539481952968, -0.12316164661070339 ],
				[ -0.03344722515467558, -0.030076649648476738, 0.034126437090901386, -0.013550934326822982, -0.007767353388075488, -0.01383802788736067, 0.019641670510544426, -0.021949086664316348, -4.91214469285087, 2.8893835778598778, -2.3836623482681505, 3.371058941475753, -4.5710330422295415, 1.1000103746964327, 1.2778070283283636, -3.8903518215710964, 1.00128508314157, 2.9458829238691413, 2.3605762140574336, -2.7076427373509473, 2.3371642029532995, -1.3197524394896563, -0.5906271983006428, -2.575737315058844, 0.41589140497583965, 1.567356925742924, 2.199074541998091, -0.2408835396772852, 0.7462763323571919, -6.019988115703462, 0.2992052674402241, -3.2286610913893297, -0.9835112581533634, 0.551905287556385, -0.06236902303626061, 0.9836942250338486, 0.03910015597645364, -0.011366266582377289, -1.8852479165867917, -0.3322491554262989, -0.6559622371344656, 0.5018296589272369, -0.4555634383533162, 2.053506871463651, -1.0496562105972205, 1.0994012688151582, -1.398375007045478, -1.5741650910900817, -1.0518875467229563, 0.47830508138866545, 0.9368300676281078, 1.2766385224056376, -0.5311980831709813, 0.03266327756793311, 0.29187730714415283, -0.9046672003506436, -0.024186927599193643, -0.015593736370242906, -0.019286229421949883, 0.024554299219558644, 0.002811824099587892, 0.0036608204876546783, 0.02594435019012941, 0.019928318653208682, -2.4108869111928803, 0.7149999380088327, -1.5656657391795923, 0.235943528735992, -1.2474396099994365, 3.046991804327724, -2.830202962850661, -0.712604703308444, -2.6206127597613667, -2.618076791053661, -1.8235641211480142, -1.384380462005117, 0.22932334974865354, -3.414732671725276, -1.1764511516338523, -6.206247885673874, -3.1298287857542686, 0.6162822629526266, -0.6005742900475085, -2.2848466059974717, -1.6122982910161952, -2.4770446980350713, 2.9288396391822134, 0.6205698997000864, -1.8803082109640465, -1.1567532120095052, -1.7397785286258263, 0.3963605532250301, -1.631695935729246, -1.790519602997632, -0.1428604897111878, -0.30503855434108934, -1.0412106514300634, -1.5700995905806876, -2.616988606584941, -1.8677312118230145, 0.15869750784672762, -0.4404987561458471, -0.8886201620158958, -1.7732083848594264, -0.3971985728008659, -1.2635022519289443, 1.5869602374150407, -1.4676798636460526, 0.9119218061236717, -2.9170030360843, 1.5299034704619827, -2.3708034427499918, -0.5024068123393777, -2.7401011710922227, -1.078226094810019, -1.4271928512020766, -0.7770131403343693, 0.5123697128913018, -2.1800654756640316, -0.46866118216638475, -0.7007630553816137, -0.9952097715720845, -3.9256890338952743, -1.2731042468989164, -6.020299729698379, -1.33083522130904, -4.167852425654925, 1.9924853991113893, 2.0508726119111547, -0.7351388245447947, -4.038470211010707, -0.16802977886877835, -1.2402811224149806, 0.5444044293298954, -3.5396746711040024, -0.5632713007215697, -2.9113707242698688, 0.26945258093749214, -1.993501940760632, -1.3921909266470889, 0.17500663815865683, -3.1840416036099732, 0.9441807594859424, 1.4102969674171129, 0.6362825865096581, 0.5482136746742587, -0.27887789674144803, -1.3765462434239926, -3.5300057481059914, -0.5461662190203206, -0.5812094235692686, 0.5045912555963498, -0.9555517077798716, -1.1484012863384063, -1.316997909600209, -0.1470192914685884, -1.2303319056366, -0.9695944126526551, -0.4587373518535563, 0.6061476369053759, -1.371170956267963, 0.19197794918516795, -1.0220242790245537, 0.07904952915620002, 0.1205647231269875, -1.2003622779460679, -1.674123809663077, -0.2530567692042621, -0.17140407570836885, -0.068025655865618, 0.46130229543651435, -0.560135528398315, 0.20814013227481037, -1.3300751851394286, -0.9100476810605483, -0.9329904606803354, -1.4475748434817555, -0.13278878109950548, -0.14197062369983018, -0.29543996029638386, 0.3080854964938221, -2.18219962424931, 0.6326562045347597, -2.9240110218988375, -1.2298582861715872, -0.13521341808496098, -1.333822244238861, -0.45863561237313727, 1.3577266231954424, -0.018819729498709647, -2.5533080304308235, -1.7940353365658064, -2.1745497296498795, -1.6643653137624925, -1.570260898061542, 0.006416994725897265, -0.3139310451109769, -2.1499118774769634, 0.1269229147977879, -0.15273457230818088, 0.7018739031940312, -0.1064447463843498, -0.6990297363485869, -0.5112260853526501, -1.7212377785763016, -2.019627363613995, 0.018059992948086072, 0.6041539540538092, -0.1989812718356577, -1.2086759419678865, -0.37350541623612576, -0.7565328666397283, 0.4327812837336182, -2.53494300659583, 0.5968955266864955, -0.02055625581569999, -0.637638688115965, -3.367587397821255, -1.1467376054422092, -2.6452445859881837, 0.432191959653305, -0.8404047123505038, -0.9673961383863515, -1.067926521318897, 0.27825697768171054, 0.5401941302021878, -0.22578349047966917, -1.3180272621304046, 0.03930099308309037, -0.8203055513736466, -0.3362480607239905, -0.39657821853844355, -1.1743286768894, 0.29633444180558066, 0.30831928350655863, 0.3395418413085977, -0.9930096490688649, -0.8419842573287867, -0.38803810458246557, -0.33211538279863384, 1.0973961731366506, 0.41294573042085136, 0.024068036497176194, -0.6458964986310702, -0.733913503998524, -0.6107007123121945, 0.8482217518789248, 0.6284112341140201, -0.2996402786803013, -0.7637820629096399, -0.9184665532258627, -0.18501358661148393, -0.38494245795393056, -0.42135144342280006, -1.3119520271215594, -1.6881903536362395, -1.1086630698404725, -2.2464799440015413, -0.9996872823687202, 0.19579569985091413, -0.2295094105128003, -4.036073656175802, -3.025120940248788, -3.550650731806772, -4.86099652572888, -0.5755102678458619, -1.0489062146118087, -1.9469316052064616, 0.133686219075295, 2.3706015434723384, -1.873058302741945, -1.4837747477531231, 0.15724292139642362, 0.1689113452958661, 0.8388970824467832, 0.136849369029276, -0.5599061635275481, -1.7982937163293689, 2.3889451958071604, -0.2659634921615892, -1.8757344012599566, -2.059216004696272, -1.2165084831936983, -2.1844391328403785, -0.5970455142977633, -1.1317094386970878, -0.17540717081556448, -0.585938485360948, -2.6151016335690627, -0.47547645751324064, -2.836171103369288, -1.4181303490470816, -3.8222022107655182, 0.4578672485417951, -1.9123308506198637, 1.0763458610643997, -0.4744432414334009, -0.31814305388091385, -1.0739519112289193, -1.4436150956816913, -1.3909110817155788, -1.503108101037594, -2.461095869071169, -1.6755909657038588, -2.118362537735889, -0.5721924385229381, -0.5527312798463098, -0.5310028393395255, -1.5181757007865917, -2.1475976999996798, -3.739586214640516, -2.1014902639607955, -0.7578419234910363, -1.8844473545269298, -1.37458604301234, -0.42676473397197634, -1.5795189365637823, -1.1407408700788382, -3.577227734579379, -2.6834438751881704, -0.35516637088371955, 0.09429412629598266, -0.9410588342658988, -2.1467710358401115, -1.311962335781158, -1.614807562624535, -3.4789357101767773, -1.2169028753318984, -3.021807064719488, -0.6187097054391563, -5.016969545870577, -4.246510592984687, -1.5190576337538904, -3.3435429067906983, 0.34909775186686554, -4.123430056305331, 0.970183348100126, -3.4998442694819523, -0.9530632999850704, -5.677029442296776, -1.884987304248554, -4.867928541234616, 0.17206347542522615, -0.817566316425986, -3.0300915086047926, -0.23831707377178352, -3.925218110272427, -1.662772665452367, -1.9924312899728986, -0.41538152464994443, -1.554319802534817, 0.10782648774746036, 1.216155109818893, -3.1520554253369544, -3.598261810502245, -0.0657511595739698, -0.7059212298190499, -0.4377040932731783, -1.018439972739531, 0.7076873334799939, -2.4986949167714214, -2.2686904366438703, -0.5629170430031206, -0.9867703221878411, -0.2818135106170019, -0.24116872737836303, -0.4792750611557416, 0.24366496226870793, -0.8563164823471301, -1.674249690579076, -1.822301131326883, -1.4877540741113846, -1.149839641186648, -1.3048866641984596, -1.1780214309626493, -0.29276505799489266, -1.739540398001503, -1.1942604614556844, 0.27084412652487766, -1.305486648078128, -0.4616612120953754, -0.5977581935545757, 0.40755842651865287, -1.8116693622307005, -0.024045930269598885, -0.008477315929091272, -0.022900730615917603, 0.028699210302020266, 0.034429170533372945, 0.022579123325847855, -0.022039857717575974, -0.014431125426249084, 0.8066413602008027, 0.6510116361547743, -0.42064980345196273, 2.37317500712461, 0.05558892657327, 1.45698709377024, 0.15820231862879452, 0.7796762745956588, 2.2332271348358272, 0.353290324681036, 1.7802030823421795, 0.4791210028414116, 1.6048933697564967, -0.42904657664154955, 2.1813856125832274, -0.6067726032313548, 1.3205221601584236, 2.9559031897498698, 0.4151917925065169, 2.0365859350425084, -0.24724771242676358, 2.213384123984455, 1.7913287002878746, 0.30981209340336835, 2.102524353229021, 1.7980595553796177, 1.6446403481330776, -2.618214656000522, 1.375864193788561, 1.2643802158821988, -0.04960578137208317, 0.5727047356743916, 1.7324480067285113, 1.1300791499942193, 1.477422782881329, 0.4707721612538502, -0.03719357273347352, 2.606536245967775, -0.8534003430381013, 1.0181137558349609, 2.45482105028538, 0.9964019156957233, 0.49207286412486545, -1.5074353254789035, 1.0918721140056715, -2.098389345998119, -1.754162696869783, 1.5647482732357236, 0.01538338894336284, 0.012888458508920848, -0.024952594980656544, 0.004224254227365675, -0.01199680069523859, -0.027817611678678633, -0.029009853335413997, -0.035536541730800744, 0.22244941004024885, 1.5762435347502035, 2.455891307329139, 2.6354640376213765, 1.2190309821785696, 2.6979600702053577, -1.8126084296511666, -0.09281725304592314, -2.7124735311291426, 2.4968119269247366, 3.0453450884432316, 0.26577126713590216, 1.5901879450897978, -2.0282791230749746, 2.6643023503628864, 1.0974364073620253, 1.4480992145009948, 1.1093451731595243, 1.3090903482739367, 0.9368216454849391, 1.6488661027054323, 1.1931722372431464, 1.6195994481989897, 0.7189661504701494, -0.40841135565535824, 2.0190934979168853, -1.1044081293011416, 2.580876562078231, 0.3249637070498185, -0.17000920657173835, 1.9435215023866124, 1.5769003191809998, 2.51424325529793, 0.9333895612482229, 1.3577858354936703, 2.6677014085818054, -0.33227540770790714, 1.0098855251417302, -1.1623545719111494, 3.6567928436924775, 1.746767767240106, 2.0852552149347754, 1.0722057539131513, 1.8681536343687493, 0.03615405017997164, 1.9574612590555387, 0.5057815166683526, 0.290683521661433, 1.5577731739081249, 0.04781132346961264, 2.6971218796626104, 1.3035605499391525, 0.7289331690413894, 1.3137921896674618, -1.3419787739981948, 2.1063839244617095, -2.7799897128906466, 2.569613399913142, 2.4572001847020806, -5.03060984739014, 2.9044508916807383, -0.5957952765476706, 3.211638824410853, 0.820606178070154, -0.43973456606480765, 2.809312474204413, -2.922516389759838, 3.5160829983441557, -2.2335294451104906, 2.283131081770267, -0.6387662793054075, -0.22986759049581493, 3.737978504944536, -3.7831554826969023, 2.2292874426610325, -2.0223210735884267, 4.477246337150204, -1.4848067650119643, 2.7210824905134205, -1.4851228932868583, -2.7910561879322073, 3.3387155948142992, -4.419399376459323, 2.6889508585723445, -2.2329432747882256, 2.8732548115451877, -0.981867522904547, 1.3296750406147215, 4.5005703777341735, -1.9054329800433163, 1.7457381905978195, -1.2764851074260664, 1.0911716700492762, -2.94724494221456, 1.761234093962754, -3.2640031584314233, -1.6074108309326198, 3.714401318083725, -1.695019026450047, 2.5609403423206407, -2.63423132407852, 2.3365565263668873, -2.308057851291972, 2.367919639084076, 2.7186819591391425, -4.578221575496196, 2.999064282386055, -3.7650649395118925, 1.8691662522658634, -5.324333320071363, 1.6365527804615376, -2.597537202893387, -1.355085969366124, 0.6589868838975634, -2.4622270842431178, -1.555735679892252, -5.297991788350828, 0.05946718262180878, -4.8558797525472635, 2.3367554362347405, 0.4374965833135384, -4.242456954204672, 1.942308570265376, -4.220251890238655, 2.9502373736318948, -7.619043948671519, 1.9603457579820933, -3.4223202276637683, 0.000010922208067909488, 0.63031248357691, 0.7974828961857251, 0.3063876224854919, 0.15594429238906443, 0.41028996991468275, 0.437063551557374, 1.9694165393060872, 0.6487632705708221, 1.0704287165240927, 1.2284844695248223, -0.3010777851271997, 0.6111838576016543, 0.7385883050445516, 1.337590125549208, -0.3042040776474412, 1.3567639772889062, 1.998807530665584, 1.3130715755702165, 0.8210359213821614, 0.5936075961750451, 0.9460069218515071, 1.7994143271092162, 1.3635299858992653, 1.2820528730970164, 1.2928636881127098, 0.8531928492783283, 1.7793570251739124, 1.187439990251703, 1.0139845175989233, 0.902046712391197, 0.3228978879940262, 1.69337812982819, 1.4480679694667944, 1.2825256520632586, 0.1633900195463852, 0.38402846474429775, 1.311567015627749, 2.077549873300282, 0.5062390835235698, 1.6893462844888734, 2.218746570942316, 1.9890381333976868, 2.4805928498892893, 1.1701802882376606, 0.46230002953085064, -0.5028514562509443, 1.9508837829366779, 1.1967003251277153, 1.2381958600327407, 0.31292287611585395, 1.1142625596653526, 0.6485282703836253, -0.8936159896890541, -0.04907073226696606, 1.0130520225655044, -0.5607342428523933, 1.2362757010886638, 0.5637646381882583, 1.2291094504152968, 1.0901916592173801, 1.3502493752978446, 1.0767553801705938, 1.2775596905836162, 1.3445247634171493, 2.657309846999215, 0.7081464944242635, 0.8237627170943034, 0.07872969506080228, -0.31903434418696175, 1.4555031738995177, 1.4989236115441442, 0.3970923846280336, -0.38893430457857214, 1.1321570218577532, 1.176432988441092, 0.9650007657170463, 0.6610377119863564, 1.733070632317384, 2.106387541439418, 0.4961016406215521, 1.963037956232419, 0.5036239150958005, 1.9068347131755827, 1.3415683065129878, 0.46690459990815314, 0.3518507237321403, -0.4736634071621101, 0.7506200716818966, 2.0553581405868746, 1.2410106732500483, 0.9604161387183261, 0.4193147683701689, 0.4529145329156223, 1.8901579360258032, 0.20997043033401455, -0.12147742358117436, 0.19824965607285858, 1.0109385642543884, 1.1071286225712422, 1.5832871024195398, 0.57440774394922, -0.4036852867814455, -0.30682696807945764, -0.4171868854528718, -2.1283000990144507, 0.25771172123404, 1.6056749537987471, -1.8666329533945822, -5.152268475448047, -0.5058168463667819, 0.1640234780507439, -0.37303961183970696, -0.36410854703102336, 0.5563876000176445, 3.017461809493086, 0.12646217884004854, -0.14719412309377264, 0.08500323167632866, 2.239351803652055, 0.2254945436080822, -1.0886521109603458, 1.6235646485440085, -0.05110066592448598, 4.60409034593519, 2.199527433940199, 0.5250456625806319, 0.4063698638314884, -2.214039201365498, -3.6650490275937067, -0.3365702028583992, -4.266854515063648, -1.1319188980978072, -1.0936872403958464, -1.7620711421958686, -2.883495168177694, -3.5586113713928618, -0.8607405454071867, 1.2458266635679571, 0.39669123062577555, 0.598676573188906, 0.2368116557823156, -1.082088613472372, -1.2510919626364398, 1.1813119950321427, 0.5537294897888813, 1.9290305938743169, 0.1408129230269562, -0.27806021257869545, -0.5953915616308583, -0.4355382188189288, -2.4615795613224702, 1.428586435969366, 0.4840774923887837, 1.2915968250887127, 2.969468533130506, -1.7136847239235256, 0.711980667861301, -2.0021481860046437, -2.2777739385872957, 2.6866555017022495, -0.6678240138961772, 2.574498852428124, 0.9218993888801568, 2.536813178880035, -0.6998945803325013, -1.007608098111659, -0.9705477554579616, 2.645797049044342, 3.889448488225239, 2.6096985434020836, 1.7860827331582347, -3.1785359833340476, 0.012185149300489542, -1.615028434901337, -1.3795841290797364, 1.1393885645079214, 3.499475009225059, 2.847308459332541, 1.151676764937715, 2.0882642699877407, -1.7911622650560144, 0.38444573750682, 0.2778369678328686, -5.508435374583836, -1.6150269639532486, 1.7647838091469916, 0.031182232628564836, 1.9800782882522512, 3.138241773250093, -1.6448634370660604, -1.0870323289065489 ],
				[ -0.005202750422866897, -0.019290386778520657, -0.0332534651186679, -0.003381769969606636, 0.004039825088532236, 0.025251231116463636, -0.017545705069136303, 0.0017407175569409696, -3.746508624323834, -5.700478294323616, -6.674879961698002, -1.2603906905174862, -1.6036275516625902, -0.17153262830788668, 0.9248615577709385, 6.19286621318087, -3.289924876230125, -3.6680776428093544, -2.342304491010472, -1.1661275382219805, -0.14595507750248726, 0.4665688060970987, 2.879400804033248, 2.2076576125185503, -2.513538374467708, -2.484676328437981, -0.5092808295814968, 1.3000080531964837, 1.4182028211124635, 1.0210493408881558, 1.9512966033350607, 2.0358962556362274, -2.4390170875778137, -3.778924493872104, -1.0841402461494518, -1.5098337496571026, 1.2401918812664152, 0.19249737898487085, 1.8365989713033992, 1.3433756145086282, -3.1804989063957643, -3.321868389172781, -3.3723594286436276, 0.37521400820658535, -0.9135899812059874, 0.6391574201839493, 0.1441709208400237, 0.6616111894552972, -2.4512248261882834, -3.4295512915183997, -2.186429207277409, -0.65156220385994, -2.2823101983528042, 0.1300174381586907, 1.3825392083443262, 1.5854808106739975, 0.03269500163988704, -0.03185052995997966, -0.005969574842582032, 0.00045188516999362114, -0.017651904955153782, 0.0343709520418491, -0.013375438631613792, -0.009998904716013932, -1.385193430008779, -2.119401041726136, 1.2220082299679582, -2.157636899417412, -2.2114412766030993, -2.783489110645362, -5.481596843216075, -4.207403444241192, -0.5312039407344258, -0.9993183913088644, -0.21114112006954022, -0.535844094371572, -0.8320976569044207, -0.32881928131192273, -1.5320186675869845, -4.386466054406992, -1.5038364916074152, -0.2260303950309141, -0.2634939630745117, -1.4042901879240461, -0.7602583000838384, -1.4368200978263637, -0.5313695796704971, -2.6484318498492128, -0.3637893939997068, -0.3006564625878293, 1.2962446240845835, -1.0718173343075696, -0.30646346173902755, -1.89263002416673, -1.4137886299431297, 1.6305426077580796, 0.24758810456637065, 0.23642528055342765, -1.323811065106038, 0.08390669635095752, -1.0560638694246223, -0.009340478485927109, -1.052890778088646, -0.4271011238744239, -1.0765914762686175, -0.1998228188580341, -0.4952438980282114, -0.13231230681515405, -0.12427363114935427, -0.5509606618396088, -0.6768064734420897, 2.795072113189014, -0.6178087511243989, -0.5523488116850317, -0.806785890110989, -0.8717774564674222, -0.15105068653218195, 0.44834960523999906, 1.3875272806086687, -0.6715130156596624, 1.4454086672193553, 0.9038891394366838, 2.3596476442791645, 1.1622522907350619, -0.5767608212272095, 0.2730265761852855, 1.9157475215855546, 2.587523440907663, -1.3877753080212134, -1.27605274941864, -1.3604491280675723, -2.2398807857587815, -2.275905228455331, -0.8797488704294834, -2.8431004373070223, -4.579203526788231, -1.188794857131154, -1.7137740919174547, -2.0082885034825284, -3.2595404523515037, -0.938282374395306, -4.986155576894647, -6.4830093080379765, -3.4233281347862397, 0.639339628424377, 0.7840598162779071, -0.4872750303131884, -1.8107284846919063, -3.954555767859453, -4.39199087729338, -2.696640452321922, -1.2146816302465244, -1.4718131296750103, -0.5693587425528552, -0.19786247976642685, -0.9169518377422896, -2.207377535688433, -2.309976642382496, -0.8543361260511557, -0.34716484085884375, -0.5962717580609367, -1.7931056088565918, -1.2621326005426343, -0.6930330635945545, -0.5298770790157943, -0.550096203717481, -0.38569678457348705, -0.2806575133473059, -1.5658287665251853, -2.407650499996093, -2.7057321933173952, -0.41173060071360135, -1.9302997998662714, -0.16385447086628388, 0.4457874487234898, 1.531171809366361, -2.4904077742421755, -3.935303972469016, -1.4696913316872229, -1.6108767075489274, -0.4594168905585232, 0.4194765970692038, 0.5382052888373067, 3.2606461703846064, -2.043708598923854, -0.9081208822900159, -2.2949891744267643, -0.71113213003744, 0.5089474423355764, 1.175540292871168, -0.1099387825336601, 0.2831835861740293, -2.2494189177316324, -1.5121700264860127, -2.648921258223225, -2.4811155561964253, -3.4293864252428485, -2.334451266071168, -1.1583986893013807, -1.5017037517880751, -1.8819562656345528, -0.8185812986151174, -0.9423639618680694, -2.7737383071120485, -0.9182835840623572, -1.6540054370644057, -1.16985279329849, -1.835750060828547, -1.2265432394997609, -2.752075119905363, -1.7778673010913555, -2.36835170873275, -1.3517574140373387, -1.5382073273686743, -1.2073791358663337, -0.07090291898119337, -1.305086458877703, -0.532311730712174, -1.3519894077886612, -0.7332752397018601, -0.5358668517932786, -1.7564086702186517, -0.36467689079552357, -1.0534841018590109, -2.072414189018625, -0.8530532777289577, -1.3177983908226658, -0.8579703801859142, -0.8729068790641688, -0.9088315729279737, -0.700890425073436, -0.5585170853429174, -0.9122706458286415, -0.7892287372580981, -0.6895405578915349, -0.06767788479417794, -0.8658944395064367, -1.0985056392736245, -1.3549017940613715, -0.12052042787393623, -1.1095483396270869, -0.21930118795324885, -0.6669648120833089, 0.561687492949929, -0.7991839916383411, -0.03779298123621525, -0.8438454526532086, -0.8754249686899045, -0.9201407945763777, 0.0009462711866476071, -0.43589583066814336, -0.8524982020564285, -1.5153267212004833, -0.8992959806941777, 0.09884518844403571, 1.1696078418231133, 0.6728777955887448, -0.614886537944457, -2.555925410705703, -1.51005686062012, 0.0344704697861435, -1.536371669292675, -4.24419942283764, -0.11457240328088357, -0.4534036343774185, -1.2649455723738732, -2.3883809914698517, -1.5804163280868124, -1.2914631882401368, -4.303263897004355, 0.8693509975796891, 0.9074074707896556, 0.17865057214980773, -1.5662718147855066, -0.08452736732523976, -0.18540923375873467, -1.3267625553691917, -2.5653233257531007, -3.9004040902720707, -2.1970709091870706, -0.46833949847343037, 0.29680720763873514, 0.2516805963798719, -0.2216470438079278, -0.10266664617645997, -4.294471014515661, -1.5052128382850458, -1.4657448747096338, 0.9656733311583604, -0.5100940501575343, -0.954898405383064, 0.07734018836782865, -1.112187088370305, -1.52946944061168, -0.08020158827436934, 0.35698532145834183, -0.7751700953282195, -0.7798756088989266, 0.5987199077383982, 0.061102898776118, -0.10553620243839004, 0.5755707819500967, -0.2373826952201441, -0.31106924377833994, -0.44120742031953136, -0.020917252813469574, -0.7036140703255935, -0.41009039287435567, -0.3862877740484796, 0.4069499496409453, -0.10934978913703322, -2.9513849990827987, -0.9479247085975736, -1.0352563319538226, 0.27181386704211685, -1.1638922118907633, 0.6542345081079742, 0.4947717670157735, 0.48971065304547295, -0.6236315659943157, 0.6039124222996163, 3.1210942965296113, 2.541848590179095, 0.9106558401940912, 0.4123088258723165, -3.86332030639665, -3.0200419743413556, -0.05721820099998905, 3.174634330171305, 3.4495742702380454, 1.7255849868044977, 0.208895203166969, -1.1521197659322198, -0.007274801040494626, -3.7245708125827806, -1.3974669506164845, 2.5155575652318944, 2.473850999418902, 2.2465968612642513, -1.243073983651216, 0.007755245543527082, -0.16122426071677134, -2.329954838508024, -1.5888143746812067, 1.2906996990890822, 3.8168419551615225, 2.876916850841005, 1.2086955297806576, -0.3237344813600189, 0.2395484104144426, -4.294048952198332, -1.8072703129759207, 3.3109639206378643, 2.611223551689185, 1.3395609672966475, 1.0859643318374925, -0.5777650144372339, -3.3721587426599493, -4.41581455908942, -1.5865003727658902, 2.307808978160064, 1.1615387999664541, 0.7862257743143103, 0.8230793184112419, -2.4816618169463753, -2.7916929372611583, -3.7317488864133974, -4.483796843880732, 2.3044511328121975, 1.7362459742491054, 2.2447104241656475, -0.04956643736050475, -0.9696113999081457, -3.0625525857248173, -2.736086705546617, -2.760106230425629, 4.1315671877064615, 6.086378273551405, 4.523073494879045, 2.9401926127056752, -0.3885514531200608, -1.7222500579879634, -1.9038761652699803, -2.108630440566686, 0.022174845326261572, 0.029398489088448165, 0.01893442219640102, -0.03553062676433951, -0.0014554456757633573, 0.011377770261998835, 0.032524359096151735, 0.016014912637664136, -0.47582975297643487, -1.4525980202026123, -0.7385746488347089, 0.28283339874163915, 0.8745402970483547, 0.6037409049537861, 0.4356042069915744, 0.8971501878494101, -0.026712872007239905, -2.458175709274079, -1.2157224863454592, 0.4625048550473352, 0.6511246630202767, -0.006620912643755587, 1.131307350475119, 1.5157878098695523, 0.3359718256344206, 1.9853947453876284, 0.3328556609004403, -0.38205074660243843, -0.17087306207317893, 0.5434262879174434, 0.8234495225575313, 0.9373603310846792, 1.228625043287121, 1.7410935340578677, 1.5068237369680086, 0.15158729915568003, -0.26440597469020943, -0.11030805538096689, 2.937870860361952, 1.3713109694711194, 1.8938092381400249, 3.3714855583254666, 2.0066802551948535, 1.4091242189189006, 0.4657722282406258, 0.17957327635377918, 0.772283504941514, 2.0682431126896983, 1.435536359461806, -1.0149102609278708, -0.22906964949439165, -0.3387044313596705, -1.5179810899449084, -1.5348834958069477, 0.0625249494363179, -1.2573023010759834, 0.012953125149476209, -0.003949122085489292, 0.02146572174515813, 0.021086973659414525, -0.02006815098556525, -0.0285112104791917, 0.015012370963344977, 0.024396343805148893, 0.7708581577901341, -1.8352748439280187, -1.0530334233266536, -3.1399227197735047, -0.7574769543705385, -0.2845790059600952, -1.8749699082557578, 2.096309136320427, -1.5637746231477088, -1.208681208475092, -1.7787383628755395, -0.19121833682960587, -0.35006814987657575, -0.8265684019853523, -1.804539541116587, 0.06042178178822813, 0.8445810785303516, 0.46288204065655836, -0.000909322047104285, 1.0612211695341873, 0.2515201760032035, -0.3533388406947202, 0.8111385566518866, -2.2415052618704183, 0.4216119146100831, 0.317496245738628, 1.5586619465656653, 0.9379251341839056, 0.7892657439325244, 0.2461636943480692, 0.5773660795083511, -0.33660904695583876, 1.9260095477856158, 1.3348269647179687, 1.1663547879269887, 2.194127100822375, 0.6179038378610611, 0.6899220734363668, 0.2572480986682529, 0.7447394996844962, 0.6403928684941568, 1.0794104213178657, 0.8523058035661352, 2.507673064187471, 0.08465145652585913, 0.17373390203304395, 3.204982304440538, 0.7708770843994477, 1.1485857307894352, 0.1579637967449864, 0.7348122064641667, 2.0669145186543814, 1.4411409486358595, -0.16698680895201048, 0.9625629527331718, 2.511102817474493, 1.0257112025187594, -1.752150296413686, 2.4041836720044945, 0.32135482440892993, 1.6775190149073902, -0.6155208952506243, 5.448283751768772, 0.9751287591053316, -1.8294508385612094, -1.4414530764696887, -1.3378939480089942, -1.6717366817842998, 0.28157166456729094, 0.9364341017538249, 0.3666697054077743, 1.6093819086900731, -0.029882525878592824, -1.8475519699615304, -2.045777156202047, 0.005861135995432136, 1.1622546421288729, -0.8040315395653718, 1.4319079063412128, -1.5948650375819267, -0.4580983955423506, -0.5258300873247574, -1.052317503766903, -0.5218529865519328, 0.8423662940701875, 0.6961855719883885, 0.35782055290354814, 2.1830405682613137, 0.04171242406824462, 0.27210773781703584, 0.7913751089065797, -0.055522005176560266, 1.8633617684397366, 0.6388539035989368, 2.495441878189157, 2.536559510957942, -0.1692901952540616, 0.5059843346942, 0.8573571915720799, 1.1750075701365446, -0.7965798381974013, 0.39428415428157065, 0.6937495420508725, 0.5134119781249706, 0.31560508735953263, -0.7874020761533687, 2.0208736510723564, -0.06971674999141982, -0.5307406920792087, -1.9832194129209624, -2.011020261573135, -1.0082012274095107, -0.34421538480468783, 1.683100530159334, 0.21506537541949053, -0.660670638416345, -2.4258225457578706, -2.6479548171484706, -2.318663596897445, 2.0343944433456556, 4.003490208048537, 0.8231117639483068, -0.7098482271569143, -3.224820889891613, -2.1564633163766183, -1.4190936027597265, -0.5025315708647927, 2.7345459581062896, 2.0774172413589462, 2.9354139359503333, 1.9317355191137113, 1.8773187715194102, 1.5705943649883791, 1.770957245201776, 1.4145464308963192, -0.07302211722716857, 2.6162336478295143, 2.4674781895859472, 1.8852141074584243, 1.9233090617997188, 0.930742229407379, 2.0008769484910416, 0.4641285163541191, -2.9707365567616493, 1.421110260538009, 2.255156962673629, 1.678143592844201, 2.5069295126682194, 1.719229718295744, 1.4704668646851813, 2.516433277602578, -1.6349932158214366, 0.9122175884949332, 2.7601015533127193, 2.1254427888192318, 1.4585860749106885, 1.0419897722685652, 1.9235275483276584, 1.9022611985154168, -1.3882375748286682, 1.287552125544341, 1.6944734152760696, 1.7068684746327893, 1.4597045143919314, 1.7859797150852923, 1.2215947157438782, 1.703769207961086, 1.6414414772025832, 1.331271022058437, 1.4094019801541788, 0.896416571306765, 1.5229997993129702, -0.03629387310986288, -0.22658095729840882, -0.3517821180433472, 2.19808489724785, 0.8607267554181198, 0.8438921232022912, 0.45827377340027126, -0.5678498501121828, 1.3684074680063878, 0.0518070224003888, 1.0132634406112626, 2.334587752637867, -0.029041335197529133, 0.6861133653959962, 0.5241211472244288, 1.2368899537820561, 0.9589883354215438, 2.5751520258371365, 1.8194956340841757, 1.0199230955229184, 1.9097632502761879, 2.249829395033954, 1.417401270051573, 0.6178255296712716, 1.5754373174539706, 2.1376005739006216, 1.4241739352047615, -3.310807153985927, 3.4639832637977666, 1.7354064583507094, 0.6865236652061969, 0.5139564845246233, 1.0371774135265812, 0.9573090481145156, 2.026764434574792, -4.11272903265302, 1.4849499576183385, 2.2850981238497803, 1.3282258338159185, 0.8924369866418193, 1.4243886220188273, 1.7535085717428553, 1.765234240086081, 1.0548493873414397, 2.497970915583254, 3.06613378841796, 2.0446874162937343, 1.764108427087822, 2.672624651073912, 1.3624112480009396, 1.7319775505366168, 1.284396296441891, 0.4946399765617135, 2.074321525054217, 3.1176936658749925, 0.8932881827767649, 1.3012261184537997, 0.21746562421484503, -1.6145019355274541, -1.1432184241151742, 1.8003328922581279, 1.1903513341152372, 1.9139087127914207, 2.47146329938328, -1.62969976962891, 0.5665169424465005, 0.3897523408924299, -0.6183703773276902, 1.7725908885131563, 1.87285517462856, 1.8841296817577953, 0.8338043359226535, -0.011075696001876738, -1.2101613595762457, -1.277350431388363, 2.090708523744326, 0.05656870086659113, 1.5720843204053385, -1.4739577866473759, 0.3404568018616583, 1.1452104133894305, -1.0957023501092196, -0.06715821321155636, -1.526315000055233, -0.038169775199713644, -3.4796768728011274, -1.6915923875934937, -2.511144629850786, -1.5377482034526935, -0.6269183026913652, 1.2480807473916617, 2.135152215142154, -2.5909273308191394, -2.0399473067271385, -1.8258924231379248, -2.322453915046741, -2.1548046883431775, -1.7168176486496585, -0.24254935348607012, 0.6354849340565314, -3.180764718567947, -3.1674538091859272, -1.003577785534768, -0.7506648864011604, -0.7397955537611546, -1.5615147181659574, -0.1872468943377848, -0.477500955582979, -3.6318519474797037, -4.163350692779176, -2.8163028371439265, -0.5821975447801716, -0.33565168724131406, -0.2318522048766439, 0.34949569875608383, 1.196643210580885, -5.382366206024894, -5.914712500613674, -2.6631557055883177, -0.07355275177484656, -0.43752024429795033, 0.8456503961316891, 1.6785099819612885, 1.6512941310487106, -6.651061315290397, -6.23348147417274, -5.638704779362797, -2.4174215539501196, -2.2463031397007573, 0.8730091119540933, 2.6460178743715854, 2.6497328801897195, -5.561387520566892, -3.666768535814771, -3.0677009784777556, -3.056573058762282, -2.84897407904372, 2.273543457826597, 3.2179386931842915, 2.6839130997386875, -3.342449435474379, -4.137606090733625, -3.4713637823570553, 0.4349060381696699, -0.7186253475898516, 1.0231096424485158, 1.3917656767855984, -1.2079859601280547 ],
				[ 0.010863192119422119, 0.034731320313305815, -0.0008659944933467336, 0.0017929351095516614, 0.024508687465561077, -0.018646396568391538, 0.012609984617276724, 0.026786030162100356, 0.6260544984251776, -1.2483796795757789, -0.0687462265811864, 1.5311181928991542, -1.5710545463679497, 0.8925081722349141, 2.040669373003425, 5.06058844194545, 2.468776559151516, 0.47286108889075656, 0.5659769843956423, 1.181678808775061, 2.130838928731171, -1.171918125869885, 1.274693245472754, 1.8219167426284386, 0.4846414539983588, 0.6535232423279993, -0.6751610051315835, -0.7611432269913828, 1.661316445326602, 0.4072974663488995, -0.6928738411822463, -1.1117800102895097, 0.025401666700759665, -0.10897983323918808, 0.6305668946370375, 2.0911216594127806, 0.04489710115391456, 0.7393947463751894, -1.1911639269429106, -0.5324694076536703, 0.3296051124182779, -0.0008210812696574088, 2.746757058445801, 1.5342059961544885, 1.5795827798549749, -1.9044671103676147, 0.5788013573717667, -0.3437517970652067, 0.004467978778981493, 0.4498950313983489, 1.449168763228101, 1.3558987583999422, 0.9200561757409309, -0.6768067825810717, -1.3035857119130065, -1.7567272570856622, -0.016888464128812626, -0.008064198447045194, 0.02441877503699451, 0.035382115499266155, -0.013276747167049963, 0.004782809353935878, -0.01141194659554104, -0.004684397800101891, 1.898154415101932, 0.058729122124503645, -0.16284202157424216, 0.40316544844566465, -0.18116323410280435, 1.9433264129578438, -3.782939958073184, -1.7321396832580094, -1.5010879657214884, 0.8758585848114777, 2.1680318408533616, -0.7010188552849567, 0.7571980255314548, -1.3766276548688519, -1.385752902161541, -3.334136967522367, 3.284617928633868, 1.6676709485265668, 0.5741938919336302, 0.07081224821211282, -1.7385953316621607, -5.306858117955025, 2.2038073349974328, -0.5615953031375689, 3.602436907747875, -0.6485838574337711, 0.33211142067670185, -0.5099973027277604, 0.311916712184014, -2.035251255548528, -0.22940527087142068, -0.1538003611284249, 2.16301736552695, -0.3315696379540221, 0.680526193758639, 1.147736820730388, 0.5487040092495872, -1.9580827337383253, -0.7616014681519544, -0.5494048917724302, 1.191587739308284, 2.287084576322908, 0.8546348036329325, 0.925821941529306, -0.4777251020375436, -0.7026098000842461, 0.8301050842910396, -1.4906002205296784, 1.2766685327066578, 1.982681411324032, 0.9739062952606045, 0.9477052275815785, 0.10131382544080235, -0.39882842944133756, -0.8954415577998586, -0.2884067873882573, 1.3766070316768233, 1.71147204619294, 1.6038776658617795, 1.364258706233573, -0.8501144534833458, 0.9279780025338294, -3.393081407348197, 1.2617387645842355, -0.12246080382216466, -2.0629125686546534, -1.5444211302170965, -0.05848930038056512, 0.7088785068825274, 4.328868098215306, -1.963511223610069, 0.8329008471336025, -2.51944725904793, -2.6332389029998327, -0.9360639211487709, -3.8935035237507174, -0.46618421133768123, 0.13761100169717605, 4.390206294164459, -1.7451224081221137, -1.5637863553895415, -0.3568302728372858, -1.5337077183993488, -0.33416300382472286, 0.6279866528803165, -0.2017984208291771, 0.049355339449689596, 2.679194470136928, -1.642641774593464, -1.5053162090983403, 0.4475150712465143, -2.673689044891605, -0.44021379916263026, -1.7618130678523367, -0.8340166603314393, 0.21280567342449166, 2.330021499070615, -0.03700064624482503, -0.8542341617583935, 0.7605244742795356, -0.3082275044410886, -0.6534618837196801, 0.5178444703709126, -0.5722037534984638, 1.4604234585279023, -0.4087784427612154, 1.4295181734974585, -0.3548647514441242, -0.7168667561271248, -1.767260173246742, 0.2855441045671013, -1.604853194555946, 0.8283588923389837, 2.267086184973513, -0.7645502530888488, 0.5039861527422603, -0.16030013704473042, -0.2388414134042013, -1.9517774439642677, 0.135015049788267, 0.42560008858933157, 1.632079478902408, 0.7562251042044796, 1.0886405706446214, 0.954873159465066, -1.633459909088407, -0.7168939013941439, -1.9269798826947695, 2.2413654991941168, 0.8035531495176778, 0.01291837357258783, 0.22324365455628742, 0.8436565186511502, -0.9070534220310533, -1.2618436376014919, -0.9619473429821045, 0.9994877928277669, 0.32496504705367263, 0.07517608665832476, 0.3486841885758047, 1.9381595991750813, 2.576210514054891, -1.3928455670301745, 0.9099602355982789, 3.2082023728956646, 1.192448238863101, 0.8762570575011911, 0.47727794752953867, 2.106944764809327, -2.1345197814157375, 0.5149835383506877, -0.3445728968114255, 0.4125969022374697, 1.4483213596865265, 0.3889403750705117, -0.015944873413526607, -1.3532094228818567, -1.2902846760275826, -3.0687472866367793, -1.4138440059272295, 1.0511160643075927, 1.6269043723211063, -0.28812900292333443, 1.3428708919484784, 0.8802792512734146, -2.5706847439449514, -3.082084891592934, -1.5030926392771757, 0.832502263769569, 2.296881070153337, 1.1152613844694668, 1.9315262428948754, 0.1761092099713844, 1.4062108543939191, 0.5109891185721114, -2.5500909757847485, 1.3529938529370382, 2.174209589428163, 0.2969215950273051, 0.9308918483466698, 0.6398298651527147, -0.0556474053236883, 0.029972632407273055, 2.679555892095549, 1.501766271730342, 1.2264550586267744, 0.8257410031466624, 0.7437061136167586, 1.3179709752043631, 0.8086096381221539, -0.7911281714715845, 0.03407636004220207, 2.3781596563679397, 1.3331131208953868, -0.23490414175940483, 0.8048780744346463, 0.5367806879215127, -2.2875729467999855, -3.9539242993927632, -1.3857647524733576, 1.1332035764157669, 0.6855952229790894, 1.4607396081542527, -0.24620142874201922, 2.0517925457511508, -2.49865440734186, -1.5335376989564313, 0.3530864931806389, 1.529121247961472, 3.484940881812939, 0.59111289800148, 2.094949164770523, 2.5424816316620196, -1.4311125716391007, -1.1718752815224682, 0.6067573349280588, 1.06887987786268, 1.0304656034352804, 0.5834029290451399, 0.4935829254838576, -0.37474503157738875, -0.5742443935775549, -2.3383534250477407, -0.35695254280576216, 1.0881869147325516, 0.9684902779544846, 0.4919544425028561, 1.0009077254162884, 1.338261617542684, -1.263846130055934, -0.646981163274979, -0.3853452341723657, 1.8845690185184392, 1.170561294995243, 0.2928766512320879, 1.3077846029538402, -1.2175981942934404, 0.9668692339854339, 1.0110496438822332, -0.23901152140152282, 0.03640783672152065, 1.6988524057875467, 1.9450169358157425, 1.1178605530840355, 0.2914835160136675, 0.3740513241575816, 0.5253814446840063, -0.19579920128170278, 2.082512509939768, 1.1506284129739457, 0.5889303150195753, 1.0144169898943802, -0.08975560021345222, 0.6190739447491922, 1.438672051927935, 0.2883047845267505, 0.17159023875098947, 1.6130545723547773, 0.45984327282099824, 1.0288884938007705, -5.311489220314991, -1.6054643233617822, -0.12524551177443574, 3.485327662433114, -2.9018353717212015, 1.1079787954545124, -3.6015636336408483, -5.487948523370911, -2.7541907991947343, -1.9651365276088408, -2.6477920541243534, 5.682567775849744, -0.8221880699397508, 2.204545603004787, -2.6297904288725737, -4.206862408065587, -0.732483424359961, -4.053850544452644, -1.925518706500719, -1.5662932155898897, -0.08496864950296518, -4.651964030885809, -0.8709975303320022, -3.1904088855641897, -4.581999047097864, -3.3517707257839513, -2.6172060001617226, -1.2241229866792962, -2.777795519115351, -6.2407308233486125, -4.968719209786488, -3.873689061256683, -3.4165949223399847, -3.2619582593962257, -3.1667198688902967, -0.2522877047825118, -3.8440508376397764, -5.128283980652031, -3.587832438008421, -2.609259933225675, -4.472154382906088, -1.076051826319069, -1.8398847896781292, -0.30685067045478753, -7.063545535938351, -2.5452366459045828, -4.59250942405907, -0.8251300920577013, -1.0817230271459681, -0.26618680609957496, 0.6888386994742688, 0.10138047293306028, -6.577424179501446, -3.2090916936406555, -0.33244474036690086, 0.38471698790786113, -1.2294995816357754, 1.3148825067065169, -0.0842865857605909, 1.291945974455656, 0.015527992822389092, -0.002991333891369131, -0.006905855376294711, -0.03331779182684421, 0.00856045344174449, -0.023446285473323784, -0.02115432014100528, 0.00818597155460575, -0.5518654329754913, -2.6138462225865164, -1.6360679374650515, 1.564150081395783, -0.14998624898895774, -0.17146550921338172, 0.04126412436991597, -0.2820887376652378, 0.0801797190785836, -0.9693050160441095, -5.401352268152118, -0.15891851127838733, -0.046225178505389125, 0.22477564586584609, -0.25569347397231423, -1.1124760177084259, -1.1159002540712712, -0.11367034113295019, 0.08830432446318243, -3.8054395767322484, -0.13784544596596898, -0.12348343491713171, 0.9176945500411336, -0.6157798167365807, -1.3884908209842786, -0.23034426370213523, -0.4972705970709678, -0.3613332289979417, -2.387670512948733, 2.1672930930052705, 2.3914081260567706, 1.02633362612892, -1.666729873764664, -1.5662415486372532, -0.3408832297088075, 1.7616983070078585, 3.217199034771753, 3.643298644100879, 4.55045865931918, 1.4811819922517167, 4.314207440832449, 5.540275231619528, 1.835979672692495, 2.5540994251928084, 2.495498142482426, 4.406214845166708, 2.4058025766968267, 3.177408317364413, -0.0270529406670719, -0.0028520069117586345, 0.03237974517859273, -0.023920570458591375, 0.024600743186823197, -0.03554145711450732, 0.027181360042421887, 0.021259436719800663, -0.4033410958800058, -2.273403958195646, 0.3562051592269722, -2.1492035624621235, 0.1662052061916311, 0.6811124042404912, 0.7604511666940049, 2.3460424707778085, -2.9308046119870106, -1.8886503240419545, -1.5409968029342793, -0.777952515602852, -0.48705370797752734, 0.45236335315519444, -0.6153616120180653, -0.5916727596477402, -2.0262740807914645, 0.9000368457038417, -1.0390904859663386, -1.432568058802165, -0.3540599746037647, -0.09458707725161447, 0.4016882579124094, 0.3471356443786647, -1.0584348400641534, -3.5639810163186456, -0.7204188876615532, 1.4848533705420452, 1.5764530951227838, 0.10845506414776394, 1.4282620440505716, -0.41371086444826194, 2.199430100627558, -0.5696209418152018, 0.9814938260416133, 2.0777392508057835, 2.939599710945836, 2.157740017043531, 0.9899572041955343, 1.7405526454137707, -0.8565700139284289, -3.3495338130172714, 0.6326721650935101, 1.1827049593775105, 2.0152937442852292, 2.4542081466217045, 1.9620241597637456, 2.515315194253201, -1.0568577152432197, -2.3676821438263804, -2.1510868367728406, -1.303195970513725, 1.8919306557955533, 2.0875799098079355, -0.018432241853194718, 5.088712447467727, -2.4705386482638714, 2.73773809312262, 0.11511161519178473, 1.9191779813095395, 2.806951102638874, 1.7627052757697388, -0.8416144679999206, 3.096804768818462, 5.928963840328745, 1.0889493304931683, 0.7509697914988736, -0.22407251731267816, 1.5584377334478963, -1.5699728738804044, 1.0280579866163886, 1.871641680974821, 1.4058979456834109, 3.104274123888546, -0.9774908636238115, 0.6454193433056734, -0.6109820539717322, 0.11682436223531234, -1.8528011698161346, 1.500164003006392, 2.1387245863814357, 1.8945007074053235, 2.1517996797729237, -0.6997400355900748, 0.5046877694382481, 0.09444343299368058, 0.4050868356312468, 0.6378846998768288, -1.0195682554298235, 1.4483657529736, 1.6516486298325015, 1.5448093867885524, 1.8726712973070012, 2.1048632899558752, 0.49545589139387775, 0.2698879661702483, 1.3718083790994746, 0.6014115618843063, 2.77060595530086, 0.4572305847806771, 2.1600169408659498, 1.7573820557022108, 2.753878501407099, -0.16417866365139952, -1.879530651991014, 1.767034743823426, 0.10118104782662653, 2.5918963938318007, 2.4478211864251915, 1.3176850465151828, 0.0029810529456189157, 1.331855034282403, -3.5869649321615693, 0.8312369574150915, 3.3918435523698833, 0.5800330271153296, -0.844029367044312, 1.244676853871168, 1.2149409382551544, -1.710512432645426, -3.1538634070392995, 0.21417532775948372, 2.1651362868550708, -0.9244182170981591, 1.3415098710850688, 0.144073454110015, 1.2147830535611923, -0.4455412830202072, -0.3415124383404851, -0.13628930021371324, 1.2789225949337126, 0.445153667211374, 0.2717917515011741, 0.2913904272455436, 3.235679669846757, 0.8903704501127174, -2.454545513291578, 0.6259828822258554, 1.6465667737006302, 0.48561284869015636, 0.08011652488561191, 0.7513647098585822, 1.9399072933923256, -0.5484008764611695, 2.274706240804414, 0.5715079888964397, -0.528125979616859, 0.007437749601441711, -1.1503474172182355, 0.7091155751557654, 2.6921047116633288, -0.007096099239896716, 0.15561289470751558, -1.3983694662428712, 0.541425561689824, -1.1139229972422275, 2.163478986638615, 1.478781842815141, 2.5515189112014887, 0.6346753680462056, 1.5995481866262031, 0.5869534995573035, 0.9778854002532179, 1.6128425071340726, 1.174217138521948, 2.4056461011941996, 3.4711853872544656, 0.5558113661577418, -1.2727484080952685, 1.0087073929786305, 1.3068095806281803, 1.7880952759081647, 2.4423587121322847, 0.9446968294090697, 3.354938838992082, 3.2270496118434573, 2.7565444639902363, 3.146623498606076, 2.012522763318427, 1.8679727816088767, 1.7474399744729996, 3.8122521645407605, 3.378797884033408, 3.200140730436742, 0.21453920369066484, 2.217989399743601, 1.5100940816671777, 3.186434606858577, 2.270521654890023, 5.128768818428744, 3.774307107922947, 2.664087934587161, 2.5200394859302806, 1.2443215841298318, 0.14026834038545333, 1.0201645678980846, -0.3348653391481583, 1.0737814623222592, -0.3098870928607865, -2.414720916291792, 0.5601412032977997, 2.4199384044337426, 2.130858479349518, 0.7692789282683783, 0.3621906992734416, 0.6694217491040524, 2.1375493662061635, 1.7337525626238939, 3.013651215128928, 2.010431568706599, 3.720909931337624, 1.414300226126168, 1.374465614716572, 0.7374270786351933, 1.959142582061917, 1.7600657646123012, 1.1843410781999808, 0.31947499135326923, 1.769145746037058, 2.434957436240284, 1.3611743095427677, 3.2919648376873143, 1.8481039493795381, 2.6294879260540394, 2.0786729680289064, 2.2728331310711063, 3.155335218496146, 3.2009378870450056, 4.0664223203807195, 3.249068690334397, 4.5478219915282905, 2.963901063144138, -1.565732840378935, 0.7837010726101256, 1.8759755362137625, 2.248249218645105, 2.0730407459241524, 5.950753860500633, 4.333034044573692, 5.0918492157063255, 2.187621138045105, 1.709050482423483, 2.5826321939886423, 1.7060989047227773, 3.246096181442098, 3.377472893744061, 2.4993333120231664, 4.381328114082222, 1.782597372901149, 3.2959718472098984, 2.7164530987244726, -0.9221326436594803, 2.9578727581984343, 2.830066934132484, -0.4446490364119696, 3.4463385324030384, -0.9112012803009768, 0.11850270572485232, -0.7524938975708152, -6.67117540041641, -2.9148854500163077, -3.9152148708653387, -0.7137642742667749, 0.2711251637465288, -2.9183812257700823, -4.719957791245389, -2.5767358113827865, -2.4756975187600516, -2.1178024420999115, -1.6379317261847326, 0.6999524736289271, 0.8349802986040303, -0.24434581562355276, -2.0251527552030755, -4.8625663176389535, -3.184606218513417, -1.533993219736451, -0.6351621572617241, 0.7481106095105693, 1.0740071133604665, -2.868248737994728, -2.0707917194432226, -2.737220098899891, -1.5675618499063797, -0.17637293849629354, 0.0899826271219802, 0.5421349984564046, -0.07030513089563008, -4.3021752952862515, -3.5843722237788116, -2.6825820267156724, -4.358204538774986, -2.3970400710132354, -0.37097565631029, -2.4646698896831216, -0.9139574043054117, -3.343428303547494, -5.65702043170729, -2.6961490722852886, -3.6085227852237574, -5.2458610978342906, -4.6331728938686165, -4.386777112759196, -3.959482659120649, -4.171750725951308, -2.0767319590413162, -1.4099068360071334, -2.8139489095626837, -0.6782890765977083, -1.7214108324851585, 0.674028121589332, -3.0773911089338877, -6.069820096375415, -6.296993206222374, -1.2649516092875044, -1.097548444045963, -0.6331798354260492, -2.8736557406694003, -2.430303863507131, -1.456505639750581 ],
				[ 0.018266328740525153, -0.033304444120792524, -0.010190901433106674, 0.011805344054030897, 0.009084031161511245, 0.014797298113221006, 0.032717073007751236, 0.02710906870079654, -6.125594442035268, -3.1963055533107925, -2.786822488797545, 0.11224860300106226, -3.0148002233682227, -3.022547391361323, 4.636532582373718, 0.4251713625484179, 0.9080032797904544, 1.6473436462746915, 1.5358818282710085, 1.0416445454303587, -1.126951010583361, -3.6348694971524442, -4.53451502517886, -4.475373597245241, -0.02370115082682661, 0.36655047348529274, -1.6640201311652059, 2.3808570249829133, -1.1809096736055316, -1.1238289140475004, -0.22199728648574202, -0.5430336361261683, -0.5516549058283359, -0.2785092827503838, 1.6824200335327095, -0.09470854287692997, 0.6025096417545581, -1.8976311947880717, -0.4217068331256012, 0.041563338712361536, -0.37547151514346794, -0.04925576426400162, 1.5488788132142088, -0.7100291774650236, 0.6034980198740233, -1.5271303518242019, 1.9843006173062645, 1.6248219295885207, -0.848230754828588, 0.188598628224049, -0.11881025034343524, -0.1888964320204162, 1.8375676180146854, -0.4241345440629165, 1.4856222801268741, 0.9734381142036432, -0.01833181600440028, -0.031713605605022635, -0.022585713832286972, -0.0064436842054661474, -0.0013974276830968388, 0.02344448047469337, -0.03502784427471658, -0.00827004646161894, 2.49169100709749, -2.670703340894632, -1.4455660964822827, 0.13949125040864968, -0.5412663626893005, -1.195219122418936, -2.644726783232356, -0.20022102635877484, -7.044479131162325, -1.9338631891528946, -1.0244632776318092, -0.605713808735483, -2.1505500291168986, -0.12729281797177758, 0.8367621674638462, -1.6404093842679532, 0.602654125652367, 0.6739032679593675, -0.8790342969168616, 0.5989070425164686, -0.263238581029119, -0.0169877505806895, 3.677138718225803, -1.899830165165388, -1.3977129123253271, -2.647676088742243, -1.1750197094493189, -1.7222893012367664, 1.022092968271769, -0.7556363736825831, 2.020282194418335, 0.31539986023613586, -2.161371599831163, -2.23549023386213, -0.9268507925917502, -0.30205127544741134, -0.231094941793305, 0.7817306552488774, -0.0931796993486244, -0.4541779539169562, -2.0096349410967753, -1.2098192500113438, -0.13129337679869824, 0.1919639265865949, 1.4037522056958747, 1.1732090570657276, -0.679214039108649, -0.6749526258604346, 1.0637039752058546, -4.1340540122182174, 0.995468888728783, -1.0785266582013082, 0.6982775739111606, -0.9805364700011315, 0.03659611634288608, -1.7742080225448364, 0.4503612999152577, -2.934204996507956, -0.09295299826103502, 0.6140611568338742, -0.7548453827219069, -3.72312283600101, -1.5706182838561533, -2.142231340425293, -1.216456694480069, -1.9793988481240699, 0.11209865460911032, -1.5754939773723413, 0.7021479553612415, -2.5725649704251485, -2.375441594121592, -5.049563413828236, -3.245412672490207, 0.11236220084331094, -3.1489660582334476, 0.9336109048198532, -1.355463100906748, -2.5466924101761204, -3.738036420483783, -1.2414049225061004, -0.7578130559704879, -3.7503296524720544, -2.0536897694830905, -1.3295651810122877, -1.7963966643905578, -3.1173243043384127, 1.003842638185445, 0.5700205591043789, -2.986306932725977, -3.5655622060128946, -1.6472681080790648, -2.0593436630109427, 0.28183140779873944, -1.2922852803774785, -0.20540949594852603, 0.595899636106441, -0.7404466214758924, -2.1054482684442717, -0.38443662173612253, -2.8385247315436373, -0.10644452874537418, -0.5473778013313693, 0.08619673876157018, 1.945199208561162, -3.116567223559133, 1.4986138652275358, -2.1556014934881693, -0.26324938848254104, 0.09574617082521408, 1.1583234589396285, -1.0729858732920403, -3.908686310719728, -1.8378387708924346, -0.1703219083407774, -0.5065588217473168, -0.36732015529465656, 0.7797666268305667, -2.3230725266115297, 0.38670027908126087, -1.6445208140728855, -4.357402377789211, -1.735340716104124, -2.0678598830535773, 0.7399149723432472, -1.4203028917612879, -3.228213095127711, -3.1126997579625075, -3.6083377657035287, -1.3094494054581292, -0.6174011294171164, -1.3326241028478238, -0.26213966936138183, 1.46126027996994, -0.20845575785755105, -3.769616533726264, -3.1490689910190977, -0.414655607688325, -1.2817275315750476, 0.32433432277873137, -1.559065816024886, 0.382837112735136, -1.571077500711004, -3.456958497422301, -0.7432983161321106, 0.8197609194898857, -1.770799659491247, -2.041204842331467, -1.6533954862842506, -3.679259009263576, 0.20736473342591902, -1.8757213969661812, -0.23114577998526478, -0.8836050658982761, -1.323247594737321, -3.099040309900273, -1.7891895537254554, -0.6559266793323125, 0.9968805840224899, -0.6911267917785456, -2.153541736038596, -3.108162011790649, -1.0021722862960754, -2.4811612942802093, -1.2488987120271038, 0.22963216577647547, 0.2834976859566658, -0.9660201832213016, 0.40522195465188177, -1.1339603190339025, -0.2951714739495824, -0.7022061171970945, -0.42866460471374396, 0.2386419600084825, 0.8416507903813254, -0.8659238368763212, 0.591132134038758, -0.016444425959119085, -1.5065361033508937, -0.08462810550367902, 0.3398642045617912, -0.42652290372091184, -1.0991737761496159, 0.9904270737611943, 0.3925172401469926, -1.1996367826978829, 0.04610102324016471, -0.8392837872776495, -0.553409810674612, -0.808834335427631, -0.9856668945727134, -1.3033088071464316, -0.30542079505332, -1.9067761192729817, -3.04263380365781, -2.0008751647006426, -1.59297754170708, 1.1131909814219245, -4.893333050133967, -2.0838556368104553, -4.10144781695427, -3.274735550038384, -2.5181005322177024, -2.2545747021516074, -0.7217584202640364, -0.26305733829786965, -2.9363517481511914, -2.647220713673912, -4.6444658687455425, 0.2648427859265881, -0.7145413769165313, -0.9265627149354786, -0.29117343405114754, 1.3226708547978288, -0.7418302746026487, 0.12805815240279517, -0.11258896687501241, -2.674682263694072, -2.977265955901085, 0.4850398742322271, -1.6346386537021682, -1.5116934906308774, -1.9348893911695184, -2.3398937699011575, -0.9119455362958654, -2.3288386699029338, -1.0281741877037611, -0.7572941538700755, -0.6787045421965725, -1.3754946840459177, 0.49530678862601607, -1.818528244860468, -1.152181369862808, -0.4174482440676106, 0.49381709270527774, -3.0753870545343878, -0.8145605678235074, -1.9299894282984664, -1.9800577089785865, -3.001459282622101, -1.5105067799123648, -3.4311048641658424, -1.8516001461552305, -0.2211727933682943, -1.4690577756325702, -1.2427029018843834, -1.8296932162518789, -4.0018429206264, -2.541823446628273, -1.1859352520867297, -1.9856325198995015, -2.174497549038263, -2.6955947277703407, -1.6308023496068553, -0.31234990073357494, -1.6698888295885572, -0.5929381095344252, 0.9110154767977472, 2.39407169932135, -0.04729484264804579, 1.6056793691965399, -0.8436155163685878, -3.904448243720541, -2.0469119024524574, -0.30455316062768373, 0.1463422111191981, 1.507710073083687, -5.162281735885383, -4.600081986860228, -4.531332163102625, 0.4643630486227453, -3.172179878786671, -2.7192145311420624, -0.5134008434036392, -2.4377060364526884, -4.945067731948732, -1.6458896796700875, -4.830745209068229, -3.4853908223565937, -3.3175293578347893, -3.902129194998831, -2.7838585900643364, -6.753805304745293, -6.602154634215453, -5.426129653576249, -2.089191062514667, -2.350035101298611, -0.3334150133172902, -2.9773749398653244, -1.0993775898084328, -4.1252430477144, -4.375581855251642, -3.8401060528075117, -2.4063164177902334, -0.6649005033295775, -3.0089819933851785, 0.7167384043719185, -0.44855476875551403, -2.062887422904557, 0.6438581770717782, -2.665685948512937, -1.2533181301487866, -0.797922406174203, -0.21854912034330307, -2.3259894286664577, 0.17979825886329992, 1.010943415929732, -0.04909491385185327, 1.870961865720542, -2.268007043460468, -0.4908000515614014, -1.0344465426555045, 0.20893120249618702, -0.322449899381945, 1.58789138274435, 0.11874873723988078, -2.872385203123453, -3.7654241256264998, -0.09111246890067105, -0.7400475965013076, -0.678936990141479, -0.0034182744182167024, 0.0032816513952201136, 0.013232924105085444, -0.004390390140112343, 0.0038081543757170202, 0.020854347172304062, -0.019829900003007404, 0.004977341348032639, -0.1038815455532932, -1.135482873129356, 0.8451202227814102, -1.1861813220447361, -0.8174358260852569, 1.5713661980541018, 1.471877539962877, 1.082673072914187, -0.07637065496733872, 0.563248310511551, -0.7083454231796431, 1.1435815922150372, 0.7018503025332479, 2.2401343055894225, 1.4467353481634182, 1.4828202288727412, 2.444618117565829, 1.4035347435791077, 0.9051001427219326, 0.5151173886208531, 1.3908410568111287, 0.3359065282287243, 1.4915300165346979, -0.002205126543954384, 1.7584905086778841, 1.393122105711018, 1.1736137133775149, 1.4653569191746438, 0.3484271367261548, 0.04403099930243457, -1.884799391447016, 0.32697049660718563, 2.2227161605543118, 2.5136100184634573, 1.7503937723867249, 0.01813785864739068, 0.1027072986143674, 0.2455204105777669, -0.08237645856146233, 1.8585157564275774, 7.016744648320663, 3.5131373618127997, 2.233734742252486, 0.7885473682545487, 3.2188585538282966, 1.2451010102462086, -1.4153161373358956, -2.687414443805441, -0.033262975861680893, 0.03522894419835105, -0.013257005896757646, -0.014310811752410127, 0.005597309553235003, 0.028793852889891267, -0.024940326694818018, -0.029312809853565096, -0.18891868901037928, 0.6350359412169994, 1.7559059988184906, 1.5128787802846568, 2.830834482328914, 3.8674998146986748, 3.3201597393259763, 1.865810534074262, -1.251819732806769, 1.2301467668964954, 0.230165295527664, 1.1318962532272197, 0.5074246935355816, 1.7578704227601236, 2.1828646318741787, 1.3275202281533809, 1.7811184417294375, 0.20896128799883973, -0.553904878359873, 2.2404252389591126, 0.03709482310501248, -0.05019967095511279, -0.3981183958986415, 0.5763656527798329, 1.4134231794770078, 1.961868463276307, 2.2393681421245, 0.9372130189757469, 1.067537170726729, -1.5135419343478298, -1.0704311549427714, -0.8655964309549964, 1.2816407396301532, 0.9093888796873734, 2.541530331164734, 0.6770606682883862, -0.5045776033252016, -1.2039758288658655, -1.031374195834281, -0.23551893446891328, 0.663665276481161, 2.1737353680309215, 1.0827190913136688, 0.7211026098808146, 0.9145353657956174, 1.4403946696623422, 1.9680655341936586, -4.065421682269208, 2.3592484309688917, 3.493005102918445, 1.6409181971419928, 0.26812544294953045, -0.3562950326974589, -0.4283201169298447, 0.6561887384695193, 2.7171002556279706, -0.570599220875982, 2.6857581944154694, 4.767641513487352, -0.9927438856297686, 0.7885021771302742, -3.1485357219501062, -1.1781866083015757, 1.7504530780502954, 0.37902664102921585, -1.7544083550061098, 0.2414813573437881, -1.5640776843225166, 1.576882793446826, 1.806286147299157, 2.518055199223726, 0.6723794823585407, -0.6692237928426119, -1.5012160900098086, -1.4493127528417482, 0.5489387854509914, -0.676893014973246, 2.1500007688949587, 1.3197442686456518, 4.583111714930102, 1.0908551183215274, 0.22145221583849065, -1.3479555350105374, -0.0022731032094403135, 1.5012012697549768, -2.5019524431399423, 1.4544471814915303, 1.014354699019174, -0.4009011557781224, -0.2498737417027926, 0.558835214581148, -0.36393804396013557, 0.16890781819114356, -0.14028558632738797, -2.131684254005823, -1.937108411501156, 1.530652199717385, 2.113637895293489, 0.8053809711470614, 0.9557874660248428, -1.7425951835125937, -1.7337351795383673, -0.016246038135352348, -1.9168080574553208, -0.35988431547949357, 2.7100293774848474, -1.1790859493651047, 0.6951920249655013, -1.2957785632384204, -0.22584303175128345, -1.313976832709866, -0.17736201720379668, 1.915117396878878, 0.7240601034668921, 2.341314713737413, -2.6847398271799268, -2.3846361017671494, -2.5866370146094773, -1.6694229372670304, -2.427888314837772, -0.2455050830998051, 1.3571103631702366, -2.4689553142051675, -1.353925106748174, -1.916022214865159, -0.22519057084865843, -0.6293139286522901, -0.618470934910861, 1.6262734125567577, 3.001870104017437, 2.3317215422551314, 1.345594046153879, 1.1101601903181106, 1.1171282536378295, -4.582951562004731, -1.1951040200656515, 2.458640251361618, 3.3570577433807043, 2.297224845423909, 0.9620494803638733, 1.591412989906983, 0.9231179212265318, 0.2965558808194202, -4.53735538914693, 2.7880980211548647, 1.3345779919849108, 2.385339538603472, 1.3628227648670845, 1.9803101549512132, 0.899957597720189, -0.7057639927272177, -0.30420606898352204, 2.565948672312202, 1.4519118770562238, 1.658728666718686, 0.48131024201647976, 1.5652016115943628, -2.216288871479221, -1.7620376409268657, -1.5088360204187947, 2.8482261880838227, 1.7736663791463843, 2.1512752230597294, 2.45678990005092, 2.2730546676343306, -0.8010509912700339, -4.279033170739168, -0.8544884270089212, 2.17923204291442, 1.5707701638714702, 4.025025270425462, 1.294334469656772, 2.5172299030315637, 0.6577400402722506, -0.9007046951096357, -0.2313153205998889, 0.8320963528784792, 0.4457377283626926, 1.2245668250260495, 0.11649875390183603, 0.32390026181244264, -1.15466574476757, 1.157250338624441, 1.5157118969991428, 1.1077238389796797, -0.04157217294798406, -0.9964087868046929, -2.062147172721951, 0.801220928809726, 2.467585320528888, 1.5775843099383842, -0.3359825206720064, 0.8044222696822879, 2.1080371750957987, 2.7952942929404365, 1.6376056154369718, 0.9199254468650753, 1.7619560168079536, -1.0408595372907001, -1.2410445292204675, 1.87567178606185, 1.8283196668375263, 0.5407854822745845, 0.9536144829696396, 0.3704821933759568, 0.3668515639939389, 0.706789068180863, 0.817779514281448, 2.395393991650406, 1.442125634171088, 0.37510223599610143, 0.3796775351736067, 1.308975500307164, 0.8164924147706173, 1.2102986254196342, -0.32235304641273915, 1.4180900716694793, 1.803220535716395, 1.382073230084452, 0.35739880737084334, 0.03271120469444504, -0.9459052236180836, -1.0092779794888644, -1.673863452621992, 3.019002306511024, 1.585388430878256, 0.8890613371154654, 0.9050257086662289, 0.08594724134526659, -1.8227153314100244, -2.19872321520749, -1.868206679149114, -0.00528100793802759, -3.106896638700954, 0.6957639355843583, -3.043069281673227, -4.904949897728256, -4.040023962607563, -3.3571118034661103, -5.766263580351294, 2.120417434810012, -0.6306637482403579, -1.0351167941537693, -1.2805952265755347, -4.599345530346934, -7.013578444813546, -3.459338957289702, 1.4148948387195797, -0.6799628233135393, -3.9023672933327838, -4.003844279600494, -4.257190773070855, -0.17133439294562747, -1.0776830236203552, 0.35598816935575117, -0.627145130397767, -9.108226440422927, -4.191183562593632, -3.3083161937592003, -1.539407479868821, -2.1247437305556893, -2.9991833752724584, -0.6140007113588981, -0.35083956320762333, -3.903310283297652, -1.9658379116709968, -0.1995728730882715, -1.0907944390938942, 0.06981323910403398, -1.2967400084055944, -1.7298096012322999, -2.746268675256413, 0.226727502172364, -0.5385454021640526, -0.0188467673763568, -1.0754013103570206, -0.19449178231456235, -1.0866106480976456, -3.2410238385127066, -1.5300329656663392, -0.04541920576009022, -0.0433721300914822, 1.1658909154330126, -0.7454946468427437, 0.5523872770114329, -2.230237342821776, 1.142063744353822, -2.508873992436455, 3.327558305388994, 0.6619573296961698, 0.6018180784647462, -0.09100815067156236, 0.33940371533908914, -0.9891123959999569, 1.1097957775564344, -0.14428385204849165, -4.04365757931455, 3.5353405781703904, 2.924412834028802, 1.2767682182200841, -1.843894249304055, 0.014718713474993645, 1.7440690813885897, 1.4401160570420777, 1.0193483257006475, 2.9611116467224656, 2.657662378657762, -0.11231486178886374, -0.6198488497708341, 0.39645684333454867, 2.5444090514992026, 0.3111354353854353, -5.150959298899378, -4.265794812352913, 0.12511640688039838, 0.33078943540615946, 0.0032873849695269275, 1.8722769340727112, -0.4610465050592344, -0.2419176695496185 ],
				[ -0.00416224277483012, -0.00480435470905693, 0.033232496108729116, 0.003383386859606835, -0.03144262167092148, 0.023942271003742785, -0.028635326055428706, -0.024364065264205655, 2.049500579406507, 3.966306889073738, 1.4927722558384064, 1.5124219043287088, -0.7602032662521014, -2.3688391293842606, -1.249762213856885, 1.9812624316181093, 2.7072277729419323, 2.5530546708349324, 2.835993114596686, 1.9544829458609965, 0.5983814661636324, -3.1320499323002977, -1.6566673789275645, 0.7782447674347217, 1.3734519323882222, 2.593389309131484, 1.988452812570343, 2.1249579604731794, -0.5363402828638597, -1.219937910085771, -0.8535990856734399, 0.2549334791862117, 1.6866558988611793, 2.1216061242221054, 1.552264188936685, 1.1613521992955471, 0.7425300847497899, -2.109353100363879, -1.3295301390214869, -0.8587743608802688, 2.029560010880609, 2.6600846390162225, 1.559519137632579, 0.8049015508983816, -0.1457814978078666, -0.6050298677143928, -2.1938926006060733, -1.8960614667692202, 1.5873551242749824, 2.069670375773863, 0.9181236270875205, 0.9480295711907104, 1.1241695703465764, 0.3775113960402937, -1.6085080821103397, -3.0746956774605385, 0.02550284577464281, -0.008302958462064605, -0.017936980474400895, -0.015070363891273746, 0.017405767753119014, -0.012168672003694484, -0.03317326538882634, -0.029032947317670445, 2.3156474393364066, -1.2276078097956598, 1.2516209360212316, 2.5688650139422284, -2.765074461467074, 1.051526301960949, 2.6568518361853077, 2.9270560612564283, -1.5376050208252994, -0.7801415337922015, 1.0478981198787136, 0.4939619074969813, -0.6626728601689994, -6.444395507515795, -2.7916824259410156, -3.9260592906111094, 2.571778093137628, 2.7499299819397063, 0.9820490046631952, 0.9375393421226011, -1.2489598955097776, 0.8098240033237382, 0.2455386160976476, -1.9512790467140797, 1.1924882560216796, 1.2718396849421378, 1.032822528378116, 0.1682182023934181, -1.8887266647347494, -1.0460901661077333, 0.07979841681931757, 0.2517390480960067, 1.0332530405171247, 1.0106941358049708, 1.1962683944111645, 0.3191814480834669, -0.8452500154119386, -1.2824353628780982, 0.40826230637328326, -1.1652067734722416, 2.3811361907107074, 1.3162931245623197, 0.7454102577284114, -0.5687902220353581, -0.5135592997653491, -0.18320997906285355, -0.7057782119473042, -0.4103231484904669, 1.2315829093408575, 0.636739399278381, 0.4943994066613427, 0.021311877358141093, -0.0755984049053282, -0.579534380023616, -1.0845595603559592, -0.752838211057346, 3.5469261832169514, 1.3248057424088768, 1.5841320552482157, 2.3184473132285426, -0.12894757836082107, -0.18616818594190046, 0.8077840549659827, 0.5973596693969839, -2.689230933754502, 1.44230604915965, -1.2631683542273437, -1.0643398740703318, -1.7189904940812633, 0.33332999876855546, 2.2709721570449983, -1.7450029044719393, -0.26625722381301986, -0.7054310133399457, -1.5067039735901997, -1.3290324347524567, -1.9387084523180218, -0.5938878498766547, 1.1099926496115051, 0.25086694969781637, -0.18607558201182142, 0.7167905336251212, -1.503237283150597, -0.5401262446759758, -0.2237359576057672, -1.8193291096907807, -1.5654111576479823, 1.5973943653161042, 0.10366329558168459, -0.1795817691772778, 0.6077490661140738, -0.12115996521543643, -1.4300940629900283, -1.232020379929514, -1.5868575393041002, -0.3428786507606006, -0.8041158032690877, 0.7051420029580225, -0.5582325389267595, -0.6668574108580883, -2.405575332585645, -2.4269001652134095, -2.455712868276595, 0.25144897831478635, 0.5298449577165881, -0.13309504254191798, -0.3002732983091235, -0.4789684793291568, -0.9651692520137222, -0.9058347554751235, -3.3292194785726594, -1.3966604261519395, -1.0842495121051292, 0.4611516182062177, 0.8346746952008873, -0.19252005804740077, -0.46061643396385393, -2.3826985484363634, -1.23556139376308, -0.9043273221637255, -0.5344279371032781, -0.3126080442080569, 0.05022797136997459, -0.20331719888404218, -1.689855125523706, -0.9454752980293916, 1.4501759690413973, 0.7962537769031709, 0.06958193788734438, 0.44075395180030613, 0.3741281627546422, 0.13040175805348356, -0.6654724325276731, -0.2696492233525362, 0.8092964577000074, 0.6879086921724719, 0.9509751489751062, 0.642486104923147, 1.305669897783026, 0.23257685527400884, -0.029098878593638477, 0.005079268284921136, 0.9264451764590977, 1.00560318784343, 0.6633622740631402, 0.6543754896276379, 0.53123617251765, -0.45184715887440735, -1.037857339108658, 0.462380067783059, -1.0977859061966504, 0.28308425312021424, 1.2375413767848762, 0.8188891632384488, -0.3180080620267127, 0.37313491370500107, -1.280558398180307, -1.3703840414234223, 0.5219551083637736, -0.3935241345989484, 0.7702167541065057, 0.9322114264010645, 1.003647810583759, -0.2167529135519334, 0.38771019412033303, -0.52279995158452, -1.0088342224810836, -1.0385410786925577, 2.339812326540336, 0.02121662554049457, 1.6636198184867164, 0.4814388415930818, 0.33063246050084516, -0.30104744186517396, -1.4243953958493203, -1.0000978626671357, 1.2667853613599653, 0.5265819472030244, 1.7776278699516148, 1.3922305342982892, 0.9358286883577508, -0.07424980751807936, -0.21632779184235204, -0.7108220254731276, 1.701341107864408, 1.860236114063976, 1.44765082888783, 1.2311539656641088, 0.9852020639272774, 0.5238413901802551, 0.2780463846909327, -0.8940982142695748, -3.3964120745983517, -0.3806651906084793, 0.26977049372523454, 1.2476690435583455, -0.5134297830226514, -4.603362532941957, -1.4747004636487517, -0.21724854223722082, 1.594524995828677, 1.5989791047874744, 1.210748581287692, 1.071386262474921, 0.38995444919757744, -0.9282668066165762, 1.1332178004703328, 1.8410111363213035, 2.4890253294417937, -0.011836601975040856, 0.898650859080312, 2.023953515725072, -0.4112082159212094, -0.8273722058302464, -0.7656308540397748, 2.4720466501382408, 0.09491954014148206, 0.38104657747836174, 0.88498285343028, 0.9312808649698598, 0.5635203251001852, -1.5636381396264025, 0.8663044123146306, 2.2974193935196934, 1.2658250531858013, 0.7748367391736487, 0.9770057528247135, 1.2052789646982638, -0.9798349639491764, -0.5079222908887165, -0.14145917024542196, 1.3412768433341549, 1.410652927079956, 1.0305861033777894, 0.6591609762421501, 1.3237241665472848, -0.22340482976029757, 0.2581132467264634, 0.09694219887901287, 0.8580680124958887, 0.01592684112683455, 1.282803028628961, 1.5880402288459414, 1.300174715902335, 0.9531329148943125, 0.3513781784174588, 0.606745738931099, 0.023282955625725854, 2.3413804321932083, 1.5143924898448546, 2.202390255277902, 1.2663738826688895, 0.6796583331688748, 1.8811276247957178, -2.53013918636052, 1.7544352063002062, 2.8439180346758257, -1.2011515570967268, 2.941016091821979, -0.39543628378519163, -1.2931777822234374, 0.1948097636962448, -0.6998404637888603, 0.156716196059764, -1.5033938842765435, -4.716757065240377, -4.966065311348289, -4.3535760871782, -2.213998580815592, -1.6762937232212225, 3.9222063328904286, 0.036683106227133666, -2.6979492241442746, -3.0584091983596164, -3.1990414246422345, -5.328773893285765, -4.684434577375139, 2.251760271675528, 2.6030267828278535, 2.5710541639161275, -4.440346767250238, -4.847967309729273, -4.651915751634653, -4.888558645130022, -2.750351517361334, 0.29181423925783123, 1.5291838748978972, 1.1612262756493104, -3.6052909738342556, -8.745058104036184, -6.367403222445431, -2.8033931842409654, -4.9660876558703775, -0.6044184895510281, 0.4366906749617322, 2.232033169197277, -7.412980532210003, -4.566679527765177, -6.099608825866396, -3.534395809951259, -0.746625928172906, -0.15252970631066337, 0.7100607554819769, 0.6851708774945263, -10.253264978580557, -6.93061294443453, -4.4823051005546475, -1.1706668630707848, 0.453161137919854, 0.6547790250228358, 0.3758680187002093, 0.07321172629512773, -7.427314729304187, -10.152165493216216, -6.745924405521696, -0.28930730475791155, -0.09966156108975775, 1.2405037293589638, 0.24479028861352886, 0.13347185855704877, -0.014451482649899369, -0.00510316088870892, -0.007005357123486046, 0.010165032192812128, 0.008172918748012702, -0.029031189611291582, 0.011537227781799251, -0.009692850073757017, -0.27349023278430085, -0.5793851659680965, 0.3481650416210853, -2.7612968214357307, -3.1803811970855205, -3.088038791708572, -2.263274215497248, 0.01485421775741378, -0.40424248863464624, -0.6099715325642494, 0.3486885795588138, -0.1805930973107925, -2.148666074483254, -1.7064503364475816, -2.380429738068918, -0.3309358002469824, 0.24086521529350807, -0.08043156139018441, -0.39581304434607334, 0.017926443071254943, -0.2847797302383552, -0.3619944620642352, -1.1422039761542286, -0.5713204785687405, -0.2692740936750154, -0.8055997907253708, -0.970115037651551, 0.7182073616377462, 1.2732695754482362, 1.3914939635076211, 0.46128886877867536, 0.45875419871902917, -1.3778072956113336, -0.2888602314139602, 1.1710422471024275, 1.7989145239534186, 2.191144410800093, 1.534911266233741, 1.207792884951645, -0.00026070130081429156, 1.6541565413490362, -0.2868049075293441, 0.47858859348304195, 3.1152831024158325, 2.246910745328347, 1.4649199346923827, -1.3962555265171628, -0.5717101577678079, -0.034316746519379354, 0.03536386698769909, -0.0280392173228088, 0.016370457293601086, 0.026058745938454295, 0.03180676163823116, 0.005463065649755341, -0.021182901417847455, -3.455519304167327, -1.3445711047993123, -1.4124681208730343, 0.26742965838183386, -1.2170962132172354, 1.644095868653622, -0.5693753504207726, 3.1872926848876886, -1.884909994775367, -0.5831346779344443, -0.5207847277118226, -0.5919592714811128, 0.36778603803704835, 0.1261564931848169, 1.1467310505615698, 1.397175919366106, -0.40156179414526544, -1.6156908798770586, -0.37426467419284287, 0.6155246336004123, 1.2903017198037454, 0.5303603447585682, 1.906524211117524, 1.3589077901663345, -0.45637562610549953, -0.11801746903674085, 0.6659662371731585, 1.0256427876377687, 0.9529332838489137, 1.8514923413707711, 2.7530911029976024, 2.86625951750564, -1.031536319051033, 0.6701959661594057, 1.1168591784170105, 1.358840934838493, 0.6527563687305382, 2.12299813209783, 1.3419281606077542, 2.687571752837287, 1.914867652794915, 0.3237689766529107, 1.1918763760184043, 0.8298273696329532, 1.5678442940908082, 1.9066224962988993, 1.70774008336135, -0.34884477389831403, 3.0369226956536863, 0.7903920917542859, 0.32103757639334257, 2.260271310262268, 1.9058087638470047, 2.204172209058837, 1.1931441794842694, 3.1056366475829082, -3.130343604864241, -0.9459127022439446, 3.337256111879906, 0.6024371034601061, 2.3924544683914677, 1.5084673391308683, 0.7047189505710277, 0.5386716326337775, 1.0811373492618472, 1.5212040965950377, 0.9423975778231912, -0.6859607956103192, -0.5558780054470955, -1.096875440933772, 0.10319890667154813, 3.3472842333725374, 0.5378918626346594, 0.2725850006526873, 0.777827669992778, 1.5704180047737404, -1.0217445487303463, -0.9740573165630042, -0.22528034070704747, 0.6464624705828915, 0.4389935551087656, -0.4110921249915849, 1.4115962465385232, 0.9003801160882149, 1.4869788537823494, -0.3365783969786149, 1.7737041522490595, 1.9559122495592371, -1.1536374055071204, 1.252081159591417, 0.5575776051163873, 0.6799986103117861, 0.6772660558887629, 1.5900923134382992, 1.1334290197884607, 3.097104830429682, -0.22289005161040756, -0.0008443525286626747, 0.6672396100995637, 1.953859220950543, 2.193126011306521, 0.554678882188226, 1.9364064906116158, 0.5153426730426238, -3.8997270061679608, -0.061688546479392654, -0.557081868843468, 1.1279949362152049, 2.1542633427233513, 2.4712150079797235, 1.5663311708799936, 0.14749720818968265, -2.1588898826310174, 0.9162603323995423, 0.10429859258200855, -0.5992866340676948, 2.202759513352497, 0.9558423061655138, 1.8640037602550936, 0.40648763536548893, -2.737846236413979, 2.1843228143900544, -2.4540591295507244, 1.5295063750388325, -1.2441875559997064, 1.1129978488272936, 4.305763177778453, 0.6896023665719674, 0.04288253138135414, 0.28455461000757665, -0.45142222276298805, 0.5918894763607087, 1.4805235292989563, 2.706443273179951, 3.7299332447515434, 2.3167173254081233, -2.740578132622377, 0.025397883954771616, -1.7067658502305165, 0.008107660890893747, 0.7405644824645254, 2.9459834135088094, 3.1159542717457804, 2.9980056227236074, -0.14606542608665388, -0.12993106783505362, -1.2546862125064322, 0.5544414813497741, 1.6133940848720307, 2.226660851714938, 4.381770402271043, 4.151219033978477, 1.1025118462591528, -0.7280625331788504, -0.038176644485121314, -0.21206710568285508, 0.47599398369980506, 1.7020726794612333, 2.8922639284056317, 3.090862910252324, 0.35606701478191294, 1.256685705874632, 0.8734323211299634, 2.544216072490193, 2.594329104832908, 1.5762675780551239, 3.2826998583225655, 3.8277414173392645, 2.01912788185634, 2.1304027887025723, 2.1472210432924608, 2.5297793271524194, 2.9396335160055282, 2.800507225302067, 1.999701571994635, 2.5475994354342, 1.939624660177835, 1.4144525705261681, 2.1767226920077443, 1.3201318362045917, 2.19464003598844, 2.6489310315064074, 1.1514367992381556, 2.5810113490170883, 3.305569053449024, 2.4439663588035665, 3.4260955536134525, 3.1062064346489477, 2.728143387816564, 3.5541891142909074, 3.8562982945799478, 2.1560275834527616, 1.7444174745774208, 0.8760625166302101, 2.547582741835294, 1.7734736148924932, 2.4217704067101806, 3.0187164922166794, 1.8960121304610966, 3.8060773298324744, -0.5252747036333809, 1.8420065137217627, 0.5240598618496621, 2.1652896231401506, 1.4744327871143705, 2.4054671329935147, 3.473644753604626, 3.174463050291356, -3.1207170031443208, 0.2596300584479551, 0.9442522184887046, 1.7203532830862016, 1.7189937331417884, 2.243773963889561, 3.365939969416144, 4.115670714453896, 0.06779935733351776, 2.80148220310529, 1.2036039532486975, 1.2770514499860288, 3.0569817186398827, 3.234237126893366, 3.0560003783803245, 3.9068201482481912, 0.4183074478835462, -0.21141048097678591, 2.5814066844276797, 2.8101130609525127, 3.4701245162468273, 3.710411789097065, 4.58927113197044, 4.673109210305511, -0.18438025727196208, 0.25027468197940717, 1.52677768112467, 1.4385471041748532, 1.8294234808786238, 5.815761594473978, 2.7595563638163902, 4.158274522745128, 1.4209732138288302, 1.2892547235424534, 1.0413969175182771, 1.7639198948605064, 0.4137518315218968, 4.1381416707021295, 2.9032245652557367, 3.942798023893072, 3.100799930281788, 0.017313929688619417, -2.5694694367855493, 0.2678598463515712, 2.5756651159834663, -1.5141437840808039, 3.0804681232261606, 4.466958302988739, 1.315740890247352, 0.1328311706668493, 0.10643871759791604, -2.7796046051277314, -0.8922734561842582, -1.2929063651348762, -1.545519243328755, 1.0132975554324324, -1.5868594573910342, -1.0331833015021814, -2.0615591490794594, -1.5329589646475998, -3.31485988555712, -2.3869366000808614, -1.908504923410048, -0.9845603632190889, -0.07018508773893437, -0.84088587584515, -1.5646952630310207, -1.2347018127946534, -0.9855119729079348, -1.1120040644110925, -0.7596800747923558, -0.45957703803101857, 1.0310318187115464, 0.48377136928020853, 1.1869813751267988, -0.3994844740490502, -1.1892055682580605, -2.1113334662681154, -0.6161410732296624, -2.101379151365866, 0.3469108165268682, 2.5046505706243347, 1.0852198740544146, 2.3386917976655677, -0.7514428011784712, -1.1980726500696393, -2.4330375603547916, -3.1574958501240262, 1.9688555585475622, 1.1073918299644903, 1.2272909046717866, 1.7083176931964594, -0.5400623005133259, -1.196169221260756, -3.1191975005554062, -2.338681618609739, 1.3838127320028069, 0.8173895265164889, 0.06577973049847385, -0.15987638219509323, 1.349778408092257, -3.441170415242555, -5.020480396218203, -1.3895642850180543, -0.32559125316591764, -0.4286845128451587, 1.3947869587021235, 1.6513248393992754, -0.4576384270527351, -2.071329048274273, -2.1823880456372704, -3.728441063573229 ],
				[ -0.008856473081550482, -0.02073354729925636, 0.00025296560292589873, -0.0276930771581985, 0.03009630870890949, 0.02541226989001088, -0.014654089633623246, 0.019143831388145897, -3.499399220887511, -4.335876866824277, -0.4124573911707327, 0.506689453274858, -1.2875696496402638, -2.501875209630389, 5.24042871968614, 0.20164978584252172, -0.3391912598913483, 1.0236450385611424, -0.1267112710749059, 1.649416988108842, 0.19358943313830812, 1.1185624072360498, -1.7923825252845584, 2.662758280722505, 1.2972172746613644, 0.7004817857545789, 1.4007258277124977, 0.8734569475230519, 0.39904632593813133, 1.2579091567721168, 0.8305573619848873, 0.759710193350154, 0.5615925203212017, 1.0871335250851073, -0.8077321832133059, 1.172721669201839, -0.4812044281714134, 1.3328910063025752, 1.4151814655658703, 2.181532928378496, 1.299760437653157, 0.2697585336032262, 0.17420223706874974, -1.1337090838916717, 0.17594295138221697, -0.6277060131966224, 1.2916457352701516, 1.4367393737093463, 0.6385711849388075, 0.18826440445489173, -0.35908506085638225, -1.6036664700393344, 0.6629323285711156, -3.1126992566319363, -1.2839977636590105, 1.296230656769288, -0.02463357852169447, 0.0032188503994433904, -0.009633986781358867, -0.034125498357743936, -0.0021847489743817804, -0.010080350070041724, 0.01944270775388804, -0.011334193635691926, 0.24193802104759554, 0.1557649175037427, -1.1504171968710961, -0.16782350035424717, -0.6436938870921138, -1.921415091255178, -1.0110812034285732, -0.9356817287224959, -0.8449860959614344, 0.5530141627422827, 0.8675340026069248, -2.2250477222982137, -1.6884997327307452, 0.6439466515350489, -3.7187476902902574, -2.2013092566408954, 0.7136569529359511, 0.9813939602920331, 0.3305380860804519, -0.43585762355904784, -0.28071471278573495, -0.9931128397547574, -1.3937374722366351, 0.07796542779569456, 0.6579505399459911, 1.1048138897016075, -0.4080558428470187, -0.7771557200385322, -1.910011681724928, -0.6217523949170292, -2.2719961524877683, -2.1163477705756084, 0.3402507999856246, -0.056142653546531064, -1.0996818103943697, -2.2950698563961436, 0.0849998940728832, -0.38750290427601364, -0.01412124862584018, -0.13252291569131566, 1.6826491621105917, 0.5806446457556963, 0.6961901023401503, -1.9093632139207581, -0.5009820733878098, -2.376770814350376, -0.38407544666662335, -2.3327774338088725, 0.604192399690404, 1.2729301665045862, -3.0243447411588433, 0.21192617959153978, 0.2477346624117012, 1.007841810478461, -1.9463329705401358, 0.0005670695161698585, 1.9558137413110424, -1.197597553136481, 0.16618975157182084, 1.0767250575683516, 0.7175960564406094, -0.05037432405058741, 2.1823255289394803, -0.4603245203491936, -2.074521732421688, -0.04383463906676176, -2.567187037225868, 0.4715629281020689, -3.028488992655858, -0.12809316764967638, -4.461339907262011, -1.0761090102979947, -1.3733123868672228, -2.3723845426031587, -1.6139699147044908, -3.3314641150912365, 0.4811375401984156, -1.0564426729492533, -0.6722438989419274, -2.017804237118531, -0.8199907855269709, -1.3555556636069024, -1.9711804597191882, 0.3213619486696704, -3.695941932736938, -0.9108627154397079, -2.7114334886264664, 1.5073416784087454, 2.1853093762321723, -1.374241575506918, 1.0965779570572685, 0.33860923482219385, -1.1094196034777168, -0.809574138558908, -0.46892121039742896, -0.9938225072042397, -4.226471986865531, 0.3951267496850136, -3.60723949313178, -2.1517452592077406, -1.3475282619713138, -1.5386180324616994, -2.6181249260578094, -0.1462518542435866, 1.266281496629806, -3.423603630568658, 0.5702785824161096, -3.1571252567204033, 0.009506557556629075, -3.4339043221271854, -1.828474021112728, -1.5821580153961348, -1.0708088888362675, 1.2348095289237755, -3.444741278012208, 0.8643439358990772, -2.8935273817727665, -0.715531884778635, -1.5551691105435526, -0.6908265453078242, 2.486365567090069, -1.7524031728082592, 1.7067891711219603, -3.2320055426861236, -0.6063582299996767, -0.6509505600059139, -0.4518761564794448, -1.6187520583729276, -1.8249659553158484, -1.2636748396534734, -0.600157400801332, -1.605050727638058, -1.095788982182913, -0.5380799219360819, -2.7091273061353967, -1.5921745303910562, -0.0933806903076991, -0.9132695528516391, -0.26882326175060667, -1.4066923898479056, -0.4469593613774487, 0.36338056632964266, -1.1564609971572621, -3.756768839324071, -1.7767345382037325, -0.7554915717858781, -1.1284025251724392, -0.2821096979556943, -1.4910820677369925, -0.8844532983575064, 0.5910992490739079, -0.28675660836958505, 0.36126779605198606, -1.5150357771918694, -0.9384212901896192, -0.3620968380037042, -0.636692173626237, -0.7493318037391551, -0.961437145252919, -0.33717237106447023, 1.1338970879815253, -1.0484890149325723, -0.9083044216794319, -1.7942205874148165, -0.04588842116231218, 0.016053326706715408, 1.7960265571369574, 0.36689948625070334, -0.21739332747193396, 0.5762510287053021, -0.5618449919742434, -1.0468637209574851, -0.48681025152974583, -1.2043077143799739, 0.018160912486385475, 0.09792353120619428, 0.2131212967999962, 0.8410606361600906, -0.5372295233892587, -0.740922819204243, -1.3989049696124984, -0.9200889029092034, -0.7799542669677205, -0.568075289871277, -1.1586226332155198, -0.11324658049183417, 0.10074659846855366, -0.8311346524621273, -0.7325636805498058, -1.1223270442026962, -1.3893824515660727, 0.900969688090296, -1.4345834513446818, -0.89043563025031, -1.6793108009367523, -0.6849748988688064, -1.895873262053001, -1.8776154141374506, -3.688883391875596, -1.8845538564331816, 0.9715068570121018, -2.5899453597159385, -0.9961238171785274, -0.723720466192703, -1.95845055309409, 0.014699841501402078, -3.423380011050816, -1.9285066673041489, -0.07361182794730774, 0.010375310647824064, 0.3977305706946744, -1.3349947025520277, -0.3035613039089282, -1.024362089454308, -2.2229330281645554, -4.289588634498812, 0.9675779713601756, 0.1713260532001433, 0.08770738816319278, -0.6835494877196073, -1.341888126973029, -0.352907531701099, -2.737195289330527, -2.057422157844265, 1.512151729099016, 0.7769842712982445, 0.35969842091302107, -2.8850281619902134, 0.18839507706069208, -0.8689998580006109, -0.5855698057745017, -2.664101854606191, 0.9354030903961645, 0.01178217550507312, -0.11575037869577462, -0.08858512700128625, -1.05069733959682, -3.277574897879558, -0.8011817350553493, -2.0539910839014652, 0.5374348441227049, -0.4387593610520923, -0.6604837058736361, -0.296851015329969, -0.8117528504891851, -1.3687764338030426, -1.304829944568833, -3.5301757014792385, 1.683607868975789, 0.9693339511502069, 0.6675190343022085, -1.2359582801633997, -0.5672254642038105, 0.30597176644383045, -0.23232747569360476, 0.28941132285637555, -1.0256262747069462, 3.1124448368923865, -1.2292586581238594, -1.2394586071726095, -1.9015532850284051, -1.0503684871742394, -4.492258214455867, 0.3087125797538213, -4.09236480981517, -3.4066558631022197, -2.22381051970158, -4.75208336803996, -5.741515157193842, 0.82600537880095, -3.3079462013730443, 0.05266723565783828, -3.44036754602484, -3.0401960318872865, -0.5295006093760564, -2.2230639919905952, -3.34297044421693, -2.0457248040510323, -4.592218293865218, -1.4094866273509525, -3.413273476590529, 0.6164097777326816, -2.262234955038187, -3.308134058768771, -4.2723800997501264, -4.902441033947757, -1.5305743950947115, -3.1425542501524215, -1.1003877927576189, -2.295380309456502, -4.018265167065584, -2.529908506025429, -2.914203905833524, -2.915208115814878, -2.6567416287728087, -1.4670349498769097, -1.9205153404202406, -2.509638220003332, -2.0008920898425218, -2.0376034378624563, -0.615689661916617, -1.6698510379779519, -0.541834199175079, 0.27973659658331734, -4.399027553960428, -2.035923839831149, -0.05305330639384197, -0.7607886189045302, 0.05531734897249066, -0.0725337862551505, 0.2074389612946993, 0.43570706564903033, -3.1971938148206087, -1.5030227702744654, 1.2277923509884525, -0.11213250988797087, 2.584577512942831, 0.6403847851725447, 0.438755262455929, 0.04134682603129315, 0.03483096722611382, 0.0241456703385117, 0.00671065601769277, 0.009799305355475407, 0.02837382494882844, 0.017971531701967594, 0.02676151907135184, 0.0025752189067604217, -0.5457327811457496, -0.8289154382545235, -1.8683629170576914, -1.760468731917346, -2.946788051117805, 0.1350229549498998, 0.7754107780213324, -1.298593456659749, -0.09110736346119143, -1.2409065411835578, 0.1433702871663451, -2.7597155966561155, -0.6059961365513187, 0.05209177107521589, -0.5573508739130448, 0.4611549675785957, 0.06025289453317137, 0.26242301731284395, -0.691237712315156, 1.9049174226203742, -0.5835533118198573, -0.2981385716790589, 0.23791472626727336, 0.9456514283715272, 0.22514862473366018, 0.4156966808683294, 1.2351106469952597, 0.60035163833642, 2.9325129074686394, 0.6451196368319828, -0.3206878560119077, 1.3607312511185283, 1.692969389990477, 1.5057880809340518, 3.246393675503256, 2.0888586989123956, 2.6120744637664375, 4.057879572650744, 2.4150230035717066, 2.251311923931914, 2.1146584579154943, 3.421524977598079, 2.0267646001347117, 4.6101959467017535, 1.5733530907899829, 3.7549056382009196, 0.9234494930986359, 4.069963949273372, 0.008979707687333721, 0.0004557985634694882, -0.0005027168931221119, -0.02005111212324908, -0.034134579859970385, -0.002659685891888413, -0.03348612974701094, 0.017311504450479305, -0.4407925512519953, -3.190887964896987, -1.0995306789514039, -1.226627394526696, -1.6117579222502518, -2.626105418749135, 0.06411995316041698, -2.664709221225742, -0.13621668433227543, -1.8811326974700175, -1.0308148037205658, -1.618975020877249, -0.12885346603165598, -2.9602037241146815, 1.0986859264084228, -3.5218480839024324, -1.7850547672967338, -0.22641673161439502, -0.8593960448241879, -0.548318391800923, -0.42923235851443353, -0.03220018481718927, -1.7831786974559194, 0.8196502072491809, 0.44767419569291333, 0.4098192992531004, -1.064174376988877, 2.2027749934779233, 0.6138389199844385, 2.602228747488555, 0.5762134500296796, 1.3099609145375295, -0.4530049767087064, 1.1548802102182014, 1.5410268714979305, -0.16336033545838985, 2.71460079083858, 2.984805009917432, 3.320974427666463, 0.46414977391512224, 0.4548255739435147, 0.6107152894247774, 2.4263935568674606, 2.07023961556909, 1.2255661271000868, 2.4409611638883986, 1.913525863190489, 0.8861250530431908, 1.9382284945719561, 2.1234311556992185, 2.0723429986538338, 1.4330098722922475, 0.47797282208480407, 2.8358432283548884, 0.7401669770669168, 3.536697521334455, -1.5198470465088683, -0.47906169966537515, -1.2428687525346638, 2.619561184829101, 0.5002140347274187, 3.1846231874359385, 1.3841636981933507, 0.9460643582042295, -2.6830722456905938, 1.4078686355561523, -1.5545651573904904, 0.3202717352776189, -0.4704275875366168, 2.997110506307691, 2.3039615465992758, 1.5550784304106708, 1.2621101536788473, -3.0212656201211523, 1.4336804378993695, -2.1382144946312094, 0.6823415179634531, 0.5625621076201984, 1.5554028167906175, 1.5119432094920902, 0.5856859473458549, 0.8113537256469925, -2.0071572068641457, 1.367572812816354, -0.23715379797830446, 2.194375778673295, -0.4841500368349954, 2.177779967583901, 1.8915878467531564, -0.018918210291717048, 0.5463558449376804, 1.317084331824439, 0.758199941461402, 0.0056515580304114235, 1.933620724873835, -0.8354673577083335, -0.6196666031433693, 2.313996898922974, 0.43912046983667125, 0.7498904265370617, 2.0262446117048443, 1.6347952589958545, 0.4645436614931433, 1.8992855366061272, 0.523851011801397, 0.06207093009015659, 1.132734865231182, 0.9269187869663134, 2.1396901120363965, 0.09864201746361781, 1.473520744949074, 2.7535348293347783, 1.3036919720784594, 0.47512603878812565, -0.0474006715204261, 1.7826796722424216, 1.4447350365281382, 0.9286224948400554, -0.23735972859205834, 3.1950362018144483, -0.5516642544638564, -3.9902791369704897, 2.4695124326170688, 0.4426946494028518, 1.4600503575511825, 0.015703600612308678, 0.8657167026054934, 1.3679824551289168, 0.6304883238339397, 1.8346746256823654, 1.3042596887083509, 1.7929430648390001, 1.8544607755850975, 0.5730670585569357, 1.4660715295279858, -1.1200165500470134, 1.7076631836955152, 1.090905437429654, 0.22129057336400706, 0.40219090434229, 1.1915194094630621, -0.5732782068056502, 2.3512954419898957, 0.7213911683654222, 0.8290410603805712, 0.5864729227543094, 1.3870123311407354, -0.38699927212771146, 2.611799262330043, 1.520735067008792, -0.3504845677305305, -1.830847446367298, 0.7929653257392204, 0.4712174051239644, 1.4726839128905373, 2.6359112531814013, 2.028775990866008, 1.2529662396826322, 1.488450606833414, 0.9507809800944738, 1.9388775047289435, 1.2740724421488967, 1.1009065803306335, 1.9530278671837797, 2.8129771171677764, 4.020817289035502, 2.867912138130114, 3.100934087454723, 1.3382761438146251, 2.18836253609637, 2.585555229583676, 2.5237809470659105, 4.179147915162354, 3.5670088452583957, 1.6541438479670678, 2.58990822207578, 2.12759126850508, 2.2022421741623743, 3.5770364918989883, 2.9426326422685167, 3.9734677938675147, 2.2836537689211642, 4.187511327868592, 3.1640608435992514, 0.7673464264263286, 1.1842652675807581, 1.3269279752124283, 1.4244637884721385, 0.9873847243332144, 1.4986075762943862, 1.9700588245730977, 3.186707317220648, 3.0587737019042893, 1.4022907765726647, 0.6074657871565263, 0.46035965237308213, 0.7729740754102697, 2.6828809210444278, 2.532647641784291, 2.144615805919435, 2.8166272638376904, 0.863536157426841, 0.719919384596524, 0.6049540027866797, 0.4473821332996635, 2.0164577534555064, -0.13980319905481756, 1.8991214857824, 2.016731560958473, 1.6964518789964822, 0.05214411542561212, 1.3315158187964782, 1.4066607989514788, 0.511031548074814, 0.8177522902071145, -1.0083883272524514, 0.26497927201073473, 1.3217444730764452, 1.1201026877790838, 0.49515188931740944, 1.826501853178797, 3.677827049447309, 0.9606673499522784, 1.1304576637557227, 2.713021116841021, 1.6719891431998077, 2.3099237423720473, 0.7889547299197689, 2.4143257913826135, 3.513191572823407, 2.9898774400020605, 2.3375332805201303, 2.0503585028621387, 3.8667003399604245, 2.281155976041291, 3.114148322517462, 2.168673827728336, 3.0563632961725427, 2.366390954314618, 5.125414169898329, 2.972883148488667, 3.664522996009649, 1.7574185575276682, 1.1663800457108984, 4.793948405185108, 2.3698402764804656, 6.820177499627594, 2.018203714990329, 2.1000279454882818, 2.3679027284185366, 1.6735540673806193, 0.3271920777541441, -0.16484905181009257, 3.1037135217513554, 4.753671719599489, 4.431394897635004, -3.112674854428567, -5.916676877421941, -4.154639468802035, -4.263109767444577, -3.1865952409399494, -1.9706848097646064, 1.7280844998015434, 1.4808624345172554, -5.28974370119605, -5.257946821841291, -1.8334672968611, -2.5094139279575183, -2.4922817037507583, -0.34810876634919463, -0.418545552310166, 1.23561517674563, -3.5123637682656375, -1.9512100885144579, -2.29350942913221, -1.4548603798944306, -0.6684858166501183, -1.4819431421392846, -0.999427390139071, -0.943318865922255, -0.6464188934540057, -0.2178808363975391, -2.4069229166671398, -1.3858399717864, -0.6497989791566586, -1.394403747505678, -1.131063108082805, 0.7388264124128737, -0.6994967731267652, -3.7003813357519078, -2.7001920715421255, -1.8264147899142176, -1.3338521901369091, -1.0883069311488014, -0.9211106781111322, 0.8430595467494585, -4.191405061837665, -4.661287319997961, -2.4326087181266693, 0.06142425680200098, -3.2474874594444585, -2.207667805267284, -0.32434912569448004, 1.636669108017157, -1.5966924156695974, -1.7964930790452704, -2.671404413908344, -1.988964813861957, -3.3019105481100826, -0.20046267546899188, -1.7251404247655813, -0.7677610888445832, -1.5515892684907986, -1.4997563108364027, -0.2270927503985711, -1.092463548733686, -1.701442512963925, 0.6060974031048912, -0.5205118450242264, -4.028917368423871 ],
				[ 0.03228229201054874, -0.030861647186756807, -0.03016463616650023, -0.01854162573912953, -0.0000700373079733171, -0.024684542197243885, -0.023658816387700878, 0.0038502459420877468, 2.1357936258010395, 3.669376265526892, -0.557686771981304, 3.071094054550512, 3.1234348446635787, 2.4853276798438175, -0.5343733735690015, 2.6996888308016174, 2.827547893119535, 1.0250952441038161, 0.9547406272086639, 1.1438727547010343, 1.5947280816414848, -0.018252751723567384, 1.2771821076819152, 3.3341133096886546, 0.4319364341256825, 0.5046398202455861, 0.17840647455313247, -0.24004020567335882, -2.784594710910504, 0.686654133378129, 1.2083073854131356, 1.509158808067649, 0.11174259996103378, -0.5513822640380905, 0.20218544984389003, -2.9902826507155136, -0.8884517721689406, -1.525534621890181, -0.2658097713231146, 0.5291718376998921, 0.8356303827116944, 0.3973284915468996, -3.3878521333463456, -2.6745481950070866, -0.43585417484311734, 1.471002750028055, 0.4952569990818712, 0.2176489824778334, 1.5144226318757734, -1.0854792272656089, -0.360153729943096, -1.4523048314883618, 0.373197168435937, 0.8202602952660222, 1.1173182974737175, -1.251842321914615, 0.014320734530341384, 0.03030095528564023, -0.01904287333495797, 0.01848118676545428, -0.012458205886102455, 0.000980375306396609, 0.03570133582699817, 0.0037980369957048062, 2.0087082131796485, 0.6214363861722938, -2.164499243377355, -0.5989122023960958, -0.2229834224725589, 2.453820185715829, 2.116048230751015, -2.3388288654738942, 1.2787107964306155, 0.8526646070524327, 0.1589561357690363, 0.05056865726630453, 1.8881529956888383, 0.6909464458353923, 2.5298384147923203, 2.33467725357905, -0.6138259101401781, -1.0202871010932912, -0.5989871283750826, 0.8936200373180251, 1.7675832535455969, 0.4124799289618098, 0.3294030768552511, 1.9849570643320207, -0.11317541024628631, 0.4688316394988958, 0.027873937432683158, 1.8932387118049625, 1.0842885334966472, -1.9280043338869641, 0.6551523236747789, -0.08087965365898465, 0.462689889032932, -0.7521295288322046, -0.38949381699006747, 0.41411855208121007, -0.25171805417061255, -0.6902822956590243, 0.6788889144137197, -0.5765010709087041, -2.7053300205669415, -0.9159350716560722, -0.9444864158674854, -2.062101123178338, -0.7254818715397455, -2.413144690785114, -0.5477941742277652, -0.45124059578853154, -4.2774014864120415, -1.0502508471167893, -1.6530546472324381, -1.3360663679253173, -0.8833795045193613, 0.4872461627804635, 0.782586028153215, -1.8459609239482346, 2.273061587183427, -2.4964848982737338, -0.3242465604835077, 0.795738290907423, -0.03157976787829224, -0.19441597596542134, -2.6579236658686565, -4.578047354294302, 1.2450686495784653, 0.14296583148328817, -1.8389904232064087, 0.4861668073819113, -0.8631712676547764, 1.7491763299416991, 1.2648023512899065, 0.7674448484466487, 1.87116079748643, 1.4028999067292307, -0.0843658816658873, 1.4081123250990555, 3.4208621417668255, -0.01993248139625966, -0.5882964937058519, 0.9153235484956505, -0.31959842252899934, 2.434184310342601, 0.8360230420522168, 3.0973478285633727, 1.156708765377009, 1.4950563516591584, 1.4178690439046095, 2.360980823119553, 1.1092137199716996, 1.3714741953533545, 1.5153313601129765, 2.6231193429209307, 1.5809471999432403, -1.7215037941165352, 2.6942641242079644, 0.2511265993887091, 0.2567201532940443, 2.2255769335900784, 1.2386565812888763, 0.5775607401614958, -0.9456593666522108, 1.6092743771102986, -0.6091828147597431, 0.20900620255198146, 1.9120789194729497, 1.2159161148022637, 3.017168968026594, -0.3784897587691499, 1.8656309446747918, 0.040764483436736, 0.7622914652168976, 1.6914680322827165, -0.10088833693450407, 3.9835794340277206, -0.008516066885685077, 0.15507936501346836, -0.14874304423139784, 1.016259163184836, 0.09023984399638592, 0.7879836042530433, 4.058026994497398, -0.37082921233401744, 1.2472732131922453, 0.8093744188876364, 2.4387044996766756, -0.19887368310517461, 0.6337960255014555, 0.09280395100209729, 1.5865545249938893, 2.1601419828821204, -0.4756883024973143, 1.5349211773639906, 0.026777965638249784, 1.448628110266801, 4.118125845476824, 3.0197041990632933, 3.413269268724095, 2.203621066764807, 2.2061210450866313, 2.9733426850761937, 0.3932195777094833, 2.373128002352333, 3.6291418512781752, 4.126788488448711, 2.889746881487737, 1.2569311924932665, 1.6376375815383413, 2.7166251876917205, 2.4030479015135953, 2.802621925966478, 3.0269613741568726, 2.056623967577964, 1.542924375057507, 1.407462568885906, 1.496254709488576, 2.8310894789699463, 3.2449565376485188, 1.7642721643060555, 1.4579400603266137, 2.125767227173462, 2.7772658137118063, 1.7686782081587926, 1.6232982301758423, -0.2506515240620195, 1.9520734912762965, 0.5347369402798572, 1.475646646162166, -0.4278799069417721, 0.27093988116712464, 0.2822771652839369, -0.011038567257507794, 3.1499604502700422, 2.454023358138569, 1.803858139418596, 1.983137547694047, -0.7117843161642492, -0.8079735689125584, -0.4177081492419682, 2.9289096833856187, 2.62248602458079, 1.350560314215091, 1.3372770704283425, 1.0923090234375643, -0.849791470220348, 0.26962284669643444, 0.6964305503756493, 1.717195482970944, 2.045370702022874, 1.163647594154898, 0.6875308841492334, 0.8483286170689034, 0.7004168538404831, 1.8180008791167466, -0.04518533942327044, -0.5821682736832517, 0.3201106371777994, -0.2978218801560064, 2.6630841350309824, -1.4349712407059816, 3.002551923601943, 1.8678014469601742, 3.049435581040792, 1.935082409088024, -0.018548879428277, 1.9804435144509454, 3.5865559770007307, 1.242653341634838, 3.6247356556392205, 2.0874045406203963, 2.5040541818238307, 2.1331901474919204, 3.0912230965448946, 2.4115626786800464, 1.7309739762139282, 2.0794239947070428, -2.5330671912351783, 2.2035551530272794, 1.9872876256315124, 1.5830505347398853, 3.5835474885526795, 2.2071850337996786, 1.9139733204507712, 2.3900127633980897, 1.3747477098971699, 1.5354598025000723, 2.3125574409299237, 1.9438074512170231, 2.5363292471476457, 1.4331659303263877, 1.1997875928045374, -0.18267656110915484, 1.6611050536247438, 1.7452542402418683, 1.2165641964617337, 3.340098843791123, 2.260024494982749, 1.5901162681063872, 0.6717060656076762, 1.1178333037164472, 1.2343684755626907, 1.7233097230178573, 2.6557265244745287, 1.8443714631011883, 1.3096444779089937, 0.5409839551980999, 0.18977778530604714, 0.4560279156959584, 0.37091436287208424, 4.172653080082941, 3.250079749660241, 3.7752677127486334, -0.06736522807066331, 0.8347652733477907, 1.319828167309094, -0.2812822738172018, 3.92729738063344, -4.148711787491649, 0.5938326297772203, 1.3531845880392976, 1.3184328420694935, -3.076844383479789, -3.11859670459456, -0.7957569231506074, -0.4655547749605135, -3.396997882869738, -0.135771381748111, -0.5914289254550276, -4.700134130348698, -4.323301046169306, -1.9115252413411636, 1.5909659832016168, 0.8131032805860852, -1.2252723808109114, -2.3233967914722915, -0.5881321665047023, -1.1856403870863783, -1.9675481107656256, -1.0277977397118252, -2.0859927044569098, -0.5797582119404223, -0.845360559270111, 0.3397462031965121, -1.2448212398821048, -2.8440384194252, -2.0944214114446558, -1.4737255829497664, -2.0449274699999576, -3.252522404956764, -2.043336349347123, 0.8450026036027284, -2.564433151307208, -2.2066279266200453, -2.7358996899417574, -1.3111470039045887, -2.0297881274835716, -3.7672959286173593, 1.8084200752073711, -3.688791750246264, -0.3205196177202566, -2.5461090637731876, -2.220522243698196, -1.0855891573032153, -1.2849292160464036, -2.6236679020179783, -1.9221758496704486, -2.218633403831699, -2.3379323340003793, -1.1253688615714499, -2.947807977412255, -1.5166320393898631, -0.4383106788041739, 0.5959380171318378, -4.884368120640419, 3.17638903474305, 2.9634219394777213, -1.7016452581430466, -1.781847826848747, -0.4402394915274488, 1.0936409008849644, 0.7895482474779939, -0.0031865640106664784, -0.006302718790730364, -0.006493103446310239, 0.032347872386280375, -0.0024641494878522375, -0.003860691871444938, 0.024750056994896186, -0.01538450907835304, 0.2801794951295981, 0.040129095727194045, -0.2571939639905777, 0.9017840870641531, -2.4870282080285704, -1.569042531939713, 0.2515238890924772, 1.6977102256452818, 0.9451060518111593, 0.04121316546486687, 0.514738626608886, 0.8972973417087544, -0.33425308102988427, -1.5247842300019692, 1.5838618598133989, 1.02660839860442, 1.5471134844812284, 1.4510320469055134, 0.4063011836257318, -0.2975272419236145, -1.891245181475529, 0.3686384062396345, 0.2870381364430119, -0.3525838011449819, 2.500760410545103, -0.20295298509623202, -0.8360098969777243, -4.698632366625694, 0.06899143524751702, 0.5714025923496187, 1.3316718206462943, -1.3869211263336523, 2.321807222458408, -0.6355255730994764, -1.1222840912082037, -0.211083343127436, -0.02371038522400952, 1.0613904275165233, -1.3894921924347612, -2.6007549607904163, -3.3233281528361984, 1.1635171954805599, -0.04007712480954721, -2.3184012606341478, -3.9301732666057734, -3.2846623501541354, 1.550860828807674, -0.47342849387190433, -0.029167569295390515, 0.0015418065017681103, 0.010995660354372262, 0.029274475419987102, 0.0006135265185164072, -0.01623057633543749, 0.03383542181428168, -0.00793340782964641, 2.8873792410227734, 1.8903686268244189, 1.894881290480865, -1.021340812787956, 1.0714897260778076, 0.5309938956990516, 0.6819610352332828, 1.723603253604188, 2.0770740609843386, 2.6966359894375307, 1.443416445692306, 0.7631497536282311, 0.8315305365724356, 0.2907031352088048, 0.21915834521549546, -0.09895522057887997, 1.7097113604987162, 0.9392606426871657, 0.5891839438625094, 0.9835853001782987, 1.3533171721324821, -0.6198027326381143, 1.6454572357595105, -0.9044340455095967, 1.8407123428211742, 1.4047301413072595, 1.0705649410488016, 1.8309927121353644, 0.9732122424552778, 1.3574408861640064, 0.23254693932824214, 0.03369706861920735, 3.8981229340507766, 1.0566469637882487, 1.7698440500162802, -2.0341965516426024, 0.8144326267507467, 0.5548292501225608, 0.044024822065477975, -0.6126126290670351, 0.8033249859754226, 2.8733287834130867, 0.2881845842342567, 0.6075290131850095, 1.3107157608915205, -0.40346240113994164, 0.9732231842379016, -1.3759814705994753, 0.2013205492213911, 1.435296018137398, 0.3345233991568525, -1.1867943973446295, -2.738068583219059, -1.186020370354034, 0.739750502642604, -1.4474040601168907, 2.4488186856459757, -1.438731130909178, 0.9044841308795275, 2.7323014680279707, -2.39493315357086, 0.8632295869338362, -0.823297021017916, -2.048118482201124, 0.21397059407905714, 0.663698198670044, 0.07346041699698175, -1.631044066053775, -1.7031924910950493, -2.5275169862984965, -1.6042304285413738, -3.0977228006852404, -2.1329257072411645, -0.44449608760251774, -2.2954666207383174, -1.0080244297350907, -2.2225597162033406, 0.11399367132669132, -4.94683093131931, -1.6501463708632, 0.5688634662530241, -1.6469743646400103, -2.0781321870415357, -2.936635415639273, -1.2323692309121612, -3.548546121670071, -2.773802835170516, -1.6325459052256595, 0.11282555106534038, -0.04480274602328233, -3.5839921280490525, -0.03623239312326006, -1.8753582352405318, -0.7007707633477149, -2.766436119435007, 0.3212600705934067, 0.46425997995140755, -1.6629225670079044, -0.5370737105669667, -2.0810028004491583, -1.6117473178415804, -2.100900641337225, -0.6994353297088566, -0.22650392915536408, 0.2251431406911691, -0.7861417824272565, -3.154274299515654, -0.8153450582061967, 0.42261206092502646, -1.0447871952505654, -1.8769462646010315, -2.080136903221119, -0.5342859337528184, -2.8766978032962025, -1.4743997833351679, -1.874192538446591, -0.5317774738472457, -2.0581051546331244, -0.34298269069224246, -1.5633723072377275, -0.738431473116431, -1.5516736451889372, -2.9646127300784344, -0.1325461926059745, 0.526937206445669, -0.5178301925947834, -6.004092507487949, -3.7728042953042538, -0.07801441846765056, 0.613842684628031, -1.453512398702855, -0.7933068022988825, -1.2483763136011463, -1.5499034007550594, 0.22370940285245908, 1.072491468230666, 0.13082027683349828, -0.0480065270797898, -1.2353539280600672, 0.26788737640513377, -1.6019355234101638, -0.9136812321790031, -1.7334233453138763, -1.1971328679247697, 1.9401021351531786, -0.26478300336678906, -0.6138866187975469, -0.9086016799592331, -1.4751636313079834, -0.8726253506606322, -2.7811337145541786, -1.4135403039471088, 0.4361591029111867, -0.2442060289292296, -1.253266262270608, -1.3967332998856758, -0.07032173015784841, -1.4713268149102388, -0.35946914929217105, -3.2882940221292127, 0.3415251906351659, -0.06142419574986, -0.42615461218165834, -0.6474346497249087, -1.1531386424292644, 0.3878285358702841, 1.0640470575107448, -0.1651212334974934, 0.04497261206937279, -1.0452154366227957, -1.734145449030451, -1.843140413921977, 0.5873253364119763, -1.260781666129924, -1.231962302673924, 0.8918994969372294, -1.0480793989103967, -1.2412933874873298, -1.8205170599644789, -0.6849067184696933, -0.8202434860229495, 1.5240699096611954, -1.9067625026700763, -4.390923098337984, -1.5800394080907962, -1.7136409594010826, -2.0896557273549305, -1.2592073640911907, -0.4111835469685345, 1.0574743646644926, -3.1167423623837958, -2.5531433878019203, -0.1784004102351789, 1.1048192489797288, -0.24686422723518295, -0.8616145920354551, 0.3317562166040433, -1.6512846085205257, -2.0388205550501604, -0.5338422939858103, 0.4949112057403959, -0.7547786437973355, -0.21298258579960241, 0.5463889312345978, -1.0843529993838725, -0.24428404839524448, -1.0157394066973409, -1.456785009548975, 1.4385015897394517, -0.03878629564650613, -0.9152902054405285, 0.6391205443791412, -0.4629890305668336, -1.100415001902319, -1.7779460933927023, -2.205921593834196, 0.5104312147203636, 2.053194982718693, 0.5061186307311942, 0.6850081744012897, 0.4527854612954911, -0.06127535212533501, -0.25102054990395745, -1.9373670696501912, -0.41142519892589263, -0.266693290381163, 1.5925485280592997, 0.16683666712879977, -1.2704656210929797, -1.14102107088866, -2.7769657507234715, -4.597236134378987, -1.2704786563575934, -2.0783273765930628, -3.1487427345597476, -0.3830406819815768, -0.3746857626041737, -0.19063866120484915, -6.605871555348482, -3.1108657023130815, -2.7150333364152326, -3.2933282466278597, -0.34859244499437797, -0.1978278879686014, 0.5301010435069918, 0.905705372726728, 2.6923005379024465, -0.7473231977558614, 0.4313790930375646, -0.7555617655470063, 0.634724340829635, 0.29075084878205365, -2.345549164274595, -5.9967475653743785, -2.22559356754297, 0.5410597613814743, -0.8194514967862472, -2.368810752666779, -0.16375491195600614, -0.1936871223110797, 0.1398913630676108, 1.1681268131373475, 0.7652518124252866, 1.230001239244594, -3.572431896396253, -1.7957290960712746, -0.7394070659550802, 0.4282688786812585, 0.3102056280872782, 0.36485651775716516, 1.1511048027029323, 0.41024657403899556, -1.0255311733020793, -2.3499488783226763, -1.1164821037830717, -0.7697183667427382, -1.979390838985926, -2.744539209166273, -0.9430669994739301, -1.7600173786872182, -1.9293987733384652, -1.5500754513610593, 0.1690845506578851, -1.755789428867333, -3.2427263641536954, -2.3082193045887562, -3.9739780967188603, -4.091085204955047, 1.0483554956565835, -1.3449753249882246, -1.1868528391572535, -3.8721321793944385, -2.0028157337212438, -1.9145052832532974, -5.317214262092959, -4.21262557174892, -1.3682525899828004, 0.5571972363365988, -3.330547200639826, -2.442756861169531, -1.8832914137150272, -5.889951364816933, -3.541125579608521, -0.3483129635384267, -0.6313336804494158, -0.5263224207036513, -0.5655192328277763, -1.9325498170951663, -0.5612201157729249, -2.404895009321423, 1.008004952230864, -3.7289697038880694, 0.6996579946645642, -3.8502821057922576, 1.9419543278056741, -2.3346444871964707, 0.647566753191799, -0.9892290249023101, -2.8483764572896653, -0.4368749876596927 ],
				[ 0.0032559102144112057, -0.02854717683311916, 0.005205317132125867, -0.0038127781870051485, -0.00609403898375036, -0.007367254971186097, 0.0048963843524456995, 0.03183982582415446, 3.3255550808442136, 1.9004535347352602, 1.35433137206445, 4.741263601891104, 3.3176637520298624, 3.021687082114945, 1.5131554005204195, 1.9640372356128126, 0.37907821018133275, 0.38097771947113207, 1.2707450219605985, 3.233898898544996, 2.122873067169644, 3.028161033672725, 2.40134802184444, 2.010787662646608, -0.20924417442357846, 0.024147515630002437, 0.9398053761884743, 0.29239817184231515, 2.9073783850008925, 1.31479961138949, 1.3758393468793482, 1.0833965119893425, -0.9392944539614634, -0.560340349208481, -0.5557896074491103, 1.0206599324916574, -1.5075597122434545, 0.5327479512032763, 0.9299655374272651, 0.15888722786820597, -0.37733398756854564, -1.0050475343277303, -0.14856504360749503, -0.7539326172648588, -1.3951287179930412, -0.8524463110215283, -0.5204565574887974, -1.0918891300162243, -0.8147948700643132, -1.2479633695249424, -1.1600698740227984, -2.074289228848829, -1.7221155240265622, -0.5628776567548566, -0.10289017454074299, -1.1800552463652396, 0.018439312880344193, -0.019273156545803218, 0.03336776649932636, -0.003487424068747607, 0.021647236900805417, 0.0011219531373778983, -0.02614650615690256, 0.0026921569246970423, 5.947496478489311, -4.184331594640806, -2.7869611964092433, 1.450868696222627, 1.3764854378475793, 2.9043732310751555, -0.6090933969964759, 4.532547916361344, 1.4995855806673193, 1.8429880121389741, -0.9725875785098945, 3.4726906047755945, 3.587436253614384, 5.015006777304256, 1.1771421016935961, 4.424293800419881, 0.028329620601161842, 0.9832332057704137, 1.1386436118102419, 2.4428222484257, 3.0283879878368123, 1.9602033044036489, 2.9206504951560475, 1.6398370234224657, -1.9120292544855217, -0.37819839867985133, 1.6590769830933239, 1.5657702611741817, 3.1201057420530307, 2.4684467928710823, 3.538440617237142, 1.4682681132238187, -0.46867905973256757, 0.5367599668593872, 0.8270615535455911, 2.0471838354453875, 2.00448416223851, 1.9649047393743595, 2.4079356652376473, 2.4457303344253813, -2.0834975070189943, -1.4493637578191443, -0.645354896301539, 0.8144817930692292, -0.45107773778889865, 0.8758342602197186, 0.4824203620064484, 1.3527615279744984, -2.6413474177968803, -2.026144535648685, -1.2867399098709011, -1.6624019206426452, -0.2355645509198335, -1.349561857385509, 1.100031384012381, -0.40365195675573756, -0.8156320514814575, -2.350839861018597, -0.8974377608824544, -0.9278762242180971, -2.982119266718505, -1.0349109491942055, 0.14672265904908785, -1.7189170186122729, 0.8891477724856942, 0.535230657250406, 2.275478094415864, 0.5143447740605787, 1.1005639376757377, 0.15863782493518438, 4.09987003475786, -0.9168442376041692, -1.4534792847283242, 0.29749759707864154, -0.5719378815209186, -0.6486963685260233, 1.9177396356460867, 3.2439724945702815, 2.637362392521165, 1.4210807980618478, -0.4500454721865759, -1.1172715563757853, -0.3035139946619174, 0.05922119527801119, 2.9951962198453903, 0.8380906243875147, 1.0111167323705175, 1.3016868821685867, -1.108368209789844, 0.8672234962087012, 0.11777272926404413, 2.3610710308097693, 1.6923525030121118, 3.334428008117857, 0.2520791350850235, 1.5040286135556462, 0.3810147363770217, -0.07634532426055338, 1.4144963812744575, 1.1789066810917257, 2.348721547712692, 0.5415093461594134, 1.5813937689697517, 0.319891795031708, -1.5727368817582645, -0.35840783957924477, -2.7537043947678694, 1.9669301426281072, -0.7064869646469778, 0.17009117724071698, -1.0182047491087818, 0.439030300264864, 0.1403741832868052, -3.63471085035397, 1.7196571143710362, -0.8768080710746676, 0.4343065778427901, -1.69936478846383, 0.5798573758389274, -4.345449676982587, -0.2766475809815644, 1.3736731067213102, -1.5068095001454005, -0.3487843727815251, -1.4553096268265662, 0.1973854984938184, 0.8019448950258116, 0.3850492941226652, 1.5329345951207551, 2.4992916362452218, 3.6151801011044706, 2.7186409496861095, 2.5363169484805295, 3.085804340012388, 3.002707024192813, 3.814479045346218, 2.762374027155989, 2.324776398551485, 2.6280004046309218, 3.0497751441300136, 3.019836099570496, 3.905883896605892, 4.2411013937598465, 3.9650722742316025, 1.055075883042147, 2.392155603461718, 2.72432647033963, 2.932956314685544, 3.3009021819894038, 4.374360997178034, 3.5029780101316037, 2.3714276403526537, -0.7077128822603611, -0.706516880847914, 0.4029323994699546, 2.688951986923889, 3.2208060726954955, 2.952536132790682, 2.7189204989270648, 2.6462142573006964, -0.43765343277093327, -1.5731309767003614, 0.5844430377951796, 0.2628078817518447, -0.5564460150709574, 2.707363414241771, 1.619201817203687, 0.681575778678642, -0.2509066040895808, -0.28352739634178703, -1.238760640139985, -0.31568871204988397, 0.09002837178485816, 1.5610303141671034, 2.085550590803059, 1.9301552859804036, 1.074830028960019, 0.4477418621283773, -0.44181655246411466, -0.6596990330110025, -0.26181043959488787, 0.4555791608804256, 1.6032898421950048, 1.9653418248629622, -0.26859184341816694, -0.35567637820573617, -0.004143387104953052, -0.008939037746646884, 0.3661285161896142, 0.20579927896460745, 0.7493020994445582, 0.6224112365065583, 2.132730116043683, 4.026110694219881, 2.4918010749331785, 5.099052445868096, 6.336066186923636, 4.635039528104151, 5.33071731526813, 5.569400163037689, 2.7661707494932153, 3.104768864027628, 3.3550252002541776, 4.636224079988443, 5.485339450213604, 4.528942662448882, 3.8510154201139772, 5.878735365474423, 1.9796610798342473, 2.224883137005877, 2.9962168977423977, 3.143441853735838, 5.575817853851169, 5.984310249366044, 5.385452833977856, 5.901805020945039, 2.248481012629376, 0.9619150691863582, 1.4267584521501862, 2.5007044735296793, 5.828523813198717, 5.777351620183172, 5.060690340024841, 4.352360771371792, 1.2879072559396003, 0.3187172962538547, 1.3256738005451079, 1.9224959367130074, 1.6394693342664355, 3.424648117943978, 2.42132850223197, 4.1191855637028745, 0.8093071541442465, 0.9184791401809297, 0.012197254396429059, 1.7162044872888196, 1.1538448163227193, 1.7738748472290893, 2.3588593202010784, 4.266677827956107, 1.3890827192415827, 0.8947895173730659, 1.5003080694422153, 0.611679322022769, 1.0259194943497798, 0.6777846748139436, -0.780071397162356, 1.3549304199825785, 0.6467246463616583, 1.894154326835937, 1.2635112612386816, 0.9693420157436642, 1.4178098525050795, 1.1048214056246242, 1.7373855125001183, 2.3806238520465617, -2.857118432073691, 0.7897528741703005, -0.3492876861730476, 0.737140600369031, -2.954559074019691, -2.7831196698327108, -1.1700934562594634, -0.5475575154801884, 0.07522234660862981, -1.7721623323718338, -0.9312175679433206, 0.4304341225305252, -1.428994793604885, -1.402672693286175, -3.0615271420177335, -2.4196357853503425, -0.5795422646374877, -2.4191204070162473, -1.5108449080921382, -1.217547850408557, -2.113426066879063, -0.5288145327347019, -1.6644914997078901, -1.5577017048653825, -1.8681737529458857, -1.792344149420646, -0.6358808730266257, -1.3489334842527436, -0.8265362154485504, -0.8734236529917773, -1.3580072117846278, -0.9329118162119199, -3.2862951274098013, 0.10655145946672015, -1.3615266335471696, -1.5642223337571315, -1.3850364323105346, -0.884626531362595, -0.2256470307381212, 0.7318649405338379, -1.9086962149694873, -2.0816744608506923, -2.7182677251688503, -1.7432016843302778, -1.064824307727539, -1.4884420690720357, -0.22020603315342827, 0.4464174822409085, -3.2278779139941243, -2.68093474101531, -2.6271268285453493, -2.513427629077158, -1.2271418783770405, -1.3688777748964993, 0.36209852703764367, 1.0370282947278389, -2.0966295065480782, -2.784397412397187, -3.6616233280811596, -1.0272104722801898, -2.0483608672367106, -1.893713518336026, -0.45623621239713297, -0.00048456726237549935, 0.017717969100978358, -0.01330314076066708, 0.006618454695470406, 0.02518020479073666, 0.017703594594592247, -0.014246737875462902, -0.014042829423442895, -0.003369816880110804, 1.1553094693854975, 1.07375590036039, -0.01710847465012235, -0.608316558716393, 0.6692878816194865, -1.4585381281989407, -1.1799750204997828, -0.8864722658014467, 1.1080844041201614, 1.5190374648621368, 1.731876748841773, 0.9840299244166651, 0.3967589208908156, -0.19818612902965332, -0.05211980765146399, -0.46713040938653067, 0.9224225840905095, 2.1432178721831123, 0.9322246967085452, 2.6989480552153498, 1.4852070266651056, 0.9737097410013745, 0.2211849530917076, 0.8152034518557134, 1.0575775980666267, 1.538278455220111, 0.8811495323075396, 2.7033827649480116, 0.9877679774547918, 0.9062166051103956, 0.7280467058355404, 0.6596855792319022, 0.8620797522540868, 2.4374180257475415, 1.7779136962296302, 1.6392678603343798, 1.0011125432029448, 1.7651831375792537, 0.033537124331727106, 1.457136857604359, -0.24588557198038893, -0.09245968797589567, -1.314115624822371, 1.9727631382449582, 1.971176285914503, -0.6490747973307207, 0.9913927589710742, -0.03493644734581052, 0.018310589835577658, -0.015336893834236275, -0.015022241499011043, -0.022312886217328794, -0.02758102250657322, -0.018346626031886228, 0.0027123555309338625, -0.0052592779094672755, 0.5498789574589129, 1.0226095034367937, 2.046255704849065, 2.2045210437317526, -1.7025283821910946, 0.45570588823262065, -0.7345547099541802, 0.0866668395534901, -0.5323040441565555, 0.37557837062810645, 0.5197538267748002, -0.45575039100920844, -0.622313737899934, -2.490645400883791, -0.7595869058451936, -1.8886893875848365, 2.3149655451953977, 0.2358685433956407, -0.2332339220764063, -2.197168225681216, -0.8446504129199978, -3.1037434032817783, -1.3042804619809507, -0.8611764226845691, 0.6259508223340228, -0.048938048809836085, -0.17092989702527878, -2.354278176518826, -0.8775578940489458, -1.4946321759880135, -1.2573821426689056, -1.4403046047085961, 1.0533530446840307, 0.833579582038417, -0.7539686931717242, -0.38491500704550285, -1.880602365133165, -0.7723507986034571, -3.4273755402632853, 0.3427986626147363, 0.3983146143503765, 0.6342586108745264, -0.15932952007720705, 0.4122461627818808, -1.1127645684693475, -3.1171333495840567, -1.2691652856767115, -3.6372452836035114, -1.1478548596863811, 0.9881269198192512, -0.04837569842704391, -1.2675881819846395, -1.8425517642095943, -4.951657046394346, -2.3210109357888795, -2.4677098090720837, 1.8680939962788667, 3.1976426485091314, 1.0797515690011963, -2.809504987521981, -0.9936789259382404, -3.6546254581220468, -3.381045707574239, 3.570029732244307, 1.6314959919177414, -0.1407083662538079, 1.1615673719596595, -0.03366734447173035, 0.7351424645854908, -0.23688499838211138, -0.530657497284563, -0.1930525815179351, 2.5477591165637334, 2.540069317423657, 0.3060735991831289, 0.8942372707049638, -1.0124415425498603, -0.07381412633770795, -0.4510141154961234, -1.6041490612045322, 1.9080284861848715, -0.0168572041730345, 1.2583246251696654, -1.0994964950652903, -0.6971371762136007, -0.8427464216069822, -2.404428175490997, 0.1881725359439465, 1.3297967284796564, 1.4870887881737216, 0.027327179265356497, -0.25576186657714756, 0.2356725369056868, -1.2737435014606333, -0.48940400157586317, -0.6025884290163558, 0.9915245507244357, -1.1732501712259935, 0.9748646327920846, 0.3782944785187417, -1.874903591003028, 0.6967172671813152, -0.7506838294783502, -0.2297205801915072, -0.9092374742929934, 0.6937823563562753, -0.21582066887220708, -0.1847305013312475, -0.6178627249443055, 0.039798694255581725, -0.2534377492668492, 1.8248553389470272, -2.442591114561283, -0.9554330509431483, -0.2547429371048085, -1.039930114371125, 0.391097657424502, 1.4523011219395265, 0.014500845740079718, -0.17625213777968976, -2.001689057473173, 1.383808902280092, 0.3954488809263067, 0.6138246577780699, -0.5769319756309244, -0.0693793294795944, 1.2084168813234166, 0.47803335131049096, 0.18650077870476034, 0.22306892629002809, 0.24300381647573593, -0.42045741955200105, 0.3581246414598012, -0.5620888518041066, -0.5939487059477356, 0.3790976999768758, 0.11256464606819934, 1.113701346756316, 0.6753090817947269, -0.6448583652254758, 0.06975866298968092, -0.9012095858183776, -1.0255285149713158, 0.061187632898008854, 0.5746414080829186, 0.8084356902194947, 1.323395791818016, 0.7556723552461094, -0.22827536498710735, 0.7028873536175042, -0.32200550214382834, 0.283241529390564, 0.48504531698606623, 0.4193557129464282, 0.8650919029190721, 0.3169977866300592, -0.7839163303060328, -0.5881030070813145, -0.2252948313490884, 1.1380880513213825, -0.22572446448582395, -0.17223986659754817, 0.3546371532869837, 0.03870796578992653, -0.561429598800143, 0.044206589454297646, -0.5740167257039341, 0.6405566993983645, 0.8605036240950764, 0.0744451272344743, 0.5873318784445226, 0.32262802172680377, -0.09853369919918693, -0.3207067922459165, -0.792711842657212, -0.28371196636125534, -0.04584837150561307, 0.8243326428363816, 0.7608195022754464, 0.03494839673550903, 0.8285810934455476, -1.1887866043857067, -0.25166184441182143, 1.1319331388677782, -0.1612977426525796, -0.7058510081280679, -0.32212874283201126, -0.252842122485352, -0.2872729156378706, -1.344781248744962, -0.7669413899223353, -1.1649628218436332, 2.578538827196175, 1.6974627254982981, 1.0599456443746875, 0.5880460733922174, 0.9950506817047016, 1.349854032052114, -1.0872934649678867, 3.149315670551037, 2.054277560865044, 0.8095249514095155, 0.31340127819362673, 0.9080452657725544, -0.16050671158535246, 0.28406946900479657, -0.8852389315873235, -0.006431862435242506, 2.052812823382152, 1.200277106370331, -0.7028151460843298, -0.47513187217983294, -1.0611678190616902, -1.535492286101839, -0.623409565333048, -3.3257939402857257, 1.150329417388944, 1.4180943102122219, 0.5225348732260415, -0.7291739138370817, 0.10713381596655412, -0.5732725628515821, -0.8438228619594339, 0.004116987804661982, 1.4245671359158312, 0.17265384335208395, 2.0973611344268974, 0.36394380153482186, -0.16883219328122862, -0.007766880403406113, -2.153188434605402, 0.7169468150728064, 0.21172337730402815, 1.6703749254136093, 0.40417432162006045, 0.40218420802148064, -1.036069775426374, -1.6489532265168216, 0.6096383760987266, -0.23322079979669622, 0.4734901852899995, 0.8515712747796836, 1.264100665261204, 1.1803651166100384, -1.5797711117822941, -0.37499270589948946, 3.576120706673112, -3.133264307315362, 1.1744945682057732, -0.2790993415812651, 1.245062066530158, -0.7115547939227542, -1.4602664819313698, -1.622476220323682, -0.850852434687725, -2.3170528757342037, -3.0641134599213538, -4.865563807701122, -1.368020469663349, -0.9477174866014028, 1.120900636104507, 0.9322038309089792, 0.48491579090635295, -0.12902535671055315, -5.510123978524969, -3.714266402481737, -2.7682831982639016, -1.3505042389350566, -0.8483395801925264, 0.703959316682878, 0.024139472734614784, 0.5082553533081086, -3.7121584124079616, -2.892668972310669, -3.271780426871106, -2.273021374138458, -0.9762473370725125, -0.04240066831478904, -0.12247854661754916, 0.2539667304716023, -4.950711696090627, -5.043944295391608, -6.478959692469044, -3.9973089970031275, -3.7826795083715132, -3.517668807887809, -1.7231082213008633, 0.4784555521480609, -2.411993616596353, -3.8412950020854337, -5.735628952354081, -6.583930893955897, -8.180731138647515, -4.140720651937889, -1.4572408831355825, -1.9152877800606658, -3.3580800086996954, -3.0667988063747917, -3.1255569618270593, -4.761940642410812, -5.567302383007435, -4.231222509464243, -4.6423271370886745, -2.290690149053848, -2.7878118542316965, -3.7198734227305694, -5.466757412153484, -4.800850287722985, -4.538692157886952, -6.716096783367972, -2.8659065649818682, 1.251911794303406, -0.441861081182076, -1.6692015822630284, 0.2578509485298643, -1.9967212637616423, -2.95338327226449, -0.11010151223644118, -1.355144551193293, -2.7091249606430994 ],
				[ -0.02629862155266669, -0.011037426191850948, 0.02646960107515723, -0.004967270410373117, 0.031588304640647, 0.012626080119671666, 0.023124998892742325, -0.017650320794025124, 4.203035445987504, 1.3549143196804943, 3.5363161188734984, -0.5853916247833952, 2.1990139955939685, 1.5071184777335211, 5.316350615749453, -0.8583250958795908, 0.8929885202171478, 1.7173976535960298, 2.800965195052499, 3.2952207653958006, 2.447625261897944, 0.9981074817540205, 2.1639782743429734, -0.13402601513054893, 1.279497985631587, 0.975400808914568, 1.6445974127307654, 1.3188343745430038, -0.1957470115700237, 2.5177598444450164, 2.1479915089247403, 0.4017723766924677, 0.3446025067326886, -0.11015589856830894, 1.6560653581223648, -1.8212281158775774, 2.1126331912299237, 1.6979591681008057, 1.7539982606722226, -0.5119541901061339, -0.3007957261543338, -0.5874216979249939, -3.258242268930233, 1.7536911570400264, 1.496476272759275, 1.1362317559794661, 0.9125198764097446, -0.7639279702710962, 0.017709082292029596, -2.933696373881651, -0.9786716630736392, 1.743669641067586, 1.8609090977503866, 0.45701794805033497, -0.5228721227943629, 1.2206587811035527, -0.027354954588038674, 0.025773749680746895, 0.007821658335229176, -0.015968778675364326, -0.0057068340317506915, -0.029987188369849642, 0.02282562705813996, -0.004875844352953058, -0.17131498021030372, 2.5678159643495184, 0.11794187060655416, 0.5062615111594907, 2.074497271433682, 3.088242269015607, 1.853900921391349, 3.24610477613421, 2.110925813407221, -0.43701665325269123, 1.9322769933748758, 0.3521117495766431, 3.0336381516526907, -0.9366000281215826, 1.887071164500947, 1.6830053902056923, -0.3081924852427642, 0.750290145375854, 2.2272152597568726, 1.1733465649261587, 2.149689936499405, 1.8235128170309043, 0.8541279733620922, 1.3471678777187066, -0.6368742979299846, 1.0369439325834433, 1.9589197339808033, 2.69291132662337, 1.4251749827242746, 1.3965734773447127, 0.6783911528832846, 1.1135170032234198, 2.234497731858295, -0.6184666800119091, 3.517291634765015, 1.9768591022746733, 2.7386844909936, -0.10450265393925359, 2.2263956942088434, 1.6247968487241184, 0.6334233489298821, 0.30876041745455796, 1.5156386473240684, 0.5390946883515354, 1.0178264292533223, 0.2112259439556003, 2.623003114260473, 0.2328917164816321, -1.1611402210960933, -0.7572195508164731, -1.0724550043372796, 0.25581089320095707, -0.09310980839592113, 0.45254375251626805, 0.030081377884913413, 2.5906383755756206, -1.5596438599123916, -0.15285984576952158, 0.44196551216109714, 0.5044491410309756, -1.0946780546330557, 0.19528109781596942, -0.39457485290307936, -1.746099573628356, -1.1480051353991256, 3.5334261574232166, -2.119977869353121, 0.47734336081906326, -3.013802219852864, -0.14227030535660715, -0.5564639939091643, -3.0004854614973073, -0.08406936682961684, 0.29159656559094543, -0.30032716822004424, -0.8428183748661898, -0.6646209358173932, -3.7977669826418077, -0.8510679774065247, -2.5713610910558367, 0.88789855858884, 1.2719497349543945, -0.3980608416139045, 0.5813033448272026, 1.214945673718671, 0.6198403295717149, -0.5864744803280761, -0.6188742211300595, 0.42005457485823416, -0.19046993992131644, 0.7577811652372497, 2.932600490662411, -0.3629544337882461, -0.7858895597222084, 0.9949762983705691, -0.126138449500223, 0.11829813812339757, 0.567278552234921, 2.0881687727879603, -0.041291411752962526, 3.115116378013511, 1.0309751560652125, -0.4399138228102755, -0.10448558987842047, -1.0342338239512605, 0.4482285325432324, 0.005047517540664627, -0.5484672711876204, 1.4217262561868156, -0.3744770677466505, 0.9228004223797983, 0.47403543981866625, -1.6011683898789926, -0.16691617084605903, -2.8986538698707514, 0.922281557429208, -0.14988702834584242, -0.5691480573278422, -0.6560408643537439, 1.4030241377000654, 3.0735060596881656, -3.9977702454673834, -0.7905235040983885, -0.6271887419161126, -0.1814528653793088, -1.453263821024885, -0.23522302751680696, 4.754863716800897, 2.0131142162494338, 1.8555864295000284, 1.2296141641297313, 2.238507108999056, 1.5693648197940835, 2.3104740721315853, 2.1175194608115397, 1.8248313058154164, 0.19668488427888045, 0.46769341444552415, 0.34964337991222966, 0.9064517639338475, 1.493778653404975, 1.8280179283332023, -0.21130092699357567, -0.23854241529650488, 1.3610522147271535, 2.097540651783236, 1.1775598349511975, 0.9166245139241442, 2.005236575925135, 0.634901303814971, 2.3171498434496316, 1.4658527475181533, 1.1071508202293774, 1.573493790039726, 1.5206632575065009, 2.642093746792747, 0.33120188028175157, 0.39216826361227597, 2.946508407013207, 2.6794032952326257, 1.349900932706449, -0.6463907861694089, 1.7964637158877932, -0.05500595897935327, 1.497056771983366, 0.6490531107894218, 0.8233523797202815, -0.3629312501547613, 3.5926628160286658, 0.5755881693973096, 1.2155292429998348, -0.1450425533043869, -0.030356598693013683, 0.46204150586770587, 0.489705936642763, 1.2072380657641582, 1.5988974213537273, -0.5432867730175633, 1.339910807339735, 0.702574426336357, -0.4793099554513872, 1.4301917740619072, 1.8766064696832598, 2.319473209791449, 1.0225807922639794, 1.5453825573452675, 1.4980397587560794, -0.044286306107237994, 0.43017138289929824, 1.3320527147059709, 1.3292824146586626, 0.24333039118437358, 1.5485143379097568, 0.8648802961297346, 0.7315470775170149, -0.4723515767150302, 0.6144706142189895, 0.019924548628967434, 0.5583420836020361, 0.9354720258681711, 2.034525487492088, -0.051092065625590266, 1.561753430479724, 0.024679471932609, 1.7586508754194798, 0.12402924620698644, 3.90839608480387, -0.7382719463791471, -0.4795545868294385, 0.3925446960634076, 1.1397476227183418, 1.615174300930612, 3.7497471658112835, -1.6511982109417347, 2.4130425019892505, -0.5929529264977171, 0.7541380991816646, 2.3733775806127815, 1.1899210043832036, 1.9209176731522764, 2.322370705628006, 1.314739897020726, 0.8161076448070103, 1.5464058808233974, 3.115222418843579, 4.534885371428469, 2.157326140488999, 1.181163024276716, 1.7238514114403676, 3.217927175087194, 2.046333374978951, 1.2985781591141727, 1.6542638571025647, 2.2926522093995585, 3.827439674563916, 0.13847388553972578, 0.2475255657513809, 1.934091835743709, 2.236582371702336, 1.1670124915914333, -0.9122805212243914, 2.372018756369805, 0.9473784442748935, -0.33660603158793057, 0.7402005317869457, 0.5841376756071313, 0.5788487764500991, 1.0541919911460405, 1.8115482281906357, 2.9362399170863323, 1.3529961637226402, 1.2757693971553863, 2.8223038606914264, 2.4821837948111365, 2.508537571801552, 2.2398575757707406, -4.69906116780712, -0.6305071586607485, -1.497812439509872, -0.7802562140486083, -0.19935920113232153, -0.09984788821061055, -1.5582754619435994, 2.6146523936044286, -1.794256933500329, 0.7423253296177081, -1.4763966940984623, -4.72605320700768, -1.513894497400035, -0.05991797110838938, -0.9671364689388549, 1.3055246553285742, -3.42254993079484, -0.8571413586038147, -4.04290222065266, -0.6217678251383938, -1.7195190206095439, -0.7922511660799874, -0.5985741423073884, 0.8304266771749343, -3.6942811373363127, -2.9532458037066216, 0.3486902466448124, 2.059522599319465, -0.056965390319041645, -0.9131312713899398, -1.9965130653835337, -1.2759154471361625, 0.39088841899327226, -2.671710230164325, 1.0937673065773246, 0.5769465064981376, 0.32317744238228363, 0.5329120998718532, 0.7608175602273846, -0.20719061856414048, -4.140699577205871, -2.2062096128441664, -0.5458119115222805, 0.055425378877211696, 0.6197008093718926, 0.4086535302514761, 0.5237575885372302, 1.665661079646921, -4.681183178933578, -2.552398569124006, -3.471405148487084, -0.021914402636135345, -0.01987168200909983, -1.9462254365008753, -0.5611498512084462, -0.30122776452902494, -6.8248080296022655, -7.844303011151296, -3.3712942183501293, -4.109634239245195, -1.1195446675890774, -1.5190962731196012, -2.3009625074202193, -0.9480188451851981, 0.016402059592513556, 0.002745761838237773, -0.01582785209458161, 0.013563048644388443, 0.010858211889175202, -0.030181464213842435, -0.012428891085825153, 0.007464365532894118, -1.4102489115253845, -0.6375074954682884, -0.7880029402995048, 1.2022730649697908, 1.4130785849116292, 0.8409324283275971, 1.2718838253604008, -0.660567624956596, -1.4350579095758524, -0.7116834039926763, 1.4545542002289533, 1.4839074711254794, 0.5983351101467604, -0.8963206368483437, -0.12303652374465776, 0.3448219670660177, -1.7426724292847489, -0.3505515702926468, 2.4615679818089533, 0.8137065770796972, 1.8313883357144851, -0.9380455615787322, -0.5889895305347556, 0.2863349982794886, -1.354191918122208, 0.5272053447562719, -1.1270354095234114, 1.2633643351580246, 2.9637801135589523, -0.20191314800252633, 0.3673852055795779, 0.6563105847014002, 0.5280032784738036, -0.7846031353148128, -1.0056208465812488, 0.9936379505045889, -0.41086167529590906, -6.019113718318234, 0.3075231707774547, 1.019957319298432, -4.699086524702089, -6.184702035965626, -2.8819803331792633, 0.09164089397089606, -0.3791434320063162, -8.656204689175503, 1.4578095333944572, 4.377994326513798, 0.01699760807715448, -0.034593121600571444, 0.029392995041186955, 0.0077168805006812835, 0.029097031691148495, -0.019171248451886162, -0.01880423760722928, -0.027702300897834313, -0.19992249007273755, 0.7295601123936057, 1.5200318944226499, -1.576721057273172, -1.837111669158663, -0.2243575544312905, -3.0958004976409597, -5.365486808011993, -0.28647582956729295, 0.9312054667130683, -1.3665626330061804, -0.6285112671737709, -0.4630616773135371, -4.188727526040467, -0.8921156493537685, -1.6782048898073696, -1.7721567693865714, 0.9300459470741574, -1.8677326803447172, 0.22410112885756742, -2.195573985669181, -0.27589257058338673, -0.5031478483674574, -2.4932353520542816, -0.08702917404617423, -0.6598051138565924, -1.2561041593363904, 1.3441230572656926, -1.4168811725878947, -2.616293233657701, -0.2706859598756734, -1.7854320650383864, 0.5442761597703516, -3.0836642221856327, 0.19459800473372182, -0.4661169685655628, -0.39338792631261693, -2.5203980902884013, -1.5433523787724883, 1.2293170543482754, 0.09233089116610362, 2.6043782486316323, -1.2815314298757774, -1.4448484759952371, -2.4040856305754086, -2.070273390267028, -1.0093647834853818, -1.4524176469117829, -2.0405127475506184, -1.7140616906829746, -0.4449266620767803, -3.0812592810926063, -2.495772484796688, -4.486176167776852, -0.7178460421347737, -4.390930920965851, 1.3440177253479784, 0.8779952252579468, -1.5496353588303269, 0.521528707138707, -2.025218014692281, 1.5161419813039518, 2.278786025196473, 0.7792805162972518, -4.583494119354596, 0.1206862929685826, -0.2995602088251806, 3.5848823831270002, 0.9963672026088058, 0.3747166822366269, 1.639866817272832, -1.8877378237966138, 0.5483022651103102, -0.38980433566594963, 0.9214846776134648, -1.2776438946457664, 1.035214208155655, -3.157063273499205, 0.6215197742629902, -0.2762722329581875, -1.486052950635627, 2.3673930198399473, -2.045102061113848, 1.9280959201809673, -0.5431182204844709, 1.765898560568084, -0.10825171570019453, 0.9517673430662905, 2.5663881611611274, -3.4865479159506463, 0.31555469916950546, 0.5861197624042673, 0.5964032650260667, -0.4044925013579255, 0.47502154810940483, 1.3153714151202387, -2.83858038215096, 0.025654598898511443, -1.119714348550904, -1.6945930742770698, -0.8073741637924071, -1.7610107871430123, -0.624494614247973, 1.8977649669408378, -0.1396974911908559, -0.0786851133000431, 0.07936595873906221, 0.16339260591036484, -0.18117493398628065, -2.2834341014932633, 1.2735105743475559, 0.9053353598851246, 0.20929652773341048, 1.277175076782005, -1.7080618555351377, 1.210908322182849, 0.3528535596047813, -1.5557349770679496, 1.2703495736158934, 0.6077674036303797, 0.09258790269877504, -4.0878167363481825, 2.145515052760416, -2.599250805047377, 1.019689195254529, -2.8741955601548987, 1.9287778081928502, -2.2971620142885083, -0.016074584640374645, 0.6919518000661999, -0.12893087517748686, 0.24169075860810804, 0.4299090229523816, -0.09607252616807768, 0.20293699109355867, -0.3995360388451597, 0.7807557279807542, 3.0332985597357487, 0.9210833424346091, 1.8247510616250877, 1.32205945004799, -0.30439584874416903, 0.3127789064384279, -1.7558731493255997, 0.18840392800002145, 1.4604538658639952, 1.0404776376236673, 0.967682479774943, 1.3501998553595416, 1.2826757497778802, -1.0000336586714227, 0.43002782844228943, 0.5375359955218479, 1.9245101387023131, 1.0758106033035852, 0.043683436887251154, 1.0528612131448811, 0.9410426274386257, -0.39478542676141876, 0.2615978973250913, 0.3480351738749883, 1.424849255971035, 0.02366764256927476, -1.0773854194450578, -0.18111952948522578, -1.5240228205892272, 1.243624098162773, 1.014761821909094, 0.6385631587392459, 0.3689215408510538, -0.31492475538435954, -0.056282516021442984, -0.468684432076697, 0.5036832830800495, -2.490025862132363, -0.8838799222881688, 1.5777261606319983, 1.7041022450340209, 0.28464375777210627, 0.6821821455229506, -0.8907378860143181, -2.4038986320308804, 1.735871537246552, -0.04094927951327319, -0.18030594744681316, 1.3272781275464574, 0.692220176261574, 0.36355650770270326, -0.832722978514585, 1.168394837217585, 1.2835315003811654, -0.7927703522780402, 1.3902721040452741, -0.4380270804024442, 0.3580367033173899, -0.21393554753263958, -1.0261823383986546, 0.42961252212174644, -1.5909737342073564, -3.071268053506007, -0.9939549104415099, 0.0625907517567341, 0.6553855029149553, -0.2599055421075284, -0.30810019077828543, 0.19479783095808856, -1.6483352842370385, -2.6299555512798602, -0.4192408358797396, 1.383146388516032, 0.6742269702045361, -0.9592404405836624, -1.3007033180301462, 0.8613205863189168, -0.01762784059918373, -1.000738483542256, -0.03897120674889184, -0.5362791944583303, -1.2842423500212565, 1.4121550690504614, -0.30493670791148947, -0.1668792975224613, -1.5975629540023542, 0.3283447013043329, -0.5394517666365349, 0.7463571840604419, 1.9285659866833817, -0.9900490702728415, -1.6981339688579131, -3.505629632333951, -2.200903825460452, -2.1649157760398143, 2.456192966655174, 1.292264938249956, 0.9241208850804409, 2.2528723174550147, -1.9110025588379744, -3.3506333598806273, -5.900320067807815, 1.6105225739174092, 0.16858170941923264, -0.6695994209504711, -0.09794865112501738, 1.3826358319800987, -5.142914568671501, -4.406371977929313, -2.0108098169908915, -0.35515397836737767, 0.5286290305340258, 0.3767768278909037, -2.7014849855099223, -4.088089593603744, -2.479823051349437, -1.1504288110283523, -5.3522069951758136, -3.6788858753537896, -0.2307476164898425, 2.0115799290093794, 1.9700479833672593, 1.1379534297348175, -2.216992162678394, -0.48110382553311165, -1.1075632637517412, -0.29960354202503675, -2.3898602782775074, 1.3669050933042002, -1.6237245118557058, 0.0639888609735481, -1.3364180315145477, -1.2862259914695815, -1.5749186270899114, -0.9355386369539377, -0.5158323458702146, -1.1410917416716875, -2.3335046065122174, -1.9130216122896817, -3.6824502403372876, -1.8656850190398135, -0.48224617301414846, -1.125947766922943, -0.6003480499052751, -2.9327786891105623, -3.9209996483933858, -3.9718720160991468, -3.891423541985092, -1.9293930867496216, -2.9695860958097877, -1.269615648128752, 0.2691782698554582, 1.6213158249528172, -3.891741660171112, -5.794599490183529, -4.374814715314175, -2.9147163299967493, -3.108024287318383, -1.7697938287158639, -4.180527123702283, -4.266324180122502, -6.314106632045991, -0.7604313772592729, -4.050565323355042, -3.365743775301446, -0.7303852849109486, -0.8381448928007854, 0.271906716483497, 2.452930452494407, -3.574990787613828, 0.9150829645385103, -1.4959189819259062, -0.346203119843106, -1.9932908637163405, 1.2361987419881868, -0.2653343528028069, 0.13865408823143255, 2.814207425531886, 1.303300147537327, -2.055885267309579, 2.4859057436435266, 1.3055033448880402, -0.5652936150013748 ]
			],
			[
				[ 7.768978617515657, -11.611925491989432, 3.9441738871527687, 4.575165177736265, -3.3905201607118927, 4.9737676333282606, 13.62844906950327, -3.6544576791639924, -5.858902293789134, -4.983334886709058, -3.44057538970242, -7.61763902253803, -4.827469992529991, 3.952820198071656, 7.431459595356849, 3.778352844608216 ]
			]
		],
		biases: [
			[ -3.5704263896697737, -2.7846996292325232, -2.622184017153904, 1.3496171160695885, 1.8679942289640155, -2.3205661176809835, -1.8803239356195105, -2.353651271910541, -1.2724667051168264, -2.8969126345149547, -3.1772295308342997, -3.2767366336512556, -2.3397834187873325, -1.1224404425735584, -3.6588433552593305, -3.8889601555899493 ],
			[ 0.4442137605657864 ]
		],
		activations: [ 'relu', 'chess' ]
	};
