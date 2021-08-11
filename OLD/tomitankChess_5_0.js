/*
 tomitankChess 5.0 Copyright (C) 2017-2021 Tamas Kuzmics - tomitank
 Mail: tanky.hu@gmail.com
 Date: 2021.01.18.

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
var VERSION         = '5.0';
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
					if (move == NOMOVE) move = hash_move[entry];
					update = entry;
					break;
				}

				if (hash_move[entry] == NOMOVE) { // fill entry with move!
					hash_move[entry] = move;
				}

				hash_date[entry] = HashDate; // update age of deeper entry!

				return;
			}

			var age = (HashDate - hash_date[entry]) * 64 + 64 - hash_depth[entry];
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

		var bestScore = -INFINITE;

		if (depth == DEPTH_ZERO) { // Atultetesi tabla

			var hashData = ProbeHash();

			if (hashData != NOMOVE) {

				bestScore = inCheck ? -INFINITE : hashData.eval;

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

		if (!inCheck && bestScore == -INFINITE) { // Ertekeles
			bestScore = Evaluation();
		}

		if (!inCheck && bestScore >= beta) { // Biztos vagas
			return bestScore;
		}

		if (!inCheck && bestScore > alpha) { // Friss alpha
			alpha = bestScore;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var is_pv = (beta != alpha + 1);
		var newPv = new Array(MaxDepth);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

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
						return score;
					}
					alpha = score;
				}
			}
		}

		if (inCheck && score == -INFINITE) { // Matt
			return -INFINITE + BoardPly;
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

		if (!is_pv && hashData != NOMOVE) {

			staticEval = hashData.eval;

			if (hashData.depth >= depth) {

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
				if (score < beta) return score;
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

						StoreHash(currentMove, score, staticEval, FLAG_LOWER, depth);

						return score;
					}
					alpha = score;
					bestMove = currentMove;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (legalMove == 0)
		{
			// console.log(inCheck ? 'MATT' : 'PATT');
			// postMessage(['Redraw', CHESS_BOARD]);
			// for (var index = 0; index < 1000000000; index++);

			return inCheck ? -INFINITE + BoardPly : 0; // Matt : patt
		}

		if (alpha != oldAlpha) {
			StoreHash(bestMove, bestScore, staticEval, FLAG_EXACT, depth);
		} else {
			StoreHash(bestMove, bestScore, staticEval, FLAG_UPPER, depth);
		}

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
		process.stdin.on('readable', function() {
			onMessage({ data: process.stdin.read() });
			process.stdin.resume();
		});
		process.stdin.on('end', function() {
			process.exit();
		});

	} else if (typeof lastMessage != 'undefined') { // JSUCI

		UI_HOST = HOST_JSUCI;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	var uci_options = { 'Hash' : '32' };

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
			var msgList = command.data.split('\n');

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
						sendMessage('option name Hash type spin default 32 min 1 max 512');
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
		msg += Letters[TableFiles[to]-1]+''+TableRanks[to]; // Ahova

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
			EN_PASSANT = parseInt(SQUARES[Fen[3].toUpperCase()]); // En Passant
		}

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
				[ -0.030666506856677805, -0.015427814636002705, -0.0037019363210076634, -0.013386930509821147, -0.03351842027894505, -0.02091936296970029, 0.005642947217503935, 0.000953572401049094, 0.1527980109600545, 1.751118772638467, 0.38204047224251597, 1.3787394054723197, -0.7408438001021174, -2.6208452170635947, -0.020258792022411223, 1.3121677152216593, 2.732998888010984, 0.8697712327048394, 1.6321251097851166, 0.23860240034280134, 0.38136294725218106, -0.13485947451652808, 1.6474510211804063, 1.6935497358401779, 2.6865006124903203, 0.8985896318171263, 2.3957168280645758, 2.086989386689752, -0.6639849411333062, 1.2156882269989406, 2.614914629623438, 0.35461034859936114, 1.9202644297768499, 2.142747233655469, 1.733400309139178, 1.3138232299739965, -0.1168433201808002, 0.6257175480907611, 1.997833003754124, 1.8412140447326464, 1.9600217995381162, 2.496985108537394, 1.6314166497340499, -2.3861136844709563, 2.1997251039703025, 1.4191890809483587, 2.116114772314201, 1.2392716441602796, 2.840989029356953, 2.5840632336091884, 0.8117443858927617, 3.1973018243952738, 2.0771665023564356, 2.0618205938260217, 1.6136745816340115, 1.383312129712791, -0.03184650448429738, 0.02935784739225374, 0.01591983538766076, 0.030621171201350793, 0.014880632574248967, -0.008512112729992673, 0.023760210508967594, -0.019762333187766067, -3.1140476438130618, 2.5189868567590032, 1.4040527699566585, 1.9841848207008845, -2.1033497611612404, 0.9015475034915458, 0.1733586957981756, 0.3352540123022506, 0.5783146881386978, 1.2997705099031496, 1.8552846501247924, -2.768961100312836, 0.6309981953864326, -2.1125354825910474, 2.005101015430829, 0.0381031501878219, 0.6634426690427134, 2.4233817030841265, 0.35954478468088524, 1.1873029411190794, -0.738534108357668, 0.43584418806926833, 0.8879275889971036, -0.3387775099323684, 2.5432282592651787, 0.8276494831641956, -0.024878371235362955, 1.8420280459342, -1.7271427075096886, 0.36597756810783144, -1.851144057158375, 0.7229761153982762, 1.6937158642659695, 0.6738349349685697, 0.14649276197909325, -0.6301895816799006, 0.14704246962136644, -0.011598178400006579, 1.3057546625850742, 0.2989405547016704, 0.3044531348592738, -0.2057139169443623, 1.7166426996258222, -0.26955705154164594, 0.94184858912748, -1.8279226610456976, 0.8639300517483494, 0.9507469035141836, 1.9231751239676365, 2.3745558096117705, -0.48578168800431115, 0.05268328570618271, 0.5901752182710513, 1.7446601340903265, 1.1981345282806053, 0.2873242697439492, -0.10804430267694741, 1.0703382157908474, 0.47522921959433584, 2.755186234106666, 0.5631199039477934, 2.2660499040031903, -2.068247709149614, 0.9377954818796468, -1.2097416177273408, 0.00617714842852833, -2.9081046889495736, -0.13617457675764966, -0.24185819843071849, -1.51213419206192, 0.1700298301983987, -1.3776931615407144, 2.4912071814245884, -0.99489194012343, 1.0360258646488978, 1.3243293763523571, -1.1567299499127175, -1.4134076290446502, -1.919380485567556, 1.8669581761733693, 0.7070937296235001, 0.28093972668048284, 1.4858868843922468, 0.8492152710819851, 1.0337355137515372, -0.20416563417112032, -0.501490780691522, 0.6950814842653606, 0.0902241516693924, 1.2201634835322785, -0.037771765312182556, 1.563705810202678, -1.064485572484336, -0.969879541193352, 0.26883572277266754, 0.05256144200965937, 0.6477873225497959, -0.6597637653280284, 1.6367920653199526, -0.4181259784744577, -1.3574045361172846, -0.7821958423706487, -0.2500499337055664, 1.6373585345694404, 0.18445421927463823, 1.851989218367404, 1.5108498712393121, -0.9372810921630973, -0.40843688293023017, 0.052315676871005724, 0.986568763196177, 1.6605412993556632, -1.8604877013965733, 0.930313871308159, 1.8508072899772443, -2.0193953443835313, 1.7525886181874755, -0.24430571698056733, 0.6156520879081049, 3.181330280973116, 1.7653871432292758, 2.7800650193272527, -0.6637021583714997, 2.3531223927938654, 0.9349115042149793, 0.4606049349214769, -0.21929621941450736, 0.2795230822427973, 0.6729035941450229, 1.3226126980828479, -1.7351808255131012, -1.0992929444434971, -0.03489721316229876, -1.3552900748092713, -0.11533302772388541, -0.5000460725759974, 2.7953163282097866, 1.1415303889717983, 1.1823889300931245, -0.23047692643712633, 0.10499173366758865, 1.0389085022071791, 0.232907017536432, 2.0418851871588637, 2.601863087041048, 1.2601627392382988, 0.46070886627417273, 0.6933946161222756, 1.969684379076808, 1.3591635808914075, 2.551203000156736, 1.0237291759117408, 2.024079093293132, 1.8638699272537451, 0.36418648626412925, 0.31567862678897174, 1.7174499076901517, 0.7012514634713887, 0.590557268811072, 0.2078161982371563, 2.2324896334658306, 1.5385947742052197, 1.6868759349132454, 1.2949359987983886, 0.3314708603296818, 1.1481836580033165, 0.2724111556715917, 1.112268907507017, 1.3033420521984727, -0.1683955096451407, 1.4973219597999727, 2.169700065286808, 1.9573500724690784, -0.19848208083051366, -0.22497748813940252, 0.6753943090248217, 0.3016705022816311, 0.1771109167123463, 1.602904439443177, 2.6819105364344473, 0.18254976495705402, -1.2823505270654376, 0.07458868496650364, -1.6728228330955903, 0.4918301917351558, 0.6366328810357526, 0.4487734758475401, 1.121125638584178, -0.0790653916820312, -0.5399328543326379, 0.7063196141365364, 1.050497922797646, -1.590231507604023, -1.3586298302397464, -2.0158286685201863, 0.6213305373520999, -2.3917267636248165, -4.220867924241833, -0.7613758333947378, -0.07007870323457156, -2.1059115797890184, -3.7576773154343135, -0.15101146144226996, -2.1501456280166678, -1.349119895008727, -2.4608786521633834, 2.1618340285231152, -0.20843084879561377, -1.2877906781084303, -2.18362792546395, -1.6058580302034733, -1.4353585825851634, -2.9540493756203907, 1.6251429774230108, 1.4660385919434493, -1.0875709068999762, -0.41519390575530346, -0.8247846044763607, -0.32855233424416064, 0.14457539134576178, -0.9598693049624502, -1.4185394294262945, -0.48714984012730433, 0.16175188575772534, -0.6729950576603566, 1.4661151896226157, 1.4682199928008988, 2.224845311754011, -0.9247213079906543, -1.7303807077213282, -0.2934499316381469, 0.4649167956648614, -0.4128878896691262, 1.1563696917033435, 1.457884674220061, 1.7722012706171275, 0.1380414640727221, -0.3498210498065823, -1.9049117785358698, -2.4977952144483817, -0.8989104194485479, 1.8608369553636672, -0.13341924808216094, -0.6109654441339243, -0.20318495091301997, -1.1224637928724366, 1.205360968866549, -0.19875301327348655, 1.0326640450353712, 0.9454076449686208, 0.8899888961401691, -1.4609632948583409, -1.0170853269162132, 0.29702732664622566, -0.599950876109598, 0.12713454041307862, -2.057358513057758, 0.4241950733314595, 0.7968398499809692, 1.9067778798973327, -2.1241531430032574, -0.1261933082154065, -1.5017455438090899, 1.4623889920299795, -2.128079364075726, 1.381746258284446, 1.3235069995208957, 0.3876429924931085, -0.2109771891642076, -0.8346625556009133, 1.5457565977812815, 1.2191334373101799, 1.5859585672877834, 1.9129873189746371, 2.3774161454943576, 1.2423462727872372, 0.687995584777383, 0.21688789925444782, 0.9749661726103318, 0.8187492877709608, 2.6258694411303116, 1.4597882779703728, 2.385205449941638, 0.6600948596780709, 0.22351889438559527, -0.22301705679118, 0.03262700014128442, -0.4854887004372749, 0.5652969767208259, 1.4270637754170528, -0.1441230827646649, 0.7299658076217335, -0.5597193021614437, -0.19161973680598232, -1.2242323869641583, 0.9481998246674915, 1.5245558004539117, 0.7399386334705867, -0.2255186243632788, -0.3305956873609669, -0.44377180992179666, -0.7817579838557662, -1.4150002972979354, -3.289298907932717, 0.2098975904312385, -0.026356051582343522, 0.4553548724432358, 0.21956282206233538, 0.1958402331609755, -0.06022346742397229, -1.5766831295751462, -3.0692441924358724, 0.4031364245252999, 1.9051951013914812, 2.860275497733861, -1.3743298675865316, 0.051746985297128296, 0.7873262790218817, -1.9834923512471339, -2.8020450265319736, -0.03554876671155944, -0.01966063444490774, 0.03503480172119237, 0.024786732400966637, -0.006067101375317126, 0.006286539119910375, -0.0008323504591213258, -0.021883644324536766, -1.30846459514231, -0.025282501053167736, -2.3867088091937596, 1.5803370209509333, -1.7658615869699774, 0.5953456932619015, -0.46556099744335233, -1.4675827419392755, -0.37996447715785214, 0.14859267682532856, -1.5280486967799234, -0.10344825638835387, -0.9903043494784742, 0.02021509383711329, -1.2200218124523508, -0.9801769736421686, -0.1523361947061184, -0.029073737942145666, 0.5244371405553525, -1.3490604327091456, -1.8748362691357034, -0.7828153733908189, -1.4998611497581875, -1.1581243390706453, 0.09288480245405312, -0.8664373964693814, -0.8131674259411964, -8.587453973488627, -0.14686227644885327, -2.3161106866924364, 2.0887858700143913, -2.0409439707450594, 3.392040491406219, -2.703515839676009, -0.46771692040364465, -2.4639615740271332, -1.1115081777845977, -0.4623761311385865, -3.0453422674988446, -3.2653129393133957, 2.193463346706766, -1.1837623474528522, -1.2000717712111975, -2.9715688923978965, -3.1245804102744574, -0.8065164925797079, -0.4464606318034451, -1.314902842996063, -0.02227448120112922, -0.022766014749712998, 0.026294445621743847, 0.024654553115117706, -0.03332654877381195, 0.028769837588912228, -0.01068599610825225, 0.018129670822630204, -1.4665561187325187, 0.1902875241550248, -0.7108999861406127, -1.1939091451308153, -0.5022880620939849, -1.7556008817082511, -0.243558715219035, 1.9598904165033306, 0.21334605058123257, -1.5599101532301713, -1.2651905877241607, -1.0437403197673507, -0.4313649301510806, -0.5118198965931698, -2.279994909763051, -0.8081365957801458, -1.227674257553899, -0.7942493178852518, 0.12635942974534686, -0.3010341213674791, 1.1869754850858978, -0.4816791447551515, -0.45192388352371854, -2.7581477402234134, -2.7189549656834755, -0.5401315568829548, 1.3083675087825302, 1.4055452258674854, 1.2698302822997776, 1.3981013262520163, -1.0331897899571783, -1.2044707862739836, 0.7339267830184691, -0.3248600414395912, 0.38089062287275877, -0.763954657812391, 1.0736378463866523, 0.6237853461404438, 0.9000726781163875, 0.4016883557324259, -0.7540245743437314, 1.4306218783318128, 0.10771935213657605, 0.10807453453833664, 0.7015789969844877, -3.11782105445589, -0.24574167571409958, -3.896700373652439, -1.3292624057389593, -0.44317082322803236, -1.3253559135284327, -2.5192364802858593, 0.4140854169389901, 0.24687400546544627, 0.9286491141176607, -1.1952268914957476, -0.45321634152517914, -1.626101866602137, 0.15535581695534567, 0.15386662248934674, -2.0767491661906003, 0.08684161746815575, -0.8456038016852019, 2.1982511059861656, 0.40873012427197514, -1.9050575728801193, -1.3672911059061734, -1.8406479023144806, -0.3297263118675152, -2.352044651270638, 0.789582444283228, -4.151731213354011, -3.628043601372208, -1.0331210783926335, -0.521493594388906, -2.437494689503187, -1.0515855243491592, -0.44679056276887497, -2.96460953480603, -0.07132719784070461, -3.1129278312474424, -0.0030957701582423067, -2.3035996442521802, -0.3634272037414819, -0.6924065359012306, -1.9837881937950972, -0.6738243471820669, -0.39714401803322547, -1.3074011372443122, -1.6390126532752138, -2.890706717097593, 0.31522674451920424, -1.9983180082090346, 0.9927320418256986, -2.210898321562384, -0.6545360679196228, 0.1409277192345097, -1.7397853199707318, -1.2827486562636676, -0.07225532280360286, -1.4270698407079374, -4.125704453677818, -2.420710760000335, -0.694495807049028, 0.5118073911638608, -1.4141300787132842, -0.8029665095295828, -0.8371192784078287, -4.713143398995365, -1.540337159546636, -4.066652748867664, -2.6958094107557278, 0.24682300880413544, -0.5677507565014336, -1.8263314939114181, -2.4098688425023678, -5.000889049380996, -1.5909972420779128, -1.228227878744752, -0.051773368412877024, 0.13851018109248026, -4.702065627793615, -0.7381806393471567, -2.4873849137323853, -3.199769586841267, -3.2779430926410216, -3.291650843372418, -2.2343628945782297, -0.4800729211803348, -0.6613993191721923, -0.8798336834255109, -0.9157857142834145, -0.8711084317096434, -0.7103918302465274, 1.409976544437208, -1.3287997137212584, -0.7348976697778278, -1.35619182812598, -1.2456147804491229, -0.031478968614138056, -0.8319098230993088, -0.7960379583403241, -0.1426041566362813, -1.1878511931727977, -0.483071023258526, -2.012752080499617, -1.4324102192073134, -0.7326478128040853, -1.1545606615196786, 1.0242287375946106, -0.8474737682630705, -0.4675396881761108, -0.06204143088106864, -0.656150115234383, -0.52973177404865, 0.005704312349218602, -0.9147538550739529, -0.40724117241572333, 1.7400576524757687, -1.1832772120207191, -1.5057768995218308, -1.4156424476427476, 0.27116222562177605, -1.8900677524794536, -1.1633293289662527, -1.2745021469198516, -0.3287244889422508, 0.3676881426929818, -0.4454876313082624, -1.2962681694399572, -1.6453605739881079, -1.789822736347862, -2.4786950484687593, -0.27437702208368053, -0.11750946740062401, -0.35195821646791015, -1.0084288686596323, -1.099362304701032, -1.059756972606549, -0.31729374593233817, -0.7372623256345943, -1.0247142722048987, 0.0957531122055908, 0.12675793546137343, -1.2003301033569147, -0.9554065127620479, -1.280292041536934, -1.9359211358727433, -2.661450661513348, -1.092050341064841, -0.7291610922311502, -1.4689301643775032, -1.2513109589833846, -0.5826707872842042, -0.4014881682129189, 0.03691704379336821, -1.5360423555989122, -0.3582696579225267, -0.4893719309145344, -1.6929963667931123, -0.5517240641534309, -0.8081580131430413, -0.25346308044898636, -0.2540594222823009, -1.7274562345169235, -0.8803465604273889, -2.27644776020555, -0.20284207813568586, 0.09938310192077092, 0.20798763222874866, -0.13958942342508762, -0.27290775919776855, -1.4207911354609706, -0.19456993069135786, -2.4631245126716683, 0.2581285775266374, -0.13020581199939518, 0.8865204409728976, -0.8753290755227328, -2.1050039521547497, -2.3734920069320835, -1.8393362248251854, -2.4009849979332003, -1.0972221781263183, -2.347002102640318, -1.9650562629365331, -1.8410519921100985, -2.3135485785476253, -1.31973811414124, -0.9922461644063963, -1.50489019780431, -1.6500640057727773, -3.9533524163614433, -2.631011135938075, -1.320166414837251, 0.5782172502043968, -2.779788938038292, -1.0748591091389272, -5.23404225191031, -0.9528535595790435, -3.6123176205208734, -2.5716868675734483, -3.1512547200667025, -0.8660238178620292, 1.5690770568105084, -1.0938722808244152, -1.8769269760807672, -1.5876607285090005, -0.5883913230119923, -3.6094284252452487, -3.224350946242109, -1.667052764365135, -0.8138817889754261, -2.608187046765343, -2.6411848263443494, -5.805364010131341, -1.0127813979949598, -3.6294804031424492, -2.263937849799161, -0.67687103656734, -0.5516156106357926, -0.2019338843500758, -0.6462474201266103, -0.09672822505856053, 1.0066223614629324, 0.15448744623058608, 0.6949884072256665, 0.5116977827345354, -0.8199537774068438, 0.39068676123880003, -0.7845337737049404, 0.8106604780589448, -1.1124848172387631, 0.9696115594144953, -0.12455528183431139, 0.7733542824522219, 0.4100965205900228, -1.1295092312634314, 0.4071703100850803, 0.6323436799344945, 0.3633701059348269, -4.701740123432639, 0.3316750541682305, 0.7555738164746071, -1.2646713209365845, -0.12207662306869345, -0.30007917781579624, -0.8009766665448033, -0.46965503204948184, -0.398619360996664, -1.9632510230743563, -0.5255517267221294, -0.7178885680100485, -0.6932871565676841, -1.661751268264686, -0.29834090353434733, -2.0082721884342645, 0.9509706052728457, 0.7258025783445613, -1.6167305373830458, -0.5237424205450648, -4.953829315650549, -2.469855103036081, 0.04110454147904901, 1.7231543952698956, 1.7386078838437624, 1.372722730503687, 0.5532892627230488, -1.862013292280396, -0.8699068611325027, -0.4219709433696412, -2.613231563089589, 2.865822011263273, 1.0506791253077477, -1.6408832127224735, -1.1734038214399736, 1.253852977951363, 2.4659639271206673, 1.2618269760529839, -1.424872812522076 ],
				[ 0.027061169228570166, 0.03262700979158165, -0.010453312697263229, -0.010620227671070646, 0.009775246575989128, 0.02883362414330776, 0.006302321211195335, 0.020334915318106106, 3.726080751709374, -1.667877195186307, -0.20375255185896662, -2.118073669280492, 2.7372133466505213, 0.6664659075065459, -0.03735850870484367, -2.6916863217522367, 0.07555500172342491, -2.3278711259618508, 1.8982277758101995, -0.6120526156603501, 0.23468853657778324, 2.818524711494345, 1.9258027671773483, -0.39308279940583274, -0.6099491598135416, 0.5276752181643297, -0.49934423057698507, 0.40147195839763916, 1.3117494983264595, 0.3686713594315349, -0.0604700239624989, 0.7062308318367148, 0.3955614815052067, -0.15115559110004234, -0.3200207512023458, -0.032658791315546117, 0.23346625115454028, 0.41370096200468637, 0.1443353990109378, -1.4603843478919512, -0.7845138574119388, -0.7393029649882717, -0.5122655085902226, -0.017516911944147964, -1.5292693836348186, -0.8726496636017214, -0.2555905952219063, -1.8089120604345221, 0.12054568810286964, -0.9853331616789853, 0.17145831213989887, -2.2250916494905866, -2.632309114828651, 0.004497903586906153, -1.6457063835397558, 0.06573935266422205, -0.035324741780342374, -0.008379885356772959, 0.014956137647378182, -0.004448560664022597, 0.021429354879301747, -0.010770132622042383, -0.033061066894154126, -0.02761532131862465, -1.5558601259704647, 0.9214046190517438, -0.8233572247242705, -1.72057120508161, 0.9341679160273342, 0.35208596136891956, -0.2779931603852344, 3.3196046718278502, 4.632331594585384, -1.161579234657307, -1.3983900908386975, -0.4464245874528866, 1.027742122298463, -0.4145773420587159, 2.473925157355144, 1.5681880853015924, -1.7618968666220445, -2.9842462750620826, 1.4545015227139513, -0.7254440271818889, 2.1721805959607994, 2.603474774721454, 0.018358186842216823, -0.009839620268496286, -2.179766387962875, -0.35715595641528475, 0.13738770322155222, 0.3356210552201745, -1.079026584402625, 1.3344578394878068, 1.3280270766188875, 0.4752544868413023, 0.8178020397862936, -0.49659913973656494, 0.7482538731842997, 1.0372730012556461, 0.4204497674864621, -0.8912829678497811, 2.4711613100636134, 2.276949922090525, 0.8068275422517924, -0.9173327070518785, -0.6736771690890396, 1.119951842559315, 0.8151399013266314, 0.45315057243568574, 3.5116782392604375, 1.9004973712012578, -2.6109949590358967, -3.613021204958466, -0.22567555778011836, -0.11863393899689217, -0.0859588142018888, 1.6967268871503585, 2.952529126213116, 1.6143025443257277, -2.57320893713263, -0.18090389204542365, -0.2523185996516306, -1.4367955192563826, -0.1391596655053431, 2.4678372978900036, 0.8496763479615979, 2.3477426812436915, 1.5081271142807353, 3.3770482875178547, -0.44594267862017267, 0.2967605987881279, 0.42169450437687656, -0.05464282812800035, 4.463189389605421, 0.007063878519205588, -0.03508609495136048, -0.8012711804738938, -0.8700299374518717, -0.3951686426709403, 0.08472283769838498, 2.2550025239326055, -0.9404959762549672, 0.5767321500868257, -4.525048779814027, -2.7741101119523814, -0.3150869930430525, 0.929528961475482, 3.6098881449854163, 1.0552311463292514, 1.1277992096561391, -2.2256709927082152, -1.8772844231322106, 2.43162379138018, -0.2982917909640884, 3.0887252645657646, -2.055699039363755, -1.3365865569244182, 0.7277733820932241, 0.25224517446132044, 0.6853039049019588, -0.0776944061747102, 1.190091485662479, -0.4063902397386253, 0.9753745757750649, -1.1339293774401424, -0.21049434856347113, -1.1802129716484873, -0.16958500636351567, 0.2767087090450426, -1.595009885308904, 1.8013764140499982, -0.2653190785805312, -1.0514118438675173, 0.9512885472981903, 1.4256280820885123, -0.7753534068063366, -1.5302782336147527, -0.0898668076329559, -0.03247856199104411, 0.16698881505680566, 0.2614411003874933, 0.25389875072955215, 1.576536910876995, 2.3081873820110155, 1.7415461243100558, -0.15863347436956227, 1.3195889252268467, -1.1601881643454275, 1.4181426473485952, 1.9394693401778955, 1.6638076344225547, 2.0769281878157053, 0.8935784327894096, 1.2230711910798702, 0.30779293643589173, 1.6052475709011356, 2.8322725980790233, 2.7466532517105207, 2.8889086895613474, 0.21054277027878116, 0.14220998765572251, 0.42475421440168715, 0.25306286770746134, 0.4786662261208616, 1.7043664417976232, -2.1470252720448837, 2.866120748299221, -2.0351455372902585, 1.4845586615764266, -0.22373249545426835, 1.655244010523116, 0.3399289498824161, 1.5683065007037722, 1.859633799296694, 1.1454310487181518, -0.5026633076238989, 0.22720773490245164, -2.22199487948076, 0.9004166669282814, -0.7497086341659086, 1.4355770212498482, 1.2963047072133072, 1.2128081253337366, -0.9329440553479245, -1.6059018103439795, 0.4042847251938605, 0.5379913779550721, 1.1815929129383078, -1.0706555989615127, 1.4828293674379562, 0.06164787569509576, 1.4326121300256842, -0.5566342978013785, -1.6091298777099736, -1.571433172090088, 0.5833389301807227, 1.3442304483459453, 1.9226697169715934, 2.0961612624103165, 0.26725617626073567, -0.47705947938713494, 1.0530808780898497, -0.8430248109044219, 0.22379491737474072, 0.924569408367082, 2.1977956737242232, 1.375983460068664, 0.4901211073721861, 0.450828449160313, 0.6641591221303048, -0.002611018289384831, 0.962031560339856, 1.6136295951100137, 1.2957757683884144, 0.8423300957366651, -0.43971869934035074, 0.8131707003867614, -0.9367379160316931, -2.5763739838514175, 0.9980163540559635, 0.11445949374593697, 0.48209693775047124, 4.202517540205671, -0.18312515211409278, -0.9373004370612945, 2.68984949655952, -0.2904594661886031, 0.2569869816542555, 2.0014589365499793, 3.818427670654149, 3.450807701330958, -2.8819083414997526, -1.1407456355144767, -1.1757113720225991, -3.4030900608569867, 1.6522277314062328, 1.5853976518282398, 2.5884983371539336, 1.3294623298213373, -1.0196785041265224, 0.27388221825047515, -3.513850548280352, 2.280265210798567, 1.6862805366763678, 2.5658895398687127, 3.179909781549305, 3.002770779781479, -0.450185278711091, 1.6992050387386752, 0.8998648165896959, 0.08394509017376978, 1.743174197222053, 3.104615374121967, 2.2742705485547714, 2.2736239300562167, -0.1898605239216094, -1.0273447846116914, -0.05850321350138436, 1.7604203550955813, 1.0122040163796846, 1.0265806505091424, 2.0463856138315055, 1.2507030959298067, -0.7809791200820134, 1.7146810110068587, 1.2263025823594231, 1.876803716167688, 1.7836797168596523, 1.7984502235809208, 2.6214372436496616, 3.506758297416752, -0.4161689987084217, 1.8110487472057053, 1.898554745236062, 2.1123549780811364, 1.696172255552632, 1.8429323922835181, 1.6662170691276992, 0.38914029377405196, -2.4740713600469832, -1.75725794498562, 0.4783670601132257, -2.205382707973069, 1.0874276127797475, 0.12952542246993648, -1.7067798872124973, 3.6552105722018524, 2.838971624535571, 0.0058731157770985235, 1.22270176751301, -0.9809581096882621, -0.26518920886953246, 0.5306568069715988, -1.4319826289571387, -1.9165985207728953, -1.396178298174138, 1.6243154767418946, 0.44032274360231854, -0.5930142879012501, -1.2126928693004881, -2.1813196437999167, -0.36816401626339473, -1.9347956449217298, -1.5014575887103558, -2.773001271018241, -0.2531843572422043, -0.23269551642216507, 0.43391899737206485, -0.9860813916649779, -1.6095400814873786, -1.874381156476301, 1.0320498819202262, -1.862646835148854, 1.0539486246806682, -1.328676603216794, -2.2595833989634193, -1.7643623726318358, 0.018878302407310237, -0.6998375253533564, -2.3463642750469247, -1.4595469917928627, -2.2532424851663886, -1.1112872305686776, -4.2851303077423015, -2.1802505608234966, 0.5434542387751117, 1.4902692854339057, -1.4924842645611036, -2.8024684548170637, -1.5014674106630521, -2.031041682200629, -1.4487897815384283, -4.27329703187934, 0.5193356720204987, -0.6348678360005813, -1.8613363763167767, -4.55073374315365, -5.7833760086301, -4.4301694626994, -1.8340199943643396, -2.746768121743065, -1.2556565974147371, 0.30231763208610996, -0.01849526692045252, -0.033239528025478304, 0.01046266184996818, -0.008662860409118926, -0.028605430361570042, -0.010011578104935978, 0.00956024775078875, 0.032580343766583315, 0.06356717762957226, 1.1359789836307361, 0.2273532397157646, 1.5875295465079937, 1.2730965283308189, 0.23098312711187383, -1.5352212762426547, -2.127042585088913, 0.06037476852981489, 1.5754012274380462, 2.0867909860787774, 1.888779364296343, 0.5055812225312389, -1.6049609690214477, -0.9630983296497844, 0.42632865297569, -0.2550877528845409, 1.4422119943058849, 1.9624211975026833, 1.8568861166098303, 0.900425859566452, -4.149206144027535, -2.7029705852287784, -0.6736809112058016, -0.23976002207681105, 1.9705542113200616, 1.3170144301649616, 1.90817102200674, -1.7546917392749575, -3.2719037867581813, 1.1174693117555425, -0.9290603749867313, 2.8541805323919567, 1.1813884049137582, 3.329960098696269, -0.6827800263325825, -0.747204412435252, -6.249106904361228, -1.1347143494417102, -0.38592532657089695, -3.30002797574849, 1.1424266838951884, -2.9965144567001154, 2.7798981857010174, 0.5871727506014933, -2.866707685665849, 2.9260383404382155, 1.9129431710128837, -0.016000304955461876, 0.02990487152627488, -0.009437488765750032, 0.029710680866551147, 0.009149851113154495, -0.028288084471355196, 0.030440058143841788, 0.007622771967828962, 2.024670033492716, 0.24172190247108846, 1.7517141180501739, -1.8922312163049229, -0.8234974286369857, -1.3338111875938048, -2.178811304692898, -3.010397078415364, 1.2602527142483209, -0.43390569903427806, 0.02970923637644751, 0.0880978907364065, -0.1492074338024496, -1.226385235774979, -0.7061956877886756, -2.3396078758325616, -0.5886421914513011, 1.4950063772228157, 0.8438706683233067, -0.5813567012917824, -1.341177171416972, 0.0471153769880352, -0.5435135508212786, -2.1660545784900638, 0.6200443242583761, 0.7372323034049852, 0.44422386647312095, -0.775028193176652, 0.34824495260524485, -0.8690931787883728, -0.05919577659717128, 0.7949558757322167, 1.0131353159443008, -0.49744795030155803, 1.1413101455213799, 1.903620706040771, 1.4639897242392788, 0.5815611599453685, 0.677099059582941, -0.0530923681442519, -0.11913773863882984, 2.419979810599075, 0.9773811842930227, 2.0230947738656164, 0.8882806855297178, -3.264328877495356, 3.9462595578718114, -0.1209277580275, -2.7923470437561893, -0.20254681405172895, -0.06540902802511923, -2.588020366676172, -4.7709305336225105, -1.2518816510693527, 1.2312235086200887, -1.199281164068171, -0.39764177540614626, 2.6419827731132126, -0.11356661913239466, -3.8579884525595745, 1.195492698859494, -2.3737761638954678, -1.0490614408195067, -0.7392759917752003, -1.7508364451046912, 1.4439792814737176, -0.587666607631164, 1.5698774749389943, 0.11696777732442189, -1.1731398556038122, -1.1822440342912235, -2.0041726189802205, 1.7521621751476848, 2.0320392094071003, 1.9519965669979562, 0.9582270080088872, 0.9947123052696564, -0.7386119544163778, -0.26282355445788863, -2.0919150382523726, -1.1784301430651902, 1.048631212256977, 1.7453731343642336, 1.5089791864115163, -0.18427371717301597, 0.8310115293310648, -1.2894424373652214, 0.21101119777852081, 0.4379580812380726, -0.7913253028841242, 0.06374068804360052, -0.3699948293520821, -0.06962913142640177, -1.0196814365203206, 1.1683583703542928, -0.8343052869478974, 0.06322198654508593, -1.3370960322777938, 0.1492731135578831, 0.7276887994212738, 0.18398734977528533, 0.8170399890859833, -1.6812320587417238, 0.953581716501718, -0.36713521022523965, -0.2855786606886333, 0.4854389374378765, 0.6934891627989302, 0.5491363790708114, -1.832484697243519, 3.6283215955409616, 2.2134802298072502, -1.6263877905799085, 0.9994077152564522, -2.742132318111778, -0.4676790960963548, 0.2000940777470709, 1.2642837780985665, -2.4777655897753195, 1.0195837929495501, 2.3756699382211646, -2.075820290059677, -0.006322514958621268, -1.311841654781785, 0.6998529792919473, 1.7432988478335771, 0.29541313585710616, 0.016956501678435355, 1.0466584853733878, 1.0671966210760608, 1.0553304520567546, 0.4905591342214526, 0.8233406039036831, 1.111536083602046, -0.1683495868308653, -0.5813160902182045, 2.1730144801842446, -0.07127784404610049, 1.9224122358787878, -0.49110507459062075, 0.884946797130852, -0.5178449485024407, 0.033999430946723606, -0.4758810733117279, 0.7320385867337612, 1.0502771326652303, 1.3041724586715155, 0.6442070788079628, 0.2769644906345368, 1.217438787275723, -2.959542556573392, -1.338351719531141, 0.7844294771293794, 3.6572507899312803, 1.4264048022094253, 1.694942475434192, 0.01548205511415326, 0.7962380887195175, -1.755150051861752, -1.3234018808622747, 0.7398103630282526, -1.9405433006491988, 1.0453771685230338, -1.8044320738768913, -0.15809761455892085, 0.4552673421446523, -1.434741037964207, -2.4377852316927044, 0.9438297538966114, -0.723730077507106, 2.332181758128985, 0.9610261273804379, 2.399281891689643, -1.9533388425215266, 0.20968453486346306, -2.1369341066856533, 3.1150885239062895, 1.6631165724350752, 1.6542315632563103, -1.014919303385312, 0.19739143430022038, -0.6380415420963621, 0.44795950713340743, 1.8397560152982162, 1.9012966098581014, -0.5374600502356255, 2.581536725601238, -1.2703315159028237, 1.9949545615694229, 1.9435153768487448, 1.778676608379963, -3.138173025552453, 1.5728685678542242, 0.02398820208042006, 1.5136217161882428, 1.2292276156585022, 1.1733015299387952, 2.550230539575835, -1.5270820728659042, -0.8441826598099355, -0.28394465276428954, -0.14164469025462414, 1.3712330081393322, 1.3482361078701444, 0.30051929284655426, -1.2763474875445433, -1.885985315675403, 1.460672770185177, 0.5023892163646553, 1.930728646337195, 0.06135095850496547, 0.2379223723172241, -0.11583167289692474, 0.574792732864614, -0.8796846501851749, -0.6196908829488262, 1.6668756485981011, 1.225284314673178, 2.241419385657947, -0.41204796033469476, 2.4417173833805057, -0.08890800208357043, 0.64504580875398, 1.781259977422808, 0.4888850731871069, 0.0935418749027852, 2.586402575334445, 1.3424669893086534, 1.1111084732942198, 0.6721139093761775, 1.3670592307002463, 0.5081933785989678, 4.011904379634586, 3.03558801275842, 0.8372974267211741, 3.1363714770169593, 0.1035415005752504, -3.6305285716970013, 0.9082361770212701, 3.7566994755285097, 1.7098143334018456, -1.0258540518215653, 2.47244381794348, 0.15172639616344466, -0.12835358317909035, -0.36965079276780743, 0.1351688724779106, -1.4052715042548667, 1.1704150703514746, 1.9197174384667548, 0.8372705030290273, 2.472341939620102, 1.4080857258792434, -0.15743395768323826, -2.2558508710508063, -3.250761390603972, -2.903597575374407, -6.507310527420332, -4.538068366293979, -3.7586929766066617, -1.1065394088958338, 0.2888721846914221, -0.19405670452138604, -0.840617589651922, -6.96442895785698, -1.8363895031525186, -3.516899162571309, -2.527472391966215, -1.7110671694448345, 0.6371942622281416, -1.3189432614528926, 1.4013475459700826, -3.5351657467161672, -7.547630607341416, -5.2438494156912485, -4.761069532238057, -2.5713245063726937, -1.4795290558518321, 0.6786076144033412, -1.7697299936659259, -1.0287068185004142, -4.893751132061413, -2.105268620506175, -5.2515090458352125, -3.9976959895062163, -1.090456040657907, -3.22758562849138, -0.7300078044994468, -4.654991248312685, -1.9698497766450087, -3.721052123110586, -2.15241813606226, -3.317128829865904, -1.9650809580155395, -2.028925644299687, 0.28158668636891254, -3.1210041580365817, -0.7385079324748283, -0.5035466180458679, -0.588479871025479, -0.699982270546354, -2.2571638606259494, -3.442970730031346, -2.3006860213179547, 2.8166018507032593, -2.551148443013939, -2.769008610891953, -1.4536378634846026, -1.9126981275192951, 0.07820659409339967, 0.2352643276965413, -2.0211635286704817, -1.2336615648840343, -1.8648346228293315, 1.663503667180308, 2.5639227162873017, -2.2304592137804793, -0.9803577081302761, -1.6298073582848056, -1.533254439263941 ],
				[ -0.024753962519437518, -0.01081557073392657, 0.015108363151836116, 0.02137613428762672, -0.025150230086764407, -0.03383856410977756, 0.03259699025403076, -0.025998034481356385, 0.4194859277959688, 1.0183533236412519, 1.7928631937290198, -2.331729993606104, 2.0442879110650454, 0.42077216860826683, -0.2632699461263318, -0.9486376290978504, -0.20388840276312303, 0.5089681722074797, 1.7383676657343408, 0.4693663898725409, 1.2268280404438452, -0.0396284316627927, 0.7984852790000321, -0.34103907182895016, 1.50544987838806, 1.2762197897947305, 1.8520206144642604, 2.351698550097139, -0.4868219992764939, 0.15401357442659705, 0.33404780961333425, 0.5668788309027953, 0.2127464695079716, 0.8063118985215799, 1.2646705455579403, 0.04475326972722007, 0.8046053434887801, 0.3887855792116027, 0.9384298480019598, 1.4090025217939417, 0.2773485009856949, -0.3561366437758695, -0.49341484593462925, 0.504742046035001, -0.20171394958205283, 1.3699842003312703, 0.8264780381136466, 1.2827768401215767, 0.5347410957008225, -1.3294589858509063, -1.2555638190296405, -3.0096039565527457, 0.9071181638063871, 1.198479779920176, 0.5575043622699779, 1.0747853858881442, 0.017687226210538462, -0.00971203681051755, -0.010011469461360141, -0.02277745894987638, 0.00441514638853742, -0.0039219789405472265, 0.02724170448557105, 0.019660032734540454, -3.268308756817794, 1.314093530574993, 1.2264216468361366, 0.6633104278486892, 1.3741506916459556, 1.049148748615331, 0.3783681758894262, -1.230443753292009, 0.9346952095192327, 1.0901616808535382, 1.6499478202397635, 0.4824819615814956, -1.4236291120495652, -1.3838913251156886, 1.3861105297621328, 0.3712570023371178, 1.8944335841948472, 2.0748632080983853, 0.8201724009270377, 0.14355573512174588, -0.8090331336064144, -0.5370994769813197, -1.2800387419706878, 0.6707939232617741, 0.7800522039586771, -0.519071848353476, -0.19021257953517962, 2.3232031779568354, -1.2960968209157642, -0.1722935992779731, 1.1368325930072425, 1.6096272114598458, -0.6443685747014269, -1.1330679534851247, 1.1743441717159984, -0.62158486914018, 1.3867269240868685, -0.574699102232483, 0.9542280344986975, -0.6755843057879679, 1.8536853989049737, -1.9910077247352145, 1.3040336868311027, 1.0558413241324198, 0.4522891573774794, -2.244839200979002, 1.4300237783247374, 0.4777576394771371, -2.880077672213089, -0.6769917696344273, -0.4422290663944043, 0.6662435169403748, 0.5281469486261292, -0.07862832113982483, -0.7133088015849081, 0.5461684679464527, -1.4181797030009848, -2.752794905491644, -0.5875151756739049, 2.4133868436099246, 0.10838211881433765, 0.6854076372073666, 0.7885192485281024, -1.6319027456813424, 1.2235165420311347, 1.7140136991718993, -1.2726387330995768, -0.21536998261692356, 0.08001186839774849, 1.0891173617880414, -0.8513723698962522, -0.6601860229158049, -0.9843118076182225, 1.4629476281814393, 0.08887440152935336, -2.9687266445268596, -1.0654650742378096, -2.1751523155119763, 0.1337845174881121, -4.4607261012218204, 1.5840806041366664, 2.031218891965128, -1.2472745938537038, 1.5869684250824512, -1.6288798917212468, 0.4477032529091858, -0.039408622964462285, 1.1640009593709844, 0.224141535631429, -2.1094282164823244, 0.35124839369106375, 0.5423003619728458, 0.020020246220070377, -0.7468469637654866, -0.5212938798096038, 0.9131668072448814, -0.9914346847859803, 1.1183253947649279, 0.1774904821941248, 0.10953215845915408, 1.7054811203798939, 0.8762182366348568, 0.8361845714402393, -0.2896442958744731, -1.421959353642168, -0.9236626984648986, 0.9182100256792973, -1.131840253732488, 2.0255060261216142, -0.9018068662469377, 0.6062356406301443, -0.12694760385067447, 0.6891141204365676, -1.3668715457866285, -2.5961763358085035, 2.0174095379234394, -1.622132401490268, 1.5153422872799938, 1.4321695835451675, 0.991522637316608, 1.0387958602966074, -0.06424518409827121, 0.9509252746787819, -1.0490304507150732, 2.048712591864201, -0.05320975859754921, 0.5081372006691437, 3.5128569556824334, 0.8808658780226665, 1.1382409141123764, 0.7544455887527994, 1.2168022857974374, 1.1521531650832535, -0.15315452078235717, 1.5272691592184808, 1.1673266802080795, -0.09864628221354846, -0.539432523891689, 0.663800044304969, -0.7284870461339826, 1.27335121959462, 0.10102275220648557, -0.1382679337036475, -0.6343205559934196, 1.403239794963665, -0.09667230366377443, -0.022835332715971192, 0.23409411441573458, 0.6552058802889374, -0.3881602062767634, -0.0129460145791262, 2.155040582201682, 2.9675187508470815, 1.6381146754058293, 1.4462517904833723, 0.8090782026957734, 1.3016761467776221, 0.22235561664422113, -0.08120584856412323, 2.32337582051448, 1.8701350490719666, 1.1126635546646177, 1.926603398494178, 1.9856446563777963, 2.0307106682689002, -0.1265715380803111, 1.4502082650438768, 1.7698468996257464, 2.6079292094410014, 2.238524200756044, 1.8145654134448315, -0.5557467894717267, -0.1784246385301519, -0.022998878845107627, -0.7589412153136238, -0.9088777495832853, 2.437168482529966, 1.4374373592208274, 1.6219888845738115, 2.2095109648656384, -0.02730537511980466, 0.7372994139375922, -0.8199583946251469, 0.478707163922738, 1.4783626792945146, 1.671758312552166, 1.8468783642849482, 1.2632365246004051, 0.8198647400550022, 1.6951380415496156, -1.2771045713344205, -2.0106625317480225, 0.189850163388606, 0.6751986998875805, -1.254438939783923, -1.4844854651542856, -2.1142217345460224, 0.9485840798598515, -0.14272147625369375, -1.3887122807304386, 0.9225740342683184, 0.02669211899954905, 0.6901998914532267, -1.3598231552677007, -1.6290384950421046, -1.201408469666845, 1.2220462677665265, -0.4237747454002573, -0.6822562146259488, 2.1166152547962, 2.4365123243716464, 1.7487291623561945, 0.06198375450617706, 0.8074426324509724, -0.018492893987283227, 1.8582768090940363, -0.4934294991318289, 1.2544775068123302, -0.8278810411876554, 0.7111696730985426, -0.1870729496048824, -1.4019204484440415, -2.07872160060541, 1.9455264414673854, 0.9493985944498143, 2.2003688933036476, -0.03834793868527638, -0.4966295701209468, -0.18220841587059708, 0.7299873248581756, 1.288909152213207, -1.543797033287016, 1.0479375826305313, 1.9671045533967126, 1.2059799947784646, 0.6149286659468668, -0.5273583153901703, 1.3291593645797892, 0.6241641037138947, -0.2895270093145006, 0.009093044735593097, 1.297749376960649, -0.26176202362187684, -0.05340631271747465, 0.6264978053257402, 0.40675458690738997, -0.8683029146878132, 1.3736622023178575, 3.2921812167018993, -0.3080083547698878, -0.6348106436065901, 0.4393093856366006, -0.09083743173160018, 2.517607122351946, -3.897030148466334, -1.1982518492924858, -1.7528973002626316, -0.07586418061837565, -1.2167270961751786, 0.3866013062326402, 0.06074958678989, 0.36674055975972963, 0.9755330284293872, 2.708624809389573, -3.2919101585740886, -3.0955529360393634, -1.5256941817871008, -5.099724421682371, -3.818041370232764, 1.6249196046235552, 2.3701130936098815, 0.6569226138937666, -4.50685132811011, -4.384774384454745, -5.796606062073746, -1.5761119766894314, 0.4436881105362779, 0.21476403985241632, 2.1284805992245057, 1.5677658960016967, -2.4754154781135784, -3.983725753207717, -3.686694995145773, -1.5608582353530027, -0.8841947955675521, 1.387132128978577, 1.4261730575697251, 2.444225483941437, -2.5001448297827538, -2.659708870745042, -1.6609183837635013, -0.7069863122489577, 1.0496995303396657, -0.011840185772901878, 2.5823088230626055, -0.33375403007337795, -3.6702803726307685, -0.8505997587526399, -1.2003154892695154, -0.490494056714831, -0.7525609959835906, -0.42841528206730556, -0.8533416196999974, 1.3849265168106855, -4.4020523661501345, -2.608790422421679, -1.7739819614929953, 0.11831135023516744, -1.0440721664238606, -1.3732820885703305, -0.7434281045951198, -0.7138675785506344, -4.32609588693803, -4.584733656301316, -1.4675927982391037, -0.2721879433484211, -0.7544555792695946, 0.3200690501306216, 0.8020130727594937, 1.6741177703545138, 0.0030151511928965765, -0.006236864297056031, -0.00014651354583972146, 0.020000516045068136, -0.0043325700757548494, 0.023148579432783527, 0.014423825870169259, -0.025672021364042993, -1.1889935337125261, -1.097025378832927, -3.373725392779252, 0.8230080022779329, -0.15532527610533434, 1.131219229785965, 1.0938523756709815, 1.0879883446895984, -1.7501910313234341, -3.346916678489677, -4.199309530838246, -0.8400035452738256, -1.2271489913227325, 0.151280486186689, 0.2450037916143424, 0.9288455114679844, -2.5995877476334144, -4.022398212919181, 0.3584091126519816, -1.7651656077898565, 2.0633225295357187, -2.5605147061716957, 2.8217424918029863, 1.214045751625156, -1.6661180864767144, -1.19069924199072, -0.8229531847939425, 1.5807059519192166, -0.6461861288145843, 0.2778077200081952, 0.803949204785225, 3.158934250649081, -0.745219386658203, -2.5278752560587696, -2.389225779708124, -0.6778508760489209, -1.1936012574416752, -2.615903652616431, 2.553124366064921, 0.42468228908832834, -1.1853361623280831, -1.0774857252593069, -3.6219638982754683, 0.5339888619560755, -0.8573655326097878, -1.0041881540258308, -0.04400466816498176, 5.44827411914206, 0.02339028173340354, 0.009787993728776916, -0.020363650696261424, 0.014764749395633417, 0.012278803357895862, -0.02961638804647301, -0.014982942596264896, -0.005875675536456223, -1.2275674801848564, 0.026468028595574768, 0.04988212771644611, -0.25105969020432706, -1.1124256699214856, 0.49757882552820076, 1.8890591515072583, 0.11036793851368779, -1.0031268841259893, 0.811785769819734, 0.3512386111764621, 0.19814991576210958, 0.2508017462490416, -2.936806572464795, -0.330103059460182, -0.3058290297102359, 0.8577597912615934, 0.15085613322591426, -1.8208077787065564, 0.4789601447847848, -0.49848054260683144, -0.01603542466898548, -1.4072392655775943, 0.43398405445264976, -0.4445794994785838, 1.3755906716014727, -1.882292846783121, 1.1915657395232777, 0.39538175365751366, -1.0070478189046357, 0.8205077273975085, -0.5349182394609239, -0.5719792505256746, -0.48444925756987106, 1.9886514035842269, -0.6977101314440681, 1.1237018254824949, -0.5285466333884751, -1.4507980265900537, 0.3604100977492027, 1.8097927216329008, -1.0269998477337767, 0.10208980737009292, 0.47393642849898965, -1.5942610724644743, 0.24173308574875363, 0.4143408074851805, -4.027496288408792, -0.08388451415468777, -1.1527391695846223, 0.10508269607706894, -2.4157408747443103, -0.7258766125739771, -0.8078115120199504, -0.39613022591509334, 0.29426951395173956, -0.466436465108378, 0.3447512254036274, -1.019873016176624, -1.7238022890473288, -1.543853455609245, -3.427850234597023, 1.1550014946930898, 1.9652030585265572, -3.2144061609326675, -0.7117636804500088, -1.8544753265413514, -0.5807721511467455, -2.015633351646159, 0.3075745678480426, 0.48644537359007467, 0.3892908355128112, -2.8858932723936626, -3.346577119359614, 0.8900435350995006, -1.6841862790483675, -0.120199579051973, -1.2618528850904787, 0.6055173022669421, 0.10290751141540826, -2.5991847603490297, -0.5380339930918218, -2.8514465526022863, 0.34107363026567167, -1.8938745932865015, 0.9582789325347066, -0.5472004552682994, 0.008161620081025889, -0.6361316799846856, -4.456660234517301, -1.4563765553769723, -0.2263595417577655, -1.1764711785690363, 0.3459701775723917, 0.7231386791976673, 0.8221764762426013, -3.2170194791009386, 0.12408254874107578, -3.409423449035087, -1.8877681472174892, -1.3343865766620209, -3.2376449022088645, -0.25983499666565935, -0.6704200200909269, -0.438840075178928, -2.2895513610419904, -0.5115255850855918, -1.8346856726375251, -3.509425732977012, -5.228955751321387, -4.973842073999396, -1.0337667626152023, -1.2191365134341257, -0.38044246137794735, -2.1821022228119618, -2.270619062570908, -2.9942126006841736, -2.0678469571056253, -3.8600265449283735, 1.2997007070948237, -0.9480261007021488, -1.4196764738823195, -0.9002900695399252, -3.0365813826278694, -1.0576525612233674, -4.60421967649561, -2.1903740306745014, -1.845457337051366, -1.2593041532146703, 0.20341738033915827, -0.3351190677531465, -0.5625148465406005, -0.32136673210698313, -0.723211957704929, 1.7940670163992092, 0.9840473472513811, 1.856971616299993, -0.713676424238589, -0.05104712238508851, 0.241507988812346, 0.41472956527410604, -1.0941833076805465, -1.92417436104586, 0.06409857422374043, -0.06900043549019015, -0.2619743528893537, -0.43767896690043195, 0.18858081785931397, -1.2144545409714336, -0.5172204153661665, -1.1361348480489166, -0.2075796427289316, -0.9999262181932912, -0.40056885140115284, 1.0963803800757153, 0.19672604244096192, 0.5255483125472711, 0.16805320655627057, -1.5850702068853268, 0.4334457776779744, -0.3707187518754598, 0.19094937432495301, -1.178321271405395, 0.375953351235026, 0.3668837414578193, 0.07831962661315002, 0.41832515972657586, -0.5539320458179828, -0.12632849258170903, 1.0622241963888353, -0.6308048677832604, -0.1803372021863849, -1.013780440198143, 1.2396220432362748, -1.6845067462871588, -1.360381123982429, 0.24942403257828166, 1.7749001778174673, 0.46929592406087267, -0.3322074491555809, 0.1682920867226784, -1.0426032839426949, -1.1232749921823504, -0.6808634441973794, -1.989958108763625, -0.405935343634788, -2.0720471430027163, -1.2530502972055237, -1.4628877063985022, -0.23916367402279068, 0.6930840841758203, -0.7392108882936497, -1.044403175689905, -0.3207030479842371, -0.3252117566965109, -0.5617484762398508, 0.7379726276843986, -0.7376319215789937, 0.2527443687733899, -0.9800384802384395, -0.5399258012129977, 0.8595298184185133, 0.46971380238043453, 0.5392745376491824, -0.5468250780001489, 1.4259589102005257, -0.8995800319179597, -1.5014134936008083, 0.4651840337767268, 0.09491437159129995, 0.5677377920124055, 0.5601647153904794, -0.47953796563377676, -0.04440133410298676, 0.028170008341507163, 0.5300151644900951, 0.042961604753579456, 0.3526363612808429, 0.8883933005131988, 0.3742575292264113, -0.784788388622381, 0.6470205033698584, -1.1245281203968123, -0.276555478112095, -0.603055105207919, 0.6545527141294168, 1.5362174064128415, -1.3047588548955718, -0.05411176938706112, -5.456919373302597, 0.7507056319720901, -0.6954511533420374, -1.0742056448434762, -1.399884679967933, 0.748984545873631, 0.9012249330547073, -1.0680230097625558, -0.13968039745938612, -0.9812123626729011, -0.8431127461962863, 0.0367059629608918, -1.0785450424933958, -0.5678984036150995, -2.1924940968737663, 0.6385333950368587, -3.583687214077524, -1.3031109803284253, -1.718271487277989, -1.2434275985526253, 0.45217557455741436, -2.6454858364810674, -2.427067126010976, -1.3849116744772014, -3.007477724237874, -3.1037583371579944, -2.9911964903381185, 2.341774854879314, 3.2887676088212316, 3.1893561938213835, 0.5533868397361743, -0.004008779852451119, -0.03808992539342534, -2.2898326437827325, -3.0628083167724873, 2.5867458148882863, 2.9379443407795063, 1.166893883910218, 2.3711046215841995, 0.5306862784333845, -1.750958163155058, -3.5582778521145175, -3.512325586262415, 1.5049685523771574, 2.3782058267824264, 1.315980856831964, 1.9606935322011934, -1.3211103690067356, -0.04741212991147908, -2.84233512526525, -5.221669386146561, 1.6479454340187984, -0.1649699302225676, 1.6907798240753373, 1.416385364141979, 0.32294729861687144, -2.2827140393348055, -0.43325887714725725, -1.4277430264849107, 1.8730059410472242, 3.0358846849971455, 2.479576639813987, 1.925729448647573, 1.6091845725405045, -2.0959874697399528, -2.7799572747064167, -3.6839790712438867, 0.4379019783895732, 1.8938556642861732, 1.422716519737875, 2.0570272770311213, 0.02041795557688854, -2.227969316463985, -3.4388072271191503, -0.7266882272091595, 2.8313696655091514, 3.787892713858278, 2.139659710616742, 1.30427046860842, 0.5183394092153589, 0.5103537255461942, -3.3341024658477743, 0.6388894326443139, 4.883853980626875, 3.161314688643996, 2.2132536395785607, 1.6277979899338315, 2.102719897473572, -0.7298135513122074, -0.4254972256245738, 0.13351536022915034 ],
				[ -0.01671880692207634, -0.0244892165811925, -0.01162118665233865, 0.02653478856643538, -0.016594172801565398, -0.030364619538786903, -0.03064717584602487, -0.03122288704829984, -0.4303150689047179, -1.2196382742563765, 3.1169538462002966, -0.28132337213676795, 4.369682516321566, 1.2190591474209898, -0.8395126855407181, 1.333743738803449, -0.22565083829135443, 1.3390145891409042, -0.4284265787988109, 2.156504837369093, 2.228908882882273, 3.499875258226074, 0.36624721222698164, 1.437745391414972, -0.33994599263511954, -0.9726586635867197, 0.5273659900811793, 0.6899851004795114, 1.579514321555956, 1.1548882478092, 0.15553451556268524, -0.44741091999654226, 0.07357606079134978, -0.6003899845549372, -0.3572029320772648, 0.5479261351973057, -1.1344837060335906, -0.399879904809659, -0.8971760620049346, 0.2879730957413489, 0.321867682634039, -0.7591484435406263, 1.1475911553547824, -0.64170788223192, -1.5270376098127223, -2.0875843540093015, -3.035360492361265, -0.5103883455519362, -0.29385438017921917, -0.22251668069175926, 0.8358875544515101, -1.0652799990332522, -1.481501174415772, -3.654828730449365, -2.6160022744118043, -0.8016657994423967, -0.016688397132818823, -0.03279485242516043, -0.003033683494671025, -0.00926101543102821, -0.02572650822050252, -0.019652579204544097, 0.015296684245888831, -0.01983800846503815, 0.9158920856620217, -1.0936557349255405, 1.0180092552499727, 1.8115913371480519, 1.700708388515892, 1.101036495504816, 2.1975720941255537, 3.268586107832378, 1.175503653250543, 1.0415308674932335, 2.3106419612523466, 1.5937920592283408, 2.051408432495733, -0.9876762197959696, 0.4950174756687244, 1.4845857571758505, 0.2157905230371566, 0.4869756060215947, -0.16278075055783697, 1.4768140708888722, 0.5031976785173917, 1.5453300877973029, 0.8259169779812668, 3.240827652993245, 1.1901851916676698, 0.04746180170389357, 0.11648567925039677, 2.5722400381268655, 0.6214335097099288, 1.1152424931756395, 1.5835166610951619, 1.750285281209398, -1.579752618942235, 1.0190080120338323, -0.5411387656258295, 0.19453483196892515, 0.3860038413336932, 2.187806276015341, 1.9644409780045873, 2.325283606708814, -0.031942663971407145, -2.374474634050896, -0.09648661492085048, 0.378122941708824, 0.24797867194278414, 0.15851408793128474, 0.07069710102538558, 1.681227395395211, 0.7089667011585707, -0.18473048676487175, -1.164087623076757, -1.358747383526944, -0.4242291973773144, 1.0904826580872478, -1.2849060084061548, 0.2370884529183186, -0.6996529824169708, -2.497321047420242, -1.7972462022195916, -1.4207573824429294, -2.065218609167541, 0.6940633426556136, 0.4287398505523538, 1.8735675892854204, 0.2946389384402547, -1.430052879784619, 3.6467726004721457, -1.3734958518877955, -2.4122419970320172, 0.7515150124952301, -0.5050681562447106, -1.0630230273533814, -4.390040837343307, -0.07670965430930303, -0.8063799725686608, -0.7467969870275426, 0.4827221650417443, 2.5657466971580556, 0.7251560962062233, 1.3231427710178503, 0.8200346588360917, 0.036468745639269357, 0.6598083014299444, 0.4311385121505707, 2.039311057006118, 0.48375252956459913, 0.18763688636443038, -0.03207982798645054, 0.21116078486875264, 0.4600536937782279, 0.34248927623173203, 1.4290495273169566, 1.9908335651494122, 3.5920366602818046, 1.5964335140640242, 1.1661096876233743, 0.8750610526993436, 0.3929334953689867, -0.03422883214484799, 0.8854836220856093, 0.6577714666337269, 0.8961221012176754, 0.4764918079549989, 0.6278398476170651, 0.9389963449266812, 1.2562340882861192, 0.09756189893087222, 0.9327781909148097, -0.4901707851306143, 0.3216514176249503, -0.0734456590995617, 0.5035989431769253, 0.3228924718193673, -0.010537941461309423, 2.037114750036588, 0.491917127676014, 0.7685862401898177, -1.5736269543880843, 0.4533736241809015, 1.5923460296284355, -1.7481493539716304, 0.8416653180476169, -0.22508585266487713, 0.268852676019537, 0.4464984675229798, -0.18551111986813712, -2.1589552038859203, 2.102347410442427, 0.5292455855651839, 0.0421253716708231, 2.592815767765337, -0.0014617472866872748, 2.3333927859172245, 1.0491161987191582, 2.8355724889717364, 1.5625463361167664, 1.5017227695036544, 0.5199044964735617, 2.319439710009267, 1.4645324003086846, 1.1327451778889337, 1.49122432326803, 2.1096311129966066, 2.516439552288515, 2.2802745686992716, 1.4649556644402626, 0.8361571492733758, 1.8305527418051184, 1.9694413998141849, 2.4138000544884535, 1.8959120095166848, 2.7420200723580743, -0.1494896698555123, 0.4519763547103663, 0.7633662875765634, 1.0695157385611314, 1.4088291634254648, 1.3515928901106185, 2.358940737252012, 2.1053358336080565, 0.029153334304464467, -0.7714417958346125, -0.18676236344439845, -0.474718608787948, 1.1639444650414352, 2.1572504731857793, 2.9966547246786233, 2.227547758889617, -0.6752208426302786, -0.7541885513783684, -1.7089988084853394, 0.1820580628076806, 1.0134714432049219, 0.35673994518900054, 3.25865409169306, 2.6824589662914686, -1.3965948170061988, -1.4096463662138357, -0.20235787442028833, -0.4994555208924307, 0.2548526994405816, 2.4634596784526313, 2.997732824936229, 1.7479193034501859, -0.0390611263167075, 0.08619368248894495, -0.1975941306231983, 0.4379547206048911, 1.0271066340678734, 1.8148736893647202, 3.7004622657525346, 1.783174931802234, -0.9301489414232916, 2.889719979312721, -2.046269885085804, 0.6460767354382572, 0.6664590247731432, 0.8426803278991143, 0.6924638875150543, 2.998680681431192, 2.1030388441557446, 1.1923226978355335, 0.39955366767761824, 1.4353179539646304, -0.05475311226180151, -1.5677017907809443, 2.1206658104764653, 2.8942255369880296, 0.12042415423089142, 1.9462653843424411, 3.251727211172849, 1.975685912584064, 1.7023283114691479, 2.4878179565294327, 3.6885850868364067, 4.900638119170731, 1.42528130635246, -2.26258886808557, 0.021054191469697715, 0.6622998758344858, 1.4297603961515832, 3.6846743428815842, 4.571453677062383, 3.9344008305152625, -0.7697784359124427, -0.3172746659079539, 1.1386822021010776, 2.135498118336761, 1.1944151463621575, 3.393777488998769, 2.3686796578097664, 3.9399582754783955, -0.8623142426207291, 0.22683936160590296, 1.4261449128062063, 1.2630597381333142, 1.3123850998235027, 2.7773624524163334, 3.471960778548463, 5.082116045524819, 0.1792091077034259, 0.19184550258727145, 0.7525180694817063, 1.0887160922666805, 1.040382995219213, 1.691358202790078, 2.466787773273073, 3.167214924821276, 1.7845400709802661, 1.4320676155801284, 1.2225615760633601, 0.2167465519881746, 0.2256731881871796, 0.9896544900449433, 1.6127138877926432, 1.5692336955503399, -2.3674455917355606, 0.18589121263275346, -0.644635718334935, -0.47012721722538203, 0.5954665488548426, -1.0057684147191344, -1.2435841380311368, -1.1373746351341212, 1.5312466640670785, 0.1170442236716203, 1.4278787577361858, 0.9513985608210095, 0.8181707672640458, -0.7838037098702595, -1.1506497221128584, -2.057044729180463, 2.1932610501782897, 0.4895108334643086, -0.4590737210020894, 0.5664784320150348, -1.7916843713629884, -1.827765776254504, -2.7597621458039283, -0.4690562516181642, 0.7765158787232672, 1.463304322731366, 0.595479515918521, 0.10487669790045301, -0.6556089376664063, -0.3076992704788899, -3.5633732906934954, -1.6595319678183975, 0.5791385008092187, 0.02687835987944894, -0.46981946782022244, 1.9742129086231457, 0.24064637963858246, -1.7268965702302765, -1.495395014484127, 0.06510832408287134, -2.0051700952081424, -0.39542445822391126, -0.31614561979749395, -1.0662311062992356, -0.7296930940029581, -0.9813520186284594, -2.2010846391147316, -0.634053100298989, -1.9653044535222481, -0.7224322818587748, -0.8684550644421334, -1.8428676592428597, -2.0015972124696, -1.5955484186459172, -3.2571497513933085, -1.0489541298125793, 0.9708114646315138, 0.0906879881529967, -0.31675066121959344, -2.3949296779122493, -0.47560243437817773, -0.9829929200861898, -1.7227655668317776, 1.0413077111050741, 0.019384039029610025, 0.02318745504459814, -0.023768823779693662, 0.01752636104269528, 0.02706881221916149, 0.007562021214570479, -0.010807216033306947, 0.03059985986825106, 1.6037908789441255, 1.8602756895429413, 0.875076090935686, 0.5603277554360253, 1.3109150142044033, -0.33028693807913306, -1.4443174618151906, -3.251012324588263, 1.7158797561295211, 1.4881751966215084, 0.9123920443643148, 0.266470307574362, 0.1285889864012852, -0.5594582168036168, -2.1834292054247904, -2.276799996079009, 1.4767513624942277, 1.668672222201924, 1.2031192263428994, 0.5045705258826626, 0.24308601447194292, -0.9214680046057797, -1.7324181376682446, -1.3164872154943548, 1.1373239657814491, 1.846273098052062, 2.7216028346593686, 0.9431465125567428, 0.2660188630263213, -0.908345549968063, -1.5746662048165234, 0.9763947224533818, 1.8825874149447004, 1.879049112052891, 1.9258122956155923, 0.14816637848121667, 1.6243717074576804, -1.8181284620563916, -0.6644586450574571, 0.8939881073816057, -2.198996288468443, 4.62918055101743, -2.115984288460676, 2.3819759688856745, 0.1431020857796626, -1.662363611536715, 0.4603127774798213, 1.6065915044026478, 0.018793785384627847, -0.029708346782053276, 0.021675677817205197, 0.019818853642302955, -0.03137442293745164, -0.024335609681699778, 0.022055001634453772, 0.019458517432814387, 3.078790597764087, 1.9903495347231732, 0.808892414269786, 0.8750500293527305, -0.7719839305650794, 0.7985858174144294, 0.7872451963823657, -0.3358066512772194, 1.2887164166131373, 1.929838181272956, 2.0102140598120335, 0.5906753869925118, -0.2480311345563935, 0.23097305491799555, -0.8848738168616461, -0.020372024321200964, 2.430100182287268, 2.31766461088344, 0.8844629626938897, -0.40943172348063783, 0.6625375921635689, -0.44572264778604187, -0.9064683604992754, -0.6537631728931553, 0.381177451214433, 0.9571671740515818, 0.6565094116134109, 0.5883559109435776, -1.4642590226086216, -2.7151446505293957, 0.21604206483224464, -1.2015705985014533, 0.509955316452531, 1.4332728869384197, 0.5737634725609988, 1.074840483109104, -2.7929125839623445, -0.9418180268817862, -0.45708951549194765, 1.4598146408207915, 0.2155262596611617, 1.0030937855824762, 1.7069824242994152, 2.44083622803076, -0.23011298382434284, -1.3282804844467202, 1.5225097936594172, 0.371885434079071, -0.4051537783233469, 0.5837569524448304, 2.0871531776586543, 2.48277866270137, -1.0390474943020964, 1.3689072330529182, -1.0744937213824508, 0.18971417128745804, -0.6670431589648153, -1.0492248396621051, -0.024048130188389555, -4.1159440611011595, 0.7750912565420921, -0.021102578866419856, 0.09000885891167364, -0.09225639105800078, 0.5590180933601673, 0.48814882721935976, 0.7399057097058938, -0.5874480584232917, -0.7205566738275037, 0.11007200378400607, -0.9602141942966137, -3.420522491550845, 1.7890507329234995, 0.6847416870316393, 0.022300993133271694, 0.4649002864817105, -0.38073121296639667, -0.7383533018329544, -0.9734787254786098, -1.2975214349006632, 1.4421570485643727, 1.3466822633777373, -0.08724649217310945, -0.5393854500332732, -0.6800032125545711, -1.119013544887921, -0.5264678898693875, -0.44967147602553864, 0.6280001142346555, 1.6703100831942275, 0.45601837007164414, 0.41014084262882317, -1.200322503403311, -2.3744700364638036, -1.7859637953278718, -0.15605932672919717, 1.4011461430449648, -0.2505613696936981, -0.5936755888977757, -0.023110715521481646, -2.7348854744320343, -1.8909045172306729, -0.008143145477212172, 0.10918069720974656, 1.0964036925235634, -1.5324849640343483, -0.6629146339004672, -3.1635467823914625, 0.3410343462438412, 1.8385424105090051, -0.20822697282984914, 0.9385817772301204, 0.010212188025421221, -1.9194375975456177, -0.12949841756491043, -0.5282535134318826, -0.22857362297982672, -0.574352430580298, -0.4120432423933489, -1.265859289906192, -0.3756845531449558, 0.5496153834440349, -1.0632233491813288, -2.11984170605472, -1.4952780250671862, 1.5416871074326701, -0.823545639072999, -2.87616612635805, 1.9718044868811944, 1.8911207244772095, 1.2523766520705073, 2.0398328560068144, 1.5867805092616236, 1.2285855579650764, -0.0651658532652517, 0.14313888322978083, 2.0339146141760898, 0.3692845131771395, 0.6948480262145851, 0.6730674855789955, 1.1305337440984347, 0.25191898310065897, -1.635199175305177, -1.1323634077508054, 0.8556709999275155, -0.002814314786467941, 0.621206222090274, 0.40324330055557905, -0.23744457972535182, 0.12883493183881536, -1.0938489890093552, -0.7959006069390665, 1.1095795105747335, 2.441659700956787, 1.4150912477325435, 1.2101551534303276, 0.389924240863392, 0.5814145239777881, -1.1454703169132265, -0.059994048854058915, 1.2762917690679976, 0.8164247566307273, 0.9613724101066217, 1.005538709783613, -1.5005073822222952, 0.42954392223373505, -1.5748776999503742, -2.0902595778238986, 0.654899211730424, 0.43696031204291247, 0.21466933438391356, -0.4374592983213728, -0.7358995078467473, 0.0813100256610289, -0.9935804517722545, 0.5051122358699073, 0.47600854681144095, 1.5516727902599032, 0.8427237706472638, 0.7951992697944185, 0.12573123163230965, -1.1827683418253976, -0.08983980270136036, -0.7876949970949978, 1.4690005497455412, -0.34540574482825637, 0.5373032715380516, -1.8510021904530356, 0.9273324914218262, -0.49684134727937823, 0.8238136326525443, 1.4644226753932923, 2.52998416812918, 2.097464381293758, 1.910018077111553, 1.481743665936486, 0.7345671729850399, 0.028517473582229787, 0.5811132600721507, 1.7475146973556566, 2.4079304953308975, 1.8459013914081555, 1.2855405773445652, 0.9538529365798989, 0.8032365255176543, -0.05206930321574184, -0.11990571818480741, 1.9026835333361263, 1.600869078683131, 1.23193416692021, 0.40666879779140985, -0.4210513805469389, 0.35193058170297326, 0.6719476799462478, 1.7310416407223994, -0.022901775956805766, 1.0266963359832015, 2.1259240425255252, 0.5258237916136395, 0.8785775174451209, 0.3872113639235906, 1.746550748161105, 1.396525239793255, 2.5855110210272936, -0.4325592395534026, 0.3356876122647311, 0.3451479129641675, 2.055853324748997, 0.9760618418827046, 0.49630403542998325, 1.0353458841369738, 5.135975702128399, 0.88895669965874, 0.6945084596778257, 0.5484466998518558, -0.4912712427716379, 2.578160250732011, -0.21254814468256747, 1.4757380059311835, 2.849841324599731, 0.3651751339637025, 1.6054000963725525, -0.7303171738258939, 0.6208273515951789, 2.0382272008592084, -1.4064336012414282, 1.8860885603641795, 1.6076849315569623, 0.630993482017758, 0.8301524019105682, -0.08887226337491444, -1.7111063245772191, -1.2278453403848704, -0.10655940200621412, -0.9099721775141107, -4.414673330439481, -4.974250745215424, -7.802463625296609, -4.2657127492834555, -1.7005822014266807, -0.9713263994566392, 1.321136966062861, 0.9322261828880949, -0.5868938503387379, -7.275749105651514, -5.015234557418474, -4.663733665033157, -3.035643558838954, -1.1680902171236933, 0.8224611363104527, 0.9138092141291224, -0.26224688420932135, -3.0468072388225074, -5.743885840789263, -5.6318091294028045, -1.5520938557679125, -2.4454925808660035, -0.8843990519697631, -0.3976983192997556, 0.3018949502925326, -3.937725146412521, -2.0880015277470125, -7.170666498151979, -2.490658414588272, -4.0792020017273245, -5.190545557603536, -0.4479273523605753, 1.9193690675707058, -4.0878951535330375, -5.640243988483987, -1.9225172545833364, -4.723718628976211, -3.450485713917284, -3.110051114173347, 0.8418708561296422, 1.5383372543284268, -2.8219495632297176, -1.3809244559879739, -2.3191571596153255, -3.3344598247670985, -5.673661727377794, -1.158824474409967, 3.1152159480408677, 2.5888038278442473, -0.5244521117065484, -4.556870715651509, -0.9665146028798732, -3.433538728154462, -3.193913970277001, -1.5486302929117035, 3.397779172396171, 3.180069593811762, -1.2405849992197282, 1.278449499265377, 0.19683329988107598, 0.5645188358393688, -0.2929198992924939, -1.7424812594156138, -1.6629486675871805, -0.5142460511888612 ],
				[ 0.008633075816654482, -0.0028813340498539375, 0.0046723279433163265, 0.029342416507329338, -0.003961938420465287, 0.03432801618773639, 0.03445687644045824, -0.026743190812577484, -4.692827722666478, -4.423691541769045, -5.175492479897071, -0.6522233819726561, -1.6489119344751735, 0.05581950962388605, 2.2915274240115937, 2.388724228755856, -0.00260807644654955, -3.981627025079896, -2.3954940612343543, 0.406114938786763, -0.4052033046376193, 0.48414764457216863, -0.16678271933878616, 0.679439598106042, -0.2718825551792152, -0.6135726102909809, -1.1512638492180935, -0.3422392422732988, 1.0995484551123857, 0.7806174272274924, 0.30662842810739727, 0.5715055423323784, -1.375689049537495, -1.5241708728015388, 0.02757098162445855, -0.0024595538213373746, 0.9503996622205587, 0.05185156095398632, 1.944830409108621, 1.2876825990743426, -1.4358953942715595, -1.7270360921414547, -0.34144212073480806, -0.6180838932950364, 0.40595870646030935, -1.1615260214591803, 0.5637220497696013, 1.4029717552977041, -1.8108553067497646, -1.202627622671335, -2.0039095442581267, 0.7061415767056285, -1.2358048743537953, -1.9570214600406086, 1.374528663811083, 2.307246288790384, -0.02025925480606931, 0.010981261020704208, -0.0350623531446272, -0.015362320268308508, -0.005691205988615438, -0.027147508589305244, -0.027749083170305677, 0.0277923821399392, 2.5136390873149805, -1.9576225334349844, 0.702421244490003, -1.788549915802491, -2.878583273127716, -1.897179340521887, -3.075994241466237, -2.587450387425032, -1.8220795593456212, -1.2275075730975697, -1.2182223736578808, -2.411459498852412, -2.6333610975561914, -1.4077954510091353, 1.4598640535282636, -6.285054685349747, 0.7270696231016144, 0.2534660618760359, 0.27176382085926126, 0.4909217669658166, 0.2577370094335709, -3.579791023867298, 0.45466536292148524, 0.27360266721032284, 1.7142596072756533, -0.5619592335504511, 1.3727677663236528, -3.158447663877059, 0.8018524217480701, -1.6737525235742157, 0.8101725750283464, 1.0291778660614535, 0.5814761773744047, 0.5355388406828859, -1.036113064115172, 1.5593888491785566, 1.5193961929643536, 0.9013957893118536, 0.9942239345753338, 1.4709879091066485, 1.192601963486935, 1.4564708313124992, -0.11965665996867292, 0.889009789172657, -0.9146539270674547, 0.5486804243823687, -0.6174011476184621, 1.1005481353077544, 0.7493470752185831, 1.206813755966021, -0.3400816365582302, 0.08295596922228791, 1.0604922946371083, 0.28799201420078646, 1.5964099685254225, 0.6343711940164494, 2.3240453051035814, 0.4716761437185979, 1.3548686130736938, 1.396210573335514, -0.5990930099936868, -1.9809601465962552, 1.9726757004055722, 2.5461216714626813, -0.5066950693682165, -0.7631097600663777, -1.6192678108994005, -1.8149334191422408, -0.0812444651238255, -1.33556514111834, -1.3863608090159218, -2.00416261587224, -0.5886248982855348, -1.7778124532056458, -3.0836048906710216, -1.7927248995525638, 0.07572582952092245, -1.1587212779469171, -1.0513410295789434, -2.0813390390553015, 0.09316838414626076, -2.3301415256512783, -2.2951694593915675, -2.590415613053505, -2.6033860458137132, -3.7537433842567896, -3.3126006266239987, -0.13790810881656665, -1.7696670952697504, -2.1983115093809413, -0.6521043266892602, -0.4003820415934886, -0.22222973529391046, -2.0783050254155384, 0.2674576393632407, -0.02633739810032231, 0.21489163386564175, -3.613220497034186, -2.8840116239356757, -0.6783658364000621, 0.42142130962774565, -0.26275890564949045, 0.4030891522572358, 0.908320182102323, -1.4059150213609333, -1.9939924467958208, -2.7819692340404143, -1.2107808167909284, -2.5405844749993984, -1.3188756540299775, 0.5722395945791217, 0.22229421069389113, 0.09750217735733387, -1.9193076217958316, -1.6903995486072392, -1.101602691586318, -0.7071278408974672, -1.1153208447242902, -1.0361798806988414, 1.5990982228359898, -3.4604527527267295, 0.6832939033124146, -0.18808805924553446, 1.1805856539299302, -0.024568437009079236, 0.1544829764331264, -3.9239934364510995, -2.4275308687532067, -1.050999595236281, -0.9235700911978704, -1.7406199954272112, -0.9747079688818464, -0.5275215987357177, -2.5419494202466533, -1.930716820310228, -0.040909864698004686, 0.4975123351700566, -0.44987584496493077, -0.9605555875741204, -1.2026515990963988, 0.7532351173386922, -0.3847011940399153, -2.4419701157056126, -4.010517091442903, 0.20012743453256038, -1.7328837405523376, -1.4924985573847052, -2.0102740547693507, -0.3269023695197405, 0.6402707106872632, 0.18372923356640936, 0.4483639651598328, -0.7244938671231534, 1.2222483020086645, -0.44484002391784305, -0.6834077414309839, 2.370520726243392, -0.13104137857487377, 0.7750196592489357, -0.1276577900528365, -1.1666397000448616, -0.6566981110127442, -1.1329483200109878, 0.09958495298696428, 0.8902170231451696, 0.6559944189722798, 0.30936071526297493, -1.9053147788157638, -0.2261834969134551, 0.5432047659057477, 0.047991003027747746, -0.1371759278186375, 0.336396494488205, 0.900829728311768, -0.4221557956986457, -0.9079017869126993, 0.06340294800670858, 0.3705313027258761, 0.6949153026583375, 0.20410463692836942, 0.15232127179484256, 0.7402489074723487, -0.7912111682812003, 2.5890663885808127, -0.25930673561323686, 0.5326041541943216, 0.3611221201613268, 0.26878891295948815, -0.16310336254617103, -1.3397474491558534, -0.4182324600920095, 3.7344941047565903, 1.527770937444163, 0.9468282636328113, 0.30885902957943917, 1.098495365580343, 1.2715201582410534, -3.5114752727687524, -2.968780061688488, -2.3879176332273326, 0.7908745099374764, -0.6720347998566429, -1.4659220429793718, 0.00953456790225552, 0.8940131657221445, -2.677525422825921, 3.267243975323465, -0.5900049107763672, 0.29186697040245807, 0.6391088593399248, 0.17828999606331172, -0.14842674581213725, 2.273617044408357, 0.20925552272942247, -3.0505346287418265, -1.1994958618096607, -0.017450391118044365, 2.2033284103923947, 0.9998232007420654, 1.470587538031037, 1.1178864810915958, -1.6251485831053833, -1.4727178337265747, -1.1428228160014797, 1.7877351670491515, 0.9031130527734806, 0.8259344516913529, 2.361410754688943, -0.8804851852812806, -0.8024024266082738, 0.6650087973758148, -0.7706461999735835, 1.20714060793679, 0.6001380441654134, 1.9576422379762395, 0.6248296931087188, -0.43949637208592274, 0.040544968299936264, 0.4195984447150016, 0.07765368702985305, 0.3571031609737679, 0.8247212015402953, 0.500619220694437, 0.2043630550016745, -0.7484921751016115, -0.2807889059031638, -0.5645752353003701, -2.8863331892869377, 0.4947587281436444, 0.6000362983171109, 0.8035381886932961, -1.0169309224631777, -0.025939515233898498, -0.2492994833194279, -0.03542196487521708, 2.5913882144447595, 1.2137448053203117, 1.7894269870339523, 1.5720264375096307, -0.6954491119664968, -3.6180954112342154, -1.9912624149384754, -1.0678027280949285, -0.05010166853939209, -1.0733311429626884, 1.4145261792236932, -0.11954060238943368, -0.6418034201920927, -4.460021773125537, -1.8071068241251125, -4.7208460077392225, -0.11410798324295438, 0.87503419697868, -0.6789101744983878, -0.2746729271602192, -4.605779716911208, -5.696377239171938, -0.05543713113037288, -6.121218728443903, -3.712396342289898, 0.3673094133932419, -0.3386017556027904, -2.2311954010553445, -2.619927036428838, -6.463568960435609, -1.977868867547553, -5.148129048078879, -4.703112839730694, 1.0367435756302266, 2.336503021669254, -2.9198255387407808, -0.8158338155143672, -4.601287180773744, -5.038606304451504, -3.467179047947146, -2.1421142857826645, 2.221825085358026, -1.2291798545639967, -0.5963677162662561, -2.3449564966108474, -6.018268189811281, -3.4004427081719446, -3.7189698911095865, -5.518411893990812, 0.3028978653965045, 1.009991993209573, 0.08583902969507076, 1.5840738913176595, -1.402835524205102, -2.8341952012611555, -1.1303980216521141, -0.9742600728303529, 2.708317083173772, 3.5805392845616124, 3.2013003811881298, 2.3785099280818733, 0.10505945032712091, 1.1010117376554882, -0.3383406161761897, 1.5350711331617397, -0.011195022716100187, -0.035487597188848696, 0.034976209781566375, 0.014219323693690474, 0.024273957767720362, -0.0038262357593830862, 0.017288545446476032, -0.008812817232945651, -0.6790554104214478, -2.635693537339852, -1.4339223056056263, -2.090302619511625, 1.1049438282438264, 1.6224111219168789, 0.2506949602076081, -0.1086384863042426, -0.2105301277839709, -1.5450365064923315, -2.404020255340833, -1.1864152426333896, -0.017283820420876804, 1.509616234536635, 0.5149769024382779, 0.6995985283169353, -0.16443218614699126, 0.4378817440808545, 0.4518039985871469, -3.4132328572563106, 0.11731870788134173, -0.328422317730871, 0.29513123482120995, 0.5580460156532036, 0.35083584696593084, 1.2690793195393053, 0.9775061785778641, 0.8245924871566023, -2.4543636905382376, -1.2516311720510422, 2.222827724183403, 2.113716373250929, 2.9954818303415167, 2.473126476746509, 2.2289027146838976, 2.0840343512374786, 2.571629605239777, -0.668052353814592, 3.5609119060316186, 3.288039449168041, 4.345912286811132, 0.8614103435217119, 0.25499853258681043, 1.6320972078392117, 1.2951220641272312, 4.345284098517753, 4.370446821735477, 0.26121662971097626, -0.008998092492774529, 0.02358095512786026, 0.031000121548028028, 0.032663793748763846, -0.014105650996933004, 0.035803491994891266, 0.02027856947786011, -0.02230923635870062, -0.06471994576061167, -3.4354503366531004, -1.2130795797278975, -0.9217238807792052, -0.7298475023649801, 1.06465920373635, -0.4925191379146893, 0.49232831468938687, -2.8634861664236517, -1.4279859770509258, -1.787541241593704, -0.44624752872590606, -1.6481407352292046, -2.028171131437074, -2.408020577295452, -1.6599829998482876, -1.7393170353355243, -0.6074120308828606, -0.7954328642196627, -1.1901737982186742, -0.5551384868180501, -2.257286124458663, -1.641875241446356, -3.3958027002242464, 0.16514205568090629, -0.33247873210492973, 0.6286401681961578, -0.10251475328321322, 0.7145846310943612, -0.4522610291405091, 0.1747743496227107, -1.3177356252147083, 0.7418670611226654, 0.0013527875221903483, -0.2833104938327383, 3.1675759659142493, 2.147362782076588, 0.33573428938292693, 0.03425640637904148, -0.30208494348540516, -0.1827469997520863, -0.4046419495120797, 1.1687448769904334, 0.105977145913284, 1.4935288583053108, 1.4622484451180178, 2.5330886569884137, -0.21803992045773934, 0.43760120649998874, 0.07149026186284582, 0.43784640182049794, 1.304865134084599, 0.9159560224800284, -0.044638739471639, 1.8854048405960024, 2.617601763611826, 3.1588536185367, 2.1110801052966517, 0.14628464476436828, 0.6711486540402505, 4.481863923773794, 0.9400293079176932, 3.4931385120653435, 1.9856739830138908, 2.5067140190048973, -2.9926880586867943, -0.024182895224296935, -1.5306516800568006, 1.3667797268998554, 1.3834439018461187, 2.4676767594704696, -1.749112480283034, 1.1816275563053673, 0.3980937803281734, -1.453125784944445, -0.005976158414946998, -0.2890620830561858, 0.1990700251665069, 0.12893198562527416, -1.8751840554992212, -0.44804837354485005, 0.8122052334101321, 0.8353213074656081, 0.19216817511232384, 1.3957468390372778, -1.1125941117794271, -0.2639281811778827, 0.9844377507375853, -0.06826689820337441, -0.8800999701876676, 1.888002067597277, 1.566096582619811, 2.5809381766844597, 2.5061133270927405, -0.05988549674426417, -0.640894240519095, -0.6962725172322123, 1.1836369897304322, 1.5849770735449105, 1.249169993043881, 0.2481433358945685, -0.6589093672600941, 1.6811576492580578, -1.3622178219883403, -0.3590970945347866, 1.5234106314448645, 0.1380932011436328, 2.0292322400007636, 1.4450663111965005, -1.2222449748297104, -2.1261113343406377, 2.26821629484606, 2.0044032453364253, 2.17826017577101, 2.2202396751757547, -0.8212331015173882, 0.2855710497057897, -2.148958573387572, -3.1167189487539413, 2.6922692509676827, 3.4265645770593323, 0.545264907771967, -1.2889986624953715, -2.5495388605987963, 0.8013526087738859, -1.8148774597966666, 0.37379150975201925, 1.0943910161832018, 0.7447866512223767, 1.8467004192932475, 1.9610948213299633, 1.7942102737791112, 1.5170924887386168, 0.7532783831464535, 0.4891618365364546, -0.43212823221829766, 0.6864212847490933, 0.6569344041657152, 1.8031117133420311, 1.2808675593374532, 0.44392759073646626, 1.7603361376963678, 0.21909279754348837, -3.9373988145317353, 1.669464729112872, 0.6733232095454312, 1.1212540354611922, 1.0982198858656487, 1.4736677168476104, 1.943959487848267, 1.7036859216425522, -2.2012440048365853, 0.5901712162565326, 0.9878537000983293, 1.3162365190894754, 0.9678228322790043, 1.739583812420048, 0.8540955963783537, -0.4553774768127477, -3.249285603618852, 0.7838558625824106, 1.7653455633344224, 1.513008369132629, 2.603182988852058, 1.5159965559370605, 1.8120553054432897, 0.9847378357822549, -1.5820837023900896, 0.5323479726169644, 1.547089649102243, 1.4046246392433404, 2.177223842037511, 0.912955474085949, 2.2352058207849907, 1.4259585763523577, 1.381022788393732, 1.8725722569515082, 2.6269175494337427, 0.9225391458028234, 0.8309405725539392, 2.146834739043319, 0.5005820361192828, 3.0329453654172003, 3.5947898449141507, -0.08481671796465687, 0.9461395763333664, -1.1635352913200723, -0.011335418579139733, 2.4437632964931075, 0.022033702685481542, 1.7770192485157075, 2.726987110098477, 1.1496055923953492, 1.417531765946736, 0.7366427067477213, -0.39979274296155265, 0.3192759364716357, 1.943511888600711, 0.6239013005356907, -1.0202627152374029, 2.247635443295669, 1.7482596543489066, 0.4002889463991336, 0.49658161412616164, 0.27357769514473307, 0.012961209738972636, -0.37909066257487095, -3.7639796000781387, 2.0735423008799567, 1.1639628577961958, 2.269379989886607, 0.8394378237208648, 0.8696694917880866, -0.6395663163004518, 0.5096693882206751, -1.458172270473484, 2.6923832206336265, 1.4017003073847907, 2.213205937454618, 1.758252664758392, 1.7896528184126532, 1.169704702549727, -0.8731885652825804, 0.11234842471034255, 2.2001861184200244, 1.8365763978683327, 3.194877608871755, -0.44106741031999, 0.45409898382720243, -0.9543194409106087, -1.0707069733250851, -0.0707386830473233, 0.8041902993608872, 1.7281585418681624, 1.842710346585275, 0.8713229185964136, -0.1288202725653463, 1.651860716052925, 0.17706659346058237, 0.5205258542944909, 2.474596875353963, 3.1336714408239095, 1.6787285262519096, -0.8225601130545601, 1.8332415757875997, 0.24624937750024362, -2.3335297856343145, 3.061256356146381, -0.4355751267220042, 1.1764490021721223, -1.2226651164909736, 0.5380625281309073, 1.334723621165929, 1.0410854868306132, 0.9724597313242169, 2.6182813734172456, -1.5660217135568115, 0.4780883237359914, 1.1144196196989653, -4.718621098256369, -2.8856415655988643, -1.129215905267488, 1.415277875826113, 1.7421861868451565, -2.4030962561490425, -4.264493429698217, -3.5484628197297834, -3.5810731608369446, -2.1461383600923636, -2.928690525616989, -0.23645800543039722, 0.6122012135667728, -0.3957538008971492, -2.7511038763505917, -1.651522274367149, -1.3493885880247645, -2.9794439684888188, -1.9729130505164967, -0.7045745062070707, -1.3870172435969106, -0.3537945642605635, -4.411611219093592, -3.504090724559571, -0.6632999133447134, -1.815168445302469, -1.5211303549935111, 0.5338001496697582, 1.3664315641408145, -2.0027786973114288, -3.965547336133778, -3.806765121718634, -1.1137876129536215, -1.7866999629918403, -0.9713980273161674, -1.287660133274807, -1.0972102159135548, -3.941683323113343, -5.331574156215802, -3.3151979371849873, -2.0566293808552465, -3.594106688867516, -2.486658608640138, -0.8829183300795976, -0.5243940926043029, -2.4944337039300675, -1.8291321511623317, -2.274258758578674, -1.5737947493492999, -0.58115106791766, -3.323996479827954, 3.2814380689200413, -1.0596777494738845, -4.803301877242953, -2.7423642195874165, -1.8366502314740178, 1.2519713204499798, 0.10955109500417881, -0.37403354201722877, 0.7030686540559814, -0.3530466101490271 ],
				[ 0.0038070075787342123, -0.011197783027822327, -0.023713549325764537, 0.007895922577002187, 0.02755181583811881, -0.031177345269500067, -0.03474699378451563, 0.0037129581878372737, 1.1255086420234262, 1.9287386839542038, -1.6097731413804413, 1.1149415190471395, -1.0389646904869465, 0.8994311775805058, -0.331167082141483, -1.806057741556272, 2.314947210066629, 3.101526488085969, 3.4242784219956963, 2.2485044832889844, 1.4141994231110944, 2.199630182986794, 0.9490850028984337, 1.2278956959015823, 1.927324460190178, 2.0963000224120996, 2.7100005734465924, 1.6126715253954866, 3.27903600005739, 1.5978308472796041, 0.04272722105306212, 0.2918999077668801, 2.5378416985652086, 2.117332502625473, 1.05210803395118, 2.8121216027845097, 1.2868978963468587, 2.3351069217400453, 2.724040981397425, 1.3206263953103856, 1.1752052552775618, -2.36469208521761, 2.2830061396830037, 0.6748946773658074, 2.080030591847296, 0.4588841766075291, 2.0281134123425075, 0.6023263259509917, -1.1543721576820707, -0.28617535521524845, -1.1919296264404677, 1.929254698599132, -0.6048509322945097, 0.7250406129347322, 1.2823712702915269, 0.7929109972410232, 0.011644201974045545, 0.02005131027740774, 0.03604429008793558, -0.011712861573563675, 0.01756697316471761, 0.02961129640700215, -0.02690732750212453, -0.012326127699613972, -0.6929274797500694, 1.1491900344398187, 1.0224590004365046, 2.9987534734341716, 0.4294836663978035, 0.635927565476564, 0.9265891581284945, 1.2769036250189771, 2.7044417263403733, 0.7935595338308354, 0.8209177144028188, -0.9631439621587612, 0.43228967367649407, 0.7385658604422888, -1.1122277876090094, 0.6345498846491283, 1.2600733096913455, 1.7086511471024293, 2.3428897394227293, 1.3459120831667097, -0.7333816965836161, 0.560421618117611, -0.6873982309531781, 0.3754744134572464, 2.111992563731046, 2.939052160737052, 2.6982114696899555, 0.7457113604559432, -0.7722033554873492, 0.6918046846128321, -1.346129809044086, -0.2162906911201265, 0.6767720113965835, 2.0132695640083886, -0.8041443586745498, 0.7680879773326086, 0.9885246505529413, 0.3570888323094169, -2.5698518180128715, 0.21594875217290027, 1.3732036783514292, 2.173113971079774, 0.41182921690037205, 0.3603510010294302, 0.6218501773637516, 0.49403187752405636, 0.2930906418824947, 0.23294942960046638, 1.524337123939175, 0.22968675107600575, 0.2518996800323335, 0.45305284389470063, 0.9597083912008496, -0.2763636372197058, 0.6557679309196893, 0.37521996425604964, 2.394172335540349, 1.8892773588744978, 0.575065942571367, 2.600922384774512, 1.5321159308585164, 1.511610724662429, 0.22287458311140113, 2.1474360725476878, 0.04959230041545284, -1.7149537673572806, 0.33849800973319716, -4.771202435216896, 0.07249785451114614, 0.049032964243361246, 2.496739133625529, -3.134692339797402, -1.2994457808567657, -1.2027566286926532, 0.28124503858867395, 1.3009387083749289, -2.6026696797491056, 0.2222244579961148, -3.1953852639819726, -1.01498768846998, 0.8341781056864266, -2.128148293511024, 1.4743226922455868, -1.0534548729262514, 0.9296744131989932, -0.6165303710382765, -1.760504022804823, -2.2434613009758158, -1.4708512303558756, 2.9349790053757467, 0.19483548055025193, 1.137111152762137, -1.599424323394063, 1.3275318272842809, -2.0855028581767208, 0.814559381752159, 1.5780588325530995, -1.3213295255959177, -0.10265368898777516, -0.32154945220481845, 0.8722163401978628, -0.8420597721499211, -0.003351812795209217, 1.8393074273091983, 1.0081081963137035, 0.11187820329660038, -1.8912845957260895, 1.0535544895084745, -0.79048077194849, 1.222472156012475, -0.3919351849565122, 1.2490051009832257, 1.7014477590005126, -2.4409158783570035, 1.2005994931922226, -0.7264997796910856, 2.3262995972485663, -0.28901570846813485, 0.8539289156721269, 1.8383354286638411, 0.629369358001217, 1.6696044941936414, -1.6010314605858285, 0.8092157127733351, -1.55044288561903, 1.4362831036467945, -1.5431728906104327, 1.2576444129268147, 0.1518678115425127, -0.07577791445207639, 1.9774076247345769, -1.0812970629352336, -0.6814305154222173, -0.7118355664381284, -2.102693999316595, -0.7619877171463135, 0.5782661436141399, -0.29233498239488215, 0.5112227298530714, 0.8817786192504422, 1.5350231728096608, 0.2062710373440636, 0.2229374721831508, 1.0556213810714234, 2.1016566237435095, 1.177238780083544, 2.3180117188514657, 0.8413116436818174, 1.823080362471472, 2.103688891971079, 1.8263298072030614, -0.7329643322200372, 1.5046844355932576, 1.3041827910781685, 1.3690572600485225, 0.6801628457039797, 1.0227801689632487, 1.3992731284321438, 1.6223776286615414, -0.0821168858506116, -0.4089092761276595, 1.3716829979895475, 1.045047465864292, -1.3006268321316847, -0.04607533121877472, -0.47710592494839565, -0.6572753269047149, -0.5218443540845872, -0.30037049470089117, 2.8040953691231736, -0.3741269250797241, -0.1588561809189805, -0.3581174080458713, -1.6726803374015065, -1.068806905219463, 0.020214375641542284, 1.7376078813106837, 1.542132367147784, 0.6277088351810944, -0.013879178358751654, -1.6140877022948912, 0.048599681520927654, -0.3832604541030182, -1.1416389077562044, 1.7803310467806686, 2.5228346458329964, 1.7993950094762945, -0.7522989026502521, 0.08607010042825554, 0.23042416124208084, -0.7599823542011849, 0.33443113594672624, -2.615051277376077, -3.6139089242547406, -3.40150379488404, -2.292263513912267, 0.6278886533254993, -1.4470080192680241, -1.2777934885690867, -0.12313443561152138, 0.014834842688199405, -4.197906276684551, -0.7191228869798704, -0.5160031108515889, -4.579180665678418, -3.197664445718743, -0.18880711640654033, -0.691893738901317, -0.9693754194589629, -1.4905064122540745, -1.285910902554709, -1.5414989836075255, -3.6998704335254304, 1.3182054721762324, -2.177764542903201, -2.145475694942694, 0.6226129612728776, 0.3858893049771996, 0.8332533703186794, -0.9920387325195744, 0.10701819429268523, -0.5846104032450444, -2.365022815203672, -1.1034672489936233, 1.882373087004278, 2.76222572695699, 0.24185067153395162, 0.7483905042782224, -1.251884392267589, -1.6902858020541462, -0.8306115448974228, -0.6921464659742073, 3.0810671954213573, 2.6822460844083422, -0.20596676739409117, -0.061355299690205395, -1.0540006213497983, -0.6089660540753238, -4.394939890822966, -2.6294663234184084, -0.5231201564181459, 1.6276155611382919, 1.2681244532556277, -0.18159075098809838, 0.38582656554750494, -0.0441134965579408, -1.094815232586488, -0.10062343511689582, -0.07573589301772408, -1.2390770839555183, -0.48332931473124763, 0.41439640377183506, 1.0730498866421574, 0.19529466962905975, -1.1444591250093026, 0.21436613122521436, -0.9798934747447955, 2.966030564085783, 2.482595603061468, 0.5570383212842888, 0.46326250150135173, 0.6803779408907263, 3.6618147767856892, 4.0105378922380694, -1.00690115967916, 1.6223808467626182, 3.0210091522152562, -0.5842661820415911, 1.1924946993770829, 1.2884829501724455, 2.9319650717771366, -1.788760090386915, 0.24347728169091468, -0.6047223011755395, -0.3986122273470752, 1.5109213951831675, 0.9663750419033541, 1.7784781830536742, 1.8922026931867846, 3.652683023365161, 0.25063706888423176, 0.27660381872178585, 0.7400332356028284, -1.3584126741021345, 1.619388729452266, 0.6755110515879752, 1.5184506890898035, -0.1547869024910061, -0.5159395160623977, 0.5480088649747168, -0.00014096348920330203, 1.9089511073632257, 0.15572066543858937, -0.0007811944145208591, -0.13165905921863272, -1.2944650750100728, -0.2489723569956246, 0.3981333451047121, 0.3991419651425383, 1.1993757884947793, 1.3035429367911933, -1.7829554164983275, -1.4201855679697837, -2.8110377057316875, -0.8542991264940474, 1.5788561725239376, 0.8784265962977758, -0.4979049775751383, 0.1330925323979057, -0.7597238897573766, -2.0372478141982056, -2.5707254532005464, -0.4528178835169824, -1.7321820650904707, 0.4239789305642503, -4.890536966761179, -1.5051252326181028, -2.1417662800995254, -1.9919234071537941, -2.9074203841133, 0.030716758280549695, -0.017109754271354045, -0.01465891498436338, 0.013928707132709932, -0.0033256518787905752, -0.008285582026349821, 0.005707426384373833, -0.01951453917979966, -1.7697933505169157, -1.0660813977391261, -0.22051694294154414, -0.5211058228659626, 1.1100179602499827, 0.18276864168587229, 0.47183803309305833, -0.3488007585181864, -1.1788833823990772, -0.8004643022195836, -0.23581275201847007, -1.221900392604259, -0.2523685304434564, 1.1260345947541723, 0.09594574003502539, 0.1463244355286743, -2.1431974927551676, -1.4232968693672592, -2.011270097033212, 0.2944495372462053, 0.13039178333784623, 0.297444405555817, -0.7295683258144952, 0.04793501040903107, -0.48772977554882585, -3.1194103176132724, -0.662441746800499, -0.08336376615158365, 0.35709548966292354, -1.2454196259249053, 0.36128478188753277, -0.7122459312768821, -0.844593252560484, -1.4532421106292963, -1.1772606277983417, -1.1012537479094642, 1.0600852339103333, -2.003639472135058, -2.878895130316922, 0.7936128759104184, -5.269989183303002, -5.2296724995911985, -5.561133319186954, -0.5595392929661857, -5.123570427877471, -0.8211712133314, -0.16569248565934858, 1.7811285836830668, 0.0037274857371456197, 0.021427438068049774, 0.012388786614392178, -0.012093418117327136, -0.011196063396912273, -0.026636829603773452, -0.008232756179281507, -0.0007189065334770727, -2.2653729157001474, -0.8628014922908533, -2.317546972302405, -2.846868963722866, -0.9231620793521599, -2.3919803359519114, -1.7343219809309016, 0.4062196245605028, -0.23136303448232198, -0.849769142251067, -1.0128829447495187, -1.6639041751093075, 0.2137344611359986, -0.8587756017809616, -2.837748625758845, 0.40710821199158725, -1.3494929017755335, -1.5063489025599524, 0.874251174626654, -0.9233866602180376, 0.6283402034135569, -0.4527959486899622, 0.14521070050388338, 0.24490279273226856, -3.8566755938612034, -2.738020131634502, -2.7808742854854764, -1.791252776343117, -1.0743204816241028, 0.8140865324110415, 1.1143878706279078, -1.2903507059621788, -1.5720408899635019, -3.710809824291323, -1.997793243487345, -2.130032766721297, -0.8305261905399673, 2.0941835732356893, -0.3949163890290902, 0.9911931558807592, -1.9314252090604493, 0.5683832237770818, -0.6500004745256575, -0.45740532227366115, 0.3076835452045142, -0.4378455483426653, 0.8725886928747965, -0.1344224794539167, -3.7633580039471837, -1.2118591301769617, -0.48583754079997543, -0.628225076685677, -0.7999177419068922, 0.057292936666222066, 1.1104961560514315, -2.7657306629742635, -1.8396953679361687, -2.1042990838302527, 2.1120752401115426, -0.12493970534446631, -0.26515497042177055, 1.5958208237179747, -0.08950574119523785, 0.22689232615965518, -1.0440739453964138, -0.04359683628191489, -1.5966930948840166, -2.0222259787582852, 0.2727893367754789, 0.3604018821685551, 0.7992578143126089, -4.672485543484506, -2.0115151884978397, -0.9072675367578192, -1.9268483718254716, 0.014823767402712537, 0.07527741058294528, 0.5650475348831739, 1.8360805254137877, -0.5912992420304214, -2.14619484418329, -1.1806237729922016, 0.3875703832445178, -1.4218836531134291, 0.5326684892201811, 0.7622179393193081, 1.3853985457652942, -1.1006896801377288, -0.5193971641146813, -2.035699206972411, -3.254796471682613, -0.10474113385376957, 0.3935209312846246, 1.0921354186065666, -1.1948069822652791, 0.07466568213564043, 0.226605369085719, -2.5533019287360594, -1.6668019563251317, -2.6961828482118224, -1.3852638666466885, -1.7220466056137984, -1.391627731330181, 1.3781642315390694, -1.4451953559838806, 0.002031701605699794, -0.945300705427004, -0.379119693200641, -1.8647855426660156, -1.1154796420719741, -2.1997484685716184, 2.222359151103251, -1.4328481594245899, -0.26464555307575377, -0.9178760794502697, -2.460708252533921, -3.262862255000931, -4.627293851455612, -2.8881597689467795, -2.166555096097791, -0.1714603729816731, -3.3498326469824513, -0.5189226021589187, -1.0146070602597164, -3.8588049601962924, -1.7382104964667198, -2.4838654062440586, -3.812278456325214, -0.20164520130297364, 0.12383292451887043, -0.34711991904049044, 0.42575442973255795, -0.4988320023598854, -0.18099533766493806, 0.8279023402410312, 0.1591601684874183, 0.42738564782330585, 1.0692700898853598, 0.8630085216842743, -0.6333940324730363, 0.2935487120441567, 0.8316106959470482, 1.4595835702845186, -0.4920971220801387, -0.7325183463641353, 0.1503462748714677, -0.24128364899533142, 1.146073472436591, 1.281023776739009, 0.4811943278130005, 1.015379695209733, 0.04222225722444321, -0.1940560586359546, -0.9759456623736066, -0.2557378014344506, 0.14076006691594528, -0.5489691278109685, 1.5321147771831614, 1.5175365955827194, 0.19837588218476965, -1.7264788694664477, -1.8112118295514945, -1.634182240459694, -1.4879209095620434, 0.7603678547423643, -2.054066305340045, -0.16353847352902515, -0.33812008795299775, 0.18683484876151468, -0.06500104029366013, -2.7239074735491875, -0.0522755414862895, -2.1097143418206787, 1.062559913724396, 2.097814903955994, -0.6197311243302985, 0.308349810392833, 0.4284164152755588, -0.1891383028236822, -1.440032262125807, -0.32519791925336594, -2.766481735898965, -0.9201441375224741, 0.45589401790348005, -0.2902747215940598, -0.045921578010102826, 0.1763386040327654, -1.5506743757744197, -0.3496671859775111, 0.12970538594191416, -0.679963247240862, -0.35647556692725985, -0.6641422612343957, -0.7684508535915164, -1.2698474586332307, -0.4726900461654994, -1.0465538781683517, 1.8410862019755554, -1.0273749750281527, -1.0500514512050354, -1.0272110232936937, -0.15480867911641563, -0.25843722520374846, -0.8752436535716378, 0.22859724690296251, 1.0362700058080345, -2.5644199670205357, -2.1421321651133995, -0.16255792420538098, -0.7336368041378978, -1.265398128675761, -1.0157405038527294, -0.5940513790458953, -2.491344325929611, 1.4946573414482354, 1.3740259187337869, -0.5245421203443402, -0.4727863933115363, 0.3848594285679577, -2.783537866795211, -0.2685464427802742, -1.1638243111365016, -0.13174188132985232, -1.2734851284417548, -2.9124476935094945, 0.7909017023453295, -1.4952058539563113, -0.7107797405555224, -1.8475421585710434, 0.9489661511126849, -0.6412520392366102, 1.8399095832878551, -0.7820669770816352, -1.5873046770470651, -0.25976358324285, 0.04401647734661068, -2.6590768166710017, -2.3323909956128346, -1.4094283028287566, 0.35106116627868494, -0.13221685748012044, 1.3914966183096253, -3.6265849601501827, -4.416627271506223, 0.02481876368482319, -3.070911072281009, -2.3130194624381377, -0.03590828375521605, -1.266231630944853, -0.8377887293634293, -3.17158272365666, -1.8105843398333743, -0.9264487121904945, -3.392746807560203, -3.5034457296527073, -4.423819337302711, 2.4549877092580825, 1.9625217058447184, 1.210113032483334, -0.4105156010795205, -0.4210979299401445, -1.4316997427745959, -1.0549316297204563, -2.2974347305081104, 0.3754315737346892, 1.8085647361048307, 0.8359994319810097, -0.3377527714872557, -1.7139900453734036, -2.155425623280196, -1.870036138289467, -0.8283934697079418, -0.3708533236932502, 0.1806396990040751, 2.3727866323537334, -0.36389118854098707, -0.8379223424892305, -2.1128843430281754, -1.3074472848500605, -2.1479741462405944, 0.954548380527835, -1.058057712953181, -3.1685492195634537, -0.588391663965041, -1.050508729520041, -1.6642074006731198, -3.541845641226364, -1.1832669200468158, 1.898232065545624, -0.7772527627097737, -3.6472270600599033, -1.4363475860552486, -4.798977304309497, -2.029485436611171, -3.9085792026807464, -1.9395709912897627, -1.7359140591851203, 0.5685909145653824, 1.269073471353662, 0.020735579536832596, -3.924022688680447, -2.370093337257688, -0.16659930028838554, -2.9411757157473186, 2.757565957350937, 2.0177057879675155, 1.7496771637791921, 0.6834474192157436, 1.2048346874876492, -0.8666135720998632, -1.6705472057470683, 0.12427682872050251, 2.8657399648664876, -2.432087342830371, 0.3174308754278913, 0.6327031638629741, 0.2777458872021571, 1.8784021137789568, -0.3639725537521384, 0.23906115673362915 ],
				[ -0.027466381857759604, -0.0340035953113613, -0.002169648350369324, -0.024872369544020112, -0.0005811979287314844, -0.03279932627628584, 0.015276754258521161, -0.007478002073106016, 0.047582566617790846, 0.11179396275805652, -1.8848744331304723, 2.1767809992626406, 0.41467190715222874, 0.8338257169529226, -1.9273620122107666, -0.4374728740790354, 0.4680370079057527, -1.7103573866782187, -0.41860294173220386, 2.210271735247779, 1.0938782630724821, 1.120722271257022, 0.8847197009539985, 2.632340304860019, -1.6904618407041907, 0.0693524110456299, 1.3093012810986944, -2.062400209876232, 0.36439321884006437, -0.8526844804264834, 0.1741395696582068, 0.627187825639564, -1.4897681442627269, 0.48769575061749354, -1.6996569178400247, 0.8390529711061224, -1.8779579844859433, -0.7790043425535532, -0.3944640177262824, 0.2553231061788805, -0.33923039605591065, -1.4643983993213665, -0.4356828807611599, -2.9200546208774196, -0.1839459303848906, 0.49092493219797106, -0.22075862608098074, -0.696125243367407, -0.6352792131969969, -1.2121075903299228, -2.544453590811531, -0.4667674273132977, -1.0431219790679405, 0.2660961042726596, 0.8677135497334542, -2.254929430991172, 0.029182242499469525, -0.005867319608626628, 0.027623072312918443, -0.02948429216913556, 0.012384963725382942, -0.01800484749247115, 0.034871987296947, -0.02556655301804369, 3.641770898179333, 0.3199483725887219, 0.507783128348589, -0.19048381923092408, 1.171022874828936, 1.8168396203148407, 0.3370162929814937, -0.5832623863310288, 1.0174058121827254, -1.0702847854818351, 0.7182615160323528, 1.0897434814520621, 2.155375795086062, 2.264003157825652, -0.3343371810286618, 3.0741492983288, 1.4237839806136134, -0.635496804036247, -0.806900647973952, 0.18587583967643106, -0.7835436233565201, -1.097210928263662, 0.9222984724390355, 1.6109036044399145, -1.586092034641311, -1.0887274610846969, 1.003463215232952, -0.6130989683019018, 1.665889685324135, -0.06203881625768319, 2.5569522474899125, 1.2101316889041025, -0.25866985088517613, -1.2594007553683004, -1.6194418532821628, 0.8598257163414412, -0.6494838164433461, 1.618562686583676, 0.0023677943158679307, 0.4721124927001858, -3.543722692770113, -1.6661088614018438, -1.3734162990795025, -0.4210411938432737, -1.6369233047924505, -0.3067329953748407, -0.8591199189858432, 1.556555340105748, -1.898866311568553, -0.6570284134518938, -1.4306120507590625, -2.4229640365482554, -0.23184549340733046, -0.7362715377387086, 0.19064851911980515, -1.4233654656331698, 2.6647229343654932, -2.6750842301357958, 0.48155248711673, 0.39792438461784624, -1.5520136348946145, -0.7195711989909251, 0.2164533242968016, -1.3863084808304504, 3.0982938869534853, 0.4988287169133276, 2.6806286486087423, -0.18451209522118683, 2.0541770285094083, 0.14090882800530066, 2.9648677968511215, 2.540746095215251, -1.0325275309911572, 2.7812293880594128, 0.2291364999234493, 0.8184930994769914, 2.5156440423025708, 2.9064471983307856, 2.6416884336023476, -1.0950425256946525, 0.4347291608461285, 0.02879383550402143, 2.40327764181335, 0.5528297996497082, 0.5196567845734598, 1.0016076024184555, 0.21426695905645762, 1.764778116205592, -0.7915302857123386, 1.191258458603755, 0.6126613316375987, 1.3898363947970704, 0.21976074765657588, 1.3205110237108055, 1.5059254516813325, 3.0482103233576, 0.5196413262246006, 1.3059478376165756, -0.3353076032360934, 1.551114962637318, 1.5696084325855244, 0.73727933938217, 1.856314428976052, 1.4024156932791605, -0.5320955287423447, 0.4945788557072709, -1.7306319989974666, 2.156411347992841, -0.33490983926183504, 1.0215012068132536, -0.601023908297973, 1.3844162104140056, 1.6300010337645794, -2.018857420433446, 2.0408415814513408, -2.5617843647572336, 1.0096139700747166, 0.24360270335575654, 1.7500165045710807, -1.5425191904600857, -0.8360217978899293, 2.625328736433568, -2.2595318141837586, -0.8906796336481945, 0.508522836000631, 2.3896452189450472, 1.8746246221005847, -1.504562800124848, -0.17676452065130963, 0.7658023325537128, 0.9243010095127213, 1.1413016865736187, 1.0709251820991148, 2.9277758451912206, 1.7062946787632431, 3.0886087259891943, 1.207769667533797, 1.0926868169851742, 0.69402288988645, 0.13723021023942772, 1.0348983767277207, 0.4252665618676633, 2.7283306570837116, 2.398513562791727, -0.9385018693075197, -1.2288242142849093, 0.3490632175651455, 0.5813335340935234, 2.150747020667769, 3.2232501374180673, 1.616337657319467, 1.4685671080022324, 0.43309792231340183, -0.7928025502317646, 0.005693585445950988, 1.3923039747968475, 3.050434986364888, 0.8398945863669454, 0.8882258393049534, 2.122264431304973, 0.30178554952666353, -0.31765298353101634, -0.07526813745607552, 0.5945944719880328, 1.5003925901968642, 1.6241785437476655, 1.748754565108106, -0.37522165144911224, 0.8265458826959412, 0.9565360069159954, 0.9026521297442461, 0.7292271020078454, 1.4185746326985782, 2.140718145243181, 1.5559443187565223, -1.070326661592272, 1.3574722711505665, 1.643127733389526, 1.9344508561245957, 1.8077534101641017, 0.13000624229323918, 0.06357660755555476, 0.5863177009939162, -2.090874796190908, 0.9546554804642611, 1.3927973910684908, 1.2313180137447977, 1.544748259937142, 1.6042921166261004, 0.4006571359386468, -2.0675778180540565, -2.2000878431964495, 1.6356912602493376, 2.455102879524052, 0.12775406877180376, 1.5765816736898037, 3.062799634077082, 2.1187430794418365, 1.93684553376587, 1.9950396183599817, 2.407282699611827, 1.430234450868445, -0.045370252449409454, 1.391585013424942, 3.7034832289622095, 4.202837686685934, 1.6128578495624264, 1.9471615986948354, 0.8250155013461589, 1.9189148637550122, 1.1020143183068218, 1.8150215621420016, 2.640266808535093, 4.880315417593156, 2.49552826927444, 3.9698962788065106, 0.8413544140013953, 0.5058798209540166, 1.0134450979761975, 0.46892070040801814, 1.3865364464559407, 3.4995688529844537, 2.9645176793152275, 0.7203125067829976, -0.9487965463436211, -0.2531511239448101, 0.4901590868134838, 1.385682646819258, 0.983422158897432, 0.9927271818015708, 0.7082692903500291, 1.5782782973891931, 0.42242739688284053, 0.45648819529359314, -0.3547919764021616, 1.152465880352099, 0.5659146956703639, 0.11550716119981805, 0.12130325230877285, 0.002691193343771191, 2.1894954186627635, -0.49474469457293585, 0.5693944887650942, 0.12604517683590766, -0.6658160404421812, -0.43537197370838243, -2.1153176033969365, -0.4111633322113, 0.4811603573031677, 0.3308653356632511, 1.7320142630668225, 0.7799765991767253, 0.32721457143788374, -0.3754590883967638, 0.12764720236221982, 2.2308296448877325, -2.473323178042292, -3.50711299285781, -3.420576283203287, -2.2208960532086617, -2.0308305562569653, -0.4906994247272617, -0.48584021413740724, 1.997323815533562, -5.9407248915760285, -4.093034638745352, -4.173713613087353, -3.026500256469738, -5.256702804826216, -1.4932265990928706, 0.3979138548069665, -3.299263459592515, -4.333312656491828, -6.092872502124455, -6.363892637176728, -4.366875794044731, -4.079653205630009, -1.4667715912604045, -1.5549444693260925, -1.4719498771983055, -3.612187888699431, -4.905287468718642, -5.352304069905986, -4.266528206297339, -1.7465358624976974, -1.068765025139306, 0.22433497207313507, 0.7240175714004093, -6.454520121949363, -4.974698118343681, -3.4398319572546456, -4.5266471003871205, -2.6287995298421594, -1.3761055293233146, 0.17767182869061443, 1.6586917076537249, -3.3963793512939793, -4.193369376038357, -3.937357395314591, -2.224781130655508, -1.8202910966075405, -0.21995247585374192, 0.13840948807326098, 1.5858557605280037, -3.103593228073362, -5.039445653731935, -3.657522699030075, -5.161980145750297, -2.244805216621478, 0.34290463374426644, 3.0603718918200116, 3.386185884907996, -1.2135198069857882, -4.789871723450859, -4.183303134438213, -2.0355870843577137, 0.6243289549501508, 1.655944787114451, 3.2551003477326623, 3.2274762837461366, -0.03228121999767803, -0.021677829089106704, 0.014263776991206996, 0.00775233235622433, 0.026606544663977057, 0.010220682104215636, -0.01959333851894825, -0.005366175518021265, -0.7130988662548059, -1.10904836293317, -1.5534391860051535, -1.3685445304201436, -1.3248421360028098, -2.485026831607006, -0.26307862362404616, 1.703643755775275, -0.8464825386737462, -1.495079136069493, -0.5160226891231122, 0.4096057416602781, 0.05126706621441516, -0.4423693293763551, 1.0888220455137148, 1.0765751152110894, -1.005148342413651, 0.018449666452806338, -1.6600017548800956, 1.6792897734317893, -0.6248254198925315, 1.9030267762396817, 2.100281246615452, 1.7271883360597895, -0.1998728839397867, -1.1149200441854912, -0.829281895702129, -0.15402399690366275, 1.1889576513739217, 3.524053217418319, 2.446488540981826, 3.005790954322167, -0.08461490943792319, 0.09653166388364491, -0.010618042245958241, 0.4093257493212544, 1.7881860438311359, 2.8511816640543963, 3.4591363136643403, 2.6087660095905814, 0.7875041607277643, 0.07075472423763667, -2.473803138013562, 1.2578522278815867, 0.6060341583476205, 0.30908527700073807, 3.4754370805385872, 2.257184223208837, -0.02595041624697101, 0.030909073750364103, 0.023806036413886022, -0.023366334041669667, -0.019754607211676514, -0.016185475416314262, 0.014497209126589833, -0.0335383758329284, -0.9720725198050897, 2.0713398287829694, 1.2036031569908805, 0.8022681526740593, -1.2120607821229366, -0.6889867168318401, 0.5951368402037333, -0.16884477660540037, -3.0109314856310525, 1.0238634881087185, 0.13445115178373188, -0.13212305182540954, -0.4414418346072278, -0.2365669266789006, -0.3683499163480776, -0.8310725031616504, 3.208465468215214, -0.2341842592382745, 0.41874571537460786, -0.379833424806174, 0.3294850703412622, -2.3711818469523553, -0.6779616669437275, -0.7380618566353493, -0.002896734901446156, 0.09274612284599705, 0.73210107228238, -0.9939789417879188, 0.1445797240052019, 0.37951990390484563, -1.9705460178446232, -0.138638720864823, 1.4723414033382196, 1.8354947375733697, -0.8518260504303213, 0.8524214593113474, -1.0780647880459036, 0.12697440781777736, -2.8992827599572206, -1.512676781140033, 0.9201543419855541, 0.7541368746996018, -0.8976169223075671, 0.6058456967442066, -1.1161738602629017, -3.231063835362171, -1.4402873686111952, -3.6388129825952102, -1.8103469525384666, 1.5593273693374514, -1.219055408312135, -0.6889184705976811, 0.20592104284443202, -0.622548911277562, -1.5812324921133916, 0.5614801717190805, 0.8800835571455854, -0.05529029514910666, 0.6025669021798772, -1.2699162717096004, -2.9128733274923695, -5.784144622901537, -2.489719346495154, 2.55751547789087, 3.121860387739487, -1.9394802866046108, 1.0726365633308412, -1.370504479144315, -0.49824358622747267, -1.15321998076806, -0.36952407336379356, -0.10598460003434161, -0.8506487376048075, 1.7665396713988457, -1.8637777463990794, 0.47839987884686763, -1.683006703509145, -0.44011674700935666, -1.4954752185492795, 0.5761590069346738, 1.5932043874157542, -3.1881204346975416, 0.03659607014109838, -1.5090528330734496, -0.7118784577386269, -2.1075348954399113, -1.1619292912595092, -0.1688120423661918, 1.3878999476434843, 1.1211126965819143, -0.9063272747620852, -1.170147735677543, 0.6292331423131678, -0.5331580369698484, -2.640622036318849, 0.4915363565420247, 0.2628091659920715, -1.3780297274752311, -0.10892248912559833, 0.5252564697746706, -2.1598218385097154, -0.11472704984648747, -0.816565024907657, -1.1776495746915228, -0.6024963074521688, 0.7362407765296884, -0.06071374166607428, -0.3786773171231097, -1.8560046898954503, -2.1469257499124157, -3.3394842144033308, -0.4589167935789116, -1.5917384359223068, -0.47509057746824956, 0.9162866494476418, -2.86253677106327, -0.3456709340711886, -2.9094234817204288, -0.9379521349896857, -2.3032022263148786, -1.0594266914564265, 1.9333241618687822, -3.0968896854336236, -0.3595194259252096, -2.2020954834959134, -1.4249843924366132, -0.9088328651317313, 0.07028475683094056, -0.48754755108077413, -0.3360488450328436, -0.03236614898918158, -1.5398690815795357, -0.10629471589571803, -1.0382420007992446, -0.9552045397813715, 1.480285677686536, -1.665015696225986, -0.3754442645815761, -1.2646592559827952, -1.3568026167189924, 0.09289763166973217, -0.9627294039595568, -1.2502688828960131, 0.9585572454464453, 0.04018036150656726, -0.03671298891258067, -0.28769645974532077, -1.1688324678807447, -1.1762852389391218, -1.3033796818742225, -3.3693028348643184, -0.2217539582259656, -0.6811450820574043, -0.268387732442282, -1.1741546765118085, -1.548294714398954, -0.25651306785623784, -1.1087301724824337, -1.146766894740494, 0.31430138925877615, -0.1552842589417678, -0.744658276352779, -0.2502460073896154, -1.2298927562807442, -0.372433465159536, 0.6749682182762651, -1.372643312868057, 0.19268954625872464, 1.092977491719494, 0.3267710462965149, 0.7907071520549687, -0.862650675471608, 0.4828102650871918, -2.707395009050672, -0.43124445791615373, -0.2779321362405098, -0.4221022925649445, -0.13261338187662403, -0.764004304984429, -2.4792216088324035, 0.5452049870636339, -0.5779882927752656, -2.8128910201577555, -1.466652959782344, -0.9384360275966124, -1.6997664791218525, -1.5364623169014087, -2.302671243857326, -0.26807883870693566, -2.8586763668898256, -2.702086189747036, -3.8006514935894655, 1.916485262807881, 1.6002057546048056, 1.0281237547857858, 0.1616716338569805, 0.9335622524912542, 1.222908172777681, 0.15916691193806437, 2.425740335231502, 0.1563191062403879, 1.373009712746657, 0.5955023001979205, 1.668592297494153, 0.23223040087947147, -1.012945344743747, 0.6170273248607981, -2.253020112573553, 1.9035565554100948, 0.45270958632551905, 0.31860167386721217, -0.040037351418207676, 0.7019584161656741, -1.8735079450604895, -1.138935059835498, -3.2435039415829054, 1.272433174930775, 2.17452406191751, 1.6792073517700072, -0.15750367360373999, 0.7321472156636047, -0.5442178074541869, -0.8027025975050025, -3.33032363919426, 2.052624896136253, 0.8583850938548503, 1.7503886721215305, 0.6765965280209635, -0.28194078906780157, -1.1284649115630399, -2.5998393623269314, -1.6617752074668115, 0.15937479379441527, 0.3972057611658317, 1.0237044974202405, -2.0925304268334695, -1.4449263123619858, -2.8947771109160985, -2.4632933479794272, -3.9417144712634706, 2.128952747536051, 0.7452080986310893, 0.46991348609122463, -0.4195244239462105, -0.5499879864514511, -1.8467629957805887, 2.0060617622693906, -2.5256189438215584, 1.615532069347637, 1.0581804806160573, 1.3450032579897964, 1.0225983989750767, -1.8436622927896094, -4.042617319335707, -2.5272487119072684, -1.0982329725465536, 3.054911451758235, 0.1387888119004505, 1.688352732268707, 1.4017741357546705, 2.018270532603027, 0.3628350630749539, -0.061340259990344925, 0.1142267128779322, -0.8001182758403077, -0.055292240886055694, -0.40503602063551, -0.5855848618187375, -0.6615299412361152, -0.638128645797304, 0.13458175892282426, -0.09750806049293599, -0.3151515636332074, 0.08338181464600873, -0.2390218813430987, -0.23929753318843489, -0.39316265270346246, -1.9299943504766952, -0.9320376555257284, -0.4464330904317619, -1.2876675725586686, -0.056267113386794444, -0.38874346320068426, -0.6560150149458707, -0.39459053840388525, 0.2785681449338467, 0.24166678352752574, -0.6375134161506233, 0.29515979518045077, 1.3943303988570768, -1.192862125019123, 2.1935105212663237, -0.19721806808712317, 0.6623275097847356, 0.5186924629977504, 0.36746500962772183, -1.338670273837071, 3.262229853700189, 2.695958358605738, 0.2889363813779051, -0.32290706209450554, -0.9595651992076325, -3.0648506580715615, 0.3522125750956377, -0.0924491820122574, 1.4536397767676714, 0.9871961514303272, 1.021525558436579, -1.135222326945264, -1.0013740076028157, -2.0824282670905943, 0.53147774431082, 3.7704301845186565, -1.2703286626176644, 1.693654393295839, -1.9949562586803158, -0.09655560560267071, -1.61064905056087, -1.7817111237968402, 0.05833708766518812 ],
				[ -0.00683052690116578, 0.007832231644539191, 0.010606474967849598, -0.011435544344397919, -0.006564196189512049, 0.02353381405148386, 0.029285334621573168, -0.005123637643848507, -4.431426190426805, -2.257634232932783, -2.49073484744883, -0.1423053084698951, -4.901055589342535, -6.188817557961351, 0.5180437804376746, 1.2048741674716492, -1.3246152683189056, 0.07542742935036158, 1.2967398725109116, 0.2721047159965052, -1.0749100055007241, -2.211071010736937, -0.9939862118888064, -0.5280134976543763, -0.3023875255153858, 1.3407851399609307, -3.157887518169352, 1.308021250931339, 1.3144398113696694, 0.0792883871869792, -0.5674721323579394, -1.199967608556482, -0.6127705123811327, -0.8874244439846859, 0.5676902954847817, 1.1205197354153758, -0.2359672439108097, 0.5672487462294681, -1.7430785223225895, -0.4920720079034321, -1.9157448360254534, -0.6055680575003067, 1.961834053015978, 0.28425273945306184, 1.5253107668850134, -1.2787580295726726, 0.9724571247447983, -0.21550005015381923, -1.4811726546672463, -0.8569428535093163, 1.810298950892152, -0.34015454112006266, -0.8207358139332604, 0.6003471426339314, 0.23369557337307403, -0.9072889291479659, 0.02173374050570672, -0.011916175525305956, 0.02332049440282475, 0.024457233091369268, 0.006890248612342832, -0.03349647997067354, 0.01698230570504446, 0.007293254941911384, 2.2847249832426972, -2.5288081951300927, -2.4423772613888435, -1.3775338993349107, -2.000014108968585, -2.9642080423668618, -4.2754091905295315, -3.6764330666253717, -4.542660924052974, -1.931739123362398, -0.3973749242210236, -0.9969994315783232, 1.265700914235233, 0.553541667198274, 2.749504012088647, -0.941863600926322, -0.9502116479329203, 0.36156514858190997, -1.3594005442532078, -0.6047965743878743, -1.365904448194813, -0.9271684565664629, 1.0650546239663596, 0.345513896302186, 0.1815607535782239, -1.019694371476509, -1.6527372839634482, -2.761388540742072, -0.17230038283145882, 0.23083326907715568, 0.5818280720666934, -0.5730292360126255, -2.7881572152635306, -2.8597131221831726, 0.9034162235489104, -0.3535065866242637, -2.614786257677322, -0.10068535880156071, -1.6344238741874295, -2.5549504519456008, -1.1491933385468889, -0.8519731267441961, 0.6337959932135965, -0.870598606270892, 0.1786016755858228, 0.6445292065010025, -1.1294605985431883, -0.5612329402662634, 0.4945771232671797, -0.49637827518233146, 1.0582572766208935, 0.5485069635021639, -1.382818207962046, 0.26342020084582124, -3.0625766464544664, -2.7466210941388205, 1.3696282941747626, -2.5058462776363606, -2.362933903632761, -0.8016168842659153, -1.4360530175176465, -2.554638214242456, -3.795743242145907, -1.39032914141516, -0.5135573337401567, -1.5739571839541895, -1.032599288758559, -1.849135404526728, -1.3505696580652597, -2.1164512419528063, -2.1821688662687895, -3.9595432979405008, -0.6895913130408674, 0.762203125696539, -1.8277823464498857, -1.3733611792016542, -1.7049451731646725, -2.66514833681085, -1.9056529173971992, 1.2264440840251403, -0.7800991208224071, -1.371485226319403, -1.1714805430198783, -1.1402184490367266, -1.0462965347621298, -2.279343024713595, -2.69314104222369, -2.0224498078741724, -1.5582267113221497, -3.0263359219178105, -1.5632771562164203, -0.8091737312190278, -1.7845828803592843, 1.2502215182299605, -1.7528421813010293, 0.27377563179017156, 0.2670018826885025, -0.591625360333012, -1.8972862643430435, -1.597048213294844, 0.2638927649096537, 0.17375539351212063, 0.19268469643821082, -0.7444231528440415, -2.426782390977947, 0.838166279079583, -0.8016183429244294, -0.1281219330791469, 0.38011859546781485, 0.051102010355046086, -0.07537281018021645, -1.292978464068062, -0.6404708931272184, 1.5090969435266148, -0.832372137233843, 0.922221054437055, 1.3442596343176136, -0.7202392674313076, -0.5846486552862681, -0.412428672627213, -0.40985854362119045, -2.1743875062943707, -1.6877776203895396, -1.1109733848355807, -0.4284496710391585, -2.451505949820345, -1.852957748935605, -2.8974646910804336, -0.912535357669296, -0.3882430673355713, -1.4008799535965297, -1.5955865779366867, -0.5383281850444612, -1.0940980205202864, -1.7055441863961565, -1.224106339088946, -1.405921797148956, -0.833436300153428, -1.519971605421354, -2.568690640566334, -0.6346471917429397, -0.5602138022974548, -2.848016746072058, -0.9299014750338547, -1.077164834018556, -1.4630859563681433, -2.915723230974716, -2.2341639622702694, 0.41038175558440493, -1.0056972346188755, -0.8289851779881682, -1.604905487988597, -1.538777610648417, -1.6078003014540871, -2.4447414157847316, -1.9139374143232828, -1.618771586727675, 0.08380925135933534, -2.6546840555515288, -0.05987749690026275, -0.8339314832777235, -0.5139396865019805, -1.3118498560716119, 0.6872150063575806, 0.6782725907957777, -0.08640485744217906, -0.44530581751041093, 0.4442112158766668, -0.8902118199790078, -1.188038662014449, 0.5431722415971334, 0.1406642304633989, -1.4444388924671852, 0.24673702605979464, 0.2526275491380353, -1.210112967051887, -0.1626939304779498, 0.19712211355670076, -0.4685410879937912, -0.16727252961470684, -0.5397691911044615, -0.670139447346777, 1.2416102131906757, 0.6218289457394744, 0.16051831104722222, -0.02089242412187847, -0.4003243901523546, -0.030070571050422157, -0.18509490920654506, 0.362395597591044, -0.31255917579696635, -2.0731949004152073, -2.7400575939867053, -1.416840185157311, -2.93787552584545, 0.7126678966384751, -2.26929352892219, -1.960986320262066, -4.965824689920533, -5.464277014595622, -1.152971444116806, -2.8082841416116073, -2.1731312428194847, -0.30327562213572223, -0.16672029100770927, -2.900594490594118, 0.9576804810556695, -5.664086127760474, -1.2736510933478378, -0.301680111538946, -2.238631720868026, 1.2468769038156808, -2.351064188604211, -3.8030921225617593, -0.5736401556847116, 0.04554949520939142, -0.9852748987464861, -2.251773922015405, -0.38669186335129635, -3.813900457059847, -2.686092410029153, -0.4906262609990884, -2.7712683031870693, 0.567408872210692, -1.3426732102653431, 1.2100732511581773, -0.3908842591532727, -0.38258279143204604, -1.3544243948293102, 0.4162024972416597, -1.598401444185679, -0.3440842530421235, 0.18815802724016953, 0.7856184432442634, -2.7746931795741365, -0.359018005354168, -3.1062090992054485, -0.9269912685378519, -0.9033573452068426, 0.14958935989264013, -0.512899736729692, 0.6918918370908381, 1.129742176225901, -1.6869528624229009, 0.5848937433799067, -0.7389577257255766, -1.4606861909781266, -0.30730112352475725, 0.10774737280257607, -0.9732427425511417, -0.9990648088544333, -0.28356936678084776, -1.5111239223303161, 0.6263372223237276, 0.06227380112533391, 0.23314203931090594, 2.6923617302714584, -0.17350802936490722, 1.6607511904284908, -1.7533098504371107, -1.924397163436992, -4.2321124488109, -0.3210952544339513, 1.669805385348579, -2.038488356975657, -0.1515736040565795, -1.1372315648865576, -1.9232812091666314, -6.201441941824247, -2.085799695492736, -1.899499132316298, 0.19674954841762934, -0.5482855488011044, -3.823818963432218, -7.189249947417438, -3.851525114055981, -4.592718425510048, -4.435886981392858, -3.6395395483500574, -0.6904180118554492, -4.839378460235492, -5.476550743297271, -4.267718130943992, -4.944199823563913, -3.0591897042460645, -1.3183566482825835, -3.415953834985559, -0.9261093238726547, 1.0409531922743602, -3.5703904844560777, -5.785234158015115, -1.567697241360075, -1.5280582230737003, 0.3472005242355952, -2.493844483219504, -3.5624423983504125, 0.040926318742297255, 0.2156622176838103, 0.49191833199560847, -2.3564934948810783, -0.5561814548394093, -1.3576734751486936, 0.5166254593443236, -2.428706433783832, -1.6670593408980992, -0.7737204820871598, 0.2867803053836069, -0.2636458548217187, -2.7815591335208674, -0.7290359264717213, -0.3198554483914428, 0.0003672466362712942, 1.257985901994905, -0.38443542618166243, -0.1427182693279668, -1.7293346068330984, -5.347197218992618, 0.32890881000559996, 0.4040928428859327, 0.09101167134492218, 0.01772981003599238, 0.0024329404891116537, 0.023715024910401082, 0.021303949614800047, 0.035184010992295116, -0.004795513538455967, -0.015083206564665327, -0.012039418894788032, 1.2297531732932185, -1.6014745277729308, 0.19530753257889563, 1.4456579733751564, 1.4563665070907035, 0.47565966384989816, 1.9334214519701514, -0.3980554475755147, 1.2015612334856913, 2.1690961420986685, -3.2737903362304928, 2.689417772744616, 3.127898226401407, 1.1967270805778543, -0.07518935103980583, 1.2302245431072079, 2.2014826378384718, 1.9678089757849406, 2.6885130390231726, 0.38097002057115303, 1.972232297236957, 1.2955803694842274, 1.692596019233468, 1.4983015160722324, 2.1836436785278233, 1.7676274328640629, 1.354175307132986, 1.8547429469200731, -1.7802180167765034, 2.291197336856913, 0.46140660379206505, 0.6255601522555788, 2.8595812613326665, 2.349102793272576, 1.678895344537359, -0.9380902087936002, 1.1818381053141855, 0.6744203484994483, 1.531792734915996, 0.9942062154773855, 4.058274785810947, 3.99298079806828, -0.502798935673563, 0.7403492843016645, 2.332372606112172, 1.8620622342626887, 0.06244272984068394, -0.6715347724916262, 0.025968169908662707, -0.01615851337508602, 0.00123715816003903, -0.005163745788462742, -0.030434821604073504, 0.019004929865867378, 0.030534763745502087, 0.019256739740769163, -1.181447350097608, 0.9222297033200803, 0.633175647739382, 0.06183799917649967, 1.7609259093565606, 1.9739520907178978, -0.6280307288392546, 1.8860097085563385, 2.270099916288678, 1.442239683134514, 0.7117340936543745, 0.2351013899982951, 0.42864730679275903, 0.6648998304501511, 0.5179003171273859, 0.26137793752173727, 0.54735585281124, 1.1733015828403297, -0.10607776471687526, 1.15120248116679, -1.0699937897914071, 0.3501480843041874, -0.3671707970035104, 0.5963469205848424, 2.16558581799333, 0.003306779252777647, 0.7678498016545916, 1.6186490797245643, 1.2890224573517608, -0.2745516341696351, 2.990668439725517, -0.23868439275621345, 2.373833240634281, -0.2227108069105642, 2.8384787676729566, 0.695515785379425, 0.04610002795585077, 0.7565355760376857, -1.2046188050489441, 0.04558462873069194, 2.1890679583629935, 1.9728645685379238, 1.9908407231475473, 0.5724137337493382, 0.6365798175936913, 1.6536857341723994, 0.09011992195947333, 0.6302335939756878, 0.9571921536252052, 2.4820795565869997, 2.841943997078393, 0.7538363383633099, -0.05750495978876865, 0.48491540622362966, 2.851022424347106, 2.1550332015146885, -0.6835998567848124, 4.239536587307096, 4.2995765649092785, 0.6786774086731503, 2.796075787785436, -1.6123760936034248, 1.0676923907292502, 2.140721896288732, 3.7921299317445833, -2.1477517501609884, 0.18864109701287152, -1.0466408972839263, 2.032615610987665, -0.002245236605781841, 0.8172028684094059, 1.9075476295923761, -1.4756674965594372, 1.4343079125783467, -2.3876840317814683, 0.45125213201889636, -0.0655643734995319, 1.652945401978691, -1.7974046761116416, 3.3839174619975276, 0.08966679068145413, 0.7179866143898723, -2.0484701151792386, -0.1314863992851253, 1.0053096237665942, -0.3769326513246639, 0.15817763719755293, 0.8908784952872542, -1.0065934189352674, -0.12635620526568844, 1.185166978390517, 0.48359726978028666, -0.587089780699794, 1.5479719151562843, -1.3357308594216073, -0.9931654217971153, 0.9653894639941833, 1.4804918306149328, 1.497508659628157, 0.17856580750117965, -1.4253872918308308, -1.6139286006160383, 1.6929736416193255, -2.6756315710538856, 0.6279754896741191, 2.260167410117194, -0.6227691862993678, 1.0685533994253398, -0.2608423007335587, -0.5178860236573121, -0.9507402543910133, 0.7659634207395587, 0.5115555135184443, 0.046138298206381156, 1.7306345210644387, -2.0867784412950363, 0.9843992618261614, -0.8532269593096148, -1.8307042385073253, -2.9679859942821354, -1.9380406857706622, 0.5956953389395373, -1.1748512567868359, 0.36849107062749026, -0.4959829100586195, -0.1344722682630832, -0.8995498162382698, -1.447736838428511, 0.6461732972216088, 0.9194497292053891, 1.1784716387456, -0.19387374320612513, -1.2611341374022476, -0.185622297642214, -1.9713581010594612, 0.43026201002427955, -0.6439082463614455, 0.7470506515699464, 1.5102116535924328, -0.1098459545040443, -2.2331416487524867, 0.32869841428057883, -1.6284651086806317, -2.420279261285054, 0.8785403681585243, 1.0932844662934678, 0.14205159146138094, 1.2572812176216133, -0.179500533439211, 0.6155161174609128, -0.41772257109624183, 0.5214787053747718, 2.350050756953922, 1.9116520311215497, 1.6537857647773426, 1.0234569200223418, -0.006823056866266658, -0.5958028159977905, 0.7512872494043759, -1.3940109975261838, 3.0425865424782783, 2.7631999716058964, 1.0741278343155367, 2.546316879809405, 1.7430130577427247, -0.15695776694411517, -1.4347993486894597, 0.6813268378617875, 2.51724255304597, 2.541515649664229, 2.7089375595860496, 0.8114865029746081, 0.6356064329581496, 0.6099968116644577, 2.12971379157646, 1.203623790237821, 0.06267119202341591, 1.5948960096277767, 0.06203918075851643, 1.9495023035420425, 0.771739277522808, 1.348944041322642, 0.5687596479736616, 1.5366839051441537, 0.7042503905974559, -0.5024944486932127, 0.9995930780005514, 2.1672043782287513, 1.1791754924980027, 1.0967749757537577, 1.3117665275757442, 1.5153327511444465, 1.9124786665609377, 0.9677501594963557, 1.5022317565719254, 0.055106683959673414, -0.1534471073720141, -0.1093639564315979, 1.6762244541835367, -0.40065953726377046, 1.0585149387273005, 1.781279342253434, -0.383418895002516, -0.809738917282031, -1.101844083831029, -1.2240585131514277, 0.8406229543154959, -1.2647475493981075, 0.4297840148685711, 1.4669303930173512, 1.7309262214969423, 0.6735908383784625, 0.7410666489301461, -0.652746197459821, -0.18149994509988626, 0.6499635349654418, 0.6101407560359139, 0.7013664085160107, 0.9142864147574362, 0.34112824128675007, 0.40299586191653214, -0.3797519735260234, 0.20591790168543478, -1.7303456264110677, 0.427353398964595, 1.1277111833018207, -0.4188631643131798, -0.015666325075522156, 2.0570758022757927, -2.7341677730925067, 2.2065771338574196, 0.2605375791880561, -0.36136563009353706, -1.8670446593504333, -1.1888786179919668, -3.0179231356231733, -2.1298610272248784, -1.4672480050443109, 1.089710199045809, -0.22349107297924187, 0.4795215918954983, -1.612146132025123, 0.7750791807195895, -0.8897975752160081, -1.9097452003518827, -0.4486139539848421, -0.9047132305434438, 1.203749672698385, 0.41627471859096954, -0.16650365711331838, -2.1609862689111967, 0.5435190545482124, -0.5556169803657027, -0.9698987099756374, 1.900855320004464, 2.8947829435172303, -3.19047432418913, -1.7703013910142902, 0.3999468561277894, -0.9549955870682614, -1.6015837316345696, 0.21122517170506486, -2.102459004949651, -3.1192135554088978, -0.5494731727789324, -0.2590703716641403, -0.3208781330615753, 1.1509727017257125, 0.41329269225586646, -0.3073315444297047, -0.972920886272809, -1.251806195150257, 2.06212367918793, -1.2724459977717106, -0.33201482967976564, 0.10129304320881495, 1.4316991651249213, -0.9119872116710164, -2.165955285764289, -2.12680796614322, 0.3795001323372174, -1.3415827182314486, 0.18234101510734094, 0.11596117698521, 0.5847199065920293, -1.0612343805481137, 0.30993962308808415, -0.7509955599820342, 2.5483177308447162, 0.09258270308589615, 1.3684078717405432, 0.6731296199732675, 1.091303557441633, -0.39898016751845516, -0.34978640013194856, -1.4055082215164436, -1.1750434619726222, 3.0973141737866086, 3.040573706192918, 2.050759620452144, 1.150241443305082, 0.059422737070984756, 0.3265104086516655, 1.1098194615336658, 0.6560040089434745, 1.529110758781645, 1.0432043851012376, 2.9743903813026575, -0.249224396301534, -1.3126795431387066, 2.49373477243728, -0.6037478539066994, -2.9850721932912303, -3.321686687880716, 1.367018888202725, 0.9540453437593442, 0.745043400099686, 0.7793010123604236, -2.554032651134173, -0.16935339677627242 ],
				[ 0.012730542850903939, -0.007277606235824953, -0.002242234491765514, 0.034345486110941736, 0.011402678500209243, 0.013097149599046003, -0.005193032434979239, -0.0026442552822092, -2.9930528267814926, 3.613396754495241, 0.16912578374821766, 1.2288941424493711, -3.5822203688868353, -4.03157844430207, 2.5334833754364907, 4.128996914513331, 3.0017000488716405, 1.843708822033925, 2.770305095577581, 1.5317566425115452, 0.8187803159085634, -2.479208831731745, 1.3302154088506064, -1.0120867584139375, -0.00712008878088309, 2.6068654551934807, 1.1133740750825123, 0.6388491052273657, -1.6994127108560864, -2.2342152714275065, -1.2439159586594282, -0.2692137871532712, 0.371341086065575, 2.2475094026791944, 1.0268682459185938, 1.5314286486596838, 0.2201702965776637, -1.0354441340444067, -2.0026084846901946, -1.1803496800441202, 0.8924767790657318, 1.883674811493984, 2.133267583165658, 2.549401625325994, -0.8048401490432316, -1.7005628408178983, -1.7663531071254623, -2.1500528747777485, 0.6828929489968749, 2.066090507322515, 1.370959243137447, 2.3980624269082753, 0.4051356865171287, 0.03170889683304877, -1.274690019686988, -2.406240138188214, 0.02052953130989742, -0.0011607350088242206, -0.0271393780206809, -0.030767743731999832, -0.0014262823901938823, -0.007914896842317035, 0.025635952336054046, 0.021502184376054192, 0.4018819550261961, -1.3878622350059977, -2.1383353659540694, -0.4033717672456198, -1.871511685756755, 3.345781095714806, 1.62975668995612, 0.11914382394731325, 1.6805779169785962, 0.46500208605777293, 0.8652258863055458, -0.8617502831563109, -0.43162018881542946, -0.8320589193898005, 0.5690815243534524, -2.3461736052844944, 2.060437839181557, 2.54005075580567, 0.18841084510215622, 0.9393071718884075, -1.230942439683392, -0.42545997942529457, 2.5960649168436167, 0.03634229501470367, 1.1711853568950852, 0.14451841421557013, 0.20354335580441668, 1.3790575524115771, 0.11193715223935916, -1.4211967577870828, 2.0141273653192426, 0.5986019502611386, 1.2794864420345684, 0.6055741180748865, 1.6460590004630855, 1.1338546526334277, 1.0543932613006723, -1.7554966110209833, 1.2434063128666941, -1.388185985024735, 2.1924186490716315, 2.116483400038004, 0.8013914837058647, 0.13047436874183754, -0.04705454403206342, -0.7388102963464684, 1.884483826296367, -2.514288651012749, 1.1456113576384916, -0.844235231379399, 2.082299414083598, 0.28342992063856254, -0.25614798959690654, -1.0783435947392797, 0.018588865960470484, -1.0798114709758642, 3.527589916362746, 0.5454002575219337, -2.422347091795555, 1.775103452643737, -2.175716912978231, -0.38821828992565477, -1.5380051960698669, -0.00673758489069267, -1.9619361534271715, -1.7954233656772745, -1.3739886814784987, -2.9384105283656443, -2.3835204028650727, 0.2954222780795298, -1.0641759169050624, 0.11553601490698776, -2.5068089422189757, -0.0757423717732981, -1.2412718472888564, -2.2348486886446826, -2.4911310256493353, 2.027813139929372, 0.48728741814442234, 0.3372275003649273, -0.9433944393145443, 0.45133840946834597, -0.30520074465269376, -0.6673739193085153, 0.6077207648397319, -1.4398968279437183, -0.4814926698061998, 3.2556299881397943, -0.22311437688841482, 1.117715443752936, -1.3058124393414399, 1.5020254171090244, -0.301512966880189, -1.7179878476408148, 0.5479708630311368, 0.12173823057259729, 1.6219358595021267, 1.4063849626087561, 0.11698889149818482, 1.2297781742500267, 0.09989290592706648, -0.8771972012094715, -1.223280243664884, 1.6818696541639462, 0.39372035619288753, 1.0808885471272343, 0.43758363432813385, 0.8103449600392064, -0.4571494284329573, -1.3494951399570054, -2.0386227118625677, -0.8239881509806257, 0.5263359003416642, 0.21704977902502443, 1.3562205143665194, 0.6472188031330247, 0.28695254126506403, -2.609223727719014, -1.6870337572613405, -2.5340429988954396, 0.11815981391558443, 3.1192889509679333, -0.2949374833948096, -0.33378060873206566, 0.10746866670730779, -1.566880126296457, 0.019534253677058737, 1.0781044323715143, 0.21701493863737872, 1.3655369975556375, 1.1056034201351408, 1.2943648655324929, 0.9216289343887041, -2.3342489743587302, -0.6526838555436512, 1.154919817074922, 0.8202794743237037, 1.2712682961454291, 1.0985732558462307, -1.1560517775931016, 1.3211678470107386, 0.5465441689250988, -0.4032805684283208, 2.8912324069227573, 2.214191089242479, 0.958241480208041, -0.285891509718585, -1.9040956974115786, 0.15832624024705688, 0.07100678982346692, -0.08880685617710923, 1.111064434761874, -0.06313937043527511, 0.6835131919727635, -1.8235062726468036, 0.2360504710507726, -0.031141832297019625, -3.335550919375855, 0.8791856462145926, -2.3011087702502917, 0.6385030195715669, 1.5438435430886472, 0.29320368611707887, -0.1144020736447371, 0.19293566420851999, -0.602269356585547, -1.2909151493065554, -2.7320488174520183, 1.1503304223678437, 1.8873614710981823, 1.4571577828957483, 0.2074670878294556, -0.14162160416725816, 0.38001699881306417, -0.5016477272518601, -1.1050884521349034, 2.0935288728514694, 1.3296779564420582, 1.737079708439978, 0.29986182785825954, -0.42984586985591966, 0.4800222884991813, 0.0939033369319127, 0.5737211487468604, 1.9920491419028425, 1.590601995300831, 1.1261251608248692, 1.1014694874562854, 0.918871368516725, 0.3976749809593358, -0.9288486553976031, -0.41612376568222453, 0.8947429613329211, 0.03826721145224376, -1.078659576040692, 0.08148441926394051, 2.115251520107613, -3.0470669732500713, 1.464708047591789, 0.05660974318062386, 0.5023734121238557, 1.6830056315787683, 0.29123962789324553, -1.535983305906038, 3.3961958307376166, -1.6168183473869044, 1.301418836666587, -0.18887595677070354, 2.5042622456356356, 3.1501325571003553, 1.3170351729600767, 3.052247355768978, 1.5669609553376216, -0.7232205864494378, 2.9051589817982535, 2.74790683152924, -0.31799702477930264, 1.6976020798050566, 0.9333542253012967, 1.1859278277923362, 0.13392239561858035, -1.4337094675504398, 1.0771527982164824, 0.7503927266067568, 0.2845126526887179, 0.4531383133760316, 1.2080374137954584, 1.902703906485903, 0.2676710604743932, 1.3621029232186355, 0.9542315258485666, 3.14249537244335, 2.991784849529558, 1.6668279880557446, -1.3946534457352227, 0.7692353299279524, -1.4056310105240857, 2.033043406750665, 0.30854046786537886, 0.8758095190206945, 0.5315870134921843, 1.5539809638043989, 1.5912828841679194, 1.1685643800548395, 0.6698007452526259, 0.11177632875736664, 0.13602711030956827, 1.1431567009030459, 0.8018789464001296, -0.6861807587613338, 1.1097334658319078, 1.580972603767639, 0.890563636457762, 1.1582612823985379, 0.8100188035897194, 1.3395388608263306, 1.6979188632253166, -0.5159125960259756, 1.8867990408688122, 0.898969532848, -3.6369315311343513, -3.1175095563211035, 0.0003278187560732831, -0.24487991058082054, 0.04280313871552191, -1.8955546387981197, 0.09354390229058676, -4.21317675137356, -0.10808760233426432, 0.3111119059885161, -1.9782025268292818, 2.3611760606206973, -1.4614182253182457, -0.2407922738795554, -3.720276229563062, -4.813663116713372, -1.3863686612516029, -4.816983805156292, -0.06394417832893058, 0.6288822178872074, -2.6412481853041823, -4.065001136760264, -5.158350817628098, -5.991203858890363, -2.860473854548742, 0.7144324873763933, -2.9977049529556528, -2.3335961784518027, -3.278640322549664, -4.7986133625697835, -4.354410545545755, -2.427920250773658, -4.607186316537867, -0.7565005995967192, -1.6631548848389206, 1.5030160918655857, -2.925646866647574, -4.987035561405183, -6.150710401674321, -6.57455125243648, -3.687132338108981, -1.0700663149134946, 0.12112176789441813, 1.0690180800155158, -7.9313335050574025, -4.746795825627152, -5.828920242014814, -2.233336535368308, -0.3297985396795012, 0.3735218595398292, 0.6874352974263374, 0.3204173396402851, -6.942993010056241, -7.794593620489232, -4.574107342229856, -0.883143512059587, -0.28750455793498503, 1.1064943402376088, 0.88621130920225, 1.6192348869217124, 0.02077732033191736, 0.01226257808699773, 0.019063662675708925, 0.02017632324761955, -0.03470483202511617, 0.020673884600470177, -0.02666653597200773, -0.016834493361565426, 0.7756081265925003, -1.6590413664583867, 0.4771905966207908, -0.603883373936934, -1.910645268047215, -0.7024270976218019, -2.630826585342869, 0.026029208280411525, 0.48922347698745555, -0.43426765870615275, -0.019192924799791216, -0.5729287234029673, -1.2011035835514945, -2.9160895997941543, -0.5531072695333124, -1.0728634094613647, -0.15154193579247283, 0.1959998201503042, -0.8100848811370065, -1.5654703811396287, -2.206265696729548, -0.25779650175694274, -0.42699719885742543, -0.7556226830777474, -0.5537206589350228, -1.6780513530114942, -1.0379080430403027, -2.681205529999998, 0.36310941837343796, 2.230401684260257, -0.19484208752683105, 0.30105669055542705, -2.8891321415220648, -1.9091295945960287, -0.7075935095484196, 0.0648087862437701, 0.8014562815618743, 3.9660871778134625, 1.295351076424155, -0.7493109952081871, 0.9908638360439236, -1.0997463517755792, -1.2035038502090896, 1.4508430658549194, 3.0282217436516516, -0.08336449765254098, -1.0814971459183476, -2.12821390205664, -0.024891429175924976, 0.03387187475846196, 0.019904095589297795, 0.017009281746088463, -0.025430867443091292, 0.025101387799314444, -0.0017858047822910152, 0.02596021527583083, -1.5901948520059233, -0.25995492083879396, -1.456063518416812, 0.29703235344555423, -0.6465096048322316, 3.081658543105657, -0.21521596671119664, 3.3194872186034994, -1.9939769645571077, -2.3128540407037597, 0.08420569466734802, -0.13762615599872977, 0.3762332021962841, 1.4460052720011272, 0.168571626266438, 0.27569884318799914, -1.086641469855003, -0.5920482369484023, -0.6279670082291307, 0.37838097929075337, -0.1989224148747765, 0.3128718432834833, 2.04062534314108, 1.079312123634598, -1.3230257935388021, -0.7449358601043591, -1.6636842986710505, 0.29848964489899393, 0.5470746111224464, 0.23123951529801184, 2.480128438793154, 1.6726225477488796, -1.4078358450038881, -0.23805896482241415, 0.34701882350216395, 2.232816234448632, -0.08293255018990875, 1.2715271434241944, 0.3709883431114257, 2.5870285276451823, -0.4299601896581303, -1.2403901976699405, -1.2938049422482147, 1.0289979481695581, 1.469807948771626, 1.088286794430242, 1.1884719552450012, 0.48872944663279033, 0.8506551959366758, -2.6739443702396097, 0.07845644087240465, -3.686346487818164, 1.5436587706666176, 2.4435489784628346, -2.3645082750333066, 2.0799504294445543, -2.211956163677587, -0.562358781380432, 1.2156260454488383, -1.520387885705151, 3.1582336604559798, -1.4997750368456821, 0.08951010184443256, 1.1637669104665982, 2.7575064291641183, 1.1677258020770507, 0.46148568437625026, -0.053156061835411064, 0.1707484007356234, -0.1078476908782453, -0.6156133175010503, 2.285232301774635, 3.5024139817556885, 0.5125904678718799, 0.08194029773991718, 0.8689444885985681, 0.615196550388529, -2.256498540542025, 2.017735779643793, 0.103269158581189, -0.3347176537608806, 1.9211204778923472, 0.7340315914945625, 1.050006956791985, 0.5007230349949356, -0.05083895173889132, 1.337551699997847, 2.510014368971802, -0.9203782891935925, -0.5467146249976061, 0.5080719467104315, -1.6112098265908295, 0.6822723974127732, 0.22692592619799, 1.2469969749395045, 2.6964666444946848, 0.5147691740007263, -0.49377484004212685, -1.8080171892028396, 2.1559279347331164, 0.8026311833760109, 1.5647307268650026, 0.7784067293466433, 0.796825709565729, -3.2922632577949438, -1.930956840841932, 0.9517361102507899, -1.2096971670003427, -1.1063457734294617, 0.7241761724260964, 2.027292064837688, 0.6445648024817133, -1.4137935807282214, 2.572998562463421, -0.5876879233302352, 0.2618740549288225, -0.331328953408899, 2.3414768255467626, 0.8253990045386975, 0.4019647557239479, -3.769639669869561, -0.9010309943438388, 0.5480943294585463, 0.3920533467368606, 0.9014267223082246, -2.296026097738948, 4.18446527883425, -0.2985828238013697, -0.8680537063280694, -0.6804615353865846, -0.19795572398311245, 0.6033972201042216, 0.9479862008810438, 1.6970778211289952, 2.8973292327851126, 1.2224306289967344, -2.555476293113946, -0.09169909777175511, 0.5054990179893765, 0.43283868139878373, 0.5335971926596963, 3.0390747692639635, 1.843880040210098, 0.5882246679564767, 0.8504563967374854, -1.1551291123455487, -1.0912008193511245, 0.5424772295751654, 0.019517001580316277, 0.781422503780013, 2.6646718561999108, 1.4817714931136383, 1.8116873351468772, -0.30541294475720804, -1.3542124568862712, 0.21141176580307577, 0.4946704612479451, 0.49361018913415616, 1.557838164319091, 1.168705326579005, 1.0900231445548836, -0.223900307097991, -0.2878287150290851, 0.21899150955586424, 0.9900208980880242, -0.4992078172933767, 2.4171032876216114, 1.1549256026146473, 1.5785595862183812, 0.9218828669855548, 1.0076900671143725, 2.3097640102599426, 2.8517507683442784, 2.4836339800475447, 2.093851952533749, 1.523315413412085, 1.6193563037729115, 0.307459485748136, 1.2591868975422293, 1.2761087799206814, 1.3233303943994625, 3.1091010855822923, -0.3317782975743723, 1.843336234192373, 3.002744474148928, 1.7954714801075966, 1.185562016387454, 3.715583761470991, 1.8458055360229513, 2.797096098935536, 4.128417418859055, 0.8701194570920282, 1.6543785550252033, 1.3241994732573767, 1.4377236131412297, 0.903485693536249, 1.2607169596391459, 1.4225964928016506, 2.1919814074907205, 2.447804368184661, 0.11222608175977888, 2.340402647240271, 0.990921843601509, 1.540712674148225, 0.8186207832106946, 2.045000233537487, 2.3570208085619773, 3.775331961428632, 0.4058180025462114, -0.860882687545111, 1.632609119502921, 1.6231752660093062, 0.8473199725381697, 1.1649824598814222, 3.5148902550205405, 2.080020838889668, -0.5868068124598724, 0.7293165115528927, -0.40494440129377757, 0.8420785896561168, 0.6415364034938051, 2.9092069390709554, 1.9933735524522735, 3.1361014252358532, 1.280796118632588, -0.06603997461119726, 2.6513138609522193, 2.603421201985923, 1.8599666278538056, 3.1047322509495126, 4.6213519723367575, 4.5124983327368415, -1.3301595056651316, -1.341046636806551, -1.1442378298677567, 2.335843888142232, 2.263323211400393, 2.9632706794472603, 4.396840491780651, 2.3839100861435933, -0.2019517566194756, 0.6432472112038699, -2.2992560859434934, 1.4482008528841455, 0.9975587534454519, 4.2857607363234, 1.1942110590016126, 2.6397907219455075, 0.5951714351731668, -2.165205037204718, -0.08925283535880414, 1.2914067396109772, 3.293377899660822, -0.14574883648577017, 1.6538587529987328, 3.189026868162588, -1.2718804960929726, 0.19221947715695006, 0.1521476742472864, -1.5558549796467023, -1.5888727908817464, -1.0495120482428528, -0.8464954960103382, 1.6161037046487063, -1.771292782971257, -1.2515437967329894, -1.6525199469752319, -1.9961780201914827, -4.56638959403326, -1.915494174324559, -0.543556791335742, -0.8581033262360662, -1.9866065704629956, 0.636702619974265, 0.42949723841132115, -2.5809222394227045, -1.624787514584064, -0.7927596900174281, 0.05059463419461598, 0.22529803389708455, -1.1774078013616256, -2.452281783393193, 0.6556749850696927, -0.23403919929601344, -1.8592596991205765, -1.7107499934112889, 0.20334467459373884, -3.2754225504409593, 1.8156669205474045, -1.0426925719447853, 1.5707225249936208, -0.23722097021661737, -3.279246099181908, -2.2603362116922936, -2.3102328649419945, -2.8395026658574096, 1.6112908834951796, 3.8451645020176772, 0.5259671422429242, -1.2603270652216572, -1.3524493713074528, -1.5010730962960137, -5.034759782502591, -2.3696098515951958, 1.2943391352230225, -1.277606235357483, -0.429395200008964, -0.2896425990159532, -2.5142750876333184, -2.2005372612886287, -2.8729728890372135, -1.6464660981093149, -0.5211520614825467, -2.78783375881275, 1.8721862822175341, -0.8604537191277374, -0.9802768031645324, -1.217183918668248, -2.7088502547712565, -1.3751275512198233 ],
				[ 0.024292801875204505, -0.008050231865396964, 0.016335407219161786, -0.010291066314461174, -0.023116123413931117, 0.033466582771780995, 0.012737765173041399, 0.02024896598171116, -1.4768374470620749, -0.44925042507493357, -1.4399453713777166, 2.199433739920197, -2.875654408946609, -0.843057075213969, -0.10334279649728705, -4.296577351826514, 0.49101561356302115, -0.0668315304278867, 0.1702143844401359, -1.1193632977371653, 0.4709745741218903, -0.7135181676332543, -0.49972054244019826, -2.1416023256995316, 0.11136740976104935, -0.6582715584108546, 1.4876407678694856, -2.314721605329023, 0.9398126557969375, -2.11639405743539, 0.7304259361781391, -1.3309996051617032, -0.8853688189456762, 0.4123077606849761, -0.10637703762020256, -0.44378859034409296, -0.5278162536547255, 0.7428248974651501, 0.52533360795874, 0.46749855861228595, -1.8377977008203241, -1.5656087715545455, -1.1029990872007394, 0.7199629851791376, -0.3341225196115241, 1.6466429528024529, -0.6779424738506474, -0.5510890798650252, -1.5505250658567606, -1.2895564660945626, -0.9994786135598999, 0.4630518157949711, 0.11606371404625543, 0.5299265814235193, 0.5076052204490159, -0.5460306547241958, -0.006092875273840912, 0.0029519552327245363, -0.020065470442620525, 0.0013210003951824192, 0.03316759264554732, 0.0028586268941872012, 0.02129474209562172, 0.002031621974665495, 0.4363150223714478, -0.06260799542846811, -1.8953579628579729, -0.9417535708849482, -1.6664209814440931, 0.45308533989848393, -3.368728767922023, -1.5506908863341438, -2.5726716337056095, -3.596815942585763, -0.8023046444147804, -1.816913950712999, 1.9127411848977882, -1.4121934591996437, 1.8494377475618444, -2.4554517523235675, -2.5026276287534426, -2.9167032041677685, 0.3946238711976726, -2.727676868721414, -0.8054696534049733, -1.905409782094621, -0.4328931585698267, -0.08813797656663712, -1.20752655244398, -2.277036337157268, -0.305950216274628, -1.1407603608227892, -2.2582530770853877, 0.0055160827922159416, -1.3682528149561055, -2.322018635709373, -1.5120449976898955, -3.481094942106844, -3.5426647691270903, -1.9326845257393952, -1.1942240092943268, -0.8858642455958359, -1.8409976590255808, -0.3761990979388312, -0.9540715131302346, -1.3760346024677872, -0.325299526510926, -1.408940680624029, -0.5096759434688714, -2.34698641233974, 0.3893211396546449, 0.04221991033821677, -4.122510718692288, -1.6194352244607388, -2.582162322892048, -1.791576915546708, -1.1790778617269202, -0.3966209555927107, -0.48663032709874066, -1.0924769846549713, 1.3777290276800949, -0.5552912527214355, -2.483743756371884, -0.9102768336793998, -1.881254830995236, -1.0996420161181133, -2.649476505491311, -0.2678821535563618, -2.3115668458619294, -2.847882573766777, -2.893175588761563, -2.1776241825551033, -2.768934601797655, -1.1669890434864456, -4.326273677432253, -2.1056404888478717, -0.6607446830629736, -1.2249690987010278, -1.1273931846417746, -1.8113510575577754, -1.7287017396566215, -1.9277904572155726, -0.7661603646736495, -0.3800396747083924, -1.1890939180464888, -0.8874594714016597, -1.1173902230531112, -3.0974750252839103, -3.2203041842912308, -2.473375268627332, -3.828471567515238, -1.4774276594501687, -1.9381134862244933, -1.3651098734881357, -2.222706924062632, -1.9433498177901847, -0.8160085771059188, -1.0652821373301686, -1.6066450323273398, -1.1344742839540791, -0.6518552363458792, -1.1970536176562858, -1.5864458991679733, -1.2316404909368937, -0.07417000483490252, 0.07273347901765163, -0.7129183278805188, -0.1746087616063542, -0.01271999384255561, -1.7086160088349414, -0.8258629728162484, -0.7111055759990439, 0.18261504841502857, -1.2817631359665205, 0.7263291228589203, 1.2597100038909277, -1.9256197012371068, -0.2512966735305045, -0.608076553932069, -1.6960273603307534, -0.1849078263031572, 0.04800233365899512, 0.3327910668620293, 0.4351525363022766, -0.5367457106002507, -0.800681364447023, -1.1806931243099883, -1.4528824883118636, 0.8429949975686948, 0.3797033427747823, -0.04564054180055914, 0.6111947022386115, -1.175518420564317, -1.9446174212706369, -1.3021583245850419, -1.9019033039010105, -1.3935243227133243, -1.257294259083596, -1.7371022482937972, -1.4343634958300329, 0.002428525410155803, -0.9628607583209546, -0.8820095043462217, -1.5426612594322522, -1.1964110437038007, -0.9735800295874947, 0.9963596689744311, -0.09856749996116243, -1.3476246506057858, -0.8902750415317419, -0.770122171781723, -1.3311011997010846, 0.4295152772767354, -1.5764184441155336, -0.0068367216088945975, -0.9155752050438319, 0.42916157775860925, -0.4778848902184531, 0.43223966067342945, -2.003955267560943, 0.44525882567334835, -1.9424397634951673, -0.4235325843564531, -1.592857519487935, -0.3350394648079195, -0.26395218100853335, -0.6055617537118914, -0.1764073840485044, -0.7093487420355998, -1.1618198819980707, -0.4129655802967244, -0.8231702958145221, -0.6237001639281315, -0.027596141483230346, -1.0444229261480154, 0.2557633372516644, -0.14512352894398334, 0.6536516983473406, 1.0931061027414262, 0.30845627298044714, 0.9268620431871338, -0.10026831804564042, 0.24933204470878342, 0.5978203547333512, -0.18525527041795162, 0.8092806266129241, 0.7190242980803369, -1.1014496477924476, -0.8039798736432829, -0.5912125636604543, -0.43661747996142936, -0.3614176565807898, -0.09492584193905676, -0.75687925948061, -0.31797165237886427, -0.5585232072214892, -2.216757708861092, -6.347954057404458, -4.1115902692049815, -2.8968551806724943, -4.81636075003546, -5.416878441809062, -4.544712781102614, -3.908000476114577, -3.39720644647341, -2.3804529584055554, -1.7644930426876249, -1.9148495087732817, -3.071840348016711, -2.4988400513384836, -3.5351818394481387, -4.094179341691553, -1.367499163282343, -0.1363133297934753, -0.5480229580403808, -2.2343085654415984, -3.387403972651781, -1.448848396159998, -2.661198861970948, -0.7141179958988578, -1.3104658298014311, -3.3193921402294864, -3.077843533472036, -5.246056634852317, -2.8705846302690046, -0.7260866637548945, -1.250648550431613, 0.1719549689319305, -0.35785721266873094, -1.0136675340904338, -1.9887035465840894, -2.451187529245521, -2.886809095170037, -3.641937973610299, -2.284777223230289, -1.0180865983431515, -0.6825948851050908, 0.03502671858020905, -1.5263927174911847, -1.1399114308083151, -0.7304928465060825, -1.3109004491157252, -0.8049838782373813, -0.931172298820139, -0.783277776176413, -1.697164934545025, -0.8159306164524079, -0.020356893322507792, -2.397849006314278, -0.6131915033790188, -2.192844115680812, -0.4659949072388472, -1.0831902933517445, -1.2633243859701644, -0.8375388523212183, 0.3010731648800206, -1.1732390897647433, -2.447166516129977, 1.0413556086977518, -0.5635708950232635, 0.39016538913894466, 1.9566199197326042, 1.1537211845833448, -1.3507518674517227, -3.9165279910712525, -2.6158026956091964, -3.852849553495571, -2.9632707285009996, 0.2554618551341668, 0.4037400774584925, -1.4494596477049677, -0.419827717703265, -4.150271914982256, -3.0204336233411024, -1.5519302686042284, -3.1062974708611613, 0.22570056300322397, -1.9898376594136362, 1.1462534114634453, -4.311511927500223, -2.480149419423088, -7.082821151213267, -1.502117796993313, -1.9549145148121634, -1.0003343344123121, -3.327933818930869, -1.0011725156307465, -2.2101142666301774, -3.8566931435162966, -2.8687338449953996, -4.984851264159111, -0.720489960719248, 2.472726884167062, -0.9868930803734798, -1.714993466067092, -1.8425353950062746, -2.0397482824844086, -2.0686913013352837, -0.26434383493865826, -0.8662733608996093, -1.2817258746898166, 1.3496160521845675, -0.30510979779426495, -0.4710959600471254, -1.0997258043172475, -1.3848085966517931, -2.227250839548515, -0.7465602486460964, 0.3638609178421425, 0.5664562697793967, -0.600053493171999, -0.6038206966016776, -0.704549063854321, -1.7420052418642649, -0.7655036207551641, -0.40978317090769073, 0.713427086061208, 0.08448304007667855, 0.07781289411557306, 0.008989874650813393, -0.5984041260511074, -1.4704178997388229, -0.48477130580872296, -0.5761714519112306, 0.02270810946654896, -0.010481414565817502, -0.011560431793767827, 0.015195938966436846, -0.006402732815634747, -0.006805253401596716, 0.02814567260302646, -0.02737538934045256, 1.2632292315456723, 2.243556878267883, -0.45578756087234423, 3.522004764261386, 1.5074848657177136, 1.2522346635205097, 0.5892488451344199, 1.5896547744494312, 2.383112078343799, 1.4900682593778762, 1.493364925745161, 0.5030622360916533, 2.1818834644944656, 1.246760605380252, 2.1543577485939065, 0.44112635829870733, 1.9184446539023396, 3.1068045120322676, 2.309020197108389, 1.9823716882171902, 2.11341403120887, 1.9941106117001637, 2.029882079000337, 1.1480975757237168, 2.877162876575678, 2.1513138860757564, 2.414085307021797, 1.4385944092021863, 2.806899769248156, 2.8458560123645817, 2.0942010662486403, 0.4676157382060786, 3.3294264857414797, 2.4102088105792654, 3.1024854602729017, 2.17043601787203, 1.7530798333280009, 1.4386572453234812, 0.026824264630391264, -0.3891241799625791, 1.0948547079589017, 1.1765016950497031, 1.5751128982721903, 1.3525826438124817, 0.46388548965497506, -0.07553770281616169, 1.7543623646840183, -0.1262081862829409, 0.01272196422312768, -0.005392639254081596, 0.021789976912613043, -0.03102796317810435, -0.007496547168026777, 0.0203484678506537, 0.03318165840771844, 0.014502435583401587, -0.5768158533188211, 2.203337277297943, 0.5963614255222028, 2.633414351347326, 1.9636322804619768, 0.30811667475432236, -1.290656933746076, 0.03769891046269668, 0.147863553959687, 1.4776989811379244, 2.1798794397916863, 0.34425147798602607, 0.7380342389531902, -0.9054515197371024, 2.104698615080761, 2.2019892810266875, 0.10494212954909354, 1.1361132476083915, 1.855416645198601, 0.4765043925229044, 1.399416196918233, 0.5046058396796934, 2.064367675984151, -1.2685922323635237, 1.152162794238112, 2.1741419448522064, 1.5235681682286637, 1.6120511400776196, 1.2499825284885406, 1.2948083626076983, 1.0826120018946297, 0.47752942752601196, 3.673051813647817, 1.261886939609923, 0.862422923664505, 1.599756564067721, 0.8476407161052528, 1.8860004990846786, -0.6195543567892638, 3.1288141275196306, 2.8766436432877542, 3.8094484340383947, 0.8061709772008937, 2.123043366030212, 0.625249064011845, 1.4873135147340302, 0.4250014720281254, 0.7943009993320491, -0.056532633180179155, 1.8517821413579665, 1.9249332326652555, 1.887800707032484, 2.561130825760861, 0.8120121068354081, 1.6985412844249161, 0.4196659541750439, 2.8057183275651516, 2.875779387956309, 2.8165963975351644, 0.4228180705768231, 2.6960867309634446, -1.0527170235724468, 1.63133849052748, 2.6418721787482817, 0.8044194809421951, 2.1832008903922735, -0.454771496518612, 1.1247828489438134, -0.14498568762080086, 0.31730380443522294, -1.4124846184003508, -0.8529562582355318, 0.7581421743502986, -1.4861873002905708, 0.5998062562303412, -0.922913806029337, 2.3661347404420896, -0.5389201823128197, -0.8100001267690644, -1.0561557253481728, -1.102661220629494, 1.0137431058538833, -0.92573599862716, 0.08386496447606052, -0.45837759293671776, -0.320106084575414, -1.0597218762688927, -0.2926594877350928, 2.11174956229008, 0.14316094684451947, 0.48224365859390894, -0.4265663083788019, -0.5701392301407622, 0.4756925866221799, 0.3714605848478389, -0.7480531764792606, 0.6281528396945617, 0.2807825959534964, 0.211024626561558, 1.4609296022542946, -1.3817100689027164, 0.3437746736205176, -1.6186706975142975, 0.6375286383999217, 0.3536022094857915, -0.5395381685480282, 0.9135828310347951, -0.7549779106938994, 0.9231596523130052, -4.060905682856426, -0.6455026616671252, -1.8062537076681222, -0.2893952488571422, 0.39203671529244155, -0.9379813856156216, -1.3072279452888311, -2.2140875845540235, 1.1903185860055923, -2.370010767597659, -0.19431221308677624, -0.2935057628738775, -0.3424956546061097, -0.316191295636583, -1.7074155886411304, -0.5291919294341499, -0.28404009678055636, 1.3737213804471708, -2.174022068192327, 0.6002136603703683, 0.8621630244264149, 0.8389359537866762, 0.7396111397472784, -0.4061802057036979, -1.182123666724579, 0.07268832640672332, -0.24413308610513035, 1.6803424601057535, 1.6180559429402794, 1.030721249721811, 1.3823462292095379, 0.14234280883800549, -0.43002656777349063, 0.765897308466714, -2.1165342224863015, 1.697952808368955, 2.6772458215678876, 2.018517472228757, 1.0680483877608427, 1.4251329986977284, 0.16273852520017415, 0.12753937361176576, -0.6715057799862189, 1.4402743709051262, 2.271609729272151, 1.9135519349404828, 2.3284288774497903, 1.0122199127965725, 0.1795591840057915, -1.735839071760864, 0.7353793540259956, 2.1148571676969277, 2.1313742328626275, 1.7751979478006636, 1.1648437879668239, 2.4712806410210595, 2.0324944843269144, 0.9089528094476135, 1.030998993675761, 3.037681989293573, 2.723091265259097, 1.9359332159901093, 1.9434760127117696, -0.4506372280823717, -1.1885022539864776, 1.0891332678812458, 1.2161666368434656, 2.2114012023668783, 1.163076417832447, 0.7868513265127737, 1.6213390485685133, 1.237226759950447, 0.7558131357810698, 2.296965089046553, 0.5151097420426877, 0.95006033769102, 2.760121091347754, 2.1764430884486843, 1.934509275845975, 0.5124654326919548, 0.9828173407085518, -0.08123736812212086, 0.49402098617804047, 0.5554671885368563, 1.6300170462340615, -0.13373946502040068, -1.1872533979549549, -0.937760769781295, -2.4211871537266525, -1.2622759883915908, -1.5416014466418915, -0.32662267726450733, 0.261537801904276, 0.873513808318605, 0.10737085138819812, -0.25112882282152443, -1.8468500732549187, -0.3430510692660339, -0.3890283807457673, 0.06717451447071843, 0.15255744847020672, 0.9558887717474748, 1.1034418880947068, -0.06413311236502815, -3.307477900296745, -0.30779766473723463, 0.32350984104114944, -0.4114950519665991, 0.17004076611946617, 0.8526305664310039, 0.8434456426908592, -2.0303347791476622, -2.9144515590625786, -1.434741462793071, -1.7191710503773476, -0.724794925265754, -1.191608170574175, -1.0491834764184533, -0.45165866962570883, 0.25739272583398576, -1.6063465559370234, -1.9160557272354373, -1.87641357035665, -0.9266839813846512, -1.4628696177031009, -1.9773355704757658, -1.076584925341274, -0.13765773514099555, -3.8055831797925346, 0.30587798222049684, -0.551070567840815, -4.023563560720244, -1.8248629752556353, -1.2425537693760809, 0.6523869782968112, -0.6625674330597505, -0.729277694678311, -0.515416644946858, 0.9621347438631068, 0.7465905852438863, 0.6439758076652358, -0.11794751518672762, -0.810317997617439, 2.550088540607261, -1.2781338984779214, 2.21090010823647, -0.3048023121407434, -1.4593849020660614, -2.4972059913244515, 0.5560024680167729, -0.8713434056876724, -0.05828375990751167, -1.245755045302593, -3.6046789723006225, -4.211689536879251, -1.4339064558957284, -0.1263088273877554, 0.5245520143538696, 0.8922845943163331, 0.1121206110245021, -0.35887378154145594, -2.232692547034667, -3.2474412272651363, 0.31363187315898305, 0.011793538557719451, 1.4434079782700289, 1.4294979614824939, 0.49283006618620157, -0.28267330725939105, -0.688137157444984, -1.8027206897082682, 0.5124068294675157, -1.384140329848609, 0.5603672057987321, 1.4997655278425877, 0.2886540801644383, 0.8172544711701721, 0.025932810787153135, -0.13296092611113514, 1.3690732037844937, -0.39318209432587087, 1.8780065943379465, 2.1557914311564925, 1.8512565055188583, 0.35000355351014584, 1.4457195739789033, 0.7154253349803691, 1.294194889421428, 2.745068772677082, 1.761739993617017, -0.06915537144038576, 1.791409322096474, 1.613516374661092, 3.096693596586167, 2.411206196632724, 1.380646541812753, 2.690407020904448, 0.8780327156868972, 0.9552448601541148, 0.9032972981371402, 0.02198362457880933, 2.3567553572375854, 0.8393482696037528, -0.8358569207650558, -2.5682386932296266, 0.9760577166573364, 1.048232890293059, 1.8834902959867728, 1.0426596917577209, 1.5642044752083601, -0.6037159061617337 ],
				[ -0.013987018752164331, 0.014973062774793934, 0.014708481277508347, 0.016496243140119653, -0.0318902892690845, 0.002662510232133308, 0.019642723450742406, -0.002487673837032204, 5.538429342205809, 4.187850222580587, 0.41467716032698726, 0.38599403739516114, 0.746300514656344, 0.16024990404956224, 0.8522609635283052, 3.9635331280715724, 0.5321954322019448, 2.1239957188841485, 1.1670510267333978, 1.806350081021503, -0.9775555109110642, 4.5307270013436165, 1.9853663659624317, 3.9184714389851885, -0.01089803813601033, 0.22109178897257936, 0.4020486063474917, 1.1612820192153983, 0.5680185314189073, 3.092141812903575, 1.1381976239318834, 1.9382953444707993, 0.05262816336776283, 0.714802223473525, -0.6326215398527939, 0.5284046295081133, -0.7243265181695536, 0.5846093516288405, 2.0795301138296027, 1.3730860691794315, 0.49859335356574414, -0.5711383050214168, -0.38804818686915504, -0.898875896734751, -0.08136878531175781, -0.6800162943580481, -0.4564220304352079, -0.038764860765681794, 0.2352080925635716, -0.8346627300039584, 0.18549020573113745, 0.01340735477123556, -1.5105419386756878, -1.5690363486670118, -2.3939961322819077, -0.9581182516460188, -0.010652758582307098, 0.02522935980876192, 0.01706433875403867, -0.007374101841464879, 0.011170645698272343, -0.017644624059067592, 0.007264566037980132, -0.0010478898873954152, 1.004273682252997, -0.05684363637220845, -2.5666981791986716, -0.2717192131971009, -0.5347814215219973, -4.223614869549212, 0.16359380986359157, 0.708232342797174, 3.279765129632545, 1.391966459820607, 0.3110724528984071, -2.2621459877464067, -1.4818435908168508, -1.0754802895501587, -0.1416337057331253, 2.057844348901061, -0.3081772478516644, -0.39769528008569516, -1.2526329482208711, -0.695960313231728, -1.76293946658771, -1.0865226911199768, -4.02459223969432, -0.8396163777720325, 0.595345373949852, 2.728742358804118, -0.014134764433069361, 1.2534041909003766, -3.293565370160696, -0.9936047226893185, -3.949106074674548, 0.5510469763360952, 0.5131905681605092, 0.5895045412761036, 0.6324598494784096, -2.0296368593701413, -1.231286808532395, -2.4393306926572693, -0.5747972687979055, -0.9946835524472868, 2.2726944804461797, -0.08662409343930483, -0.5562214288442668, -1.131063148526712, -1.8920310331543506, -2.8640990143115905, -1.3188832091773577, -2.8146168395002755, 0.1054551468053738, 0.17326324272280696, -2.833823159595215, 0.4518443893763933, -1.2835705749153514, -0.809695864799725, -3.1978857601051756, -2.2407428748712737, -0.26727031377466803, 2.1531296537828397, -0.47976759829709875, 1.7809157084923135, 0.17384500268992428, 1.808785359396208, 2.0002463176140903, 0.026536694256732697, -1.7587995794564237, -0.35384621723716003, -1.384286046168541, -2.327107354436907, -2.980653587372038, -3.2787929906072315, -0.4457108493990984, 0.39934532883994706, -0.7133921741908558, -2.4834001483639674, 0.17432596005911447, -3.42554536570975, -0.6632912430928282, -2.306062212897261, -0.9982841688692329, -0.9547408850861278, -0.804431078393803, -0.9188290884630985, -0.21840211548678512, -0.026487376835390562, -0.8748260086213725, -1.4969537464905451, -2.591078711333792, 0.4582197087685916, 0.847460898130157, 0.7039313283212311, 0.4193567841085651, 0.2021938013965919, -1.6941447861387948, -0.3951292839690101, -3.020846761615305, -1.8828971738461278, -1.4974205204093087, -0.23418801402593198, -0.30915812604943804, -1.6261690108954032, -0.22218929374533072, -1.5062113098812633, -2.720034557925501, -2.6047756445210246, 1.6374486179102867, -2.263944024201421, 0.6165250760941152, -0.8194622496464518, -1.157445962927965, -2.8178495099495486, -1.3141558673507565, -1.18440830460449, -0.323949154851539, 1.252503872111776, -0.635782257784632, 0.41645020944601197, -3.150623796468781, -1.1336075759382556, -2.7153591150873253, 1.123178627169844, 3.179743607690841, 1.9725310486577474, 0.9067265853644149, -2.5967790483625603, 0.40484918786596175, -0.8681645751101476, 1.129340151041287, -0.45869747900630875, -1.8196535129517566, -1.3843067936395927, -2.644220310202995, -2.8219530027660316, -2.423817740031422, -1.7202696068233219, -2.5535084560009578, -1.8405953832609585, 0.11360753535898466, -1.1473115733208947, -0.912895716491376, -1.7606537416739187, -1.5117820270654012, -0.17351828911852407, -1.7351286672152948, -0.7936875610604104, -1.4595520990817163, 0.48281053120244816, -0.9285784414051229, -0.11989839067996612, -0.22823761532681713, -1.9305644165642446, 0.6025861176915633, -2.5805352982827805, -0.7329367467190075, -0.28196728471134896, -0.3737273710481521, -0.4858857792616688, -0.3024059918672786, -0.267490204930855, -1.5120038354865284, -0.23147884366030813, -0.15059530867479587, -1.3484997494103963, -1.173885056152563, -1.7578882206983029, -1.4334908792022552, -1.0899069658670653, 0.05225507980653829, -0.9265777085507169, -1.1064533034187845, -0.6835082221045848, -0.8976874583383426, -1.924380136397584, -0.26682708052260323, -1.4572049036078054, -0.21872570689886714, -0.7707977163940334, -0.7550936578355061, -1.2454967684375151, -0.27691699705749173, 0.17619307933933778, -1.5571567401680442, -0.5987866466458664, -1.0230378370450146, -1.622571155153763, -0.4202382388032543, -0.13767126505336844, 0.011031487020565792, -0.5978295687469389, -0.900491595426084, -0.7344226141608222, -0.22056163732498502, -1.5153854345340008, -1.6308004369105658, -0.7270533302187423, -3.4334659543891615, -2.3526570855742244, -1.8999255974439357, -3.7754939299653887, -1.8852494065475323, -7.075482012884999, 0.4084790698103761, -1.1222003599105013, 1.1731712930179905, -2.1866229158489663, -2.4303311824649634, 0.7565068118269647, -2.616558428861044, -2.987271425641699, -0.682637095584518, -0.5866697135480687, -0.07631031173778133, -0.6944156024073964, -2.3179689036577367, 0.421368327937635, -4.672163791221391, -6.255026191173269, 1.1335140541188369, 2.0969598534365086, -1.1310264024813648, -0.3909033374247961, -1.6439623676739754, -1.3720646651780743, -3.1942694258279496, -2.7998652035717178, 2.6981587645008056, 1.565832799169503, 0.8641692758817423, -1.7531768324999115, -0.5736205446172261, -2.8609155934470136, -2.913460416050445, -3.104884796021559, 1.6641467082476185, 2.135064854784674, 1.4824838937955647, 0.08925440768509375, -0.5508489859088369, -0.8962623676409207, 0.1010968165746428, -0.34931289732988413, 0.9860691847394175, 0.3301193561011104, 0.29868360549607165, 0.5006239016582082, 0.4337470214400971, 0.4031522560262501, 0.22138575912657973, 0.11607938663933859, 0.9663644241554245, 1.9967543665198013, 1.943347878384285, 2.2650165412855747, 0.9015596252513918, 1.9366072357514827, 1.2502312332237897, -0.06014608376401014, 4.673694353862887, 0.009630436214691363, 0.6540877761777723, -3.1219564013003285, -0.7399042572684341, -1.8545495365834204, -2.30758663543362, 0.13174449736798502, -0.9397471351015052, -0.45884823043741557, 1.1811909697288472, -1.768357282294258, -0.6149381911298571, 0.19362059835494874, -1.1352289010703214, 1.8501361484770735, -1.3581717133442277, 1.2273972671000009, 2.0136501937744913, 1.7774529486825474, 1.6112058004669996, -1.1718734572966927, 0.2539800077678791, 1.503342535363589, -0.22156036747448674, 0.8068681199163221, 1.300913981030773, 1.4995978648398485, 1.5041949804520078, 1.2367266095986102, 0.11277468674897899, 0.34118260089726676, -1.5746877808848554, -2.260564745146997, 0.502062058275489, 0.5362871642434083, 2.0071622099000863, -1.5901873550253216, -0.45304514759545594, -0.01974367857915135, -1.9923384776430761, -0.7612387966088836, -0.5077072561216261, 0.6479219959254743, 0.6381413598126052, -0.39548679454676966, -1.403226992483141, 0.6544195021026887, -5.429111765525336, -2.0576745199214153, -0.0975358374228965, -0.6810017338682595, 0.8148599463028529, -0.3053532449038985, 0.33829099099321186, 0.37589268657517283, -4.277702263579996, -4.818432298113018, -1.7054988878141093, -0.902398969005646, 2.669467294217525, 0.24789854219884966, 0.2847474982660888, 0.9766060299881414, 0.027796348371068813, -0.017013975123243385, 0.03343540846744246, 0.004523114150242916, -0.023860876052519995, 0.022901566563597778, -0.02559044737912327, -0.018140698825835865, 1.0540943104283262, -0.18216418425614395, -0.5076409829391534, 0.47175050879523805, 1.0383839016629877, 0.08083866069144892, 0.9293247583598101, -2.44115284528556, -0.12184208783053502, 0.2738950425691902, -0.3768855273908078, -0.8867417557883793, -0.5535262692687772, -0.37690410642146555, -0.00991299105823911, 0.08122176418146433, -0.7584694495431188, 0.37901973092116825, 0.3974409461131061, 0.8653094105496365, -0.2753043274548822, 0.169860456485989, 0.438355850076592, 0.7013939683346009, -0.3330352063418281, 0.3905302395896143, -0.04533132682069886, 0.009206882970445834, 1.9209686627061087, 0.6963384200843722, 1.9948483092198142, 0.8083790937211734, 0.8467522311389413, -0.3942920109929531, -0.34482773609480977, 0.5966988271848895, 0.652351999156987, 0.5547425152681211, 0.8649537738451892, 0.18567555203224737, -4.091097779985168, -1.1645367279005967, -0.4605862315492377, 0.9507050768487921, -2.5873183526694925, -0.7637313459869282, 0.894364640396447, 1.2132883161029604, 0.004036287204426108, -0.01816331960450285, 0.01649775296417666, 0.012754055464916507, 0.015349990304401583, -0.0006164381503151612, -0.032364695446894326, 0.0010120661785006668, -0.5345724670789257, -4.81196591131117, -0.5936519595722335, -2.580553562420825, -2.4010158939753175, -2.6068648323616532, -0.023790731892273747, -1.6800106313490974, 1.2946139531720697, -1.817051515992824, -1.4999461560331173, -2.685979108217296, -0.1549378492153072, -0.5418803042329213, -3.0013403481134886, -3.6872324641546066, -2.8076757515573516, 0.42682291424065094, 0.6146096720170102, 0.8702805116038892, -0.3914282345529575, 0.5767157778724549, -0.21604175411908194, 0.45172413546521856, -1.416949111773417, -0.3433059112049935, -0.6675210041472436, 0.5832083868612621, 1.2727456475746521, 2.885457863279877, 1.70660252907634, 1.1591311711646013, -1.3775009673208867, -1.798465282525549, 0.40419414323349045, -0.8832884469156016, 2.2623491164602676, 2.652657050319127, 2.9743829135431237, 3.193809355570497, 2.335865682864221, 1.6139055001582114, 1.2991768248631184, 2.9473691676525826, 0.515137278823224, 1.4524080284011998, 1.765926001502492, 0.3916886832200059, 0.4215697785700584, -0.08519218646571647, -0.48579637461359965, 1.8867681522523794, 1.0512035203021175, 2.0330483863531645, 0.8986473987435258, 0.5585727868679101, -1.1610668888806597, 0.5255233960341276, 2.5996634472154527, 0.7905353106638819, -0.8474754555504913, 2.8027521520320757, 1.5739485158415183, -2.022103219728837, 0.9295570237749498, -0.8045527485381959, -0.6261275024297441, -0.819800243842851, 0.5260153149060054, -0.5643861813578553, -1.0756028763636687, 0.6118089296569483, -0.6013159495014501, 0.8027620198829877, 0.061203486367094544, -1.51373384650901, -1.9089723188317975, 0.057458358911245296, -0.6418230230581319, -3.95954444572645, 0.34699333937035715, 0.45993033924067184, 0.5879808059042242, -0.40894609343494515, 0.8488681978697389, 2.1512861637773915, -0.8829030131567818, 1.589874184613551, 0.5744791929999264, 1.7779591475813232, -0.8332064873206823, 1.0893628524348873, 0.7154995775312991, 1.3841290948512475, 1.6086504070658223, 2.7404820408493427, -0.5479274154069013, -0.40663709017787186, 1.4751650350736418, 0.535026953378249, 1.7049279630173553, -0.03700102341173738, 1.630898738095396, 3.602693506715849, 1.0444220314533716, 1.1640501027998695, 1.6130585347365978, 1.470978922160711, 2.253331621113375, 2.1853915968819884, 1.5456920678195514, 3.231548325949236, -0.45148248698651483, 1.0917095391046483, 0.14666377780368975, 2.1562348322756746, 2.575050908978353, 0.9302891045291869, 2.041397424443426, 3.185278420889126, 2.620194857460223, 2.2121719740360524, 2.8134587535971955, 1.3926479961008162, 2.103606123671006, 1.495739746980788, 0.9091395802701346, 3.8302084682668704, -0.9012441427208898, -0.8693823552501637, -1.0724838203815685, 0.3677243060777735, 0.5506685232898864, -0.007118394696049247, 0.1334833367888442, -1.8361605667808516, -1.1367527677627118, -0.17546315226981574, 0.29825195650757697, 0.791884097656591, 0.3292612131042943, 0.22580268851057514, -0.7637013884800462, -0.818030497275443, -0.7749867539713992, 0.151849735087035, -0.4419449503334957, 0.7395257116761311, 2.1044780326038826, 1.7517740632338723, 1.2310198256990637, 0.15533510723476335, -0.20017599408270667, 0.29531241416304016, 1.4105468193656978, 2.1409552264293072, 1.2583904592235229, 3.2219826384086194, 1.3311537760967447, 2.864242375294789, -0.07551211961387262, 1.0750390628293593, 0.7122929707924518, 0.4879508430806683, 0.6844068634641521, 2.5514672296191225, 3.1323750699594597, 2.6051357638664316, 1.4007812105086566, 1.3303417522649674, 1.2678510281993252, 0.09329936697703425, 1.310930340500438, 3.2114960668004957, 1.0205598995901757, 2.414041714978257, 1.6187238208510546, 2.180919797475566, 3.0056191617723367, 2.3721371353471237, 3.675058799452775, 1.9713367451828865, 2.3480605382672795, 1.3160027301195398, 1.9306726301570083, 2.3190190656192584, 1.930229005913273, 1.853386043742387, 2.396560319823198, 1.7882657028744666, 2.748988140943076, 1.1685143272376832, 0.37741342590868543, 0.315834242846403, -0.9634766682757487, -0.9883272014015992, -0.3020840354489851, -1.5435620098113079, 0.3811945548675947, -1.495966263328831, -1.6858079627203884, 0.8336366605821561, -1.6839234147879285, -0.17999647130715168, -1.4028317925543723, -0.4322514992282168, -3.362180803580965, 0.29262109835451966, 0.9555016358927025, -1.1895385089954968, -0.25075772041850924, 1.0543775387757999, -0.14143371190546722, 1.2074391178948352, 0.8279512502965614, 0.14304655982500777, -0.31947269853501653, -0.11883183066669331, -2.147592449903493, 0.8713359543702481, 1.1076729836659847, 2.300716379100624, 2.51252552764701, 3.148326846367643, -0.6730164576601703, -0.692598876267605, 1.3263590878107516, 1.8117136460221863, 2.591406645893968, 4.4193096413702495, 3.444818816270362, 5.291429337940033, -0.06888690563264449, 1.5330895622833363, 0.988517525643769, 3.231137635320428, 2.8251001105802453, 3.4990335414856846, 2.927586618908068, 5.020653770194398, 1.5926647746973648, 2.0629677508674042, 1.899448856787552, 2.0489830066515435, 4.4337228172601515, 1.6501458064581573, 3.847978342983466, 5.093549717216891, 0.41289814720460327, 2.9630646086910537, 1.3215759681780823, 2.6977921621956162, -1.7673191953300595, 2.5207410007508178, 1.5039257384709537, 3.414503986359378, 1.9917061569871537, -0.6881495846322316, -0.760309681046193, -1.064810552837915, 0.46680138897960477, 2.908430030721738, 1.2272247449397458, 0.813715473349411, 0.19780370595807117, 0.8785580362575489, -0.16052467694658934, -1.08633112384046, -1.4612438845688163, 1.1211736318476397, 1.4134104545507131, 1.630980505240805, -1.8234504777155476, -0.4477098003719894, 0.4246564808595141, 0.8087513275013121, -0.6569494954554906, -0.6565568839175241, -0.04929623333272726, 0.12998145347632062, -1.127344996138885, -1.3327105323752035, -0.8356256593237269, -2.105739241332067, -0.6579111749787733, -0.15248048447181878, -0.24176260612970113, 1.1973307836760072, -2.048195542102141, -2.0063397609889324, -3.267461702553472, -1.5867110196299696, -2.600098968383573, -1.6312056737711884, -1.7892971170341527, 0.7155097596423764, -4.521325633125371, -1.6749837714586222, -3.0668259932545205, -2.112283330593948, -2.5460243028300713, -1.7012260727575717, -1.0931782328111979, -1.854126540234215, -2.9110252547531736, -1.8829328534194156, -4.6474619261716645, -3.302777617082803, -3.2769522323472753, -0.4924755218381392, 1.2488150108122222, -1.8475277277947335, -0.8644862931229215, 0.28056060583771414, -0.5590257094349401, -2.231710172702097, 0.3281637628645116, -1.407386897149685, -4.732534868547891, -2.1362349596175894 ],
				[ -0.023254843060272232, 0.023950644190703124, -0.031710243542096554, -0.007493029552753026, 0.010757623233715945, -0.01042124356653924, -0.0004162808868948086, -0.00395480535976823, 2.8715139902191424, 2.7403489100312024, 2.435397791820044, 4.226349316645089, 2.4459857675095593, 1.9337763598208944, 3.020925186296807, 2.3447338852625523, 1.6852594754717494, 2.934712352701593, 3.7018967411320407, 3.7168679339874844, 3.008325324980781, 2.698577412110857, 1.8873128399264665, 0.9573771221439697, 1.4166521601552207, 2.095586291011977, 2.4395085245913473, 2.934127449342405, 2.5345268148940803, 2.957366636478459, 2.0576687387139496, 1.9192448339095312, 1.4022867564377264, 0.822154291656953, 1.9897319843537646, 1.533247156062686, 2.8646662900759874, 2.011266623740841, 1.8453715117362923, 0.9647193179230871, 0.3790913272702556, 0.8918588862341262, 0.43552755923052483, 1.4939352006362714, 0.3385700433521321, 0.7024608355521332, 0.06867977701812844, 0.2770746903672845, 0.7598403821935893, 0.10855580867491307, 0.8444807558623074, 0.18741519545188495, 0.6371915667402887, 0.3082687481383759, 0.3433421944863858, -0.4566135219038162, 0.018939136383738113, -0.003281618197016203, -0.014550018159929174, 0.009949738421987136, 0.012551584760409346, -0.0292589964466615, -0.03573529058594182, 0.021776166898970738, 3.345887135889635, 1.3657412698625861, 2.0008260965803353, 1.3652063598272237, 1.9031759681099851, 2.5451885886996517, 1.7835193491415933, 3.0912849830588462, 0.3607353741699027, 0.9758030266569361, 1.728848426768469, 2.706215079923665, 2.584735524053288, 1.6163117605088966, 3.5494339869558473, 2.781567299954015, 1.6160239308169817, 2.533434480028866, 2.621959232752844, 2.663342035697956, 2.4022173125201904, 2.919123217667243, 2.4284320570910394, 1.1687628333308595, 0.43991642532997216, 1.468848387845631, 3.1601489547610293, 1.9589917037852007, 2.4023650685802287, 2.62601595338507, 3.0705329096574276, 1.5477984777544036, 0.3787284167866772, -0.14309693333699852, 2.3225857302957276, 1.9005955235464458, 2.0851553840056685, 1.768601790896111, 2.4124345805370258, 1.1821301208406731, -2.5418180736486358, -0.9257611179911998, 1.3213868031508347, 1.493013962936857, 1.019016170402531, 0.5414428183938779, 0.4547590667990157, -1.4469237671590875, -1.8400837519037025, 1.3402752090018368, -1.2373276247992282, -0.6101687482948953, -0.04974335875536981, -0.676835316511983, -0.2979524538271515, -0.1893692537549501, -3.740003515593077, -2.641364926669423, -4.150249946628212, -0.2953981598130797, -0.546346604164086, -2.3664025199777843, -0.28175062125869765, -1.0891508605560485, -3.2467948861679243, 0.9033537349186824, 0.07783383943889381, 1.7465018347763295, -1.3542160531513046, 1.5130836997402568, 0.9103798638945306, 0.4771033943251914, 1.2445712444344623, 0.54704704672825, 0.4814154958684197, -1.9529868447198773, 2.0476888751245252, 0.07695734319884574, 2.379881234222309, 0.726228387719788, -2.126054671543685, 1.8728225207291906, -0.3531506578675103, 1.1690614219984778, 0.2545354598835428, 1.6753146064217166, -0.22607498639583984, 2.2977182936670446, 0.9328180893150463, -0.9776898753583334, 1.8441030456083607, 0.7570530192517763, 1.9114976200476734, 1.2806279523269057, 1.605064970336221, 0.11794435848880003, -0.9085709065151927, 2.533571060020362, 0.9051464891653456, 0.8684365661988973, 0.6126683436297071, 1.986799133342308, -0.9395087466708879, 1.7781053967121105, 1.6943889415595277, -2.752395814274638, 1.4838785975749758, -0.10947013727406674, 1.4068611215693694, -1.588112217609321, -0.4214754884755455, -0.9640583158472568, -5.252969126969187, 0.8817097217440293, -0.9504571917071624, 1.133216702345509, -2.1240763204817945, -1.9443803121600571, -3.738953655351307, -1.208585310905695, -0.5950215954955249, -2.146142435901974, -0.09740579795241257, -3.1829335987765215, -0.30507535338730396, -2.4609290921020555, -2.0342800401747816, -1.716761896246278, 2.9497168084470746, 2.7883847859381197, 3.1106914686414986, 2.6018232062040783, 2.308018525008933, 2.7161109973658935, 2.299075856424392, 1.8639791120054505, 3.091832439796683, 2.395185403259598, 3.348453404910682, 3.21869449414687, 2.995546630941729, 3.279441159408284, 3.82675322966767, 2.5039497747980275, 3.0780322950787067, 2.9629006180573714, 3.4032885514258084, 2.1998938704123483, 3.032212728518843, 3.2994475971716213, 3.0979249251009287, 2.474867077574717, 2.12961628530089, 2.7101438842690997, 2.930373283273101, 3.0931769690613304, 3.0711296464691005, 2.666334220347819, 1.9125535036929873, 2.6779281114430593, 1.2078217977674577, 1.1054439403362717, 1.2275017544420177, 0.8826011020322545, 0.9547261587168073, 2.2230903307892453, 2.31893515337905, 1.7311776493030901, -0.41168139859694325, -0.045028785108914726, 0.25299684895479646, 0.7621008731758011, -0.2877949494156754, 0.06407237323456783, 0.4887125284510382, 1.3343582340878808, 0.2686598393925354, 0.22832463956855453, 0.6547257639125704, 0.2013023849568631, -0.4247486193788701, -0.6571585392815582, -0.7973425553597739, 1.1994992216654259, -0.10346089625372469, -0.5912555105153928, 0.07271938176095347, -0.008106477712946803, -0.4019139113913433, -0.1316852002199654, 0.5032483348611094, 0.19119131701797726, 1.331307257687206, 0.02331411520462938, 2.150866981874954, 2.0950709753397083, 2.100089798191513, 2.348921111885927, 3.5313012311826615, 2.2708164523942695, -1.8657857180553072, 0.7685637058671556, 0.7664449287873674, 2.0693231084122625, 3.1707920297986547, 2.101065550478345, 2.654679700672588, 1.1306668119823515, 2.152961530348808, 2.009084716860461, 0.929211332167441, 1.3005988961377135, 2.706820368869754, 2.978854754539685, 3.5286962055896622, 1.839410991910365, -0.12324490918201743, 0.6305006658281314, 0.17301168883232027, 2.3453413732215025, 3.052756916845619, 3.019989872704215, 1.867627377771515, 2.9434852215151164, 1.0247445837333722, 1.2221699416322522, 0.2550983331745801, 0.43761472982301725, 1.512960794976451, 0.8131394703564416, 0.8333424272719687, -0.2226531487412919, -1.0271771659226767, 0.414369029908039, -0.9205287401567472, -0.9643518432795065, -1.3670065909914464, -0.7712595464031508, -1.50190645196783, 2.565559050914297, -1.7019413954313234, -1.6380043505133322, -1.160493321558747, -0.1557227870572004, -1.095442244342634, -0.3586511481514693, -1.7874007235099352, -0.4537271427971805, -0.35859671547646427, -0.22877841154795903, -1.3878556513414335, -0.4444600292732274, -1.874926489409499, -0.5316085098409599, 1.0237419591591759, -0.30974293614251525, -1.8603010416803873, 0.4799444985890716, -0.0907117664448604, -0.8814844718600899, 1.1022461226403315, -1.5494953491548946, -1.3880444438593276, -0.6141641780297759, -0.06396674795133012, 2.5038420495993265, 2.2436568562235153, 1.2163948723733378, -0.0033302518008568698, -0.285723460536439, 1.002275984003312, 0.33185170107757667, 1.7135513929100015, 1.32852548386126, 1.8459453336219949, 0.20004811139619136, 1.2485454564640932, 0.18680824726537448, 0.5032984851400203, -0.878669901187399, 0.24827433563830908, 1.6601490281298716, 1.5746940728924383, 0.8525304581159159, 0.012091105596178242, -0.11211947623526612, -0.6419195558133338, -0.3969955820949435, 0.7657470634498874, 0.3997917284863503, 0.8237018834537476, -0.4398963811921822, 0.6682901134162966, -0.5026789018799732, -0.4563949416993754, -1.2780051718513823, -1.7043790735644808, -0.40086343649958517, 0.958047281524496, -0.17071651759212958, -0.4776044873151508, -0.6377963904071227, -0.9252476735895483, -1.4993233444342633, -1.199454587298523, -1.149012189158296, -0.3510619030589641, 0.0951057882605126, -0.6789417109231514, -1.2768612538286435, -1.0319027716435865, -1.559092167940031, -1.838921490656873, -1.7434935615425093, -1.201765760152877, -0.03958804732997783, -2.3390550751263026, -1.4213828126027106, -2.1146490999214316, -2.440017813907675, 0.00027503676062785057, -0.008494222505536973, 0.007504561196816449, 0.004873879651541654, 0.019104387835585615, 0.01346321504083805, -0.016953657941906376, 0.014137193959079607, 0.35503102096458317, -0.4606781260313042, -0.5028100417407505, 0.3780349858537692, -0.3851704055130162, -0.7124603681770623, -0.9087756205586864, -1.158052614821438, 0.7267063718127282, 0.527099677481107, 1.5976059216202045, 0.11536984878246176, 0.598537973551142, -0.4697790355908746, 0.06876856750305166, -0.9849331058414531, 1.318843574755625, 1.4590650685052984, 1.2508103575801428, 1.4190876426811034, 0.7221706346085895, 0.2718497688141816, 0.8010823909947768, -0.36455836160185545, 1.3395469177865964, 1.2708717425146046, 1.2082877886088863, 1.8330098736148248, 1.254361793404932, 1.5400352287601262, -0.4741132678248806, 0.24617271316487604, 1.2116532989362827, 1.9255424191627692, 1.1874800889975021, 0.6051036883014992, -0.3715330243944288, 1.4877544837048748, 0.23552118439072664, -0.06627018674153995, 1.9654610656714826, -1.8053366857763378, 0.43429130011231687, 0.3429019418389544, -0.28909237229267887, -0.6019667703962811, -1.5647408133692515, -3.0193897931431013, 0.017119185277663256, -0.0006354409632668987, 0.030627899073523614, 0.03495605246460965, 0.02230926537622865, 0.034146928578280236, 0.02390044066040122, -0.03283210225705682, 2.1389876469059597, 0.8010582742804534, -0.6829738355192286, -0.2416955848203699, 0.6538192808318469, 1.1532213347203637, -2.293887908623842, 0.9196832367392676, -0.7221228212531395, -1.7587085210147964, -0.4540684451695841, -0.797460603521041, -1.02887220729765, -1.3050947453779385, -0.8103817896722, -0.5748795197663314, -0.9524153408913041, -2.415766952564692, -1.9382642255354654, -1.6490954767439656, -1.9980436757023612, -1.8612336352010923, -1.5235817394290134, -1.4968303612270595, 1.0557543652733137, -0.8384990062450594, -1.7074714430921327, -1.644907935687767, -2.673472801703325, -2.7050827327431777, -2.3328291032761905, -1.3241314786341387, 1.3156907561247282, -1.7671657306218884, -0.5848648031533085, -2.6691547372920086, -2.7003470746305327, -1.882775118290826, -2.249707035433682, 1.3378465884978572, 1.2617028305995848, -0.6119443823101637, -1.0465836089419356, -2.1618568738429147, -3.7565010249316972, -1.8289341863277484, -1.010924342563559, -4.588815156719635, -0.16767186508928328, 0.2782236826157808, -1.0683572541921966, -1.1255554860217114, -1.278034433174129, -1.406564667905736, -4.418772195565873, 0.5130654790063385, 1.2445520028665848, -0.5226857982529628, -0.9056904137005803, -0.9516268506881759, -0.5273986511064005, -2.5020727897555846, -1.1667267103951549, -1.043802840195755, 1.7681315631253922, -0.3827515994335661, 0.45245511106020997, -0.3378729441649364, 0.39376096976775277, 0.13541637760792977, 0.12253496346913625, 0.7207557333583134, 0.2972951953580101, 0.2402310426350048, -0.7136855576336514, -1.1542770868705807, -0.9401332866767218, -0.44370339171201545, -0.15481726741601087, 0.9369056176481299, 0.2521887605485478, -0.1066903341084662, -0.6242253924858667, -0.8978655077039497, -0.647850081020866, -0.744622233928963, -1.06906374603723, 0.5042904526333596, 0.2186527594646125, 0.1125168741303898, -0.8855770501598386, -1.9362570299815163, -1.2690492111754734, -1.9590133924094235, -1.1053180976409758, -1.586432827914309, -0.6423671770414701, -0.824386300242142, -0.26123842710088707, -2.0050997577078102, -2.3724442947955016, -0.017758875416172246, -2.0807965768290684, -1.795175744829122, -0.5428056823312504, -0.3527661188781228, -1.7475772086813526, -0.3451621800819531, 0.18907257744734804, -0.6597147201515836, -1.963216083516266, -0.8367712726973927, -2.502868195434631, -1.1311939952117658, -0.3439925896981886, -1.6852626274111697, -0.6191360859753005, -0.2262756723165102, -0.6617113415885806, -3.924601956525972, -2.7329882993657493, -1.8633631868799447, -1.5609611831612165, -1.8675765962205093, -0.6011711220423739, -0.8957983360444031, -1.0819620464100415, -3.629648918463756, -0.6882153253581141, 0.11728748788787527, 0.12955984662150077, -0.18406521281405927, -0.49469375549454686, -1.0109005854067261, -0.3401410449585023, -0.7448456488003822, 0.02366767675824578, 1.1152346488027929, 0.044524988190244114, 0.0043840628604449846, 0.14068485417185386, 0.14928059199492016, 0.11208928394751058, 0.6185507325728611, 0.8876717524589567, 0.4647241730341573, 0.00467325340229689, 0.23422097747836526, -0.2053229559575603, -0.07816573754095267, 0.8420855907148906, -0.008824032385932708, -0.1998577702228088, -0.37907920541119783, 0.10978834682708918, -0.4945448055203272, -0.2845611108908332, -1.4174341615131982, -0.6336840078688529, 0.47010215139020495, 0.1837458295352299, -0.7830642482973874, -0.14248912109781195, -1.0344499384223662, -1.9181711847690015, -0.19936052485678857, 0.18381190907716108, 0.005069230774659766, -0.7592767655964349, 0.2007450221369237, -0.7259237212334252, -0.7127884279716264, -1.2820792948700794, -0.10811972356284615, 0.00653677382768747, -1.1507100686532716, -0.9803818925588025, -0.5252874205766362, -0.557407673755073, -0.6507546979469541, -0.9786536054305358, -0.5172495661461259, 0.1498988188715396, -0.08865567994215853, -0.9149738449556382, -0.3872936822479564, -1.3567583766950557, -0.18465857044780698, -1.2863578017589736, -1.2801746549642932, -1.557521745870258, -1.7481043984233064, 0.7404427413405762, 1.1748409355547325, 1.0924189416359769, -0.16033654015555257, -0.44190163515463027, 0.40257806778182514, 0.45716632712805844, 0.8186451736640417, 0.018610598112374956, 0.5149941846645184, 0.48250186880348256, -0.5040518193984628, -0.2782374417009084, -0.025101840844585294, 1.195591639283932, 1.4154162499507574, 0.9883033102479836, 0.6165438222894715, -0.4024653628700617, 0.3759775195511672, -1.0597866078805729, -2.5056198756832413, -1.1238011657843612, 1.4464918662467348, -0.18919146419510224, -0.29831035620198143, 0.1524728027570328, -1.087774121427904, -1.9475235377952975, -2.9229252015220433, -2.3793861410703414, -1.7322593927383942, 0.9892655154101623, -0.7570635590095026, -0.5607336325170348, -2.297442190220747, -1.0443764093860242, -2.8996078377763514, -1.8777228408791187, -3.8130425149058214, -0.9294419401203499, -1.3827491970255983, -2.04310835922287, -1.330354527938717, -2.9993734415535225, -4.698409106933, -1.5068266595000157, -4.2559983840466895, -1.2836054801597063, -1.647381426701534, 0.7569444378714135, -1.8286081335035897, -3.548231139001274, -3.3767159875729003, -1.5231692094838698, -1.5491046994843056, -2.9721553067133946, -3.580481289651747, -1.4982705735869, -4.203634165915894, -5.025040828439255, -3.659101917063913, -3.697596341503434, -4.726529235682531, -2.0904216765525634, -0.8876302439410436, -0.5231781784820392, -0.5170505033943692, 0.8269754026019582, 0.41978681574652876, -0.5680941771407877, 1.1512613429417526, -2.044649060195984, -2.034782982331635, -0.6902345250344423, -0.7803604185320037, -0.5511282538018613, 0.06272657943198026, 0.026535069035534535, 0.21722672820098482, -1.8656358145831813, -2.1525120206640085, -1.6951009735490767, -1.2127505038873863, -1.1000451345847113, -0.45922053595670453, -0.22684973307655115, -0.25338673966330116, -2.5872335513479574, -3.453157630430555, -4.611608058777572, -2.6128835384637257, -2.319881086797462, -2.3894996689425003, -1.634539335093411, -1.3935567592027938, -1.9585873433928873, -5.864271704954334, -5.125645642709673, -4.31656230151284, -3.4806182470431666, -4.508323492128574, -2.462929245317956, -1.5018129895245724, -4.1576345502053424, -1.4890884025763595, -5.817564769030051, -5.076565622482413, -6.610454192557375, -1.6795629673286467, -3.205075145256903, -2.0555823041220136, -1.4419179930537018, -3.4558607983583887, -5.106385156349361, -5.580606275765368, -3.8586119208828507, -2.7508688342701064, -0.3047120712425962, 0.8912174627980912, 0.005290265534879271, 1.650716099664703, -0.9435924629984779, -3.70705031120112, -3.358707961701079, 0.12539684255666037, 0.050125224529125906, 0.2746277723317027 ],
				[ 0.016816892774304724, 0.025510402326797445, 0.03224949178845484, -0.03325069285729892, -0.015383925098285942, 0.027403044975206868, -0.022517354155272, -0.017144648423874996, -2.4336730828198045, -0.26768619564844554, -3.800712905510319, 2.0913149536912594, 0.013325048913912564, 1.3974698906264014, 0.9832018136792575, 3.7522404139860224, -3.5803076988393654, 0.521732111459974, 1.658330552162161, 2.042415052798753, 1.24245390384125, -2.442274318272574, 0.6818963963379356, -1.1348545143721782, -3.881558160063111, -1.7297305862768189, 0.9879049120863899, 1.9327461367153704, -0.4101522628315076, 0.048609280195658126, 2.4690148120057405, 3.711593231893806, -2.2056341966385684, -4.771026053949882, -0.15137081842630792, -0.9493048938267515, 0.831923593871382, -2.6829253602821908, 1.9669702579253199, 2.371041072907819, -1.6802149808170337, -1.1669131979846974, -2.15675735656802, -0.01529874939422395, -2.338681817649378, 0.02179205029694487, -0.12370204890481709, 0.741011163786349, -2.0955475001183412, -0.593444590225482, -1.148766516778895, -0.38619173209631424, -0.5262874144801923, 0.8365305989370028, 1.4415373822400146, 1.1148701584541139, 0.0256055203985636, -0.015587321274949035, 0.0009530038641450532, -0.0341053437707926, 0.016874474942625395, 0.034649579691640606, -0.004604980358807736, 0.00214260556725794, 0.1203553211316599, -1.7511354951023077, 0.7747267975770591, -1.6141491038442257, -1.886857838066624, -1.7802716405779504, -4.592943089245828, 0.45110641900661264, -2.479511533697998, -1.5412852231389658, -0.6324171198620498, -3.061121112887365, -1.5966736534295802, -1.1926447311057486, 1.5513171799150791, -4.189981646540998, -2.8492081561020344, -1.1331942241603536, 0.9397937556612261, 1.29820340117709, -0.48554490927492855, -2.6142800519172376, -2.141772805124364, -1.192876309048897, -2.761987641347935, -1.434697173596296, 0.5463507071373002, -0.03288132481518514, 1.775188985600633, -0.8884290184421212, 0.8162738643207312, -0.9932960777168334, -1.0510356048814966, -0.40396420795296156, 0.5285904866551632, -1.61296491510883, -1.3426649670836865, 1.3161299766543202, -2.0302144584189232, -0.6746499199903794, -0.8016410236237121, -1.2171810600670492, -0.17207222628232316, 0.09017655323982701, 1.219023793508086, -0.42728962938480225, -0.42320066548878793, -0.11748242913415172, 0.4518412654987786, -1.7987215927171658, -0.6508684217408764, -0.7678109039821187, -0.5486478886519729, -1.9424917572195826, -0.6507505624130135, -3.203758419976608, 1.0045884066746726, -1.9572263358496482, -0.09432899788379069, -0.7015337998681953, -2.070595900327853, -2.025283578343348, -0.9311401277254892, -2.7300464923279497, -0.9812064998799651, -1.9234359153302396, 0.1475961275177756, -5.219040175303155, -0.8865845010662751, -1.8647907905005894, -0.33401497113432127, -2.1683495413351768, -3.995010490212052, 0.6347606077373803, -3.4528517080319148, -0.26511934636901385, -1.2536390309116803, -1.010727259811572, -5.216708917671406, -0.8532788342887581, -0.2457304937240918, -1.6484067496618142, -0.15965453939502008, -2.4131524809901803, -3.683598698799559, -5.710262431360653, -3.335904711108345, -1.1454273579755925, -3.303574662180358, -0.5318826445009067, 0.019464443796392814, -0.8751306743330785, 0.7415111508100916, -0.14009396537271307, -0.7165950476714864, -0.2240533581369063, -1.7607531212022631, -0.050423094286796345, -0.7039314420915568, -1.5703774532439938, -0.6693205795066245, -0.37003733098603525, -0.15241914667073755, 0.3492146255661439, -3.3828407548913995, -1.1177187367313637, -2.0193809431595255, 0.7490660856974601, -0.11648789390449958, 1.287241387719469, -1.8062909321409288, -1.4069147101738066, -2.513176305527335, -1.6796407991817066, -0.048994767835188316, -0.8644145634858189, 0.6578704157154683, -0.9606732922717197, 0.4970849832970191, -2.962914250946888, -1.562679820653523, -0.2156088004115363, -1.9988280680902868, -0.0874779586580086, -1.8968363479623385, -1.1567509340377822, -0.8473609927827711, -2.164957431832079, -3.1303528026127587, -2.4961181451502754, -1.425176491702, -0.13003160704657085, -1.1691540874326474, -2.065890217281124, -1.8760337419503903, -3.145117747342958, 0.30500146268984957, 0.4875918989346636, 0.36098006224935153, -0.8612858001498087, -0.9926667379011046, -1.7223238774003573, -2.242085951043767, -0.8599621594025796, -1.585781492910564, -1.512041179112588, -0.2642181210966939, -2.0385866741749514, -0.4360594866602034, 0.3831709474141761, -0.8632680359809793, -0.9094097076231167, -1.0754749948016933, -3.605757256798196, -1.7568279520952594, -1.7535541810752555, 0.22327904423503067, 0.7308211237387179, -0.1885118423187389, -2.1569919062183303, -2.27479145426842, -2.6455245683644493, -0.63104814569071, -0.7634688076847567, 0.3838056236260848, -0.15652278543427034, -0.22037749342738625, -0.9216170270306009, -2.3116288549960076, -2.1105754991851766, -0.06705613240584535, -1.354705976607427, -0.5217065045671935, -0.728203098077252, -0.9762905529186616, 1.957771199871508, 0.06323181870689167, -0.6700349933396015, 0.17874412515285104, 0.5453430879339605, -2.1202189607730872, -2.7006998410406395, 0.48201892028496923, 0.061773427452785974, -1.324835915849136, -0.12784537098831764, -0.9472452983026239, -1.667552777695724, -1.1636096432697207, 0.16924699232431326, 1.6290552690952484, -0.4279691050644005, 0.4906434691062499, -1.9005458064467668, -1.0986237541510937, -0.7632295382145315, -1.2786572893222388, -4.810697573803645, -2.6174966253873966, -3.321180335392452, -0.5628141445310972, -0.16513858368888754, -1.4129984186305415, -0.4890953701980865, 0.4744056876269348, -4.900179596316979, -2.475546744591108, -8.128630525693984, -0.09661214616089793, 0.3577621287315392, 1.2216627221669534, -1.4216960055213503, 0.4682620479703764, -2.47890043422603, -2.098204353780377, 0.6444744137475276, -0.6680635956192712, -1.9009447049785484, 0.11919355405803014, -3.072855671733298, -1.5862096959634746, -3.275538478775145, -2.2348375493616293, -1.039413611731469, -0.5224834222840689, -0.1527357746439664, 0.581834716649856, 1.5671143622665344, -0.19559052492509613, -1.171291635316734, -2.2274994120875475, -1.3473271785959298, -0.7773125230279812, -0.6998064195594882, -1.6672666570881993, 0.9304913236039734, -1.1005703870580354, -0.13693508713575286, -3.1837880575844317, -2.313622591307603, -1.9057510729005738, -1.5509983892387162, -0.09612946282520532, -0.40771143961740575, -0.5490688636990932, -0.8694749936164906, -2.0448079239558115, 0.053380450720937375, -2.511407001010586, -2.2951179355961284, -1.352336503016988, 0.09987005937598732, -0.39033089051335446, 1.6496849596609677, 0.3251223192519284, -1.4697880646100348, 2.246490718093244, 2.4729633819186927, 2.0659060769435635, -2.134613688433716, -1.0888084940909375, -3.18914879875113, -0.08794299134724042, -0.17194253544246074, -0.1764193038963191, 3.4297603051433145, 2.942836331668256, 4.031485297749402, -1.1907929107248394, -2.1685004824211753, -5.3675950200162905, -4.512507634071052, 2.541371522081845, 2.3425415409482295, 2.183413910357636, -2.166518173742012, -1.9922629356580146, -6.0582800574189415, -6.862826381380742, -4.972029318764945, 0.6073747396484763, 0.6583587145905281, 1.1016877514898804, -2.0729770551413074, -1.535451651338052, -3.383747878488385, -3.434502812458373, -1.0879481674479903, 1.3465697962849004, -0.3267391541794448, 0.8256932060688542, 0.8290959470765874, -1.3143366625316555, -1.903123856882093, -1.4751643932809195, 0.7639501742160815, 2.218838776477366, 1.3460010410318688, 2.048771749515355, 0.9664892840133646, -0.29366924473070055, -0.882481634461944, 0.25998368922765297, -0.3289361044205634, 1.415327547000829, 2.599912260317532, 0.9338493521374654, 0.5985373372875837, -1.075802284492421, -1.0515486863670012, -1.4997176147639775, -0.06734520788492354, 3.0233653837795136, 1.3797919854713454, 0.17461351742766432, -0.15292363471622888, -0.687154518032203, -1.7079648139491077, -0.9359784934642406, -1.621327989340675, 0.031803499192799387, -0.032751460520304664, -0.020371608122266134, -0.03349205199840697, -0.016309382472769147, -0.013793224685822397, -0.000441695835334463, 0.00973430261076244, 0.32964995305040584, 0.33004753885643523, -1.7987523615957968, -1.2551616268616186, 0.8386767853019327, 1.5357921429223087, 1.6794583521702455, 1.403916902742685, -1.2268397292690187, -0.10548071753191901, 1.0325474292686814, 0.724439646154061, -0.27293959338404783, 1.3043637401045949, 2.7721564360119313, 1.7627614209200557, 1.455750450201354, 0.02686325189853812, 0.006842800913720644, 2.4470691132861235, 0.7615331130808787, 0.7443690409359934, 2.6680646903381033, 1.1004344293069337, 1.1853607823777892, -0.3292492457925267, -0.853589216666446, 2.4493723137592402, 0.9270198424422784, 1.4131224644816827, 0.7454714780353934, 0.17960742010749303, 1.818033157714453, -0.6965615680737085, -0.4530870624497991, -1.5963932487223993, -3.017463179829897, 0.5424187756448644, -0.11618233593133595, 0.8944324280895273, 0.9032945609132145, -1.983014390800953, 0.5437261679768314, -0.17909720327954898, -0.09119109063219183, -0.998222592367155, -1.307231428607732, -1.8084957519873706, 0.026631562887980575, 0.03138839546127477, -0.026335989204515502, 0.00681858063241556, -0.014541978091540151, -0.026039371005624434, -0.018068470892964348, 0.009858457510062554, 0.11618267280106613, 2.598469887521934, 0.9180857106179716, 0.9701489017798113, 1.8256908006312376, 3.642215483131027, 0.7155348692572204, 0.5614327249203337, 0.8650428779939565, 1.977838756284559, -0.589251550082028, 0.6580734508664544, 1.3411756207632084, 0.13044668586032054, 2.49514413122736, 1.7204134193778593, 0.2503494673374781, 0.5469004185220555, 1.1424274525165903, 1.300702762680184, 0.8156561578756409, 0.05400978879475262, 1.3047225852874529, -0.59608978556303, 0.11183307321098836, -1.4699197488873204, 0.24490584703695228, 0.08872168433284071, 1.4164407244271937, -0.162403479056527, 0.04682913611850421, 0.2393481769314859, -0.05408618593087196, 0.5812430108994336, 0.44754218619939007, -0.6812927236425123, -2.7716074107407773, -0.5184046894668969, -1.3922420184765065, 1.8922166112012615, 0.0099007394901744, 2.2833630288424254, 0.5365439574180917, -0.18134841460397286, 0.361160469198547, 1.8072322998202783, -0.3797441893300775, 1.5125216250988425, 1.3407921758427994, 2.5422410262719612, 0.8785467927878273, 0.7492434319253666, 0.30616173504700206, 1.9324720936979687, 0.23649958080346858, 1.0723527893896003, 1.755686884115973, 2.2936469537003825, 2.8894156419179553, -1.7503793604985365, 1.1874060001489029, -0.09410853242974333, 2.7717998951503553, 1.4963695625551319, 1.8578192820012143, 0.02103802805328467, -0.273557447982234, -0.26036007022884244, 0.2657800965584541, 0.5483043281691506, 1.4317488947556012, 1.5614847053527912, -1.7610148572352835, -3.10341881834408, 0.3435924827252321, 0.21516471724362177, -0.9455072597041272, 2.1410547520695062, 2.032742367305522, 3.190090193481726, -0.6396667569208514, -1.0049386207622422, -0.5768295081790247, -0.8820093996122895, 0.45437068219806664, -0.18017325691077576, 2.0378384094014144, 2.2997326907215316, 0.5775708572355728, -1.6361218506679622, -0.4149538994993056, -0.5567936829987671, -0.27703279091962874, 0.5359116744515681, -0.027181919112735018, 0.9909935399501386, 0.25418083083426707, 0.7946457725327803, -1.7274699170443562, 0.6673977122304047, -2.087030476111043, 0.8130521852903371, -0.8543380422275826, -1.3503420873280267, 1.0556455129209268, 0.584272418317419, 0.06772804651532162, -0.3330297189190931, -2.1273116317029928, -1.0406229893889618, -1.6232963065656028, -0.3332213947121126, 1.3246966466413872, 1.1536607247461514, 0.5403179958547663, -1.8854812054278882, -1.2424856057767395, -1.020243410386589, -2.8465785357429993, -1.2843583785783645, 0.3948014041394567, -0.8120636581120851, 0.19898349324734113, -0.996775503111693, -2.0635772559525782, 1.142045358869225, 1.687831403803062, 0.3749461499057337, 1.6629160003738888, 2.0455759349554423, 0.6621583003619196, -0.12607755047785227, 0.087780252514486, 1.0681037565454636, -4.6423136571690256, -0.6317623913407558, 2.1039234520051044, 2.7860733530837356, -0.0021653440442309596, 1.3806661254547181, 2.3061360073778965, 0.6065160578902633, -2.4511962157079474, -0.025977996373101893, 1.0442064864047254, 0.9176365861993555, -0.42915659489702007, 2.2619642150075676, 1.3788407390033706, 1.6909179002333734, -2.34588720902877, -1.7402701741316697, 1.2981599253588856, 2.691390434102016, 0.7082640612946942, 0.12092903090150849, 2.17588549118346, -1.6058548606576726, -1.2411004306972369, -0.08717796780500238, 1.5553106744328187, 0.3087511073339812, -0.15127011642502944, 1.1096242960606906, 0.6261748625555359, 1.9403573165684946, -0.33251974937018186, 2.903894931383336, 1.5877529768674583, 0.8042421763544225, 1.1142205662492901, 0.9008338778019727, -0.4969066512103928, 1.3366533859776004, 1.081074017595762, 2.0450415725846782, -1.3195388862610202, -0.24497797945952787, -0.9579414769501765, -1.8214732436040761, -0.24577162963233357, -1.391616978673141, 0.9142274572732589, 0.974327158306598, 1.6343006781297513, 0.9635656324991282, -0.067276142554606, -1.2677142848271488, 0.05566442503843574, 2.9694233284585754, 1.7822756172477336, 3.3737019022985772, 0.82764285121036, 2.775781371638889, 1.3494098286932372, 0.3733178986566951, 0.3591782279445662, 0.8255622381109045, -2.7001313571045187, -1.3024152618277272, 2.314880799729339, 0.5262748198058139, -0.8553667150981934, 0.6722426745322697, 0.09601439543731564, 0.13058428920001264, 0.39790859978514037, -2.1940033470533904, 1.4745397362520287, 1.3093815399399404, -0.27519349380965347, -0.7378034446198796, 0.5133561451028307, 0.19340892865794299, -0.23621800822609473, 1.5799537932046817, 0.4410599855392381, 0.5503620464639122, 0.09958108413300316, -0.06599106859717828, 0.7452956574080932, -2.0253297347413097, 1.607641860372332, -1.004589705943983, -1.2108742285226723, 0.5439771000683762, -1.7969688173749414, -0.8072582268763995, -0.8202955232342676, -2.2033623337938133, 0.8025807814678468, -0.32666204248721253, -0.7725053855077479, -2.9738462268193744, -2.6299744016283015, -1.8906447993728035, -1.3291368378884978, -1.4534972942926299, 0.6554496562462165, -1.5980711144667956, -1.9526030283286295, -0.7864148277928665, -1.6984198577142178, -1.2052781308519096, -2.519728322872627, -0.4637367842328661, -2.4831492847258416, 1.6139608070533162, -1.9971261836755712, 0.6458107907363178, 1.7549210069246508, -1.2054397761101028, 1.0082499021728137, 1.3468474622299365, 1.5392545980967887, 0.5657046647317905, -3.6879616204525623, -5.522100784268705, -4.949807916334781, -0.9492905568155146, -0.0747769708591117, 0.23937014756031932, -0.1328957618031882, -0.31829281537648446, -1.5980823154631936, -3.3573447688641664, -0.9220018382625956, -2.1029083197493494, -1.8116373393460279, -0.739462510420083, 0.1587285921877765, -1.4133218718509073, -3.0105014090944335, -1.605250389336059, -2.0419400061486437, 0.878191031697569, -0.43937684709169716, 0.09116077733733602, -1.1327367915145694, 1.9091212817570429, -2.1790346039561928, -5.00612122891644, -0.22763573498073184, -0.009592529111854495, 0.24847374854083415, 0.6024066389231956, 2.666238390334335, 1.5756112449821857, -1.515792846400804, -1.8810858430710564, -0.47075720736508736, 1.3442530459527828, 0.7933642209706547, 1.19447789479636, 1.934977908412024, 2.5222729985934986, -3.0267169173295945, -2.2814221212282515, -0.339101044337543, -0.08773919843659518, -0.7935497346679209, 1.7437679681751077, 3.0294690380816545, 3.0715402270251455, 0.5265764447886323, -1.828921560520998, -2.8501029158413806, -1.7907550945929962, -4.110119223459982, 0.39854004440311686, 2.038415552814503, 1.931612420820167, -2.5993214426348636, -2.3907828144602616, -0.9976718463084607, 1.3257376257089855, 0.8863506432581807, 0.504001513920852, 0.5819105988039058, 1.3269933697858078 ],
				[ 0.02635445520664952, -0.026704215268842556, 0.01668478215530425, 0.006297873460157423, -0.03433259491635819, 0.03077404446803322, 0.01162672057167616, -0.0018178037865420565, 2.790646098364134, 0.4048159436988343, 3.344298558819776, 0.1914903222242384, -1.2512897806393208, -2.6679598719373416, -1.6717825383333265, -1.2277202306650836, 3.1402674150148524, 1.7538044030716715, 0.7365280166108893, 1.8350063320342225, 0.6423762838036762, -0.6732445003262395, -2.613587144735496, 1.0584728897391522, 2.138243144321631, 1.9135076819115306, 2.670241651354627, 2.4570387289171447, 0.5230616417605153, -0.32061624567655, -1.4037595029405172, -0.5196729038246494, 2.0177052770071002, 1.5653201670859598, 2.516356642386028, 1.254103005399284, 1.5131248857810955, -2.0586857897992075, -1.0894049900132567, -1.525038570728975, 1.2725202798478463, 1.8983440718677294, 1.8208089303859423, -0.21077445079244578, 0.8187258711660862, -0.5401689579026335, -1.2522442222329437, -1.4470538636876988, 0.7981047864957376, 1.2293051557695363, 0.5795026293082786, 0.3729710795597018, 1.3372990736883799, 0.03376793559683816, -0.9810594278218354, -3.2225232381653206, 0.020773863251556952, -0.019437083011741324, 0.030549754354519797, 0.002719366459811047, -0.015353349574332327, -0.028617664738448893, -0.024557166147700638, -0.006643730955217756, -0.3332780099468415, -0.651468242149436, -0.9708250629371037, -0.24485546521297744, -3.3397665727098476, 1.1141920417379232, 2.101588527811848, 3.373105019010444, -1.4528430189077055, -0.27938758975314854, 0.5795148723699614, -0.8173068734939224, -0.23005809254434625, -3.759090697200732, -1.4355529601490566, -0.11105403206778801, 1.974696774994863, 1.7304654241760908, -0.23066311147128438, 0.06858954560974306, -2.8291301078518254, 0.33026960527629834, -2.260900752803453, -2.8136229220401683, 0.5469453150893531, -0.47272950770387434, 0.15984641386471513, -1.2755987096963672, -1.803087291893774, -1.9224350118996234, -0.7156353238856082, -1.2444307750121886, 0.5589663627220218, -0.42333465022149813, -0.4342521043049367, -0.9563497921566089, -2.351872915943423, -1.2102646125101195, -0.673843167867066, -1.5871365134126645, 0.39282791938492484, 0.810490051258458, 0.08524618477264544, -0.6171191485733983, -1.981530110842874, -0.11197989405465968, -1.8810830221717771, -0.4461762427123637, -0.17933735171020707, 0.8124603823892949, -0.8129426901926604, -0.5188058086413105, -0.0030291715366374985, -0.3067151542004713, -1.9814451250645742, -1.5097938177901535, 3.5096737172396906, -0.09261041718009139, 1.0874713148585158, 0.24138458012276298, 0.6102665942257705, 0.04546220304462921, 0.8016351046513944, 0.8234710747627598, -0.5539183234360155, -1.2279854286450442, -1.042438369723739, -2.4588151554872235, 0.16931291458078118, 0.541542003562229, 1.736818755573252, -0.6213383257645494, 0.24029988335813388, -1.4966554754520869, -0.44019160042698674, -1.4527706226271782, -2.3345365711212684, -0.35678423934289927, 1.0484924582551507, -0.3243774052456639, 0.7492071820717244, -1.2805438329119219, -1.2710517789187956, -0.6226216527765901, -0.08784651708267441, 0.5815584802026967, -0.02804460648766048, 0.36601436534546455, 0.009661022316032306, -2.168753619577891, 0.6161959222976938, -1.5355137525115727, -0.614112975842072, -1.9566855461928236, -1.0922035028522423, 0.856398308037256, 0.8770893210585086, -0.7311898100184764, -0.7116682134762947, -1.5275945566091016, -2.428039880417232, -3.2965573925911347, -1.4165001722369028, -1.4623749618475534, 0.20096631791004926, -0.1285022557023099, 0.21813853712849945, -0.6015099439566861, -0.857435078845774, -0.09043445450173963, -2.3850531182216113, -1.4869794776513086, -1.0131287728289746, 0.7544485344378563, 0.8304535894145039, -0.862419834295555, -0.22934441631181934, -1.9534451909684636, 0.3457584401543615, 0.28453305904233017, -1.3362933742292475, -0.6492756233077058, 0.7741281586027827, 1.2814972941852134, -0.1667994576361446, -0.27134518780265027, 1.8464268867926896, 0.866668391428481, -0.029796916183797872, 0.03370082440923911, 0.031815926944797686, -0.009705128783031028, -0.46449662145143245, -0.7860221895739328, 0.12063395403398258, -0.07916507893853213, 0.2584637102830704, -0.48614748425790844, -0.3061146401977053, 0.18211194770452963, -1.0665800869848618, -0.7923012133072539, 1.1951694871199003, -1.1311896292721073, 0.016074988296603514, -0.16780069803097378, 0.576055890333944, -0.04918516470150236, -1.3211189458172665, -0.009309761502995556, -1.0989731936121103, 0.2005985236305758, 1.6219908633480395, 0.08479654549857356, 0.575700290726146, -0.08365104330285118, -1.7053688096853334, 0.5128601404325455, -0.16095811074427552, 0.8332779088186294, 0.9904852806118092, 0.2709937998043484, -0.4865302613071496, -0.06747863447659645, 0.9821578374794241, 0.1322877963358369, 0.7725505398490784, -0.09314860676236722, 2.020818799664894, 0.6944162833219334, 0.24210826891976886, 0.9461064958448048, -0.08326547966732879, 0.9638481808482602, -1.8824375197960121, 0.23488139490598828, 1.2352296836427041, 1.3782964909936595, 1.758598184408646, 2.051090495301036, 1.5480649422300974, -0.09448664482065391, -0.3037619759579619, -0.09306533658807242, 1.2566115163740998, 1.4423495702279283, 1.2772089420758874, 1.2862432519412592, 0.9125227809971609, 0.41298811195396684, -0.4026630793938645, -0.6036602393906233, -5.560631865368872, -2.2700901943721856, -1.2863391503806958, -0.6526347264620069, -4.791141686174245, -5.254186691471159, -5.264770874645901, -2.059810048896587, 1.1457950243239616, 0.20655661616792678, -0.5035727940685317, 0.4593959741529668, -1.2537254883654048, -1.6202026816996815, -1.1193828532337293, -0.7446977370927519, 1.2306905430910429, -1.3051236536618713, -1.2923319648594513, -0.32969541800698626, -2.9437946768960632, 0.6303863796080316, -1.9048622370651804, 2.5620880182963686, 0.3983530583724088, -2.446484461220901, -0.7448423403756782, 0.11598393919462101, -1.086645116793632, -2.2568662867454905, 0.6947406492738094, 1.7043616185818322, 0.9299616559599, 0.4073494917072255, 0.31107675382100247, 0.3677337212649368, -0.3597541251308206, -0.67631809405377, -1.5629312548875782, -1.2271127071728696, 1.0974298407421366, 1.346228813848988, 0.2803472000611134, 0.3921383864523325, -0.03990454409898617, -1.089624044447452, 0.6195284285916682, 2.8800666238387302, -0.6147462846640257, 0.9110179503049051, 1.2311049946840615, 0.1753632373648601, -0.33983059087413875, 1.2455888116976488, 0.5592242658452077, 0.5803752697982479, 1.8215550573013164, 1.7365848886262192, 1.629568619916004, 1.0311984800324296, 0.009600945159730413, 0.28719487060396043, 0.18501255673802777, 1.4020147977079807, 1.6721359588180293, 0.5263210331522833, 0.4540164328244742, -1.2458532113068752, -2.2269506465813436, -2.242103782660604, 0.0860361722573962, 1.7889393551177903, -2.3979521487343307, -1.8300637867771878, -3.889857352065472, -0.023019786087242634, -4.156139660310243, -0.08178305276726085, 2.39359789856748, 2.256433095070756, -5.133581612232945, -2.4134711401504445, -5.025541057355785, -6.444015073744671, -6.631484855615216, 1.163592676139366, 1.529358236946449, 1.1472378526797784, -2.9418905996516305, -4.60152782268237, -3.5702768284897726, -5.680467778182918, -4.670980544525857, -3.051247115496179, 0.8957562499139661, -0.7641455326882639, -3.362540065585452, -3.522008670169041, -5.648316329976511, -2.04139186276623, -2.7254017169136433, -1.7973106116186288, -1.5500218748145111, 1.2184037374185825, -4.694270555401233, -3.1453074980891866, -2.931696442049938, -2.307553941635195, -0.8895227870696655, -0.4351152295361502, -0.055274576970057734, -0.005190050592278955, -4.204626809334988, -4.6177419534586965, -3.1033883791788224, -1.6022284839169172, -0.5580263477756783, 0.001951058204707048, 0.04768759463673368, 0.5417263218359366, -2.049589576483214, -4.579866332834785, -3.7348086759294343, -1.5434934423268776, -0.6281715474334925, 1.1750403056014715, -0.10651671147890437, 0.3266627980292629, -0.007032683443045252, 0.015886597136452418, -0.011241206127652054, -0.0230371260355322, 0.0010898057299828653, 0.02428737867097403, -0.009487745634984387, -0.026160332993642406, -0.29263164058648444, 0.32454009263703415, 0.4204837675194935, -2.8899387395038105, -2.377085062618017, -2.1366643219020145, -1.0961007206391544, 0.12714536568361068, -0.20751848428389819, -0.24929199953251432, 0.7541570709598645, 0.5901001508287252, -1.3617820244032093, 1.0577531422238107, -1.399489437785894, -0.49651885858863354, 1.0189344999915704, 0.5970496897615641, 0.6372936088568275, 0.688586034691958, 1.8938725247224797, 0.6973112867406867, 1.1717781937047702, 0.24521068631871373, 1.0339597672050873, 1.1422516072002395, 0.6487323102220695, 2.723802378017333, 2.3752254198797544, 2.4988632566198463, 1.3401614075380928, 1.6201009237391775, 2.0661453324033294, -0.07740794919037707, 2.222659522935376, 2.5539735203152603, 2.6635342902344967, 1.6473058510449494, 2.65157447875394, 1.8356583332048386, 1.7419884108064418, 1.6842619383093616, 1.3273274679018086, 2.640794703700734, 2.582379600863562, 1.0697869537149114, 0.9548143193569743, 2.0035993244742314, 0.03553223083680059, -0.020635644040582345, -0.02677195155443034, 0.03496907019343159, 0.02976119022098014, -0.007416073832332232, -0.009981471916490821, -0.002941686986930641, -3.139961897638923, -0.853367331635263, -1.374377838124205, 0.47227480451809767, -0.30618276020405216, 0.19551724956631933, -0.39921029919806267, 1.937889717857388, -1.4755958222078505, -0.620618192124185, -0.838567579085613, 0.2844992193960412, -0.18577462907340503, 0.4821994955128839, 0.47949595142705936, 1.3200428460992797, 0.058069011575077184, -1.7546436771849487, -0.6645437662426187, 0.7309528658405853, 1.6001585600628914, -0.04841461659096949, 1.2683751565727033, 0.7186237651089116, -0.4439513099117951, 0.8632101582841936, 2.5872710317613143, 1.482867313117223, 1.677926015989251, 0.8596416490611517, 1.3946698331938758, 1.58759802657698, 0.6942114060826754, 1.166967225348529, 2.118640757792511, 2.2207384244223736, 1.4750039518071785, 2.173866891596151, 1.7053329578456347, 1.993780177283647, 1.951319201144105, 2.2650092275530387, 2.5889524955197905, 1.0694733405264438, 2.1188405658866643, 1.2420992179475228, 0.5119947852707041, -0.23441227388451608, 2.1202059224549172, 2.267923407692892, 2.0851469596632715, 2.0952292453579764, 3.0770915061325494, 1.2402197319311699, 1.5472474162493648, 1.4514106522889167, -2.6112735945367795, -0.9231496391457646, 3.382379365222307, -0.33135852809277755, 2.765696171328986, 0.32573632243206346, 0.5217183004744739, 1.0803402047174893, 0.6911828657970643, 1.1819299738834246, 0.5928351223500539, -1.6884405584312985, 0.24107710611544522, -1.9284728786716232, 0.3251011456909293, 1.606658121285976, -2.0137160389920727, -0.2926845509456095, 0.8417700826014083, 1.2189320667437056, -2.476954182593157, 0.3185264951227412, -2.731685201765401, 2.531031321589165, 0.5109460370561539, -0.7306610115687768, 1.7245502487774045, 0.2908354223131754, 1.2934260197131662, -0.8475662108172072, 1.4587926533271176, -0.31621756550706104, -1.946208747414723, 1.4714321323996025, 1.1500775977467064, 1.7861198049597267, 1.2841395311884833, 1.932974049583727, -0.3424965054911853, 1.302791805272318, 0.745394920269909, 1.3764162103262731, 2.119640036500471, 1.1070479323599038, 3.259226865918682, 0.9160297359214158, 2.215741109103988, -0.09526510132168534, -2.7000124151472216, 2.593777913902017, -0.7962373061828276, 2.8675897270250688, 1.2647840756455737, 3.045448637431703, 1.3085762304132667, 0.7324102842872441, -1.499538071024511, 0.2856309978563495, 0.7240507269259939, -2.9214592520956724, 0.3249062984982514, 0.18035147476524735, 0.10474171435649131, 0.16331092994005156, -2.5695162404815077, 1.6973193501575092, -2.9647317733456204, 1.9108421206409438, -1.8312732707097243, 2.0157587793317324, 1.1434281189733833, -0.531559932456853, -0.5301974225898927, 0.027132468487047305, -0.4102704880993595, 0.021378244045299245, 0.8749468257869658, 1.3842270356269526, 2.7667482421761824, 1.9501898991871653, -2.4425802926892315, -0.27750559655068, -0.6774675684096967, -1.3408038154960618, -0.01485105676787297, 1.138147074980608, 2.059586550414838, 3.4428036947716394, -1.0356656001093703, 0.30960251561805546, 0.47751343514239114, 1.132558667134742, 0.9052188851459854, 1.8083791449988127, 0.9329252746641842, 2.7572605958549357, 0.7744164200682041, 0.43458262330708974, 0.8036889304934848, -0.676065068953701, 0.911132050485049, -0.022701192740629678, 3.331514895762677, 2.1176657766981064, 1.1896646118359295, 2.8467844208527606, 2.8533998057688534, 2.259288001140044, 2.0161158931153325, 2.5024260105419613, 2.4857966814948105, 3.2416260955970935, 1.8788504450253838, 2.935939961213891, 2.7582140900585954, 2.7184341398186, 1.9768207156417181, 2.037988030822085, 1.6498341773029275, 2.2211380332923043, 2.954164279643328, 3.0031353508186127, 3.119621712751158, 1.962900098665271, 2.3337473830000053, 1.1400067425919072, 3.0710425647376223, 2.1977414126117987, 2.981946828685058, 2.9501184937638203, 3.893415829760592, 2.202992205936394, 2.412015932158644, 2.4741708934511935, 3.223292593694419, 2.184861644742714, 0.4839634634228564, -1.348212324861996, 2.023153390135139, 0.42573765312184847, -0.29169046981931646, 2.010000680249976, 0.8636886420294992, 2.983184624432174, -1.9937978804778171, -0.6183137457429716, 0.17613932178585925, 0.3851219261639908, 0.5419036596652114, 0.7611321415687511, 1.047836434375776, 2.0280208383963503, -2.5820139306477063, -0.5477784206903881, 0.21055245570044057, 0.08250833283840614, 0.5464532342957023, 1.0276713523884466, 0.6335651950732692, 2.8834121130215276, -0.27201483845072055, 1.1758385831242728, 1.3771761870239798, -0.44440061716087814, 2.9361683705054227, 2.2799143508103237, 1.196905677960211, 2.314294139162857, 1.4282410404436505, 1.002798885488594, 1.946082435594374, 2.429757165921356, 1.7901411632382, 1.1589264547983165, 2.9796158526856633, 3.3051995557675737, -1.6335788827505222, 1.1381271218755225, 0.2827531502257065, 0.5934345001387489, 0.6996209294494233, 4.2586928918847, 2.7416157479827126, 3.870028019383429, -0.635673772929753, 0.2080133608984647, 1.8540498903906422, -1.2804189462591913, -0.008056562468623785, 2.371146156964007, 4.277876704537574, 3.2172024818991343, 1.242831832577823, 1.6286571701197352, 0.47798586787280317, 1.4613243094711206, 0.9871388485014102, -0.15145892530282312, 2.413716346562218, 3.265449175731378, -0.1892350119795909, 0.5154404820429334, -0.05348933807602396, -0.9066399585340021, -1.894040612682071, -1.9920755333101816, -2.3412007200685077, -0.8675852455461216, 0.12456098409569422, -0.446310609618607, -1.337024631535097, -0.04361142318808712, -1.623355284818376, -1.6354446047475943, -1.5858010699425866, -1.0058665039229504, -0.7254733347353387, -0.19271135775123774, -1.0071533663220817, 0.5350919352661124, -0.7868407129688695, -1.249965424384113, -1.4562650617510216, -1.9159916723781611, 0.5852787309439298, 2.911385214248355, 0.9796120422003994, 0.518388774870348, 0.0647821149265208, -0.7007509725747681, -1.4733093771169423, -1.4590719806936345, 1.9847364663454938, 2.892642783637469, 0.792027602443484, 1.8157646265596321, 0.4689736196178845, -0.9352733674950798, -1.8083861032741553, -2.2317191123756124, 1.2811683452674523, 0.9996640451756689, 2.2804070206861597, 2.195664261414047, -0.23595913508391095, -0.7827934591813114, -2.51863853916595, -2.649552101450558, 1.8846702214105346, 2.798539690083504, 1.4643919382689699, -0.7514019925692018, 1.0949462638260001, -1.8805969554677393, -1.285993498788215, -2.0132341172367028, -0.15002478670172534, -1.3058112139493976, -0.12090592154288773, 1.3710989701855036, 1.3550489540510615, -2.3599838026322617, -0.7114379945744673, -1.5848542389079479 ],
				[ 0.02776257989630118, 0.0037434271567101094, -0.015651695577407605, 0.008631852460016713, -0.001121162090577638, 0.02196918079209222, 0.024490470174481548, -0.004943253263099589, 5.264259593321364, 4.212046384880688, 0.6534610726786, 1.2934451319712101, 2.0349000337801995, 0.24217144837084015, 0.5780634856060717, -1.2472098545462642, 1.5779105451764976, 1.8940960378713332, 0.1961102834030091, 1.116745459482653, -1.744075091181614, 1.1559526951965853, 0.040811136347095836, 0.20157003086975828, 1.3540680058745962, 0.29355508940402697, -0.13645050147010396, -1.3755051837112224, -2.4819913993263985, 3.113206642819952, 0.8581840749225472, 0.08501189727353245, 0.7384101125753925, -0.4154660167444788, 0.5222443601867891, -2.8283669948529084, -0.30082202934749463, 0.7180345397154668, 0.9172702027533965, -0.013102267039942633, -0.04097329571111266, -0.7904663688223305, -4.363898273073547, -0.10680462051718002, 1.9940685867571752, 1.0375172245705755, 0.25598014710403694, 0.23552387344212605, 0.31211069860580665, -4.398036986963856, -1.4076896671472625, 0.39573379447159845, 1.086404874929644, -0.3660440400632003, 0.7199326719594626, 0.7188691259292913, -0.03212658618842385, 0.029377821757013752, -0.002546441441586526, -0.0107777413213087, 0.0018315598871104322, 0.0053365196845025905, 0.008997410502181044, -0.015649729156393156, -1.0282246593061262, 1.6952739267335, 2.135765615935406, 1.7974305105548443, -0.7180768081283404, 3.1041153735390754, 0.41254083365762384, 2.500232795984248, 2.4107059269589315, 0.3178842674890199, 0.9808024672175898, -0.14822134049514096, 2.641842704931408, 1.1944587245991614, 1.820070891661596, 0.6664245177854666, -1.2837585141185233, -2.771008083507125, 0.8850896033576269, 0.8135575556029757, 1.4775825739089568, 0.5960426779775502, -0.42881961156705106, -2.6028857381645136, -0.2633764047722859, 0.3511272018456278, -0.21170689770723822, 1.7057076086078138, 0.611967332207006, -1.0053405585558266, -1.888764021018945, 0.011928018567075866, 0.9609643532128952, -2.220668771667721, -0.02283534176957473, 0.776399226412736, 0.8878574237146303, -0.3448418900270284, -1.956955761423055, -2.45708364779185, 1.071288025800286, 1.234302076526614, -0.6256293537057966, -2.488153851631054, -0.6592470256764739, -0.3005610831914845, -0.2986167318418434, -1.0391160379296807, -3.6568841115782815, 0.23056202485598631, -1.948366425260386, 0.7014643108640699, -0.7916316983112083, -0.29458993118482646, 0.43428050632455867, 1.2987464730926892, -0.2546776141682123, -0.1627504136640929, 0.0041592700639851675, -0.39019688701388294, 1.4057265148856672, 3.1008034554201904, -1.616233815487901, -0.8591909763952628, 0.8808818963886285, 0.6464734015493651, 0.7514372481813858, -1.1479921226215206, -0.24310743253417327, 1.1507892725353295, 1.9179940759890792, -0.39379656992532436, -0.1542715829618778, 1.214740151181595, 0.0921810944550935, -2.0216488350807698, -0.8954706635289688, -4.996289543753882, -2.2775776209880743, -1.4768393310056187, 0.5935432497528527, -0.6054208926589517, 0.5319603537486824, -0.018970243304518207, 1.2759606283874758, -3.475858418511371, -3.5647022479341492, -1.8956291201552355, -0.5434320821792604, 2.920775334822959, 0.4238536352608418, 2.545212267704519, 0.43186922409069306, -0.8590758357786603, 0.4739718157305748, -0.9550035205661178, 1.3725350122483417, -0.24839728164184546, 1.0036861183099963, -0.783579596068969, 1.6611170229828414, 1.346469739330263, -1.2635499555606284, -1.095500655122672, 0.8063546045398158, 0.18035140956583318, -1.5372821445550047, -0.5623958334052678, 0.5887249798269513, 0.23836718119227615, 1.479471741370519, 1.5032211135257294, -1.611381220294645, 1.0718738049127505, -2.4005827523638645, -0.04177418025895419, 0.22812815622316857, 1.1047745944366592, 0.9710948122602181, 3.129368275864036, 3.9053022303124276, -2.837900108557734, -1.22021576775156, -1.6950251587173284, 0.45327205547362204, 0.9338257378758422, 1.5172713233199038, 2.135971590944692, 0.7993357400158635, 0.04941333220063017, 0.03725448201019737, 0.07616515795698585, 0.6745399126502355, -0.2090599641591093, 2.965620689666182, 1.802139130819405, -0.048942436858699034, 0.07120161819860783, -1.2080226139374215, 0.6298355460601299, 0.9291875159153316, -0.22016714376045843, -1.232227620139028, -0.39993061416837666, 1.003609202006177, 0.6842150587748319, 1.0644083110082005, 2.0059578052590203, 2.209194764180985, 0.30096218223262466, 2.592834145174668, -0.3133583112488076, -1.6066929206026415, 1.2279936301273038, -0.12597650642715694, 2.5395759137677105, 2.622941985230957, -1.1946121404365462, 3.5494675654393135, 1.019742280232951, 1.286261940182151, -0.3691869908170574, 0.3659743916221304, -0.859470357531189, 2.1306416409488, -1.3132611289399232, 0.9921689061155108, -1.4980240674562866, 2.1597057758408678, -0.5636534049912179, 0.3569205746853422, -1.34871352851459, 1.1296373596185445, 1.0015367603771252, 1.6167925903334595, -0.8777162330057675, 1.1658096858241622, 0.2996468687125121, 0.8416527675965169, 0.5455034033750626, -1.6622646833751906, 0.3334309286751796, 1.3968684963985474, 0.9044929085812857, 0.12931923390554906, 1.1330974407363363, 2.365609829380689, 1.0828561747704666, 0.8456056328404233, 2.0095037680909504, 1.1908707431359273, -0.6577046049426818, 0.33567461527885556, 0.2554720124718297, -0.13053911215109276, 2.5398880720287944, 1.4163569930636293, 2.3349914722417475, 2.0930984730779763, 5.092197082342064, 1.8502693786354931, 1.8081746646527708, 1.8824749525704252, 2.330715178933824, 2.166905811863156, -0.3760679178454151, 2.257357181538026, -1.6029354422301307, -0.3401509066688784, -0.1374559270572216, 0.7351953612262303, 2.5083659731347687, -0.0673550219620139, -1.6248360625189302, -1.2267273636392246, -3.7730858368634204, 1.3523043432006017, 2.517057706749204, -1.1314798653089344, -0.4562385510724508, -0.18418099751887979, 0.9397050434451567, 0.14162066958576452, 0.32992509592555946, 0.9789628717197756, 1.08404667454, 1.2036460118837384, 0.5664203969505003, -0.10736548506144948, 1.7131695221336687, -1.4053139261394845, -0.005412929738080126, 0.8126768703310091, 1.9763864734165884, 2.6620380824565184, -0.44599205971117595, 0.3610005491938433, 1.2760021266548653, 3.3653145695485636, -1.629344254268802, 2.257572851281811, 1.6771087244285123, 1.636502883244056, -0.04053838618566155, 0.5236002526984074, 0.3704552614112065, 1.7886341290176764, 1.2006217115976396, 2.8777292808602697, 2.1202064201747, 2.80131098083419, 0.9790066459056351, 1.85912401614943, 1.466285474770263, -0.6134893250130052, 2.674357635880972, -3.038891542375685, -0.28122856226261495, 1.8977844120088723, 0.5667797114828997, -2.2801201605439188, 0.6087555943198484, 0.9197007825545828, 4.337834363677268, 3.1263363617178084, 2.882252403997087, 0.13637192427426378, -2.9230605595012897, -2.9659103084671767, -0.11737120562205747, -0.7445708648220274, -3.0254874343281632, -1.8670484459616066, -0.42197736352923243, -4.531975637106414, -0.06999978067575754, -2.4735320752083036, -0.40070872152899684, -0.02559872578378349, 0.32776777496501935, -1.996619406585439, -2.4285136963228675, -0.8846380331074942, -0.18976353143558478, 0.057508447868806815, -1.3701460479122634, -1.7632888001855338, -0.8124401051647925, -1.6059107740132426, 0.05912436845779434, -1.3014877801388733, 1.1427933603650007, -1.9599873372687695, -1.2155766568284703, -1.4748527485824834, -0.9818573768834689, -1.477784962476115, -2.406020158888208, -1.173861456893737, -1.6185368785610141, -0.09218127310098438, -0.6327044645955506, -0.34164089613563003, 0.05942155799818261, -2.3129264821760684, -3.186838855075921, -3.643473790399713, -3.3238786361906087, -2.6774646486275557, -2.4196706318135495, -1.4365370830388262, 0.9613620420694945, -5.984049873876351, -5.535660594636726, -1.7903763889592466, -5.246049684266033, -0.7148720561930743, -3.508678351113278, -0.48932935957694723, 1.137112689198159, -0.008446269265001968, 0.0017315654550690432, -0.02293356873227891, 0.02981277571645598, -0.02994059618587889, -0.02159209954748036, -0.01796210887164526, 0.028060883728840844, -1.6545414036543769, 0.479567989257169, 1.4681500186148049, 1.0828153042537978, 0.9843428476811871, -1.5699464990073202, 0.760688968401914, 1.0427955463856167, -0.8519263510568956, 0.5783202128291711, 2.9332815444251863, 2.213053862819534, 0.43448021788444213, -1.3713038075261832, 1.3151711097284853, 1.265505701453588, -1.0750634486351043, -0.30943088393348206, 1.3834090945938509, 0.5527857734951719, 0.49392810644133917, 0.7286114785929845, -2.134554926980291, 0.2883561825686418, -0.3482861884068024, -1.2747407814808986, -1.9600844222099771, -0.18167489110592627, 2.4998015296387317, -1.1908776320118115, -0.7695788558125469, -1.355503872966765, 0.5297314828500839, -1.53821043530685, -0.15747498706817642, 1.68402046168481, 0.8709416872314294, -8.204557244012252, -2.277813186749347, 0.5439238357028999, -6.852995029187152, -3.806836355165322, -4.1863060041596265, -0.7222633591854681, -3.0770025100717966, -2.407502965515366, 0.6867965936760208, -1.5471773567468148, -0.027789310519635808, 0.0352895880614342, -0.019174833424396243, 0.026273424981450917, -0.0335301174701677, 0.02272128360635676, 0.015081361153759208, -0.007441933642496764, 0.412779571255086, 0.03398564381012302, 0.5964192200754127, -1.1259891446636883, 0.5399759035087558, -1.9293352722849186, -0.9556552760800584, -4.541378391651349, 1.220691049619197, 0.6936122057816789, 1.3555237788389656, -0.33465507184109905, 0.7328542212513974, -1.6980983908842608, -1.3952946958127812, -1.2849962409138818, -0.6272925058986005, 1.0986579546932635, 1.2745067544908475, 2.741509009948097, 0.5710922647957012, 0.2543400863255361, 1.206413914460332, -0.683990641336695, -0.3819473426826748, 0.15109054853147733, -0.7684306760325933, 0.9669016169543797, -1.0567828105951649, 1.4745841454606723, 1.5697611103728204, 0.3439221147005734, 0.9063190399423635, -2.0150472999001394, -0.1544115491961059, 0.2486484337671727, 0.7686287385067667, 0.505430128540855, 0.8032005597021934, -0.6916097570262463, 2.4558382115362716, 3.368985357208114, -0.8788026129483136, 0.5120174870605899, 2.4813701479006887, -1.1376071347034244, 2.3352643337209185, 1.7162980535680425, -1.6980156013119436, -3.0286144624365052, 0.9417518217574066, -0.6800343160613175, -2.271383604823011, -0.9175914834260817, -1.6834104374558905, -3.4568904401301372, 0.3662973316475474, 2.100431301029362, 3.861333851932278, -2.7125621377570583, -0.3958728731354957, -0.8996831610692532, 1.6072687844976477, -0.30707240187039353, -4.059828473404063, -0.9044452265551318, 0.03278236917876803, -0.19879464519881515, 1.4895333230561854, -2.421635368254154, -0.7153351210486244, -4.336194273774463, -3.587402149865021, -0.005459111549803189, 0.5799290042066544, -1.0718761114261661, 0.22013793466769419, 0.10535977948330039, -1.5185639555015868, -1.7119122587917974, -0.74914475716172, 0.8616540233171767, -1.0474696981797287, -0.28768517011069067, -0.16765772601214524, 0.36947866685711395, -0.21388693687368648, -2.1353760829514368, 0.0979187945311125, -2.3891395467057674, -3.9981310371141854, 0.9716128251748176, 1.2045212724232208, -0.5284651792000497, -1.2073382325544801, 1.5511495866881626, -3.5676684580505333, -1.7131756571666337, 0.7515468722644026, -1.5725359646146153, -0.8699598202756333, -2.829232809454067, 0.25636985649757776, 2.6424544285943483, -0.6456096042210505, -0.5050039681811941, -1.818194945974867, -1.3165734041675954, -0.04938059917724901, -0.5464389751326717, -0.6067912294133508, 1.1534021828238417, -2.417845148308945, 0.43274201672033497, -2.4695944157329595, 1.0587542170984232, 1.1282159301429027, -1.989891771221126, -0.5596773588154744, -0.37183326092110824, 0.29474075634276664, -1.6968691243911687, -0.18456952733451987, -1.810538408798575, -0.04217229442969866, -2.6263523968542852, -0.5647375913709834, -3.972549253260055, 0.4235913398680377, 0.4031336899280331, -0.9604184359053057, 0.38289918266979794, 0.3047283001728179, -0.3979712673823016, -0.6024800876529512, 1.4213397494080022, -0.5697398784931887, 2.606697654500059, 0.3211788001053623, 1.5270351570781948, -0.10791777183384568, 0.45493543835566813, -1.2225000413318132, 1.2085809202769777, 0.6213508408526032, 0.24861140867347958, 0.2960123168530131, 1.1357496331961854, 0.24958616654953614, 0.28984486108684293, -1.292585882018215, 0.5950267718149593, 0.04768406957975829, 1.6404354142571242, -0.29387692917999647, -0.408503985318396, 1.0678101580458403, 0.901263370925242, 1.6421378599814147, -0.746293666915755, 1.1023224494983177, 2.048152395819469, -2.594547310909658, -1.0860460422464793, -1.1899485946634794, -2.1653108423942955, 0.2891971310989618, 1.6607575645686072, 0.22745057274427571, -0.18485304196225705, 0.3032850284957981, 0.049640500869515575, -0.12203898493027107, 0.5026752804209326, 0.34257975116179573, 1.2868231923411075, 2.1262364294761964, 0.05259346962627556, 0.07490405378929203, 0.4243304211534946, -1.147488303749951, 0.30151528278878287, -0.5592134887024659, -1.7972561049690168, 0.1106845691018787, 1.1667967465416844, 0.9212474721838608, 2.199514118140843, -1.7692662368923249, 1.0493214749259379, -0.9131373692125122, -2.3436204922333603, 1.3136591085503897, 0.8840668318329791, 0.5252320355744033, -0.09879153053600141, -1.067339085264695, 0.10167851187694334, -2.0133956968976623, -2.8545874704449905, -1.2543566684234257, 0.4364534414800744, 0.5466668832339651, -0.019757542985949332, -0.05829913438970022, -0.006340779662893567, -3.5820318509421845, -1.4405069779955748, 1.7925416649167152, 1.1279167167423338, 1.0822365992501446, 0.9451234348883355, 0.1445997769277228, 0.1381657440378072, 0.11629025146068585, -0.7047599424713408, 0.24332968120697904, 0.029456397320143296, 0.7669619666103608, 1.3861448366256537, 1.585246585827021, 2.3587928076027285, 0.9130429414006879, 3.2833751523171526, 0.22285902388270296, 1.1957247019837407, 2.697691841493265, 0.71728414449634, -0.8170529967185727, -0.6173268047379535, -2.058482446264284, 0.5854505123920994, 2.5357472137324812, 1.5776774699228633, -0.019862599479294134, 2.1610871712827895, 1.4233295351595803, -0.022827204426033323, -3.78875954311579, 3.089787343988626, 0.4431996399963965, -0.21679495850247862, 1.5836849462590519, -0.11339464442738403, 1.8162649461738631, -0.5163428592580468, 1.179394623774617, -1.2264105690531175, -0.08156778117309593, 1.859149044398106, 0.8253674292105625, 1.5389605041247192, -1.3713702119965387, -2.8986673578967665, -2.235668316168791, -1.78829965082588, 1.12637490484485, 1.384761132860467, 0.7198346628757968, -0.42671388142780164, -1.947962074579265, -1.061050267095673, 0.2787212017826782, 0.009182290861008727, -0.6790783590970405, 0.9608347481027868, -3.1295162735436057, -1.3811689847844506, -3.144814381359144, -0.48164846136421335, 0.21742757419156664, -1.049920379357205, -2.7806661715837975, -1.0047953630950424, -1.873491154895753, -4.835313558874305, -9.19664124665972, -1.8903991906417186, -0.12699944147737188, -2.225107735472976, -0.02349180247963548, -5.993312400877021, -4.719561039362005, -4.0177789309334395, -5.230790084857274, -0.41509497932484773, -4.088212660740768, -1.0874561149827229, -3.011325084961979, -3.892021270106463, -3.7828272052383083, -4.893261979456603, -3.560242421060788, -2.3066788215470924, -3.5515189075091445, -4.106855150657598, -4.719266988386983, -0.9122309531272572, -2.0162689956345314, 0.3709906383749499, -4.090446751980615, -5.2082970608204135, -4.6660701996869784, 0.03221651821137105, 2.448724962619308, -1.7856064949792347, -1.263134621929454, -2.8594104750107494, -2.5909354280672012, -0.817719140718669, -1.78984400299581, -1.1445335509680377, 1.9286999846923152, -2.463862838621392, 1.4256730119106789, 2.0202789556031253, -2.3576431347209827, 1.4947541193360345, -1.848167458430832, -0.823159164534365 ],
				[ 0.023972380733252075, 0.020574548664954093, 0.020120312700544044, -0.011655510469325158, -0.018322463388401405, 0.004039477720070772, 0.025522685432957198, 0.02758862489120093, -3.926400532390655, -3.5613984860535837, -4.2952091575645355, 0.5349472730664595, -1.0103248053855418, -1.4057650893956308, 4.799339791673121, 0.9984809965780994, -1.621939700748522, 0.7446603624729526, 1.6327284831663256, -0.7701814050639998, 2.0069381992030815, -3.1691507233845146, -0.05177619459106785, 0.24614909778755106, 0.05740169478957494, -0.4379508072078391, 0.39449804814681316, 1.493003278905285, 0.7885074385384346, -1.510735875697403, -0.4779752837776452, -1.5348677380373765, -0.9288343062702469, -0.1125146957341312, -0.6143451434301944, 2.673814777705515, 0.46568476005450005, 0.9375891520301471, -2.2375310280828633, 0.3457223364984631, -0.30247226294335894, -0.2962098123603068, 0.19198543293091094, 0.8109935627769457, 1.0735266711349318, -0.26682191632127666, 1.8202764328603787, 0.8166609317803416, -0.6252282264655327, -0.1196421392197194, -0.06013430122557864, -3.138162174241289, 0.9537981021907476, -2.9530275308411533, -0.3820305631744942, 0.19313756538114565, 0.005296198302682383, -0.03225236489416967, 0.011035456266063177, -0.00883389909802804, -0.02757086823546933, 0.0029432328653668637, -0.01576139143674158, -0.004525239818452365, -4.8920116737846975, -1.8056097547757082, -3.237352434747258, -1.0822384858601979, -1.5632728919417394, -1.0701228578844002, -0.7460722455675145, 0.5739639684368517, -4.025194183649843, -3.139098658629302, 2.7345333402598078, -2.5920961430655742, -1.12935639324967, 0.1272790001881445, -2.2592465226581444, -4.822361468814911, -0.33060180028541747, 2.519897391470897, -0.2208901517940511, 0.27056925195823467, 0.5247778191552076, -1.6593790418795575, 1.3526463534083895, -0.6978779336332392, 0.723367507068912, -2.7515364330556737, -0.47482597391612774, -1.1660383658020805, -0.862375333203495, -0.2667411318830155, -1.0102448022389878, -0.16545208269701295, 0.31898617332219964, -2.428264186252714, -1.0959549423312263, -2.118369603911092, -0.5183513179366307, 1.0347492975125527, -0.37020969333343756, 0.6627316070351054, 0.2459831781230002, -0.2924087710864731, 1.4197982569852745, -1.6909744530687203, 0.48442158953818426, -1.7089675328106715, -0.29911872089911085, 1.1253631141749203, 0.17068785660107802, -0.964119705070936, -2.049770989114428, -0.3176391000195825, 0.837974543508324, 0.1713189015087671, -0.7122606332584686, -1.8254363302352943, 1.1883580853937588, -0.3255654137736506, -0.15969274237021217, 1.5179605939221485, -0.5705878697406278, -0.21828820930823487, -0.48427041423560785, 1.5858749577922453, -1.164257133377933, -0.403873310856565, -1.3924719863337056, 1.433228476762662, -0.061490959354313444, 1.9221091802962045, -1.3534923523876288, -2.621254486237816, -1.0606610985958296, -0.7668700630598915, -0.5483794769761052, -3.792296923661596, 0.505684767658157, -3.456868343905026, -0.2656086790576943, -1.624647269778928, 0.3654175644332816, 0.540855515049475, 0.08108079702325441, 0.2349003610377553, -2.325894179198232, -1.3249492443401876, -1.1826014549522716, 1.3925684835949588, 1.363698884774426, -1.2145460873197045, 1.39986173216654, -0.838708546792518, -1.6592975644555539, 0.7769594097923826, 1.7435648785043558, 0.980973311773867, -2.0434236804063195, 2.292973325518702, -2.4634317263899064, 1.093564534181946, -1.0470467790368647, -0.07262786621181395, -2.127143712212692, -0.7605354113225432, 0.579398467288181, -1.3467719073932913, 1.8096868414661627, -2.622468627157021, 1.2630864567468247, -2.102391188255686, 0.05529092060389548, -0.6129049052256607, -2.1022690333269414, 1.3676488253875008, -0.41701865894166895, 0.5014941563324445, -0.8215668340105217, -0.5826146177839656, 0.7376560401313057, 0.4908562431310949, -0.5587181249906492, -4.149443864916068, 0.3578356840497568, -2.054014025765564, 1.0493984570486128, 0.10047952543156587, -0.5533708230494119, -1.3299833554654463, 0.3464723213169019, -0.14798782726786058, 1.5142814286198385, 0.3956579717233713, 0.7109570545658925, 0.1794420882050451, -0.6793621422671837, 0.7078037719088873, -0.22024715238561554, -0.4830754949803244, -0.0912430579657947, -0.48159918969208415, -0.29505162131309765, 0.9626552030709283, -0.683619687171292, -0.7452545482118711, 0.19831710450382495, -0.5562937249755452, 0.22289089594611058, 0.20885682505801506, 0.44170153326676503, -1.9284121277201276, 1.0988629354505641, 0.798740616553028, -0.13694092915060468, -1.6210824356757116, -0.24823804777296318, -0.9317004827247125, -1.6580031876910488, -0.5711578213553644, -0.23321850654961054, 0.6207801023700641, 1.408375212879867, 1.9037333202615356, -0.6509563615439893, -2.94459024137836, 0.22332270875890553, 0.5980640398479226, 1.2613426938101684, 1.3923831624117102, 0.9425534465226398, 0.787683468316188, -0.632423365131382, 0.4447979258182022, -0.5538928911343566, 0.54452595260412, 0.31923684241819394, 0.6390762951657577, 0.6396431471302008, 1.549174565488353, -0.88277279132507, -0.10131368843735923, -0.7796948692715058, -0.648074357796605, -1.6447898666887955, -0.19871933336276665, 0.27285927434139307, 0.6519237279190181, 0.2010116730376019, 0.0358317180962116, 0.6021985631636229, 0.5541686202958861, -1.2100385864324126, 1.553358805352135, 1.9225567907744325, 2.6121145026460777, 0.5736509862883044, 1.6714020363141575, -1.0907575588320197, -0.7139634733138559, -2.773100112599342, -1.835042776317079, 1.3553560129981073, -0.4965446581700754, -0.46751459817801205, 0.3153163266231884, 0.5455159103474645, 1.796400239771867, -0.8075435398819587, -1.0480254555278268, 1.800024699233329, 1.7880488087402362, 2.5817351146046383, 1.4925224275499709, 1.042426118649614, -1.6222732982577022, 0.8228014835373749, 0.021302279646753578, 1.3126705600419086, 0.36496614098612845, 0.29713112809975284, -0.5425978934285547, -0.5484086821932436, 1.960141694218731, 1.1434247388715986, 0.3454414468270056, 0.6954942755603205, 1.13528030209985, 0.23781080740085353, -0.4708540769964088, 0.35225367855253864, 1.8907397564190271, 0.09017570796158603, 0.9253399692655845, 0.8223646144774315, 1.6585481213798567, 1.1160617213346893, 0.21625944230299313, -0.1573177777946776, -0.4239434531842432, -0.529806887283859, 0.8637071288582475, 1.5875423859490052, 1.2681660879111338, 0.8741835279547835, 0.5666780266322331, 0.8375304728600244, 1.3591243214219575, -1.1264131866941989, -1.824058217382098, 0.8788169567070444, -0.5745276084582772, 1.7865685924261427, -0.9142039036132406, 0.6115295586416521, 1.0995219409601045, 0.8472383419479045, 1.5324548069111754, -0.9809506401814401, 2.819058460544383, 1.9006941274616707, 0.020304593512552933, -2.5578083624809564, -2.2792290716689165, -1.1402037615965535, -0.1191285134272456, 1.6149081028709265, 2.8193518595947413, 0.16473940328810463, -4.040315011121575, -3.3849870168018437, 0.7436305161942607, -2.971258923966705, -2.946369874691111, -2.7793170701762016, -0.9176120819077905, -1.5098552896946145, -3.4096363773226597, -4.655415883131663, -3.891210844467406, -4.325686455645441, -0.16407958730719144, -2.46498923971922, -3.3504722800154885, -2.669056239593178, -1.3163675976954816, -3.522309349857174, -5.3439076142215765, -4.4721864429012665, -0.9939175573459028, 0.02338949813371287, -4.910334807420252, -3.6024432556200003, -3.946234283975893, -5.459149495714019, -3.393177099908544, -3.380398071004612, -1.6638665166970341, -2.583384345343999, -3.350681095392857, -1.895514044995404, -4.62200770260021, -2.8083108724335224, -3.4864694251872805, -1.3576053053747774, -1.252457220218353, -1.7882815303847182, -0.013070259700823535, -2.386289300123914, -1.8457865658013672, -0.9268800516252487, -0.8478571227637015, -0.3255550162984975, 0.5734739060226247, 1.2034315184056419, 1.7911250443219255, 2.9330430994812877, -0.4645054628161131, 0.7806208941973568, 0.03808298935647392, -0.001502193168555854, -1.6540055702874983, -0.016683792264834824, -0.015405395040879117, -0.005631000791503801, -0.024881804968276352, 0.03355257461470727, -0.03544515161715683, 0.03367318934992298, 0.03159143603245599, -1.642131105968419, -1.8449579655199468, -1.810459809487406, 0.6388756281749368, -4.085320226556298, -0.2599939493178635, 1.0553789542176852, -0.7373079572672308, 0.3734088124580809, -1.7615045508910026, 0.26659891047360995, -1.1702807491755145, -0.19878099720926232, -0.2685957798701906, 0.3345637940587474, -0.23909523713920713, 0.29995650648915123, 0.5088779488338957, -1.104815229643041, 1.547940670751318, -0.807595434912699, 0.5607912490996239, 1.456391257011102, -0.05219106932836925, 0.5479685417691856, 0.5056147711748752, 1.3850010508572885, -0.8657963468066707, 2.4873991248174376, 1.771383213334888, -0.2006124222560754, 1.3699402172290622, 0.21788215233447536, 1.4427716847746377, 1.7337229419791247, 1.7204953608191909, 2.3327424333969877, 4.372069227680996, 2.6787345455711424, 2.5932422933476134, 3.4062064693914507, 3.6319760169427795, 1.3748586657888893, 2.760207527899196, 2.6587791389950146, 4.131007291229515, -0.19152599906129636, 4.202726285431417, -0.0001349756043956511, -0.009659240057360373, -0.0050606579169936074, -0.02085398255522676, 0.03514630912960203, 0.01857943742005002, -0.030167289618289825, -0.001869868882233805, -0.3655050989024355, -0.6414505709459093, -0.3863294091994664, -1.6721490943733863, 0.028738910077888428, 0.7230482325871455, 0.29432187077909533, -1.2793683230298674, -3.634319089871501, -1.0199982163485688, 0.5851039079572106, -0.6181942462920557, 0.5486886648628543, -2.1939966261760615, 2.1764038450027448, 0.46554504533110114, -0.4332215696768435, 0.31707388029261213, -1.6163064033188155, 1.1336653012414781, -0.3263893790668971, 0.34712212055585745, -2.0094035725846155, 1.8679531311225457, -0.7206978316095127, 0.8598514752249495, -0.8199240292200396, 1.4561021111879306, 0.22338047042800246, 1.1336014842820932, -1.5422957274596838, 1.9966042260311239, 1.151761366063061, 0.8433251835146789, 1.0388121311077059, 0.8978447613650982, 0.7335464093463502, 2.715673433011794, 1.3491423445365243, -1.2909175001047004, -2.219573143195015, -0.785368611322986, 0.5528766783823751, 2.4823279972759487, 0.7123991369475936, 2.411898729349495, 3.7769803944265465, 0.8140339213832384, 2.412169627674404, 1.5726986735869728, -1.3914942160785109, 2.074409482581635, 1.222610290905431, 1.7469684908281182, 0.9694569209793592, 1.2731972588199494, -2.458255147692868, 0.9990708951801711, -0.44334172165273483, 0.8743357820006086, 1.5714513791277864, 2.8869345087442917, 1.8119251873909497, 1.039170666284877, -1.083590901228392, 0.4635283180080826, -2.6868237562281374, -0.1984800495572748, -1.7143644558813587, 3.6081271752992947, 2.2086067738606614, 2.8343543706509418, 1.5247245367371585, -4.382778180806692, 0.8416832712861203, -2.3961908484957686, 2.32988277430337, -0.008713347023307116, 2.789477562541064, 2.3597163479376966, 1.0689528249847013, -0.5437672141294497, -3.243041158849777, 1.6726244882083199, -1.9589260090400893, 2.3944994814948455, 0.9475536644564209, 1.7494980623071523, 3.3767121505462567, -0.8002604255789548, 1.105644061152782, 0.3838889902611591, 1.839809844629569, -1.9239823287589655, 0.9949709823658504, -3.7115899599139133, -1.3305510439441786, 3.0808533028658367, 0.04791449599146908, 0.07338126155609251, 1.083244928157585, 3.339485963295921, -0.5683970965675057, 1.97455327378003, 0.10771103587357203, 0.02209350211836472, 2.085243205653189, -0.07659848845223478, 1.0994669971832303, 0.5745906935662388, -1.7601469044384248, -0.18588328574220467, -0.347797388346749, -0.3286032892600718, 1.1241302823939696, 0.6914737930342845, -2.861867337785204, 0.5430275307115506, -0.9347456629769515, 0.8370941240645339, -0.19249057451262813, -0.8378796466153988, 1.1434795704759169, -2.256927913163571, 1.8317397683289753, -0.5611641888708294, -1.3380665824603597, 0.0743104733375595, 0.45450321304307506, 1.6656383577377072, 1.519238221402672, 0.9365802699158142, 1.4229708803220515, 0.8964223410033964, 0.784375544504539, 0.09565752349653596, 0.6639716828899116, 1.374477019256936, -0.4203345910571792, -0.3949652346637071, 1.3727770180714356, -0.596324358873532, 2.5009978592183457, -0.799298641693269, 1.6967948734051272, 0.2654484523359194, -1.1456927067110703, -2.557771960284445, 2.236692201969251, -0.6730425026153616, 1.492258728354689, -1.5049153918397113, 1.7145180800352688, -0.3417628751333913, 0.3716260510576501, -1.025175701053503, 0.0909773352779929, -0.9296206082446039, 1.2976625573852427, -0.6575348437100342, 1.818599375580229, 0.5427291659344261, -0.8261398445021816, 1.5302632353201588, 1.9805860232802421, 2.2018658533381545, 1.0676068732281006, -0.9824726522578984, 0.2609783848042388, 1.32466578399269, 0.8698164445330209, 1.8812083978865104, 2.2691818436753235, 0.003666554267827247, 0.8802417259949084, 2.2478965264040447, 1.2247569237398992, 0.24422730192416267, 0.5645076381954834, -0.8788990631187082, 0.3867820989728468, -0.38574233412779296, 3.856887514666187, 1.7707274979965368, -0.395853213967972, 1.9655212749039783, 0.6046707601675744, 1.4808808285705342, 1.3030978148688481, 0.13621522193611935, 1.5622611691279753, 1.2144106758753859, 2.2672158976501735, 1.4392915951857048, -0.07702734145089503, 0.7111600257047335, 1.1665687935328384, 2.663565254481866, 3.112178628515328, -2.399709512299903, 2.6065355940366346, 1.048225420597972, 0.4829487732846539, -0.04281924516181287, 0.7635169743251385, 2.351412705596838, -1.7946925408370766, 0.28488378954874843, 1.9102608890429875, 2.520448337256872, -0.2698794155227674, 1.2639856733277242, 1.1575517518561669, -0.1744879305490698, -0.06438006014741442, -0.5050583531324362, 1.2804292794637582, 1.2709089843928878, 1.3360504852776265, 0.8261098028907142, 1.4896995623523408, 2.181341485483105, 0.1387775252548846, 0.7682879627131975, 1.5939682189197177, 1.8851128615264172, 1.8259219991089572, 0.2693794240337223, 2.5082709961869, 2.038583684062768, 1.2662073855296399, -0.8154534493813724, 1.3666941682750637, 1.6472795667556952, 0.9882500737343681, 1.5957051907317654, 0.10425871387613345, 2.4442373349958717, 1.7550370606188743, 1.6529903760590816, 2.855304165616889, 1.4975631288799212, 1.947359948012491, 0.748463604104203, 2.824699199798517, 0.7470790447325373, 3.277321283234937, 3.377796230627214, 1.2426877746482308, 0.7229169743012894, 2.6565571761151396, 0.5061499309994665, 1.0012892182950353, 1.486787047343664, 1.5212107241783608, 4.471270178937335, -1.1276626218928432, -3.5932396315739323, -7.199251029396002, -4.679253569300066, -2.7142032314625473, -4.383092688953, 0.7995084309335776, 0.29181280551040234, -4.790788996861432, -6.586947454571918, -2.3161571312937608, -1.1299152677295785, -2.1071136940469213, -2.1495588028515167, -0.05530139631508463, 1.2610259229032172, -0.1330179397219774, -4.249884490238484, -2.6130061048593447, -0.7043067672340267, -1.2719527420762096, -1.0283640932229408, -0.008673594404526001, -0.6770753857685693, -0.9971512254279191, 1.280548342908179, -3.486329815199898, 0.4045599989523853, -0.7475300811556305, -1.2001809845040172, -2.5628529745297994, -2.334141287577733, -0.624268913149627, -3.320008987689885, -2.346898247633728, -2.219155686333124, 0.15353866970840155, -2.029263406006868, -1.3250545306076544, 0.4054637594900222, -3.774025131237767, -0.6909111227422909, -2.33903625910426, 0.2631544932334418, -3.7366578566584536, -2.3052968869419943, 0.6377713018049909, -0.9053509818839771, 1.1393211930710214, -0.6280698838542017, 0.7455227134496276, -2.172935316265477, -1.7680069832042655, -3.7513672731157888, 0.41287235592799043, 1.2548909286459575, -4.206860394062654, -0.28721123956746963, 0.0075794269274245835, -0.8035506980063002, 0.4770441020468161, -1.034893574568837, -0.2779342238587635, -1.3659310983297535 ]
			],
			[
				[ 3.6552616486592564, 4.547857797168061, 3.7008781575132272, 7.8577863750857935, -4.361954968738195, 3.8243047950947697, 4.620297395723503, -2.2332129762891513, -5.394235063196106, -4.567092784086081, -4.570427699452659, 6.691521663841131, -2.88265505238123, -5.412312538839529, 3.3272855793128344, -4.14454668234642 ]
			]
		],
		biases: [
			[ -1.1643669216699315, -3.598798227601016, -0.8677058648476441, -3.4859378852127345, -1.7752552391547558, -2.809514138653701, 0.5753125055323552, -2.6765231852565954, -2.450779446578558, -3.0425366132949203, 0.3651799232826036, -3.8255830844195886, -1.0348936359738492, -3.5290599447063102, -2.7109062169142706, -2.5104325231256355 ],
			[ 0.8749025410399253 ]
		],
		activations: [ 'relu', 'chess' ]
	};
