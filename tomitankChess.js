/*
 tomitankChess 7.0 Copyright (C) 2017-2026 Tamas Kuzmics - tomitank
 Mail: tanky.hu@gmail.com
 Date: 2026.06.28.

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
var VERSION         = '7.0';
var Nodes           = 0; // Csomopont
var HashUsed        = 0; // Hash szam
var BoardPly        = 0; // Reteg szam
var MaxDepth        = 64; // Max melyseg
var TimeStop        = 0; // Ido vagas be
var HashDate        = 0; // Hash ido 0-15
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
var RootMovesResult = {}; // Elemzeshez MultiPv helyett
var brd_pieceCount  = new Int32Array(15); // Babuk bKing+1
var brd_pieceIndex  = new Int32Array(64); // Babu azonositok
var brd_pieceList   = new Int32Array(240); // Babuk helyzete
var brd_moveListEnd = new Int32Array(MaxDepth); // Lepes / ply vege
var brd_moveList    = new Int32Array(MaxDepth * 256); // Lepes lista
var brd_moveScores  = new Int32Array(MaxDepth * 256); // Lepes ertek
var PlayedMoves     = new Int32Array(MaxDepth * 256); // History-hoz
var PvLineMoves     = new Int32Array(MaxDepth * MaxDepth + 1); // Pv
var SearchKillers   = new Int32Array(MaxDepth * 2); // Gyilkos lepes
var HistoryTable    = new Int32Array(15 * 64); // Elozmeny [pce][sq]
var PieceKeysHigh   = new Int32Array(15 * 64); // Babu hashKey felso
var PieceKeysLow    = new Int32Array(15 * 64); // Babu hashKey also
var CastleKeysHigh  = new Int32Array(16); // Sancolas hashKey felso
var CastleKeysLow   = new Int32Array(16); // Sancolas hashKey also
var DISTANCE        = new Int32Array(64 * 64); // SQ Kulonbseg
var MOVE_HISTORY    = new Array(); // Lepeselozmeny

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
var FLAG_LOWER      = 2; // Hash zaszlo 2
var FLAG_UPPER      = 1; // Hash zaszlo 1
var FLAG_NONE       = 0; // Hash zaszlo 0
var NOMOVE          = 0; // Nincs lepes 0
var DEPTH_ZERO      = 0; // Nulla melyseg
var NOT_IN_CHECK    = 0; // Nincs Sakkban
var EN_PASSANT      = 0; // En passant mezo
var CLUSTER_SIZE    = 4; // Max azonos pozicio
var INFINITE        = 30000; // Infinity / Vegtelen
var CAPTURE_MASK    = 0x1000; // Leutes jelzo maszk
var DANGER_MASK     = 0x3F000; // Fontos lepes maszk
var CASTLED_MASK    = 0x20000; // Sancolas jelzo maszk
var TACTICAL_MASK   = 0x1F000; // Utes, Bevaltas maszk
var ISMATE          = INFINITE - MaxDepth * 2; // Matt
var EVAL_ENTRIES    = (1  << 16)  /  1; // Ertekeles hash ~512 KB (8 byte / entry)
var EVAL_HASH_MASK  = EVAL_ENTRIES - 1; // Ertekeles hash maszk, csak ketto hatvanya
var PAWN_ENTRIES    = (1  << 12)  /  1; // Gyalog hash meret ~104 KB (26 bye / entry)
var PAWN_HASH_MASK  = PAWN_ENTRIES - 1; // Gyalog hash maszk, csak ketto hatvanya lehet
var HASH_ENTRIES    = (16 << 20) /  16; // Hashtabla merete ~16 MB (12 -> ~16 byte / entry)
var HASH_MASK       = (HASH_ENTRIES - 1) & -CLUSTER_SIZE; // Hashtabla maszk, csak 2 hatvanya
var CASTLEBIT       = { WQ : 1, WK : 2, BQ : 4, BK : 8, W : 3, B : 12 }; // Sancolas ellenorzes
var SeeValue        = new Int16Array([ 0, 100, 325, 325, 500, 975, 20000, 0, 0, 100, 325, 325, 500, 975, 20000 ]);
var KnightMoves     = [ 14, -14, 18, -18, 31, -31, 33, -33 ]; // Huszar lepesek
var KingMoves       = [ 1, -1, 15, -15, 16, -16, 17, -17 ]; // Kiraly lepesek
var BishopMoves     = [ 15, -15, 17, -17 ]; // Futo lepesek
var RookMoves       = [ 1, -1, 16, -16 ]; // Bastya lepesek
var Letters         = [ 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h' ]; // Betuzes
var START_FEN       = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1';
var nonSlider       = [ 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1 ]; // nonSlider (P, N, K)
var PieceDir        = [ 0, 0, KnightMoves, BishopMoves, RookMoves, KingMoves, KingMoves ]; // Lepesek tomb
var RANKS           = { RANK_1 : 0, RANK_2 : 1, RANK_3 : 2, RANK_4 : 3, RANK_5 : 4, RANK_6 : 5, RANK_7 : 6, RANK_8 : 7 }; // Sorok
var FILES           = { FILE_A : 0, FILE_B : 1, FILE_C : 2, FILE_D : 3, FILE_E : 4, FILE_F : 5, FILE_G : 6, FILE_H : 7 }; // Oszlopok

// Hash table (12 -> ~16 byte / entry)
var HashTablePkg1   = new Int32Array(HASH_ENTRIES); // (flags(2 bit) << 30) | (date(4 bit) << 26) | (depth(8 bit) << 18) | move(18 bit)
var HashTablePkg2   = new Int32Array(HASH_ENTRIES); // (eval(16 bit) << 16) | (score(16 bit) & 0xFFFF) // 0xFFFF -> signed safe!
var HashTableLock   = new Int32Array(HASH_ENTRIES);

// Eval hash table (8 byte / entry)
var EvalHashLock    = new Int32Array(EVAL_ENTRIES);
var EvalHashEval    = new Int32Array(EVAL_ENTRIES);

// Pawn hash table (26 byte / entry)
var PawnHashEval    = new Int32Array(PAWN_ENTRIES);
var PawnHashLock    = new Int32Array(PAWN_ENTRIES);
var PawnHashPassW   = new Int8Array (PAWN_ENTRIES * 9);
var PawnHashPassB   = new Int8Array (PAWN_ENTRIES * 9);

// BitBoard
var LOW             = 0; // Also 32 bit tomb index
var HIGH            = 1; // Felso 32 bit tomb index
var MagicBShifts    = 32 -  9; // Plain: max index 511
var MagicRShifts    = 32 - 12; // Plain: max index 4095
var RankBBMask      = new Int32Array(8); // Sor maszk
var FileBBMask      = new Int32Array(8); // Oszlop maszk
var NFileBBMask     = new Int32Array(8); // ~Oszlop maszk
var SetMask         = new Int32Array(64); // Mentes maszk
var ClearMask       = new Int32Array(64); // Torles maszk
var IsolatedMask    = new Int32Array(64); // Isolated maszk Kozos
var NeighbourMask   = new Int32Array(64); // Neighbour maszk Kozos
var WhitePassedMask = new Int32Array(64 * 2); // Passed maszk Feher
var BlackPassedMask = new Int32Array(64 * 2); // Passed maszk Fekete
var WOpenFileMask   = new Int32Array(64 * 2); // OpenFile maszk Feher
var BOpenFileMask   = new Int32Array(64 * 2); // OpenFile maszk Fekete
var BlockerBBMask   = new Int32Array(64 *  8 * 2); // Szelek kizaras maszk
var AttackBBMask    = new Int32Array(64 *  8 * 2); // Tamadas tombok maszk
var BehindBBMask    = new Int32Array(64 * 64 * 2); // A mezo mogotti maszk
var BetweenBBMask   = new Int32Array(64 * 64 * 2); // Ket mezo kozti maszk
var BitBoard        = new Int32Array(30); // Index: side/pce << 1 | Low/High
var MagicBMagics    = new Int32Array(64 * 2); // Magikus bitboard: ~0.5 KB
var MagicRMagics    = new Int32Array(64 * 2); // Magikus bitboard: ~0.5 KB
var MagicBAttacks   = new Int32Array( 512 * 64 * 2); // Futo meret: ~256KB
var MagicRAttacks   = new Int32Array(4096 * 64 * 2); // Bastya meret: ~2MB

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
var SQUARES = {
	A8:  0,     B8:  1,     C8:  2,     D8:  3,     E8:  4,     F8:  5,     G8:  6,     H8:  7,
	A7:  8,     B7:  9,     C7: 10,     D7: 11,     E7: 12,     F7: 13,     G7: 14,     H7: 15,
	A6: 16,     B6: 17,     C6: 18,     D6: 19,     E6: 20,     F6: 21,     G6: 22,     H6: 23,
	A5: 24,     B5: 25,     C5: 26,     D5: 27,     E5: 28,     F5: 29,     G5: 30,     H5: 31,
	A4: 32,     B4: 33,     C4: 34,     D4: 35,     E4: 36,     F4: 37,     G4: 38,     H4: 39,
	A3: 40,     B3: 41,     C3: 42,     D3: 43,     E3: 44,     F3: 45,     G3: 46,     H3: 47,
	A2: 48,     B2: 49,     C2: 50,     D2: 51,     E2: 52,     F2: 53,     G2: 54,     H2: 55,
	A1: 56,     B1: 57,     C1: 58,     D1: 59,     E1: 60,     F1: 61,     G1: 62,     H1: 63 };

// Kezdeti allapot
var CHESS_BOARD = new Int8Array([
	BLACK_ROOK, BLACK_KNIGHT, BLACK_BISHOP, BLACK_QUEEN, BLACK_KING, BLACK_BISHOP, BLACK_KNIGHT, BLACK_ROOK,
	BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN, BLACK_PAWN,
	0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0,
	WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN, WHITE_PAWN,
	WHITE_ROOK, WHITE_KNIGHT, WHITE_BISHOP, WHITE_QUEEN, WHITE_KING, WHITE_BISHOP, WHITE_KNIGHT, WHITE_ROOK ]);

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	setTimeout(function InitEvalMasks() {

		if (SetMask[1] !== 0) { // Mar inicializaltunk!
			return;
		}

		var sq, sq2, pce, from;

		// Sor + Oszlop feltoltes
		for (var r = RANKS.RANK_8; r >= RANKS.RANK_1; r--)
		for (var f = FILES.FILE_H; f >= FILES.FILE_A; f--) {
			sq = (r * 8) + (7 - f);
			FileBBMask[f] |= (1 << sq);
			RankBBMask[r] |= (1 << sq);
			NFileBBMask[f] = ~FileBBMask[f];
		}

		// Bitmaszkok feltoltese 1.
		for (sq = 0; sq < 64; sq++)
		{
			SetMask  [sq] = (1 << (sq > 31 ? 63-sq : 31-sq));
			ClearMask[sq] = ~SetMask[sq];

			// Mezo tavolsag
			var rank1 = SquareRank(sq);
			var file1 = SquareFile(sq);
			for (sq2 = 0; sq2 < 64; sq2++) {
				var rank2 = SquareRank(sq2);
				var file2 = SquareFile(sq2);
				DISTANCE[(sq << 6) | sq2] = Math.max(Math.abs(rank1-rank2), Math.abs(file1-file2));
			}
		}

		// Bitmaszkok feltoltese 2.
		for (from = 0; from < 64; from++)
		{
			for (sq = from + 8; sq < 64; sq += 8) {
				BOpenFileMask  [from << 1 | (sq >> 5)] |= SetMask[sq];
				BlackPassedMask[from << 1 | (sq >> 5)] |= SetMask[sq];
			}

			for (sq = from - 8; sq >= 0; sq -= 8) {
				WOpenFileMask  [from << 1 | (sq >> 5)] |= SetMask[sq];
				WhitePassedMask[from << 1 | (sq >> 5)] |= SetMask[sq];
			}

			if (SquareFile(from) !== FILES.FILE_A) {

				NeighbourMask[from] |= SetMask[from - 1];
				IsolatedMask [from] |= FileBBMask[SquareFile(from) - 1];

				for (sq = from + 7; sq < 64; sq += 8) {
					BlackPassedMask[from << 1 | (sq >> 5)] |= SetMask[sq];
				}

				for (sq = from - 9; sq >= 0; sq -= 8) {
					WhitePassedMask[from << 1 | (sq >> 5)] |= SetMask[sq];
				}
			}

			if (SquareFile(from) !== FILES.FILE_H) {

				NeighbourMask[from] |= SetMask[from + 1];
				IsolatedMask [from] |= FileBBMask[SquareFile(from) + 1];

				for (sq = from + 9; sq < 64; sq += 8) {
					BlackPassedMask[from << 1 | (sq >> 5)] |= SetMask[sq];
				}

				for (sq = from - 7; sq >= 0; sq -= 8) {
					WhitePassedMask[from << 1 | (sq >> 5)] |= SetMask[sq];
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

						AttackBBMask[AttackBBidx(pce, from, next >> 5)] |= SetMask[next]; // Tamadas

						if (pce === QUEEN) {
							for (sq = from88 + delta; !(sq & 0x88) && sq !== next88; sq += delta) {
								BetweenBBMask[BetweenBBidx(from, next, from_88(sq) >> 5)] |= SetMask[from_88(sq)]; // Koztes
							}
							for (sq = next88 + delta; !(sq & 0x88); sq += delta) {
								BehindBBMask[BetweenBBidx(from, next, from_88(sq) >> 5)] |= SetMask[from_88(sq)]; // Mogotte
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
				for (var bb = attacks.Low; bb !== 0; bb &= bb - 1) {
					sq = firstBit(bb & -bb);
					if ((attacks.Low & BehindBBMask[BetweenBBidx(from, sq, LOW)])  !== 0
					|| (attacks.High & BehindBBMask[BetweenBBidx(from, sq, HIGH)]) !== 0) {
						BlockerBBMask[AttackBBidx(pce, from, LOW)] |= SetMask[sq];
					}
				}
				for (var bb = attacks.High; bb !== 0; bb &= bb - 1) {
					sq = firstBit(bb & -bb) + 32;
					if ((attacks.Low & BehindBBMask[BetweenBBidx(from, sq, LOW)])  !== 0
					|| (attacks.High & BehindBBMask[BetweenBBidx(from, sq, HIGH)]) !== 0) {
						BlockerBBMask[AttackBBidx(pce, from, HIGH)] |= SetMask[sq];
					}
				}
			}
		}

		// Magic bitboard
		var epoch = new Uint32Array(4096);
		var count = 0;
		for (from = 0; from < 64; from++)
		{
			for (pce = BISHOP; pce <= ROOK; pce++)
			{
				var magicShift  = (pce === ROOK) ? MagicRShifts : MagicBShifts;
				var magicArray  = (pce === ROOK) ? MagicRMagics : MagicBMagics;
				var blockerLow  = BlockerBBMask[AttackBBidx(pce, from, LOW)];
				var blockerHigh = BlockerBBMask[AttackBBidx(pce, from, HIGH)];
				while (true)
				{
					do {
						var magicLow  = magicArray[(from << 1) | LOW]  = RAND_32() & RAND_32() & RAND_32();
						var magicHigh = magicArray[(from << 1) | HIGH] = RAND_32() & RAND_32() & RAND_32();
					} while (PopCount64(blockerLow * magicLow, blockerHigh * magicHigh) < 6);

					count++;
					var collision = false;
					var occupancy = { Low : 0, High : 0 };
					do
					{
						occupancy.High = 0; // Hack
						do {
							var attacks = AttacksFromDebug(pce, from, occupancy);
							var attackArray = (pce === ROOK) ? MagicRAttacks : MagicBAttacks;
							var index = ((occupancy.Low * magicLow) ^ (occupancy.High * magicHigh)) >>> magicShift;
							if (epoch[index] < count) {
								epoch[index] = count;
								attackArray[BetweenBBidx(index, from, LOW)]  = attacks.Low;
								attackArray[BetweenBBidx(index, from, HIGH)] = attacks.High;
							} else if (attackArray[BetweenBBidx(index, from, LOW)] !== attacks.Low || attackArray[BetweenBBidx(index, from, HIGH)] !== attacks.High) {
								collision = true;
								break;
							}

							occupancy.High = (occupancy.High - blockerHigh) & blockerHigh;

						} while (occupancy.High && !collision);

						occupancy.Low = (occupancy.Low - blockerLow) & blockerLow;

					} while (occupancy.Low && !collision);

					if (!collision) break;
				}
			}
		}
	}, 0);

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

		var bitBoard  = BinaryString(BitLow);
		    bitBoard += BinaryString(BitHigh);
		    bitBoard  = bitBoard.split('');

		for (var rank = RANKS.RANK_8; rank >= RANKS.RANK_1; rank--) {
			msg = rank+'. ';
			for (var file = FILES.FILE_A; file <= FILES.FILE_H; file++) {
				if (bitBoard[index++] === '1') {
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

	var BitIndexLow = new Int8Array([ // Mezok 0-31-ig
	31, 30, 3, 29, 2, 17, 7, 28, 1, 9, 11, 16, 6, 14, 27, 23,
	0, 4, 18, 8, 10, 12, 15, 24, 5, 19, 13, 25, 20, 26, 21, 22 ]);

	var firstBit = Math.clz32 || function(b) { // usage: b & -b
		return BitIndexLow[(b * 0x077CB531) >>> 27];
	};

	function PopCount(b) {
		b = b - ((b >>> 1) & 0x55555555);
		b = (b & 0x33333333) + ((b >>> 2) & 0x33333333);
		return (((b + (b >>> 4)) & 0x0F0F0F0F) * 0x01010101) >>> 24;
	}

	function PopCount64(x, y) {
		return PopCount(x) + PopCount(y);
	}

	// init WebAssembly functions
	try {
		var errorHandler = function() {
			setTimeout(function() { sendMessage('info string WebAssembly not supported :('); }, 0);
		};
		var wasmBytes = new Uint8Array([ // popcount64
			0,97,115,109,1,0,0,0,1,7,1,96,2,127,127,1,127,3,2,1,0,7,14,1,10,112,111,112,99,111,117,110,116,
			54,52,0,0,10,11,1,9,0,32,0,105,32,1,105,106,11,0,16,4,110,97,109,101,2,9,1,0,2,0,1,48,1,1,49
		]);
		WebAssembly.compile(wasmBytes).then(function(module) {
			WebAssembly.instantiate(module).then(function(instance) {
				try {
					PopCount64 = instance.exports.popcount64 || PopCount64;
				} catch (e) {errorHandler();}
			}).catch(errorHandler);
		}).catch(errorHandler);
	} catch (error) {
		errorHandler();
	}

	function SetBitBoard(sq, pce, side) {
		var mask = SetMask[sq];
		BitBoard[pce  << 1 | (sq >> 5)] |= mask;
		BitBoard[side << 1 | (sq >> 5)] |= mask;
	}

	function ClearBitBoard(sq, pce, side) {
		var mask = ClearMask[sq];
		BitBoard[pce  << 1 | (sq >> 5)] &= mask;
		BitBoard[side << 1 | (sq >> 5)] &= mask;
	}

	function DefendedByPawn(sq, sd) {
		return sd === WHITE ? DefendedByWPawn(sq) : DefendedByBPawn(sq);
	}

	function DefendedByBPawn(sq) {
		sq = Math.max(sq - 8,  0);
		return (NeighbourMask[sq] & BitBoard[BLACK_PAWN << 1 | (sq >> 5)]);
	}

	function DefendedByWPawn(sq) {
		sq = Math.min(sq + 8, 63);
		return (NeighbourMask[sq] & BitBoard[WHITE_PAWN << 1 | (sq >> 5)]);
	}

	function DirectNeighborPawn(sq, sd) {
		return (NeighbourMask[sq] & BitBoard[(sd | PAWN) << 1 | (sq >> 5)]);
	}

	function PawnControlled(sq, sd, xd) {
		return PopCount(DefendedByPawn(sq, sd)) >= PopCount(DefendedByPawn(sq, xd));
	}

	function PawnSafeSquare(sq, sd, xd) {
	//	return (CHESS_BOARD[sq] & 0x07) !== PAWN && PawnControlled(sq, sd, xd);
		return (CHESS_BOARD[sq] & 0x07) !== PAWN && DefendedByPawn(sq, xd) === 0;
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

		if (rank === Rank_2
		&& DirectNeighborPawn(s2, us)
		&& PawnSafeSquare(s1, us, them)
		&& PawnSafeSquare(s2, us, them)) {
			return false;
		}

		// Eloretolt Gyalog..?

		if (file !== FILES.FILE_A) { // Bal oldali vedo

			var s0 = sq -   1; // Bal oldal
			var s1 = s0 - inc; // Balra lent 1. mezo
			var s2 = s1 - inc; // Balra lent 2. mezo
			var s3 = s2 - inc; // Balra lent 3. mezo

			if (CHESS_BOARD[s2] === usPawn
			&& PawnSafeSquare(s1, us, them)) {
				return false;
			}

			if (rank === Rank_5
			&& CHESS_BOARD[s3] === usPawn
			&& PawnSafeSquare(s1, us, them)
			&& PawnSafeSquare(s2, us, them)) {
				return false;
			}
		}

		if (file !== FILES.FILE_H) { // Jobb oldali vedo

			var s0 = sq +   1; // Jobb oldal
			var s1 = s0 - inc; // Jobbra lent 1. mezo
			var s2 = s1 - inc; // Jobbra lent 2. mezo
			var s3 = s2 - inc; // Jobbra lent 3. mezo

			if (CHESS_BOARD[s2] === usPawn
			&& PawnSafeSquare(s1, us, them)) {
				return false;
			}

			if (rank === Rank_5
			&& CHESS_BOARD[s3] === usPawn
			&& PawnSafeSquare(s1, us, them)
			&& PawnSafeSquare(s2, us, them)) {
				return false;
			}
		}

		return true;
	}

	function IsWhiteOpenFile(file) {
		return FileBBMask[file] & (BitBoard[wPawnLow] | BitBoard[wPawnHigh]);
	}

	function IsBlackOpenFile(file) {
		return FileBBMask[file] & (BitBoard[bPawnLow] | BitBoard[bPawnHigh]);
	}

	function IsolatedWhitePawn(sq) {
		return IsolatedMask[sq] & (BitBoard[wPawnLow] | BitBoard[wPawnHigh]);
	}

	function IsolatedBlackPawn(sq) {
		return IsolatedMask[sq] & (BitBoard[bPawnLow] | BitBoard[bPawnHigh]);
	}

	function WhiteMostPawn(sq) { // Legelso Feher Gyalog
		return (WOpenFileMask[sq << 1] & BitBoard[wPawnLow]) | (WOpenFileMask[sq << 1 | HIGH] & BitBoard[wPawnHigh]);
	}

	function BlackMostPawn(sq) { // Legelso Fekete Gyalog
		return (BOpenFileMask[sq << 1] & BitBoard[bPawnLow]) | (BOpenFileMask[sq << 1 | HIGH] & BitBoard[bPawnHigh]);
	}

	function WhiteOpenFile(sq) { // Fekete Dupla Gyalog: WhiteOpenFile(sq) !== 0
		return (WOpenFileMask[sq << 1] & BitBoard[bPawnLow]) | (WOpenFileMask[sq << 1 | HIGH] & BitBoard[bPawnHigh]);
	}

	function BlackOpenFile(sq) { // Feher Dupla Gyalog: BlackOpenFile(sq) !== 0
		return (BOpenFileMask[sq << 1] & BitBoard[wPawnLow]) | (BOpenFileMask[sq << 1 | HIGH] & BitBoard[wPawnHigh]);
	}

	function WhitePassedPawn(sq) {
		return (WhitePassedMask[sq << 1] & BitBoard[bPawnLow]) | (WhitePassedMask[sq << 1 | HIGH] & BitBoard[bPawnHigh]);
	}

	function BlackPassedPawn(sq) {
		return (BlackPassedMask[sq << 1] & BitBoard[wPawnLow]) | (BlackPassedMask[sq << 1 | HIGH] & BitBoard[wPawnHigh]);
	}

	function PawnOnSeventh() {
		return (CurrentPlayer ? (BitBoard[bPawnHigh] & RankBBMask[RANKS.RANK_2]) : (BitBoard[wPawnLow] & RankBBMask[RANKS.RANK_7]));
	}

	function PawnPush(Move) {
		return (CHESS_BOARD[FROMSQ(Move)] & 0x07) === PAWN && (CurrentPlayer ? (SquareRank(TOSQ(Move)) <= RANKS.RANK_3 && BlackPassedPawn(TOSQ(Move)) === 0)
		                                                            		 : (SquareRank(TOSQ(Move)) >= RANKS.RANK_6 && WhitePassedPawn(TOSQ(Move)) === 0));
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function to_88(sq) { return sq + (sq & 56); }

	function from_88(sq) { return (sq + (sq & 0x07)) >> 1; }

	function SquareFile(sq) { return (sq & 0x07); }

	function SquareRank(sq) { return 7 - (sq >> 3); }

	function SquareColour(sq) { return ((sq >> 3) ^ sq) & 1; }

	function BBidx(sd, pce, bit) { return (sd | pce) << 1 | bit; }

	function BetweenBBidx(s1, s2, bit) { return (s1 << 7) | (s2 << 1) | bit; }

	function AttackBBidx(pce, sq, bit) { return (sq << 4) | (pce << 1) | bit; }

	function IsSameLine(s1, s2) {
		var rank1 = 7 - (s1 >> 3), file1 = s1 & 7;
		var rank2 = 7 - (s2 >> 3), file2 = s2 & 7;
		return rank1 === rank2 || file1 === file2;
	}

	function SliderAttackers(sq, sd, bit) {
		return ((AttackBBMask[(sq << 4) | (ROOK   << 1) | bit] & (BitBoard[(sd|ROOK)   << 1 | bit] | BitBoard[(sd|QUEEN) << 1 | bit])) |
				(AttackBBMask[(sq << 4) | (BISHOP << 1) | bit] & (BitBoard[(sd|BISHOP) << 1 | bit] | BitBoard[(sd|QUEEN) << 1 | bit])));
	}

	function LineBlocker(s1, s2, pieces) {
		return (pieces.Low & BetweenBBMask[(s1 << 7) | (s2 << 1) | LOW]) | (pieces.High & BetweenBBMask[(s1 << 7) | (s2 << 1) | HIGH]);
	}

	function GetAllPce() {
		return { Low : (BitBoard[WhiteLow] | BitBoard[BlackLow]), High : (BitBoard[WhiteHigh] | BitBoard[BlackHigh]) };
	}

	function PceBlocker(pce, sq) {
		return { Low : BlockerBBMask[(sq << 4) | (pce << 1) | LOW], High : BlockerBBMask[(sq << 4) | (pce << 1) | HIGH] };
	}

	function PceAttacks(pce, sq) {
		return { Low : AttackBBMask[(sq << 4) | (pce << 1) | LOW], High : AttackBBMask[(sq << 4) | (pce << 1) | HIGH] };
	}

	function Behind(s1, s2) {
		return { Low : BehindBBMask[(s1 << 7) | (s2 << 1) | LOW], High : BehindBBMask[(s1 << 7) | (s2 << 1) | HIGH] };
	}

	function AllPceBySide(side) {
		return { Low : BitBoard[side << 1 | LOW], High : BitBoard[side << 1 | HIGH] };
	}

	function KingZone(Ring, Rank, File) { // 3x3 square
		if (Rank === RANKS.RANK_1) {
			Ring.High |= Ring.High << 8;
		} else if (Rank === RANKS.RANK_8) {
			Ring.Low  |= Ring.Low >>> 8;
		}
		if (File === FILES.FILE_A) {
			Ring.Low  |= Ring.Low  >>> 1;
			Ring.High |= Ring.High >>> 1;
		} else if (File === FILES.FILE_H) {
			Ring.Low  |= Ring.Low   << 1;
			Ring.High |= Ring.High  << 1;
		}
	}

	function AttacksFromDebug(pce, from, pieces) { // Based on Senpai!
		var bb, sq;
		var attacks = PceAttacks(pce, from);
		var blocker = PceBlocker(pce, from);
		for (bb = pieces.Low & blocker.Low; bb !== 0; bb &= bb - 1) {
			sq = firstBit(bb & -bb);
			attacks.Low  &= ~BehindBBMask[(from << 7) | (sq << 1) | LOW];
			attacks.High &= ~BehindBBMask[(from << 7) | (sq << 1) | HIGH];
		}
		for (bb = pieces.High & blocker.High; bb !== 0; bb &= bb - 1) {
			sq = firstBit(bb & -bb) + 32;
			attacks.Low  &= ~BehindBBMask[(from << 7) | (sq << 1) | LOW];
			attacks.High &= ~BehindBBMask[(from << 7) | (sq << 1) | HIGH];
		}
		return attacks;
	}

	function AttacksFrom(pce, from, pieces) {
		if (pce >= BISHOP && pce <= QUEEN) {
			var attacks = { Low : 0, High : 0 };
			var baseIdx = from << 1;
			if (pce !== ROOK) {
				var blockIdx = (from << 4) | (BISHOP << 1);
				var lowIdx   = (pieces.Low  & BlockerBBMask[blockIdx])        * MagicBMagics[baseIdx];
				var highIdx  = (pieces.High & BlockerBBMask[blockIdx | HIGH]) * MagicBMagics[baseIdx | HIGH];
				var magicIdx = (((lowIdx ^ highIdx) >>> MagicBShifts) << 7) | baseIdx; // BetweenBBidx
				attacks.Low  = MagicBAttacks[magicIdx];
				attacks.High = MagicBAttacks[magicIdx | HIGH];
			}
			if (pce !== BISHOP) {
				var blockIdx = (from << 4) | (ROOK << 1);
				var lowIdx   = (pieces.Low  & BlockerBBMask[blockIdx])        * MagicRMagics[baseIdx];
				var highIdx  = (pieces.High & BlockerBBMask[blockIdx | HIGH]) * MagicRMagics[baseIdx | HIGH];
				var magicIdx = (((lowIdx ^ highIdx) >>> MagicRShifts) << 7) | baseIdx; // BetweenBBidx
				attacks.Low  |= MagicRAttacks[magicIdx];
				attacks.High |= MagicRAttacks[magicIdx | HIGH];
			}
			return attacks;
		}
		return PceAttacks(pce, from);
	}

	function wPawnAttacks(attacks) {
		var pawnL = BitBoard[wPawnLow];
		var pawnH = BitBoard[wPawnHigh];
		var nFileA = NFileBBMask[FILES.FILE_A];
		var nFileH = NFileBBMask[FILES.FILE_H];
		// Hack: backward instead of forward on white side!
		attacks.High |= ((pawnH & nFileA) >>> 7) | ((pawnH & nFileH) >>> 9);
		attacks.Low  |= ((pawnL & nFileH)  << 7) | ((pawnL & nFileA)  << 9);
		attacks.Low  |= (attacks.High >>> 16); // Add 5th rank attacks to Low
		attacks.High <<= 16; // Hack: forward 2x
	}

	function bPawnAttacks(attacks) {
		var pawnL = BitBoard[bPawnLow];
		var pawnH = BitBoard[bPawnHigh];
		var nFileA = NFileBBMask[FILES.FILE_A];
		var nFileH = NFileBBMask[FILES.FILE_H];
		// Hack: backward instead of forward on black side!
		attacks.Low  |= ((pawnL & nFileH)  << 7) | ((pawnL & nFileA)  << 9);
		attacks.High |= ((pawnH & nFileA) >>> 7) | ((pawnH & nFileH) >>> 9);
		attacks.High |= (attacks.Low  << 16); // Add 4th rank attacks to High
		attacks.Low  >>>= 16; // Hack: forward 2x
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function validateMove(from, to, side) { // for TanKy UI

		var forceMove = CurrentPlayer !== side;
		var fromPiece = CHESS_BOARD[from];
		var toPiece   = CHESS_BOARD[to];

		if (!fromPiece) { // Moving an empty square?
			return false;
		}

		if ((fromPiece & 0x8) ^ side) { // Not your turn!
			return false;
		}

		if (!forceMove && toPiece && (toPiece & 0x8) === side) { // Cannot attack one of your own!
			return false;
		}

		var pieceType = fromPiece & 0x07;

	// Capture move..?
		var capture = 0;
		if (toPiece || (pieceType === PAWN && EN_PASSANT !== 0 && EN_PASSANT === to)) {
			capture = 1;
		}

	// Promotion..?
		var promote = 0;
		if (pieceType === PAWN && (to <= SQUARES.H8 || to >= SQUARES.A1)) {
			promote = side|QUEEN;
		}

	// Castling..?
		var castling = 0;
		if (pieceType === KING && Math.abs(from - to) === 2) {
			castling = 1;
		}

	// Create move..
		var Move = BIT_MOVE(from, to, capture, promote, castling);

	// Legal move..?
		if (!forceMove)
		{
			for (var index = 0; index < brd_moveListEnd[0]; index++) {
				if (brd_moveList[index] === Move) {
					return isLegal(Move);
				}
			}
			return false;
		}
		else if (castling === 1)
		{
			return side === WHITE ? (to === SQUARES.G1 && CastleRights & CASTLEBIT.WK) || (to === SQUARES.C1 && CastleRights & CASTLEBIT.WQ)
			                      : (to === SQUARES.G8 && CastleRights & CASTLEBIT.BK) || (to === SQUARES.C8 && CastleRights & CASTLEBIT.BQ);
		}
		else if (pieceType === PAWN)
		{
			var attacks = { Low : 0, High : 0 };
			var inc = side ? 8 : -8, next = from + inc;

			next > 31 ? attacks.High = SetMask[next] | NeighbourMask[next]
			          : attacks.Low  = SetMask[next] | NeighbourMask[next];

			if (SquareRank(from) === (side ? RANKS.RANK_7 : RANKS.RANK_2)) {
				next + inc > 31 ? attacks.High |= SetMask[next + inc]
				                : attacks.Low  |= SetMask[next + inc];
			}
		}
		else
		{
			var attacks = PceAttacks(pieceType, from);
		}

		return to > 31 ? (attacks.High & SetMask[to]) !== 0 : (attacks.Low & SetMask[to]) !== 0;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function StoreHash(move, score, _eval, flags, depth) { // Hash tarolas

		var index  = brd_hashKeyLow & HASH_MASK;
		var bestDt = -1;
		var oldest = -1;
		var update =  0;

		for (var limit = index + CLUSTER_SIZE; index < limit; index++)
		{
			var ePkg1  = HashTablePkg1[index];
			var eMove  = (ePkg1 & 0x3FFFF);   // 18 bit
			var eDepth = (ePkg1 >> 18) & 0xFF; // 8 bit
			var eDate  = (ePkg1 >> 26) & 0xF;  // 4 bit
			var eFlag  = (ePkg1 >> 30) & 0x3;  // 2 bit

			if (HashTableLock[index] === brd_hashKeyHigh)
			{
				if (eDepth <= depth) {
					if (move === NOMOVE) move = eMove;
					update = index;
					bestDt = eDate;
					break;
				}

				// update age & move (when needed) of deeper entry
				if (HashDate !== eDate || (eMove === NOMOVE && move !== NOMOVE))
				{
					if (HashDate !== eDate) HashUsed++;

					HashTablePkg1[index] = (ePkg1 & 0xC3FC0000) | (HashDate << 26) | (eMove || move);
				}
				return;
			}

			var age = ((HashDate - eDate) & 15) << 10 | (64 - eDepth) << 3 | (eFlag ^ FLAG_EXACT) << 1 | (eMove === NOMOVE);
			if (oldest < age) {
				oldest = age;
				update = index;
				bestDt = eDate;
			}
		}

		if (HashDate !== bestDt) HashUsed++;

		if (score > ISMATE) {
			score += BoardPly;
		} else if (score < -ISMATE) {
			score -= BoardPly;
		}
		// store
		HashTablePkg1[update] = (flags << 30) | (HashDate << 26) | (depth << 18) | move;
		HashTablePkg2[update] = (_eval << 16) | (score & 0xFFFF); // signed safe!
		HashTableLock[update] = brd_hashKeyHigh;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function ProbeHash() { // Hash kiolvasas

		var index = brd_hashKeyLow & HASH_MASK;

		for (var limit = index + CLUSTER_SIZE; index < limit; index++)
		{
			if (HashTableLock[index] === brd_hashKeyHigh) {
				var ePkg1 = HashTablePkg1[index];
				var ePkg2 = HashTablePkg2[index];
				return {
					move  : (ePkg1 & 0x3FFFF),
					eval  : (ePkg2 >> 16),
					score : (ePkg2 << 16) >> 16,
					depth : (ePkg1 >> 18) & 0xFF,
				//	date  : (ePkg1 >> 26) & 0xF,
					flags : (ePkg1 >> 30) & 0x3
				};
			}
		}
		return NOMOVE;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function GetDrawValue() { // 3 lepesismetles vaksag ellen
		return 2 * (Nodes & 1) - 1;
	}

	function IsRepetition(inCheck) { // Lepesismetles + 50 lepesszabaly

		if (brd_fiftyMove >= 100) { // TODO: mate?
			return brd_fiftyMove > 100 || !inCheck;
		}

		var end = Math.min(MoveCount, brd_fiftyMove);
		for (var index = 4; index <= end; index += 2) {
			var history = MOVE_HISTORY[MoveCount - index];
			if (history.hashKeyLow === brd_hashKeyLow && history.hashKeyHigh === brd_hashKeyHigh) {
				return true;
			}
		}
		return false;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function FROMSQ(m) { return (m & 0x3F); }
	function TOSQ(m) { return ((m >> 6) & 0x3F); }
	function PROMOTED(m) { return ((m >> 13) & 0xF); }
	function HASH_PCE(pce, sq) {
		var index = (pce << 6) | sq;
		var keyLow = PieceKeysLow[index];
		var keyHigh = PieceKeysHigh[index];
		brd_hashKeyLow ^= keyLow;
		brd_hashKeyHigh ^= keyHigh;
		if ((pce & 0x07) === PAWN) {
			brd_pawnKeyLow ^= keyLow;
			brd_pawnKeyHigh ^= keyHigh;
		}
	}
	function MOVE_PCE(pce, from, to, side) {
		CHESS_BOARD[from] = 0; // Babu torlese
		CHESS_BOARD[to] = pce; // Babu mozgatas
		var newIndex = brd_pieceIndex[from];
		brd_pieceIndex[to] = newIndex;
		brd_pieceList[(pce << 4) | newIndex] = to;
		ClearBitBoard(from, pce, side);
		SetBitBoard(to, pce, side);
	}
	function ADDING_PCE(pce, sq, side) {
		CHESS_BOARD[sq] = pce; // Babu hozzadasa
		var oldCount = brd_pieceCount[pce]++; // Utolag novel
		brd_pieceIndex[sq] = oldCount;
		brd_pieceList[(pce << 4) | oldCount] = sq;
		SetBitBoard(sq, pce, side);
	}
	function DELETE_PCE(pce, sq, side) {
		CHESS_BOARD[sq] = 0; // Babu torlese
		var newIndex = brd_pieceIndex[sq];
		var newCount = --brd_pieceCount[pce]; // Elore csokkent
		var lastPceSquare = brd_pieceList[(pce << 4) | newCount];
		brd_pieceIndex[lastPceSquare] = newIndex;
		brd_pieceList[(pce << 4) | newIndex] = lastPceSquare;
		brd_pieceList[(pce << 4) | newCount] = EMPTY; // Ures
		ClearBitBoard(sq, pce, side);
	}
	function BIT_MOVE(from, to, capture, promote, castling) {
		return (from | (to << 6) | (capture << 12) | (promote << 13) | (castling << 17)); // Lepes: 18 bit
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

		var from = (move & 0x3F);
		var to = (move >> 6) & 0x3F;
		var MOVED_PIECE = CHESS_BOARD[from];
		var CAPTURED_PIECE = CHESS_BOARD[to];
		var PROMOTED_PIECE = (move >> 13) & 0xF;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var historyBase = MoveCount * HIDDEN_NEURONS;
		for (var neuron = 0; neuron < HIDDEN_NEURONS; neuron++) {
			HIDDEN_HISTORY[historyBase + neuron] = NN_HIDDEN_LAYER[neuron];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		MOVE_HISTORY[MoveCount] = { // Lepeselozmeny mentese
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

		if (EN_PASSANT !== 0) { // En-passant reset
			EN_PASSANT = 0;
			brd_hashKeyLow  ^= PieceKeysLow[0];
			brd_hashKeyHigh ^= PieceKeysHigh[0];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (CAPTURED_PIECE) // Ha leutottunk valakit
		{
			brd_fiftyMove = 0; // reset
		    var them = CurrentPlayer ^ 8;
			HASH_PCE(CAPTURED_PIECE, to);
			DELETE_PCE(CAPTURED_PIECE, to, them);
			DELETE_NN_PCE(CAPTURED_PIECE, to, them);
		}
		else if (move & CAPTURE_MASK) // En Passant Lepes
		{
			brd_fiftyMove = 0; // reset
		    var them = CurrentPlayer ^ 8;
			var capturedPawn = them|PAWN;
            var pawnSquare = to + (them ? 8 : -8);
			HASH_PCE(capturedPawn, pawnSquare);
			DELETE_PCE(capturedPawn, pawnSquare, them);
            DELETE_NN_PCE(capturedPawn, pawnSquare, them);
		}
		else if (move & CASTLED_MASK) // Sancolaskor Bastya mozgatasa
		{
			switch (to) {
				case SQUARES.C1:
					HASH_PCE(WHITE_ROOK, SQUARES.A1);
					HASH_PCE(WHITE_ROOK, SQUARES.D1);
					MOVE_PCE(WHITE_ROOK, SQUARES.A1, SQUARES.D1, WHITE);
					MOVE_NN_PCE(ROOK, ROOK, SQUARES.A1, SQUARES.D1, WHITE);
				break;
				case SQUARES.C8:
					HASH_PCE(BLACK_ROOK, SQUARES.A8);
					HASH_PCE(BLACK_ROOK, SQUARES.D8);
					MOVE_PCE(BLACK_ROOK, SQUARES.A8, SQUARES.D8, BLACK);
					MOVE_NN_PCE(ROOK, ROOK, SQUARES.A8, SQUARES.D8, BLACK);
				break;
				case SQUARES.G1:
					HASH_PCE(WHITE_ROOK, SQUARES.H1);
					HASH_PCE(WHITE_ROOK, SQUARES.F1);
					MOVE_PCE(WHITE_ROOK, SQUARES.H1, SQUARES.F1, WHITE);
					MOVE_NN_PCE(ROOK, ROOK, SQUARES.H1, SQUARES.F1, WHITE);
				break;
				case SQUARES.G8:
					HASH_PCE(BLACK_ROOK, SQUARES.H8);
					HASH_PCE(BLACK_ROOK, SQUARES.F8);
					MOVE_PCE(BLACK_ROOK, SQUARES.H8, SQUARES.F8, BLACK);
					MOVE_NN_PCE(ROOK, ROOK, SQUARES.H8, SQUARES.F8, BLACK);
				break;
				default: break;
			}
		}
		else if ((MOVED_PIECE & 0x07) === PAWN) // Ha Gyaloggal leptunk
		{
			brd_fiftyMove = 0; // reset

			if (Math.abs(from - to) === 16) // En Passant csak ha tamadjak..
			{
				if (NeighbourMask[to] & BitBoard[CurrentPlayer ? wPawnLow : bPawnHigh]) {
					EN_PASSANT = (to + (CurrentPlayer ? -8 : 8));
					brd_hashKeyLow  ^= PieceKeysLow [EN_PASSANT];
					brd_hashKeyHigh ^= PieceKeysHigh[EN_PASSANT];
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		MOVE_PCE(MOVED_PIECE, from, to, CurrentPlayer); // Babu mozgatasa
		HASH_PCE(MOVED_PIECE, from);
		HASH_PCE(MOVED_PIECE, to);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (PROMOTED_PIECE !== 0) // Gyalog bevaltasa
		{
			HASH_PCE(MOVED_PIECE, to);
			HASH_PCE(PROMOTED_PIECE, to);
			DELETE_PCE(MOVED_PIECE, to, CurrentPlayer);
			ADDING_PCE(PROMOTED_PIECE, to, CurrentPlayer);
			MOVE_NN_PCE(MOVED_PIECE, PROMOTED_PIECE, from, to, CurrentPlayer);
		}
		else
		{
			MOVE_NN_PCE(MOVED_PIECE, MOVED_PIECE, from, to, CurrentPlayer);
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		brd_hashKeyLow  ^= CastleKeysLow [CastleRights]; // Sancolas
		brd_hashKeyHigh ^= CastleKeysHigh[CastleRights];

		CastleRights &= CastlePerm[from] & CastlePerm[to];

		brd_hashKeyLow  ^= CastleKeysLow [CastleRights];
		brd_hashKeyHigh ^= CastleKeysHigh[CastleRights];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		brd_hashKeyHigh ^= SideKeyHigh; // Oldal valtas
		brd_hashKeyLow ^= SideKeyLow;
		CurrentPlayer ^= 8;
		MoveCount++;
		BoardPly++;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function unMakeMove() {

		MoveCount--;
		BoardPly--;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var historyBase = MoveCount * HIDDEN_NEURONS;
		for (var neuron = 0; neuron < HIDDEN_NEURONS; neuron++) {
			NN_HIDDEN_LAYER[neuron] = HIDDEN_HISTORY[historyBase + neuron];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var history = MOVE_HISTORY[MoveCount];
		EN_PASSANT = history.epSquare;
		CastleRights = history.castleBIT;
		brd_fiftyMove = history.fiftyMove;
		brd_hashKeyLow = history.hashKeyLow;
		brd_pawnKeyLow = history.pawnKeyLow;
		brd_hashKeyHigh = history.hashKeyHigh;
		brd_pawnKeyHigh = history.pawnKeyHigh;
		var CAPTURED_PIECE = history.capturedPCE;

		var move = history.move;
		var from = (move & 0x3F);
		var to = (move >> 6) & 0x3F;
		var MOVED_PCE = CHESS_BOARD[to];
		var PROMOTED_PIECE = (move >> 13) & 0xF;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		MOVE_PCE(MOVED_PCE, to, from, CurrentPlayer^8); // Babu mozgatasa (to->from)

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
				case SQUARES.C1: MOVE_PCE(WHITE_ROOK, SQUARES.D1, SQUARES.A1, WHITE); break;
				case SQUARES.C8: MOVE_PCE(BLACK_ROOK, SQUARES.D8, SQUARES.A8, BLACK); break;
				case SQUARES.G1: MOVE_PCE(WHITE_ROOK, SQUARES.F1, SQUARES.H1, WHITE); break;
				case SQUARES.G8: MOVE_PCE(BLACK_ROOK, SQUARES.F8, SQUARES.H8, BLACK); break;
				default: break;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		CurrentPlayer ^= 8; // Oldal valtas

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (PROMOTED_PIECE !== 0) // Gyalog bevaltasanak visszavonasa
		{
			DELETE_PCE(PROMOTED_PIECE, from, CurrentPlayer);
			ADDING_PCE(CurrentPlayer|PAWN, from, CurrentPlayer);
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

		if (EN_PASSANT !== 0) {
			EN_PASSANT = 0;
			brd_hashKeyLow  ^= PieceKeysLow[0];
			brd_hashKeyHigh ^= PieceKeysHigh[0];
		}
		brd_hashKeyHigh ^= SideKeyHigh;
		brd_hashKeyLow ^= SideKeyLow;
		CurrentPlayer ^= 8;
		brd_fiftyMove = 0;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function unMakeNullMove() {

		CurrentPlayer ^= 8;
		var history = MOVE_HISTORY[--MoveCount];
		EN_PASSANT = history.epSquare;
		brd_fiftyMove = history.fiftyMove;
		brd_hashKeyLow = history.hashKeyLow;
		brd_hashKeyHigh = history.hashKeyHigh;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function S(mg, eg) { return ((mg << 16) + eg) | 0; }

	function EG_SC(sc) { return (sc << 16) >> 16; }

	function MG_SC(sc) { return (sc + 0x8000) >> 16; }

	function isMate(score) { return score > ISMATE || score < -ISMATE; }

	function isCheck(Side) { return isSquareUnderAttack(brd_pieceList[(Side|KING) << 4], Side); }

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function isSquareUnderAttack(target, us) {

		var bb, them = us^8;

		// Gyalog tamadas
		if (us === BLACK ? DefendedByWPawn(target) : DefendedByBPawn(target)) {
			return 1;
		}

		// Huszar tamadas
		if (AttackBBMask[(target << 4) | (KNIGHT << 1) | LOW]  & BitBoard[(them|KNIGHT) << 1 | LOW]
		 || AttackBBMask[(target << 4) | (KNIGHT << 1) | HIGH] & BitBoard[(them|KNIGHT) << 1 | HIGH]) {
			return 1;
		}

		// Kiraly tamadas
		if (AttackBBMask[(target << 4) | (KING << 1) | LOW]  & BitBoard[(them|KING) << 1 | LOW]
		 || AttackBBMask[(target << 4) | (KING << 1) | HIGH] & BitBoard[(them|KING) << 1 | HIGH]) {
			return 1;
		}

		// Futo, Bastya, Vezer
		var xPiecesBB = GetAllPce();
		for (bb = SliderAttackers(target, them, LOW); bb !== 0; bb &= bb - 1)
		{
			if (LineBlocker(firstBit(bb & -bb), target, xPiecesBB) === 0) return 1;
		}
		for (bb = SliderAttackers(target, them, HIGH); bb !== 0; bb &= bb - 1)
		{
			if (LineBlocker(firstBit(bb & -bb) + 32, target, xPiecesBB) === 0) return 1;
		}

		return NOT_IN_CHECK;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function givesCheck(move) {

		var from = (move & 0x3F);
		var to = (move >> 6) & 0x3F;
		var us = CHESS_BOARD[from] & 0x8;
		var promoted = (move >> 13) & 0xF;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var PCE = (promoted || CHESS_BOARD[from]) & 0x07;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Gyalog Sakk..?
		if (PCE === PAWN)
		{
			var attack = us ? NeighbourMask[to+8] & BitBoard[WHITE_KING << 1 | ((to+8) >> 5)]
			                : NeighbourMask[to-8] & BitBoard[BLACK_KING << 1 | ((to-8) >> 5)];

			if (attack) return 1;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var bb, them = us^8;
		var xPiecesBB = GetAllPce();
		var King = brd_pieceList[(them|KING) << 4];

		// Babu mozgatasa
		from > 31 ? xPiecesBB.High ^= SetMask[from] : xPiecesBB.Low ^= SetMask[from];
		to   > 31 ? xPiecesBB.High |= SetMask[to]   : xPiecesBB.Low |= SetMask[to];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Sancolas: Bastya mozgatasa
		if (move & CASTLED_MASK)
		{
			switch (to) {
				case SQUARES.C1: from = SQUARES.A1; to = SQUARES.D1; break;
				case SQUARES.C8: from = SQUARES.A8; to = SQUARES.D8; break;
				case SQUARES.G1: from = SQUARES.H1; to = SQUARES.F1; break;
				case SQUARES.G8: from = SQUARES.H8; to = SQUARES.F8; break;
				default: break;
			}

			us === BLACK ? xPiecesBB.Low  = (xPiecesBB.Low  ^ SetMask[from]) | SetMask[to]
			             : xPiecesBB.High = (xPiecesBB.High ^ SetMask[from]) | SetMask[to];

			PCE = ROOK; // Hack: Bastya tamadas!
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Direkt Sakk..?
		if (PCE !== PAWN)
		{
			if (AttackBBMask[(to << 4) | (PCE << 1) | LOW]  & BitBoard[(them|KING) << 1 | LOW]
			 || AttackBBMask[(to << 4) | (PCE << 1) | HIGH] & BitBoard[(them|KING) << 1 | HIGH])
			{
				if (LineBlocker(to, King, xPiecesBB) === 0) return 1;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var Beyond = Behind(King, from); // Babu mogott megnyilo mezok!

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// En Passant
		if (PCE === PAWN && CHESS_BOARD[to] === 0 && (move & CAPTURE_MASK))
		{
			var epSq = us === BLACK ? to-8 : to+8;

			// Ellenfel torlese
			epSq > 31 ? xPiecesBB.High ^= SetMask[epSq] : xPiecesBB.Low ^= SetMask[epSq];

			// Mogotte megnyilo mezok!
			Beyond.Low  |= BehindBBMask[(King << 7) | (epSq << 1) | LOW];
			Beyond.High |= BehindBBMask[(King << 7) | (epSq << 1) | HIGH];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Felfedezett Sakk..?
		if (Beyond.Low)
		for (bb = SliderAttackers(King, us, LOW) & Beyond.Low; bb !== 0; bb &= bb - 1)
		{
			if (LineBlocker(firstBit(bb & -bb), King, xPiecesBB) === 0) return 1;
		}
		if (Beyond.High)
		for (bb = SliderAttackers(King, us, HIGH) & Beyond.High; bb !== 0; bb &= bb - 1)
		{
			if (LineBlocker(firstBit(bb & -bb) + 32, King, xPiecesBB) === 0) return 1;
		}

		return NOT_IN_CHECK;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function isLegal(move) {

		var from = (move & 0x3F);
		var to = (move >> 6) & 0x3F;
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
		var King = brd_pieceList[(us|KING) << 4];

		// Babu mozgatasa
		from > 31 ? xPiecesBB.High ^= SetMask[from] : xPiecesBB.Low ^= SetMask[from];
		to   > 31 ? xPiecesBB.High |= SetMask[to]   : xPiecesBB.Low |= SetMask[to];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var Beyond = Behind(King, from); // Babu mogott megnyilo mezok!

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// En Passant
		if (PCE === PAWN && CHESS_BOARD[to] === 0 && (move & CAPTURE_MASK))
		{
			var epSq = us === BLACK ? to-8 : to+8;

			// Ellenfel torlese
			epSq > 31 ? xPiecesBB.High ^= SetMask[epSq] : xPiecesBB.Low ^= SetMask[epSq];

			// Mogotte megnyilo mezok!
			Beyond.Low  |= BehindBBMask[(King << 7) | (epSq << 1) | LOW];
			Beyond.High |= BehindBBMask[(King << 7) | (epSq << 1) | HIGH];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Felfedezett Sakk..?
		if (Beyond.Low)
		for (bb = SliderAttackers(King, them, LOW) & Beyond.Low; bb !== 0; bb &= bb - 1) {
			from = firstBit(bb & -bb);
			if (from !== to && LineBlocker(from, King, xPiecesBB) === 0) return false;
		}
		if (Beyond.High)
		for (bb = SliderAttackers(King, them, HIGH) & Beyond.High; bb !== 0; bb &= bb - 1) {
			from = firstBit(bb & -bb) + 32;
			if (from !== to && LineBlocker(from, King, xPiecesBB) === 0) return false;
		}

		return true;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function Evaluation() {

		var whitePovKeyLow  = CurrentPlayer === WHITE ? brd_hashKeyLow  : brd_hashKeyLow  ^ SideKeyLow;
		var whitePovKeyHigh = CurrentPlayer === WHITE ? brd_hashKeyHigh : brd_hashKeyHigh ^ SideKeyHigh;
		var evalHashIndex = whitePovKeyLow & EVAL_HASH_MASK; // Ertekeles hash (~5% Nps+ with Hash)
		if (EvalHashLock[evalHashIndex] === whitePovKeyHigh) {
			var entry = EvalHashEval[evalHashIndex];
			var score = entry >> 16;
			var side  = entry & 0x8;
			var symm  = entry & 0x1;
			if (symm || CurrentPlayer === side) {
				return (CurrentPlayer === WHITE ? score : -score) + ((entry & 0xFFFF) >> 5); // + tempo
			}
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var bb           = 0; // bb
		var mob          = 0; // Mob
		var PCE          = 0; // Babu
		var rank         = 0; // Sor
		var file         = 0; // Oszlop
		var score        = 0; // Pontszam
		var wForce       = 0; // Feher ero
		var bForce       = 0; // Fekete ero
		var pieceIdx     = 0; // Babu index
		var wAttackPower = 0; // Tamadas pont Feher
		var bAttackPower = 0; // Tamadas pont Fekete
		var wAttackCount = 0; // Tamadok szama Feher
		var bAttackCount = 0; // Tamadok szama Fekete

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var xPiecesBB = GetAllPce();
		var attacks  = { Low : 0, High : 0 };
		var wAttacks = { Low : 0, High : 0 }; wPawnAttacks(wAttacks);
		var bAttacks = { Low : 0, High : 0 }; bPawnAttacks(bAttacks);

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var pawnHashIndex = brd_pawnKeyLow & PAWN_HASH_MASK; // Gyalog hash (~10% Nps+)
		if (PawnHashLock[pawnHashIndex] !== brd_pawnKeyHigh) {
			PawnHashLock[pawnHashIndex] = brd_pawnKeyHigh;
			var pawnEval = EvalPawns(pawnHashIndex);
			PawnHashEval[pawnHashIndex] = pawnEval;
			score += pawnEval;
		} else {
			score += PawnHashEval[pawnHashIndex];
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Fenyegeteshez gyorsitas:  sidePieces & ~(pawn)
		var wNonPawns = { Low  : BitBoard[WhiteLow]  & ~BitBoard[wPawnLow],
						  High : BitBoard[WhiteHigh] & ~BitBoard[wPawnHigh] };
		var bNonPawns = { Low  : BitBoard[BlackLow]  & ~BitBoard[bPawnLow],
						  High : BitBoard[BlackHigh] & ~BitBoard[bPawnHigh] };

	// Biztonsagos mobilitas:    ~(usPawn | usKing | themPawnAttack)
		var wPawnSafe = { Low  : ~(BitBoard[wPawnLow]  | BitBoard[wKingLow]  | bAttacks.Low),
		                  High : ~(BitBoard[wPawnHigh] | BitBoard[wKingHigh] | bAttacks.High) };
		var bPawnSafe = { Low  : ~(BitBoard[bPawnLow]  | BitBoard[bKingLow]  | wAttacks.Low),
		                  High : ~(BitBoard[bPawnHigh] | BitBoard[bKingHigh] | wAttacks.High) };

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	//						           BABUK ERTEKELESE
	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Kiraly
		var wKing = brd_pieceList[WHITE_KING << 4];
		var wKingRank = 7 - (wKing >> 3); // Kiraly sora
		var wKingFile = (wKing & 0x07); // Kiraly oszlopa
		var WKZ = PceAttacks(KING, wKing); // Kiraly tamadas
		var wKingAttacks = { Low : WKZ.Low, High : WKZ.High };
		KingZone(WKZ, wKingRank, wKingFile); // 3x3-as gyuru..
		score += KingPst[wKing];

	// Fekete Kiraly
		var bKing = brd_pieceList[BLACK_KING << 4];
		var bKingRank = 7 - (bKing >> 3); // Kiraly sora
		var bKingFile = (bKing & 0x07); // Kiraly oszlopa
		var BKZ = PceAttacks(KING, bKing); // Kiraly tamadas
		var bKingAttacks = { Low : BKZ.Low, High : BKZ.High };
		KingZone(BKZ, bKingRank, bKingFile); // 3x3-as gyuru..
		score -= KingPst[bKing ^ 56];

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Gyalog fenyegetes
		score += PawnCapture(wAttacks, bNonPawns);
		score -= PawnCapture(bAttacks, wNonPawns);

	// Kiraly fenyegetes
		score += CaptureScore(wKingAttacks, wPawnSafe, bNonPawns, KING, BLACK);
		score -= CaptureScore(bKingAttacks, bPawnSafe, wNonPawns, KING, WHITE);

	// Kiraly zonak
		var SafeWKZ = { Low : WKZ.Low & bPawnSafe.Low, High : WKZ.High & bPawnSafe.High };
		var SafeBKZ = { Low : BKZ.Low & wPawnSafe.Low, High : BKZ.High & wPawnSafe.High };

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Vezer
		pieceIdx = WHITE_QUEEN << 4;
		PCE = brd_pieceList[pieceIdx];
		while (PCE !== EMPTY)
		{
			rank = 7 - (PCE >> 3);

			if (rank === RANKS.RANK_7 && (bKingRank === RANKS.RANK_8 || BitBoard[bPawnLow] & RankBBMask[RANKS.RANK_7])) {
				score += QueenOn7th;
			}

			// BitBoard
			attacks = AttacksFrom(QUEEN, PCE, xPiecesBB);

			// Tamadasok
			wAttacks.Low  |= attacks.Low;
			wAttacks.High |= attacks.High;

			// Mobilitas
			mob = PopCount64(wPawnSafe.Low & attacks.Low, wPawnSafe.High & attacks.High);

			// Fenyegetes
			score += CaptureScore(attacks, wPawnSafe, bNonPawns, QUEEN, BLACK);

			// Kiraly tamadas
			if (bb = (attacks.Low & SafeBKZ.Low) | (attacks.High & SafeBKZ.High)) {
				wAttackCount++;
				wAttackPower += PopCount(bb);
			}

			wForce += 4;
			score += QUEEN_VALUE;
			score += QueenMob[mob];
			score += QueenPst[PCE];
			PCE = brd_pieceList[++pieceIdx];
		}

	// Fekete Vezer
		pieceIdx = BLACK_QUEEN << 4;
		PCE = brd_pieceList[pieceIdx];
		while (PCE !== EMPTY)
		{
			rank = 7 - (PCE >> 3);

			if (rank === RANKS.RANK_2 && (wKingRank === RANKS.RANK_1 || BitBoard[wPawnHigh] & RankBBMask[RANKS.RANK_2])) {
				score -= QueenOn7th;
			}

			// BitBoard
			attacks = AttacksFrom(QUEEN, PCE, xPiecesBB);

			// Tamadasok
			bAttacks.Low  |= attacks.Low;
			bAttacks.High |= attacks.High;

			// Mobilitas
			mob = PopCount64(bPawnSafe.Low & attacks.Low, bPawnSafe.High & attacks.High);

			// Fenyegetes
			score -= CaptureScore(attacks, bPawnSafe, wNonPawns, QUEEN, WHITE);

			// Kiraly tamadas
			if (bb = (attacks.Low & SafeWKZ.Low) | (attacks.High & SafeWKZ.High)) {
				bAttackCount++;
				bAttackPower += PopCount(bb);
			}

			bForce += 4;
			score -= QUEEN_VALUE;
			score -= QueenMob[mob];
			score -= QueenPst[PCE ^ 56];
			PCE = brd_pieceList[++pieceIdx];
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Bastya
		pieceIdx = WHITE_ROOK << 4;
		PCE = brd_pieceList[pieceIdx];
		while (PCE !== EMPTY)
		{
			file = (PCE & 0x07);
			rank = 7 - (PCE >> 3);

			if (rank === RANKS.RANK_7 && (bKingRank === RANKS.RANK_8 || BitBoard[bPawnLow] & RankBBMask[RANKS.RANK_7])) {
				score += RookOn7th;
			}

			// BitBoard
			attacks = AttacksFrom(ROOK, PCE, xPiecesBB);

			// Tamadasok
			wAttacks.Low  |= attacks.Low;
			wAttacks.High |= attacks.High;

			// Mobilitas
			mob = PopCount64(wPawnSafe.Low & attacks.Low, wPawnSafe.High & attacks.High);

			// Fenyegetes
			score += CaptureScore(attacks, wPawnSafe, bNonPawns, ROOK, BLACK);

			// Kiraly tamadas
			if (bb = (attacks.Low & SafeBKZ.Low) | (attacks.High & SafeBKZ.High)) {
				wAttackCount++;
				wAttackPower += PopCount(bb);
			}

			if (IsWhiteOpenFile(file) === 0) { // Felig nyitott oszlop
				if (IsBlackOpenFile(file) === 0) { // Teljesen nyitott
					score += RookFullOpen;
				} else {
					score += RookHalfOpen;
				}
			} else if (mob <= 3 && rank <= RANKS.RANK_2) { // Sarokba szorult..?
				if (wKingFile < FILES.FILE_E ?
				   (CastleRights & CASTLEBIT.WQ) === 0 && file <= wKingFile
				 : (CastleRights & CASTLEBIT.WK) === 0 && file >= wKingFile) {
					score -= BlockedRook;
				}
			}

			wForce += 2;
			score += ROOK_VALUE;
			score += RookMob[mob];
			score += RookPst[PCE];
			PCE = brd_pieceList[++pieceIdx];
		}

	// Fekete Bastya
		pieceIdx = BLACK_ROOK << 4;
		PCE = brd_pieceList[pieceIdx];
		while (PCE !== EMPTY)
		{
			file = (PCE & 0x07);
			rank = 7 - (PCE >> 3);

			if (rank === RANKS.RANK_2 && (wKingRank === RANKS.RANK_1 || BitBoard[wPawnHigh] & RankBBMask[RANKS.RANK_2])) {
				score -= RookOn7th;
			}

			// BitBoard
			attacks = AttacksFrom(ROOK, PCE, xPiecesBB);

			// Tamadasok
			bAttacks.Low  |= attacks.Low;
			bAttacks.High |= attacks.High;

			// Mobilitas
			mob = PopCount64(bPawnSafe.Low & attacks.Low, bPawnSafe.High & attacks.High);

			// Fenyegetes
			score -= CaptureScore(attacks, bPawnSafe, wNonPawns, ROOK, WHITE);

			// Kiraly tamadas
			if (bb = (attacks.Low & SafeWKZ.Low) | (attacks.High & SafeWKZ.High)) {
				bAttackCount++;
				bAttackPower += PopCount(bb);
			}

			if (IsBlackOpenFile(file) === 0) { // Felig nyitott oszlop
				if (IsWhiteOpenFile(file) === 0) { // Teljesen nyitott
					score -= RookFullOpen;
				} else {
					score -= RookHalfOpen;
				}
			} else if (mob <= 3 && rank >= RANKS.RANK_7) { // Sarokba szorult..?
				if (bKingFile < FILES.FILE_E ?
				   (CastleRights & CASTLEBIT.BQ) === 0 && file <= bKingFile
				 : (CastleRights & CASTLEBIT.BK) === 0 && file >= bKingFile) {
					score += BlockedRook;
				}
			}

			bForce += 2;
			score -= ROOK_VALUE;
			score -= RookMob[mob];
			score -= RookPst[PCE ^ 56];
			PCE = brd_pieceList[++pieceIdx];
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Futo
		pieceIdx = WHITE_BISHOP << 4;
		PCE = brd_pieceList[pieceIdx];
		while (PCE !== EMPTY)
		{
			// BitBoard
			attacks = AttacksFrom(BISHOP, PCE, xPiecesBB);

			// Tamadasok
			wAttacks.Low  |= attacks.Low;
			wAttacks.High |= attacks.High;

			// Mobilitas
			mob = PopCount64(wPawnSafe.Low & attacks.Low, wPawnSafe.High & attacks.High);

			// Fenyegetes
			score += CaptureScore(attacks, wPawnSafe, bNonPawns, BISHOP, BLACK);

			// Kiraly tamadas
			if (bb = (attacks.Low & SafeBKZ.Low) | (attacks.High & SafeBKZ.High)) {
				wAttackCount++;
				wAttackPower += PopCount(bb);
			}

			wForce += 1;
			score += BISHOP_VALUE;
			score += BishopMob[mob];
			score += BishopPst[PCE];
			PCE = brd_pieceList[++pieceIdx];
		}

	// Fekete Futo
		pieceIdx = BLACK_BISHOP << 4;
		PCE = brd_pieceList[pieceIdx];
		while (PCE !== EMPTY)
		{
			// BitBoard
			attacks = AttacksFrom(BISHOP, PCE, xPiecesBB);

			// Tamadasok
			bAttacks.Low  |= attacks.Low;
			bAttacks.High |= attacks.High;

			// Mobilitas
			mob = PopCount64(bPawnSafe.Low & attacks.Low, bPawnSafe.High & attacks.High);

			// Fenyegetes
			score -= CaptureScore(attacks, bPawnSafe, wNonPawns, BISHOP, WHITE);

			// Kiraly tamadas
			if (bb = (attacks.Low & SafeWKZ.Low) | (attacks.High & SafeWKZ.High)) {
				bAttackCount++;
				bAttackPower += PopCount(bb);
			}

			bForce += 1;
			score -= BISHOP_VALUE;
			score -= BishopMob[mob];
			score -= BishopPst[PCE ^ 56];
			PCE = brd_pieceList[++pieceIdx];
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Huszar
		pieceIdx = WHITE_KNIGHT << 4;
		PCE = brd_pieceList[pieceIdx];
		while (PCE !== EMPTY)
		{
			// BitBoard
			attacks = PceAttacks(KNIGHT, PCE);

			// Tamadasok
			wAttacks.Low  |= attacks.Low;
			wAttacks.High |= attacks.High;

			// Mobilitas
			mob = PopCount64(wPawnSafe.Low & attacks.Low, wPawnSafe.High & attacks.High);

			// Fenyegetes
			score += CaptureScore(attacks, wPawnSafe, bNonPawns, KNIGHT, BLACK);

			// Kiraly tamadas
			if (bb = (attacks.Low & SafeBKZ.Low) | (attacks.High & SafeBKZ.High)) {
				wAttackCount++;
				wAttackPower += PopCount(bb);
			}

			var outpost = KnightOutpost[PCE]; // Huszar Orszem
			if (outpost && DefendedByBPawn(PCE) === 0) { // Nincs fenyegetes
				score += outpost * PopCount(DefendedByWPawn(PCE));
			}

			wForce += 1;
			score += KNIGHT_VALUE;
			score += KnightMob[mob];
			score += KnightPst[PCE];
			PCE = brd_pieceList[++pieceIdx];
		}

	// Fekete Huszar
		pieceIdx = BLACK_KNIGHT << 4;
		PCE = brd_pieceList[pieceIdx];
		while (PCE !== EMPTY)
		{
			// BitBoard
			attacks = PceAttacks(KNIGHT, PCE);

			// Tamadasok
			bAttacks.Low  |= attacks.Low;
			bAttacks.High |= attacks.High;

			// Mobilitas
			mob = PopCount64(bPawnSafe.Low & attacks.Low, bPawnSafe.High & attacks.High);

			// Fenyegetes
			score -= CaptureScore(attacks, bPawnSafe, wNonPawns, KNIGHT, WHITE);

			// Kiraly tamadas
			if (bb = (attacks.Low & SafeWKZ.Low) | (attacks.High & SafeWKZ.High)) {
				bAttackCount++;
				bAttackPower += PopCount(bb);
			}

			var outpost = KnightOutpost[PCE ^ 56]; // Huszar Orszem
			if (outpost && DefendedByWPawn(PCE) === 0) { // Nincs fenyegetes
				score -= outpost * PopCount(DefendedByBPawn(PCE));
			}

			bForce += 1;
			score -= KNIGHT_VALUE;
			score -= KnightMob[mob];
			score -= KnightPst[PCE ^ 56];
			PCE = brd_pieceList[++pieceIdx];
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Fejlett Telt Gyalog
		pieceIdx = pawnHashIndex * 9;
		for (PCE = PawnHashPassW[pieceIdx]; PCE !== EMPTY; PCE = PawnHashPassW[++pieceIdx])
		{
			file = (PCE & 0x07);
			rank = 7 - (PCE >> 3);

			score += PassedDistanceOwn [(DISTANCE[(wKing << 6) | (PCE-8)] * 7) + (rank)]; // Sajat Kiraly
			score += PassedDistanceThem[(DISTANCE[(bKing << 6) | (PCE-8)] * 7) + (rank)]; // Ellenfel Kiraly

			if (bForce === 0 && UnstoppablePawn(wKing, bKing, xPiecesBB, PCE, WHITE, file)) { // Megallithatatlan

				score += 900 * (rank - RANKS.RANK_3) / 5;

			} else if (CHESS_BOARD[PCE-8] === 0) { // Szabad Telt Gyalog

				var unsafe = (bKingAttacks.Low & ~(wKingAttacks.Low | wAttacks.Low)) | bAttacks.Low;
				var front  = { Low : WOpenFileMask[PCE << 1], High : WOpenFileMask[PCE << 1 | HIGH] };
				var rear   = { Low : BOpenFileMask[PCE << 1], High : BOpenFileMask[PCE << 1 | HIGH] };

				if (FreePawn(unsafe, front.Low, rear, xPiecesBB, PCE, BLACK, LOW)) { // Szabad
					score += PassedFullFree[rank];
				}
					score += PassedHalfFree[rank];
			}
		}

	// Fekete Fejlett Telt Gyalog
		pieceIdx = pawnHashIndex * 9;
		for (PCE = PawnHashPassB[pieceIdx]; PCE !== EMPTY; PCE = PawnHashPassB[++pieceIdx])
		{
			file = (PCE & 0x07);
			rank = 7 - (PCE >> 3);

			score -= PassedDistanceOwn [(DISTANCE[(bKing << 6) | (PCE+8)] * 7) + (7-rank)]; // Sajat Kiraly
			score -= PassedDistanceThem[(DISTANCE[(wKing << 6) | (PCE+8)] * 7) + (7-rank)]; // Ellenfel Kiraly

			if (wForce === 0 && UnstoppablePawn(bKing, wKing, xPiecesBB, PCE, BLACK, file+56)) { // Megallithatatlan

				score -= 900 * (RANKS.RANK_6 - rank) / 5;

			} else if (CHESS_BOARD[PCE+8] === 0) { // Szabad Telt Gyalog

				var unsafe = (wKingAttacks.High & ~(bKingAttacks.High | bAttacks.High)) | wAttacks.High;
				var front  = { Low : BOpenFileMask[PCE << 1], High : BOpenFileMask[PCE << 1 | HIGH] };
				var rear   = { Low : WOpenFileMask[PCE << 1], High : WOpenFileMask[PCE << 1 | HIGH] };

				if (FreePawn(unsafe, front.High, rear, xPiecesBB, PCE, WHITE, HIGH)) { // Szabad
					score -= PassedFullFree[7-rank];
				}
					score -= PassedHalfFree[7-rank];
			}
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (wForce >= 5 && brd_pieceCount[WHITE_QUEEN])
		{
			if (wAttackCount > 0)
			{
				if (wAttackCount > 4) wAttackCount = 4; // Max 4 tamado

				score += KingSafetyMull[wAttackCount] * wAttackPower;
			}

			if (bKingRank >= RANKS.RANK_6) { // Pawn shield

				var shield = BitBoard[bPawnLow] & (BKZ.Low | (BKZ.Low >>> 8)) & ~(BKZ.Low << 16);

				for (bb = shield; bb !== 0; bb &= bb - 1) {

					PCE = firstBit(bb & -bb);

					if ((WOpenFileMask[PCE << 1 | LOW] & shield) === 0) {

						file = (PCE & 0x07);
						rank = 7 - (PCE >> 3);

						if (file > FILES.FILE_D) file = 7 - file;

						score -= KingShield[file * 4 + (7-rank)];
					}
				}
			}
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (bForce >= 5 && brd_pieceCount[BLACK_QUEEN])
		{
			if (bAttackCount > 0)
			{
				if (bAttackCount > 4) bAttackCount = 4; // Max 4 tamado

				score -= KingSafetyMull[bAttackCount] * bAttackPower;
			}

			if (wKingRank <= RANKS.RANK_3) { // Pawn shield

				var shield = BitBoard[wPawnHigh] & (WKZ.High | (WKZ.High << 8)) & ~(WKZ.High >>> 16);

				for (bb = shield; bb !== 0; bb &= bb - 1) {

					PCE = firstBit(bb & -bb) + 32;

					if ((BOpenFileMask[PCE << 1 | HIGH] & shield) === 0) {

						file = (PCE & 0x07);
						rank = 7 - (PCE >> 3);

						if (file > FILES.FILE_D) file = 7 - file;

						score += KingShield[file * 4 + (rank)];
					}
				}
			}
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (brd_pieceCount[WHITE_BISHOP] >= 2) score += BishopPair;
		if (brd_pieceCount[BLACK_BISHOP] >= 2) score -= BishopPair;

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var phase = 24 - wForce - bForce;

		// Linearis interpolacio kezdo es vegjatek kozott..

		var rawScore = Interpolation(MG_SC(score), EG_SC(score), phase);

		score += CurrentPlayer === WHITE ? TempoBonus : -TempoBonus;

		score = Interpolation(MG_SC(score), EG_SC(score), phase);

		var drawMul = score >= 0 // Dontetlenek..
		? GetDrawMul(WHITE, BLACK, wForce, bForce)
		: GetDrawMul(BLACK, WHITE, bForce, wForce);

		var tempo = Math.abs(score - rawScore) * drawMul | 0;

		var nnEval = drawMul >= 0.5 ? ChessNNEval() : 0;

		rawScore = (rawScore + nnEval) * drawMul | 0; // Ketes dontetlen..?

		EvalHashLock[evalHashIndex] = whitePovKeyHigh; // check force: symmetry-safe (skip unstoppable passer)
		EvalHashEval[evalHashIndex] = (rawScore << 16) | (tempo << 5) | CurrentPlayer | (wForce > 0 && bForce > 0);

		return (CurrentPlayer === WHITE ? rawScore : -rawScore) + tempo;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function GetDrawMul(winSide, defSide, winForce, defForce) {
		if (winForce <= 3) { // few pieces..
			var winPawns = brd_pieceCount[winSide|PAWN];
			var defPawns = brd_pieceCount[defSide|PAWN];
			if (winPawns === 0) {
				if (winForce === 0) return 0; // Lone king
				if (winForce === 1) return 0.1; // King with minor
				if (winForce <= defForce + 1) return 0.2; // Equal or one minor diff
				if (winForce === 2 && brd_pieceCount[winSide|KNIGHT] === 2) return 0.2;
			}
			// opponent sacrifice to take last pawn..
			if (winPawns === 1 && defForce >= 1) {
				if (winForce <= 1) return 0.5;
				if (winForce === 2 && brd_pieceCount[winSide|KNIGHT] === 2) return 0.5;
			}
			// opposite-coloured bishops
			if (winForce === 1 && defForce === 1 && Math.abs(winPawns - defPawns) <= 1) {
				var winB = brd_pieceList[(winSide|BISHOP) << 4];
				var defB = brd_pieceList[(defSide|BISHOP) << 4];
				if (winB !== EMPTY && defB !== EMPTY && SquareColour(winB) !== SquareColour(defB)) {
					return 0.5;
				}
			}
		}
		return 1;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function UnstoppablePawn(usKing, themKing, xPiecesBB, sq, us, promSq) {

		var front = us ? { Low : BOpenFileMask[sq << 1], High : BOpenFileMask[sq << 1 | HIGH] }
		               : { Low : WOpenFileMask[sq << 1], High : WOpenFileMask[sq << 1 | HIGH] };

		if ((xPiecesBB.Low & front.Low) | (xPiecesBB.High & front.High)) return false; // blocked!

		if (DISTANCE[(usKing << 6) | sq] <= 1 && DISTANCE[(usKing << 6) | promSq] <= 1) return true; // king controls promotion path

		if (DISTANCE[(sq << 6) | promSq] < DISTANCE[(themKing << 6) | promSq] + ((CurrentPlayer === us)|0) - 1) return true; // unstoppable

		return false;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function FreePawn(unsafe, front, rear, xPiecesBB, sq, them, bit) {

		if (front & (unsafe | BitBoard[them << 1 | bit])) return false; // unsafe or blocked!

		// major attackers from behind..?
		rear.Low  &= BitBoard[(them|ROOK) << 1 | LOW]  | BitBoard[(them|QUEEN) << 1 | LOW];
		rear.High &= BitBoard[(them|ROOK) << 1 | HIGH] | BitBoard[(them|QUEEN) << 1 | HIGH];

		for (var bb = rear.Low;  bb !== 0; bb &= bb - 1) if (LineBlocker(firstBit(bb & -bb)     , sq, xPiecesBB) === 0) return false;
		for (var bb = rear.High; bb !== 0; bb &= bb - 1) if (LineBlocker(firstBit(bb & -bb) + 32, sq, xPiecesBB) === 0) return false;

		return true;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function CaptureScore(attacks, pawnSafe, nonPawns, pce, them) {

		var weakLow  = attacks.Low  & nonPawns.Low;
		var weakHigh = attacks.High & nonPawns.High;

		if ((weakLow | weakHigh) === 0) return 0; // no threats!

		if (pce >= ROOK) {
			weakLow  &= pawnSafe.Low  & ~BitBoard[(them|pce) << 1 | LOW]; // Not equal and not defended by pawn..
			weakHigh &= pawnSafe.High & ~BitBoard[(them|pce) << 1 | HIGH];
			if (pce === ROOK) {
				weakLow  |= attacks.Low  & BitBoard[(them|QUEEN) << 1 | LOW]; // ..or Queen attacked by Rook!
				weakHigh |= attacks.High & BitBoard[(them|QUEEN) << 1 | HIGH];
			}
		}

		var sc = 0;
		for (var bb = weakLow;  bb !== 0; bb &= bb - 1) sc += ThreatScore[pce * 7 + (CHESS_BOARD[firstBit(bb & -bb)     ] & 0x07)];
		for (var bb = weakHigh; bb !== 0; bb &= bb - 1) sc += ThreatScore[pce * 7 + (CHESS_BOARD[firstBit(bb & -bb) + 32] & 0x07)];
		return sc;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function PawnCapture(attacks, nonPawns) {

		var weakLow  = attacks.Low  & nonPawns.Low;
		var weakHigh = attacks.High & nonPawns.High;

		var sc = 0;
		for (var bb = weakLow;  bb !== 0; bb &= bb - 1) sc += ThreatScore[PAWN * 7 + (CHESS_BOARD[firstBit(bb & -bb)     ] & 0x07)];
		for (var bb = weakHigh; bb !== 0; bb &= bb - 1) sc += ThreatScore[PAWN * 7 + (CHESS_BOARD[firstBit(bb & -bb) + 32] & 0x07)];
		return sc;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function EvalPawns(pawnHashIndex) {
		var score = 0;
		var passIdx = pawnHashIndex * 9;
		var pieceIdx = WHITE_PAWN << 4;
		var PCE = brd_pieceList[pieceIdx];
		while (PCE !== EMPTY)
		{
			var file = (PCE & 0x07);
			var rank = 7 - (PCE >> 3);
			var Open = WhiteOpenFile(PCE) === 0 && WhiteMostPawn(PCE) === 0; // Legelso + Nyitott

			if (DirectNeighborPawn(PCE, WHITE) || DefendedByWPawn(PCE)) { // Eros Gyalog

				score += Open ? PawnConnectedOpen[rank] : PawnConnected[rank];

			} else {

				if (BlackOpenFile(PCE) !== 0) { // Dupla Gyalog

					score += Open ? PawnDoubledOpen[rank] : PawnDoubled[rank];
				}

				if (IsolatedWhitePawn(PCE) === 0) { // Elkulonitett Gyalog

					score += Open ? PawnIsolatedOpen[rank] : PawnIsolated[rank];

				} else if (WeakPawn(PCE, rank, file, WHITE, BLACK)) { // Gyenge Gyalog

					score += Open ? PawnBackwardOpen[rank] : PawnBackward[rank];
				}
			}

			if (Open && WhitePassedPawn(PCE) === 0) { // Telt Gyalog
				score += PassedPawnBase[rank];
				if (rank >= RANKS.RANK_4) { // Fejlett
					PawnHashPassW[passIdx++] = PCE;
				}
			}
			score += PAWN_VALUE;
			score += PawnPst[PCE];
			PCE = brd_pieceList[++pieceIdx];
		}

		PawnHashPassW[passIdx] = EMPTY; // wrap up

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		passIdx = pawnHashIndex * 9;
		pieceIdx = BLACK_PAWN << 4;
		PCE = brd_pieceList[pieceIdx];
		while (PCE !== EMPTY)
		{
			var file = (PCE & 0x07);
			var rank = 7 - (PCE >> 3);
			var Open = BlackOpenFile(PCE) === 0 && BlackMostPawn(PCE) === 0; // Legelso + Nyitott

			if (DirectNeighborPawn(PCE, BLACK) || DefendedByBPawn(PCE)) { // Eros Gyalog

				score -= Open ? PawnConnectedOpen[7-rank] : PawnConnected[7-rank];

			} else {

				if (WhiteOpenFile(PCE) !== 0) { // Dupla Gyalog

					score -= Open ? PawnDoubledOpen[7-rank] : PawnDoubled[7-rank];
				}

				if (IsolatedBlackPawn(PCE) === 0) { // Elkulonitett Gyalog

					score -= Open ? PawnIsolatedOpen[7-rank] : PawnIsolated[7-rank];

				} else if (WeakPawn(PCE, rank, file, BLACK, WHITE)) { // Gyenge Gyalog

					score -= Open ? PawnBackwardOpen[7-rank] : PawnBackward[7-rank];
				}
			}

			if (Open && BlackPassedPawn(PCE) === 0) { // Telt Gyalog
				score -= PassedPawnBase[7-rank];
				if (rank <= RANKS.RANK_5) { // Fejlett
					PawnHashPassB[passIdx++] = PCE;
				}
			}
			score -= PAWN_VALUE;
			score -= PawnPst[PCE ^ 56];
			PCE = brd_pieceList[++pieceIdx];
		}

		PawnHashPassB[passIdx] = EMPTY; // wrap up

		return score;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function See(move, threshold) {

		var from = (move & 0x3F);
		var to = (move >> 6) & 0x3F;
		var promoted = (move >> 13) & 0xF;
		var fromPiece = CHESS_BOARD[from];
		var fromValue = SeeValue[fromPiece];
		var toValue = SeeValue[CHESS_BOARD[to]];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (promoted !== 0 // Bevaltas
		|| (fromPiece & 0x07) === KING // Kiraly -> isLegal..?
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

		from > 31 ? SeePieces.High ^= SetMask[from] // Tamado torlese
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

			while (from === EMPTY) // A ellenfel legkevesbe ertekes babuja..
			{
				provisory.Low  = SeePieces.Low; // Hack: SeePieces megorzese..
				provisory.High = SeePieces.High;

				for (pieceType = PAWN; pieceType <= KING; pieceType++)
				{
					if (bb = remaining.Low & BitBoard[(Side|pieceType) << 1 | LOW]) {
						from = firstBit(bb & -bb);
						remaining.Low ^= SetMask[from];
						provisory.Low ^= SetMask[from];
						break;
					}
					if (bb = remaining.High & BitBoard[(Side|pieceType) << 1 | HIGH]) {
						from = firstBit(bb & -bb) + 32;
						remaining.High ^= SetMask[from];
						provisory.High ^= SetMask[from];
						break;
					}
				}

				if (from === EMPTY) { // Nincs tobb tamado!
					break;
				}

				var Beyond = Behind(King, from); // Babu mogott megnyilo mezok!

				if (Beyond.Low | Beyond.High) // Felfedezett Sakk..?
				{
					if (IsSameLine(from, King)) {
						Beyond.Low  &= BitBoard[(them|ROOK) << 1 | LOW]  | BitBoard[(them|QUEEN) << 1 | LOW];
						Beyond.High &= BitBoard[(them|ROOK) << 1 | HIGH] | BitBoard[(them|QUEEN) << 1 | HIGH];
					} else {
						Beyond.Low  &= BitBoard[(them|BISHOP) << 1 | LOW]  | BitBoard[(them|QUEEN) << 1 | LOW];
						Beyond.High &= BitBoard[(them|BISHOP) << 1 | HIGH] | BitBoard[(them|QUEEN) << 1 | HIGH];
					}

					for (bb = Beyond.Low & provisory.Low; bb !== 0 && from !== EMPTY; bb &= bb - 1)
					{
						if (LineBlocker(firstBit(bb & -bb), King, provisory) === 0) from = EMPTY;
					}
					for (bb = Beyond.High & provisory.High; bb !== 0 && from !== EMPTY; bb &= bb - 1)
					{
						if (LineBlocker(firstBit(bb & -bb) + 32, King, provisory) === 0) from = EMPTY;
					}
				}
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (from === EMPTY) { // Nincs tobb tamado!
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

			from > 31 ? SeePieces.High ^= SetMask[from] // Tamado torlese
			          : SeePieces.Low  ^= SetMask[from];

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			SeeAddSliderAttacks(to, attackers, SeePieces, pieceType); // Mogotte
		}

		return CurrentPlayer !== Side; // curr !== side -> true
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

		if (lastAttacker === ROOK || lastAttacker === QUEEN) {
			var attacks = AttacksFrom(ROOK, target, Pieces);
			attackBB.Low  |= attacks.Low  & (BitBoard[wRookLow]  | BitBoard[bRookLow]  | BitBoard[wQueenLow]  | BitBoard[bQueenLow]);
			attackBB.High |= attacks.High & (BitBoard[wRookHigh] | BitBoard[bRookHigh] | BitBoard[wQueenHigh] | BitBoard[bQueenHigh]);
		}

		if (lastAttacker === PAWN || lastAttacker === BISHOP || lastAttacker === QUEEN) {
			var attacks = AttacksFrom(BISHOP, target, Pieces);
			attackBB.Low  |= attacks.Low  & (BitBoard[wBishopLow]  | BitBoard[bBishopLow]  | BitBoard[wQueenLow]  | BitBoard[bQueenLow]);
			attackBB.High |= attacks.High & (BitBoard[wBishopHigh] | BitBoard[bBishopHigh] | BitBoard[wQueenHigh] | BitBoard[bQueenHigh]);
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function GenerateAllMoves(capturesOnly) {

		var pieceType = 0; // Akivel lepunk
		var pieceIdx  = 0; // Babu indexeles
		var from      = 0; // Ahonnan lepunk
		var next      = 0; // Ahova lepunk
		var bb        = 0; // BitBoard

		brd_moveListEnd[BoardPly] = BoardPly << 8; // Hack

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var xPiecesBB = GetAllPce();
		var inc = CurrentPlayer ? 8 : -8;
		var enemy = AllPceBySide(CurrentPlayer^8);
		var StartRank   = CurrentPlayer ? RANKS.RANK_7 : RANKS.RANK_2;
		var PromoteRank = CurrentPlayer ? RANKS.RANK_2 : RANKS.RANK_7;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Gyalog lepesek
		pieceIdx = (CurrentPlayer|PAWN) << 4;
		from = brd_pieceList[pieceIdx];
		while (from !== EMPTY)
		{
			var rank = 7 - (from >> 3);

			next = from + inc; // Elore lepes

			if (capturesOnly === false) // Ures mezok
			{
				if (CHESS_BOARD[next] === 0) // Ures mezo
				{
					if (rank === PromoteRank) // Gyalog bevaltas
					{
						AddQuietMove(from, next, CurrentPlayer|QUEEN,  0, PAWN);
						AddQuietMove(from, next, CurrentPlayer|ROOK,   0, PAWN);
						AddQuietMove(from, next, CurrentPlayer|BISHOP, 0, PAWN);
						AddQuietMove(from, next, CurrentPlayer|KNIGHT, 0, PAWN);
					} else {
						AddQuietMove(from, next, 0, 0, PAWN); // Sima lepes

						if (rank === StartRank && CHESS_BOARD[next + inc] === 0) // Dupla lepes
						{
							AddQuietMove(from, next + inc, 0, 0, PAWN);
						}
					}
				}
			} else if (CHESS_BOARD[next] === 0 && rank === PromoteRank) { // Vezer Promocio (Quiescence)

				AddQuietMove(from, next, (CurrentPlayer|QUEEN), 0, PAWN);
			}

			for (bb = NeighbourMask[next]; bb !== 0; bb &= bb - 1) // Tamadasok
			{
				next = (next > 31 ? firstBit(bb & -bb) + 32 : firstBit(bb & -bb)); // from [+-] 7/9

				var boardSq = CHESS_BOARD[next];

				if (boardSq !== 0 && (boardSq & 0x8) !== CurrentPlayer) // Ellenfel
				{
					if (rank === PromoteRank) // Gyalog bevaltas
					{
						AddCaptureMove(from, next, CurrentPlayer|QUEEN,  boardSq, PAWN);
						AddCaptureMove(from, next, CurrentPlayer|ROOK,   boardSq, PAWN);
						AddCaptureMove(from, next, CurrentPlayer|BISHOP, boardSq, PAWN);
						AddCaptureMove(from, next, CurrentPlayer|KNIGHT, boardSq, PAWN);
					} else {
						AddCaptureMove(from, next, 0, boardSq, PAWN); // Nincs gyalogbevaltas
					}
				} else if (boardSq === 0 && EN_PASSANT !== 0 && EN_PASSANT === next) { // En Passant

					AddCaptureMove(from, next, 0, PAWN, PAWN);
				}
			}
			from = brd_pieceList[++pieceIdx];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (capturesOnly === false) // Sancolas: indulast es erkezest mashol ellenorizzuk!
		{
			if (CurrentPlayer === WHITE) // Feher oldal
			{
				if (CastleRights & CASTLEBIT.WK) { // Kiraly oldal
					if (CHESS_BOARD[SQUARES.F1] === 0 && CHESS_BOARD[SQUARES.G1] === 0) {
						if (!isSquareUnderAttack(SQUARES.F1, WHITE)) {
							AddQuietMove(SQUARES.E1, SQUARES.G1, 0, 1, KING);
						}
					}
				}
				if (CastleRights & CASTLEBIT.WQ) { // Vezer oldal
					if (CHESS_BOARD[SQUARES.D1] === 0 && CHESS_BOARD[SQUARES.C1] === 0 && CHESS_BOARD[SQUARES.B1] === 0) {
						if (!isSquareUnderAttack(SQUARES.D1, WHITE)) {
							AddQuietMove(SQUARES.E1, SQUARES.C1, 0, 1, KING);
						}
					}
				}

			} else { // Fekete oldal

				if (CastleRights & CASTLEBIT.BK) { // Kiraly oldal
					if (CHESS_BOARD[SQUARES.F8] === 0 && CHESS_BOARD[SQUARES.G8] === 0) {
						if (!isSquareUnderAttack(SQUARES.F8, BLACK)) {
							AddQuietMove(SQUARES.E8, SQUARES.G8, 0, 1, KING);
						}
					}
				}
				if (CastleRights & CASTLEBIT.BQ) { // Vezer oldal
					if (CHESS_BOARD[SQUARES.D8] === 0 && CHESS_BOARD[SQUARES.C8] === 0 && CHESS_BOARD[SQUARES.B8] === 0) {
						if (!isSquareUnderAttack(SQUARES.D8, BLACK)) {
							AddQuietMove(SQUARES.E8, SQUARES.C8, 0, 1, KING);
						}
					}
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Huszar, Futo, Bastya, Vezer, Kiraly
		for (pieceType = KNIGHT; pieceType <= KING; pieceType++)
		{
			pieceIdx = (CurrentPlayer|pieceType) << 4;
			from = brd_pieceList[pieceIdx];
			while (from !== EMPTY)
			{
				var attacks = AttacksFrom(pieceType, from, xPiecesBB);

				for (bb = attacks.Low & enemy.Low; bb !== 0; bb &= bb - 1) // Tamadas
				{
					next = firstBit(bb & -bb);

					AddCaptureMove(from, next, 0, CHESS_BOARD[next], pieceType);
				}
				for (bb = attacks.High & enemy.High; bb !== 0; bb &= bb - 1) // Tamadas
				{
					next = firstBit(bb & -bb) + 32;

					AddCaptureMove(from, next, 0, CHESS_BOARD[next], pieceType);
				}

				if (capturesOnly === false) // Ures mezok
				{
					for (bb = attacks.Low & ~xPiecesBB.Low; bb !== 0; bb &= bb - 1)
					{
						AddQuietMove(from, firstBit(bb & -bb), 0, 0, pieceType);
					}
					for (bb = attacks.High & ~xPiecesBB.High; bb !== 0; bb &= bb - 1)
					{
						AddQuietMove(from, firstBit(bb & -bb) + 32, 0, 0, pieceType);
					}
				}
				from = brd_pieceList[++pieceIdx];
			}
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function GenerateEvasions() {

		var bb     = 0; // BitBoard
		var next   = 0; // Ahova lepunk
		var from   = 0; // Ahonnan lepunk
		var checks = { Low : 0, High : 0 };
		var unsafe = { Low : 0, High : 0 };

		brd_moveListEnd[BoardPly] = BoardPly << 8; // Hack

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var them = CurrentPlayer^8;
		var xPiecesBB = GetAllPce();
		var friendsBB = AllPceBySide(CurrentPlayer);
		var King = brd_pieceList[(CurrentPlayer|KING) << 4];
		var front = CurrentPlayer === BLACK ? King + 8 : King - 8;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Gyalog tamadas
		front > 31
		? checks.High |= NeighbourMask[front] & BitBoard[(them|PAWN) << 1 | HIGH]
		: checks.Low  |= NeighbourMask[front] & BitBoard[(them|PAWN) << 1 | LOW];

		// Huszar tamadas
		var attacks = PceAttacks(KNIGHT, King);
		checks.Low  |= attacks.Low  & BitBoard[(them|KNIGHT) << 1 | LOW];
		checks.High |= attacks.High & BitBoard[(them|KNIGHT) << 1 | HIGH];

		// Futo, Bastya, Vezer tamadas
		for (bb = SliderAttackers(King, them, LOW); bb !== 0; bb &= bb - 1) {
			from = firstBit(bb & -bb);
			if (LineBlocker(from, King, xPiecesBB) === 0) {
				checks.Low  |= SetMask[from];
				unsafe.Low  |= BetweenBBMask[(from << 7) | (King << 1) | LOW]  | BehindBBMask[(from << 7) | (King << 1) | LOW];
				unsafe.High |= BetweenBBMask[(from << 7) | (King << 1) | HIGH] | BehindBBMask[(from << 7) | (King << 1) | HIGH];
			}
		}
		for (bb = SliderAttackers(King, them, HIGH); bb !== 0; bb &= bb - 1) {
			from = firstBit(bb & -bb) + 32;
			if (LineBlocker(from, King, xPiecesBB) === 0) {
				checks.High |= SetMask[from];
				unsafe.Low  |= BetweenBBMask[(from << 7) | (King << 1) | LOW]  | BehindBBMask[(from << 7) | (King << 1) | LOW];
				unsafe.High |= BetweenBBMask[(from << 7) | (King << 1) | HIGH] | BehindBBMask[(from << 7) | (King << 1) | HIGH];
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Kiraly lepesei
		attacks = PceAttacks(KING, King);
		for (bb = attacks.Low & ~unsafe.Low & ~friendsBB.Low; bb !== 0; bb &= bb - 1) {

			if (CHESS_BOARD[next = firstBit(bb & -bb)] !== 0) // Ellenfel
			{
				AddCaptureMove(King, next, 0, CHESS_BOARD[next], KING);
			} else {
				AddQuietMove(King, next, 0, 0, KING); // Ures mezo
			}
		}
		for (bb = attacks.High & ~unsafe.High & ~friendsBB.High; bb !== 0; bb &= bb - 1) {

			if (CHESS_BOARD[next = firstBit(bb & -bb) + 32] !== 0) // Ellenfel
			{
				AddCaptureMove(King, next, 0, CHESS_BOARD[next], KING);
			} else {
				AddQuietMove(King, next, 0, 0, KING); // Ures mezo
			}
		}

		if (PopCount64(checks.Low, checks.High) > 1) return; // Dupla Sakknal csak a Kiraly lephet :(

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var checkSQ = checks.Low ? firstBit(checks.Low & -checks.Low) : firstBit(checks.High & -checks.High) + 32;
		var target = { // Kiraly es az egyetlen tamado kozotti mezok + tamado!
		Low  : BetweenBBMask[(checkSQ << 7) | (King << 1) | LOW]  | checks.Low,
		High : BetweenBBMask[(checkSQ << 7) | (King << 1) | HIGH] | checks.High };

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Gyalog lepesek
		var inc = CurrentPlayer ? 8 : -8;
		var StartRank   = CurrentPlayer ? RANKS.RANK_7 : RANKS.RANK_2;
		var PromoteRank = CurrentPlayer ? RANKS.RANK_2 : RANKS.RANK_7;
		var pieceIdx = (CurrentPlayer|PAWN) << 4;
		from = brd_pieceList[pieceIdx];
		while (from !== EMPTY)
		{
			var rank = 7 - (from >> 3);

			next = from + inc; // Elore lepes

			if (CHESS_BOARD[next] === 0) // Ures mezo
			{
				bb = next > 31 ? target.High : target.Low;

				if (bb & SetMask[next]) // Blokkolas
				{
					if (rank === PromoteRank) // Gyalog bevaltas
					{
						AddQuietMove(from, next, (CurrentPlayer|QUEEN), 0, PAWN);
						AddQuietMove(from, next, (CurrentPlayer|ROOK),  0, PAWN);
						AddQuietMove(from, next, (CurrentPlayer|BISHOP), 0, PAWN);
						AddQuietMove(from, next, (CurrentPlayer|KNIGHT), 0, PAWN);
					} else {
						AddQuietMove(from, next, 0, 0, PAWN); // Sima lepes
					}
				}
				// Blokkolas dupla lepessel
				else if ((bb & SetMask[next + inc]) && rank === StartRank && CHESS_BOARD[next + inc] === 0)
				{
					AddQuietMove(from, next + inc, 0, 0, PAWN);
				}
			}

			for (bb = NeighbourMask[next]; bb !== 0; bb &= bb - 1) // Tamadasok
			{
				next = next > 31 ? firstBit(bb & -bb) + 32 : firstBit(bb & -bb); // from [+-] 7/9

				if (next === checkSQ) // Sakkado babu tamadasa
				{
					var boardSq = CHESS_BOARD[next];

					if (rank === PromoteRank) // Gyalog bevaltas
					{
						AddCaptureMove(from, next, CurrentPlayer|QUEEN,  boardSq, PAWN);
						AddCaptureMove(from, next, CurrentPlayer|ROOK,   boardSq, PAWN);
						AddCaptureMove(from, next, CurrentPlayer|BISHOP, boardSq, PAWN);
						AddCaptureMove(from, next, CurrentPlayer|KNIGHT, boardSq, PAWN);
					} else {
						AddCaptureMove(from, next, 0, boardSq, PAWN); // Nincs gyalogbevaltas
					}
				} else if (EN_PASSANT !== 0 && EN_PASSANT === next && (EN_PASSANT - inc) === checkSQ) { // En Passant

					AddCaptureMove(from, next, 0, PAWN, PAWN);
				}
			}
			from = brd_pieceList[++pieceIdx];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Huszar, Futo, Bastya, Vezer (Kiralyt nem nezzuk ujra!)
		for (var pieceType = KNIGHT; pieceType <= QUEEN; pieceType++)
		{
			pieceIdx = (CurrentPlayer|pieceType) << 4;
			from = brd_pieceList[pieceIdx];
			while (from !== EMPTY)
			{
				attacks = AttacksFrom(pieceType, from, xPiecesBB);

				for (bb = attacks.Low & target.Low; bb !== 0; bb &= bb - 1) // Tamadas & Blokkolas
				{
					next = firstBit(bb & -bb);

					if (next === checkSQ) // Sakkado babu tamadasa
					{
						AddCaptureMove(from, next, 0, CHESS_BOARD[next], pieceType);
					} else {
						AddQuietMove(from, next, 0, 0, pieceType); // Blokkolas
					}
				}
				for (bb = attacks.High & target.High; bb !== 0; bb &= bb - 1) // Tamadas & Blokkolas
				{
					next = firstBit(bb & -bb) + 32;

					if (next === checkSQ) // Sakkado babu tamadasa
					{
						AddCaptureMove(from, next, 0, CHESS_BOARD[next], pieceType);
					} else {
						AddQuietMove(from, next, 0, 0, pieceType); // Blokkolas
					}
				}
				from = brd_pieceList[++pieceIdx];
			}
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function AddQuietMove(from, to, prom, castle, piece) {
		var moveIndex = brd_moveListEnd[BoardPly]++; // Hack: refer to prev value!
		var move = (from | (to << 6) | (prom << 13) | (castle << 17)); // aka BIT_MOVE
		var score = 0;
		if (prom !== 0) { // Gyalog bevaltas
			score = 7000 + prom;
		} else if (SearchKillers[(BoardPly << 1) | 0] === move) { // Gyilkos lepes 1.
			score = 6000;
		} else if (SearchKillers[(BoardPly << 1) | 1] === move) { // Gyilkos lepes 2.
			score = 5000;
		} else {
			score = 1000 + HistoryTable[((CurrentPlayer|piece) << 6) | to]; // Elozmeny
		}
		brd_moveList[moveIndex] = move;
		brd_moveScores[moveIndex] = score;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function AddCaptureMove(from, to, prom, captured, piece) {
		var moveIndex = brd_moveListEnd[BoardPly]++; // Hack: refer to prev value!
		brd_moveList[moveIndex] = (from | (to << 6) | (1 << 12) | (prom << 13)); // aka BIT_MOVE
		brd_moveScores[moveIndex] = 8006 + (captured & 0x07) * 100 - piece;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function PickNextMove(moveNum, moveListEnd, useSee) {
		var bestNum = moveNum;
		var bestScore = brd_moveScores[bestNum];
		for (var index = moveNum; index < moveListEnd; index++) {
			var moveScore = brd_moveScores[index];
			if (moveScore <= bestScore) continue;
			if (useSee && moveScore > 8000 && moveScore < 10000 && !See(brd_moveList[index])) { // bad
				brd_moveScores[index] = moveScore -= 8000;
				if (moveScore <= bestScore) continue;
			}
			bestScore = moveScore;
			bestNum = index;
		}
		var bestMove = brd_moveList[bestNum];
		if (bestNum !== moveNum) {
			brd_moveList  [bestNum] = brd_moveList  [moveNum];
			brd_moveScores[bestNum] = brd_moveScores[moveNum];
			brd_moveList  [moveNum] = bestMove;
			brd_moveScores[moveNum] = bestScore;
		}
		return bestMove;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function CheckTime() {
		var elapsedTime = Date.now() - StartTime;
		if (CurrDepth >= 2 && elapsedTime >= MinSearchTime) {
			if (!ScoreDrop || elapsedTime >= MaxSearchTime) {
				TimeStop = 1;
			}
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function Quiescence(alpha, beta, depth, inCheck) {

		Nodes++; // Csomopontok novelese

		var pvIdx = BoardPly << 6;

		PvLineMoves[pvIdx] = NOMOVE;

		if ((Nodes & 511) === 0) { // Ido check
			CheckTime();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (IsRepetition(inCheck)) { // Lepesismetles
			return 0;
		}

		if (BoardPly >= MaxDepth) { // Melyseg limit
			return Evaluation();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var bestScore  = -INFINITE;
		var staticEval = -INFINITE;

		if (inCheck || depth === DEPTH_ZERO) { // Atultetesi tabla

			var hashData = ProbeHash();

			if (hashData !== NOMOVE) {

				staticEval = hashData.eval;
				var value = hashData.score;

				if (value > ISMATE) {
					value -= BoardPly;
				} else if (value < -ISMATE) {
					value += BoardPly;
				}

				if (hashData.flags === FLAG_UPPER && value <= alpha) return value;
				if (hashData.flags === FLAG_LOWER && value >= beta)  return value;
				if (hashData.flags === FLAG_EXACT) return value;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (!inCheck) {

			if ((bestScore = staticEval) === -INFINITE) { // Ertekeles
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

		var is_pv = (beta !== alpha + 1);
		var oldAlpha = alpha; // Alpha mentese
		var bestMove = NOMOVE; // Legjobb lepes
		var score = -INFINITE; // Pont nullazas
		var capturedPCE = NOMOVE; // Leutott babu
		var currentMove = NOMOVE; // Aktualis lepes
		var willCheck = NOT_IN_CHECK; // Sakk lepes
		var deltaMargin = bestScore + 100; // Delta margo
		inCheck ? GenerateEvasions() : GenerateAllMoves(true);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var index = (BoardPly << 8), moveListEnd = brd_moveListEnd[BoardPly]; index < moveListEnd; index++)
		{
			currentMove = PickNextMove(index, moveListEnd, false);
			willCheck   = givesCheck(currentMove);

			if (!inCheck && !willCheck && PROMOTED(currentMove) === 0) // Delta metszes
			{
				capturedPCE = CHESS_BOARD[TOSQ(currentMove)] & 0x07;
				if (capturedPCE !== QUEEN) {
					var futileValue = deltaMargin + DeltaValue[capturedPCE || PAWN]; // En Passant..?
					if (futileValue <= alpha) {
						if (bestScore < futileValue)
							bestScore = futileValue;
						continue;
					}
				}
			}

			if (!inCheck && !See(currentMove)) { // Rossz utes
				continue;
			}

			if (!isLegal(currentMove)) { // Ervenytelen lepes
				continue;
			}

			makeMove(currentMove); // Lepes ervenyesitese

			score = -Quiescence(-beta, -alpha, depth-1, willCheck);

			unMakeMove(); // Lepes visszavonasa

			if (score > bestScore) {
				bestScore = score;
				if (score > alpha) {
					if (is_pv) {
						BuildPv(currentMove, pvIdx);
					}
					if (score >= beta) {
						if (inCheck || depth === DEPTH_ZERO) {
							StoreHash(currentMove, bestScore, staticEval, FLAG_LOWER, DEPTH_ZERO);
						}
						return score;
					}
					alpha = score;
					bestMove = currentMove;
				}
			}
		}

		if (inCheck && score === -INFINITE) { // Matt
			return -INFINITE + BoardPly;
		}

		if (inCheck || depth === DEPTH_ZERO) {
			StoreHash(bestMove, bestScore, staticEval, (alpha !== oldAlpha ? FLAG_EXACT : FLAG_UPPER), DEPTH_ZERO);
		}

		return bestScore;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function AlphaBeta(alpha, beta, depth, nullMove, inCheck) {

		if (depth <= DEPTH_ZERO) { // Melyseg eleresekor kiertekeles
			return Quiescence(alpha, beta, DEPTH_ZERO, inCheck);
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		Nodes++; // Csomopontok novelese

		var pvIdx = BoardPly << 6;

		PvLineMoves[pvIdx] = NOMOVE;

		if ((Nodes & 511) === 0) { // Ido check
			CheckTime();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (BoardPly > 0) { // Gyermek csomopont

			if (TimeStop === 1) { // Ido vagas
				return 0;
			}

			if (IsRepetition(inCheck)) { // Lepesismetles
				return GetDrawValue();
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

		var score = -INFINITE;
		var staticEval = -INFINITE;
		var is_pv = (beta !== alpha + 1);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var hashData = ProbeHash(); // Atultetesi tabla
		var hashMove = hashData !== NOMOVE ? hashData.move : NOMOVE;

		if (hashData !== NOMOVE) {

			staticEval = hashData.eval;

			if (!is_pv && hashData.depth >= depth) {

				var value = hashData.score;

				if (value > ISMATE) {
					value -= BoardPly;
				} else if (value < -ISMATE) {
					value += BoardPly;
				}

				if (hashData.flags === FLAG_UPPER && value <= alpha) return value;
				if (hashData.flags === FLAG_LOWER && value >= beta)  return value;
				if (hashData.flags === FLAG_EXACT) return value;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var pruneNode = !is_pv && !inCheck // Metszheto csomopont..?
		&& (brd_pieceCount[CurrentPlayer | KNIGHT] !== 0
		 || brd_pieceCount[CurrentPlayer | BISHOP] !== 0
		 || brd_pieceCount[CurrentPlayer | ROOK]   !== 0
		 || brd_pieceCount[CurrentPlayer | QUEEN]  !== 0);

		if (staticEval === -INFINITE && pruneNode && (nullMove || depth <= 4)) { // Futility depth
			staticEval = Evaluation();
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (pruneNode && nullMove && !isMate(beta)) // Metszesek
		{
			if (depth <= 3 && (score = staticEval - 100 * depth) >= beta && PawnOnSeventh() === 0) {
				return score;
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (depth >= 2 && staticEval >= beta) // Null lepes
			{
				makeNullMove();

				score = -AlphaBeta(-beta, -beta+1, depth-4-(depth >> 3), 0, NOT_IN_CHECK);

				unMakeNullMove();

				if (TimeStop === 1) { // Ido vagas
					return 0;
				}

				if (score >= beta && !isMate(score)) {
					return score;
				}
			}

			// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

			if (depth <= 2 && hashMove === NOMOVE && staticEval + 300 * depth < beta && PawnOnSeventh() === 0) {
				score = Quiescence(alpha, beta, DEPTH_ZERO, NOT_IN_CHECK);
				if (score < beta) { // Razor
					return score;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (is_pv && BoardPly > 0 && depth >= 4 && hashMove === NOMOVE) { // Belso iterativ melyites /IID/
			score = AlphaBeta(alpha, beta, depth-2, 0, inCheck);
			if (score > alpha) hashMove = PvLineMoves[pvIdx];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		score = -INFINITE; // Pont nullazas
		var R = 0; // LMR Dinamikus valtozo
		var legalMove = 0; // Ervenyes lepes
		var moveScore = 0; // Lepes pontszama
		var oldAlpha = alpha; // Alpha mentese
		var bestMove = NOMOVE; // Legjobb lepes
		var dangerous = false; // Veszelyes..??
		var willCheck = NOT_IN_CHECK; // Sakk lepes
		var currentMove = NOMOVE; // Aktualis lepes
		var bestScore = -INFINITE; // Legjobb pontszam
		var E = (is_pv || depth < 5) && inCheck; // Sakk++
		var futileValue = staticEval + depth * 100; // Futile
		inCheck ? GenerateEvasions() : GenerateAllMoves(false);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var moveListStart = BoardPly << 8;
		var moveListEnd = brd_moveListEnd[BoardPly];
		if (hashMove !== NOMOVE) { // Atultetesi tablabol lepes
			for (var index = moveListStart; index < moveListEnd; index++) {
				if (brd_moveList[index] === hashMove) { // Elore soroljuk
					if (index !== moveListStart) {
						brd_moveList[index] = brd_moveList[moveListStart];
						brd_moveScores[index] = brd_moveScores[moveListStart];
						brd_moveList[moveListStart] = hashMove;
					}
					brd_moveScores[moveListStart] = 10000;
					break;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var index = moveListStart; index < moveListEnd; index++)
		{
			currentMove = PickNextMove(index, moveListEnd, !inCheck);
			moveScore = brd_moveScores[index];
			willCheck = givesCheck(currentMove);

			dangerous = inCheck || willCheck || moveScore >= 5000 || (currentMove & DANGER_MASK) || PawnPush(currentMove);

			if (!dangerous && depth <= 2 && pruneNode && !isMate(bestScore) && legalMove > 5 * depth) { // Late Move Pruning
				continue;
			}

			if (!dangerous && depth <= 4 && pruneNode && !isMate(bestScore) && futileValue <= alpha) { // Futility Pruning
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

			R = (dangerous || depth <= 2 || legalMove <= 2) // Late Move Reduction
			? 0
			: is_pv
			? Math.min(Math.log(depth) * Math.log(legalMove) * 0.33 | 0, depth-2)
			: Math.min(Math.log(depth) * Math.log(legalMove) * 0.66 | 0, depth-2);

			if ((is_pv && legalMove !== 0) || R !== 0) {
				score = -AlphaBeta(-alpha-1, -alpha, depth+E-R-1, 1, willCheck); // PVS-LMR
				if (score > alpha) {
					score = -AlphaBeta(-beta, -alpha, depth+E-1, 1, willCheck); // Full
				}
			} else {
				score = -AlphaBeta(-beta, -alpha, depth+E-1, 1, willCheck); // Full
			}

			unMakeMove(); // Lepes visszavonasa

			if (TimeStop === 1) { // Ido vagas
				return 0;
			}

			PlayedMoves[moveListStart | legalMove++] = currentMove; // History

			if (BoardPly === 0) { // Elemzeshez
				RootMovesResult[currentMove] = { score: score, depth: depth };
			}

			if (score > bestScore) {

				bestScore = score;

				if (is_pv && (legalMove === 1 || score > alpha)) {

					BuildPv(currentMove, pvIdx);

					if (BoardPly === 0) {
						UpdatePv(currentMove, score, depth, alpha, beta, pvIdx);
					}
				}

				if (score > alpha) {
					if (score >= beta) {
						if (!inCheck && (currentMove & TACTICAL_MASK) === 0) { // Update Killers & History
							if (SearchKillers[(BoardPly << 1) | 0] !== currentMove) {
								SearchKillers[(BoardPly << 1) | 1] = SearchKillers[(BoardPly << 1) | 0];
								SearchKillers[(BoardPly << 1) | 0] = currentMove;
							}
							HistoryGood(currentMove);

							for (var h = 0; h < legalMove-1; h++) {
								HistoryBad(PlayedMoves[moveListStart | h]);
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

		if (legalMove === 0) {
			return inCheck ? -INFINITE + BoardPly : 0; // Matt : patt
		}

		StoreHash(bestMove, bestScore, staticEval, (alpha !== oldAlpha ? FLAG_EXACT : FLAG_UPPER), depth);

		return bestScore;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function HistoryGood(move) {
		var idx = (CHESS_BOARD[(move & 0x3F)] << 6) | ((move >> 6) & 0x3F);
		HistoryTable[idx] += (2048 - HistoryTable[idx]) >> 5;
	}

	function HistoryBad(move) {
		if ((move & TACTICAL_MASK) === 0) {
			var idx = (CHESS_BOARD[(move & 0x3F)] << 6) | ((move >> 6) & 0x3F);
			HistoryTable[idx] -= HistoryTable[idx] >> 5;
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function InitEnginSearch() {
		HashDate = 0; // Hash ido tag nullazas
		HashUsed = 0; // Hash hasznalat nullazas
		EvalHashEval.fill(0); EvalHashLock.fill(0);
		PawnHashEval.fill(0); PawnHashLock.fill(0);
		PawnHashPassW.fill(EMPTY); PawnHashPassB.fill(EMPTY);
		HashTablePkg1.length === HASH_ENTRIES ? HashTablePkg1.fill(0) : HashTablePkg1 = new Int32Array(HASH_ENTRIES);
		HashTablePkg2.length === HASH_ENTRIES ? HashTablePkg2.fill(0) : HashTablePkg2 = new Int32Array(HASH_ENTRIES);
		HashTableLock.length === HASH_ENTRIES ? HashTableLock.fill(0) : HashTableLock = new Int32Array(HASH_ENTRIES);
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function ClearForSearch() {
		Nodes = 0;
		HashUsed = 0;
		BoardPly = 0;
		BestMove = 0;
		TimeStop = 0;
		ScoreDrop = 0;
		HistoryTable.fill(1024);
		SearchKillers.fill(NOMOVE);
		HashDate = (HashDate + 1) & 15; // 0-15
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function ClearForNewGame() {
		BoardPly = 0;
		MoveCount = 0;
		brd_fiftyMove = 0;
		MOVE_HISTORY.splice(0);
		HIDDEN_HISTORY.fill(0);
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function SearchPosition(maxSearchDepth) {

		ClearForSearch();
		RootMovesResult = {};
		StartTime = Date.now();
		var alpha = -INFINITE;
		var beta = INFINITE;
		var countMove = 0;
		var score = 0;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (UI_HOST === HOST_TANKY) sendMessage('startedtime '+StartTime);
		if (UI_HOST === HOST_TANKY && maxSearchDepth > 0) { // Also szint
			MaxDepth = maxSearchDepth;
		} else {
			MaxDepth = 64;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var inCheck = isCheck(CurrentPlayer); // Sakk..?

		inCheck ? GenerateEvasions() : GenerateAllMoves(false);

		for (var index = 0; index < brd_moveListEnd[0]; index++) {
			if (isLegal(brd_moveList[index])) { // Ervenyes lepes
				if (++countMove > 1) break;
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		PvLineMoves.fill(NOMOVE); // Nullazas

		search :

		for (CurrDepth = 1; CurrDepth <= maxSearchDepth; CurrDepth++) { // Iterativ melyites

			if (countMove === 1 && CurrDepth > 5 && BestMove) break; // Egy ervenyes lepes

			for (var margin = (CurrDepth >= 4 ? 10 : INFINITE); ; margin *= 2) { // ablak

				CheckTime(); // FONTOS: (Nodes & 511) !== 0

				alpha = Math.max(score - margin, -INFINITE);
				beta  = Math.min(score + margin,  INFINITE);

				score = AlphaBeta(alpha, beta, CurrDepth, 1, inCheck);

				if (TimeStop === 1) break search; // Lejart az ido

				if (isMate(score)) break; // Matt pontszam

				if (score > alpha && score < beta) break;
			}

			if (BestMove !== NOMOVE) { // frissites
				BestMove.lastMove  = BestMove.move;
				BestMove.lastScore = BestMove.score;
			}
		}

		sendMessage('bestmove '+FormatMove(BestMove.move));
		sendMessage('info hashfull '+Math.round(HashUsed / HASH_ENTRIES * 1000));
		if (UI_HOST === HOST_TANKY) {
			sendMessage('best4rootmoves '+JSON.stringify(GetBest4RootMoves()));
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function GetBest4RootMoves() {
		return Object.keys(RootMovesResult)
		.map(function(x) {
			return {
				move: FormatMove(x),
				score: RootMovesResult[x].score,
				depth: RootMovesResult[x].depth
			};
		}).sort(function(a, b) {
			return b.score - a.score;
		}).slice(0, 4);
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function UpdatePv(move, score, depth, alpha, beta, idx) {

		var flags = FLAG_NONE;
		if (score > alpha) flags |= FLAG_LOWER;
		if (score < beta)  flags |= FLAG_UPPER;

		ScoreDrop = depth > 1 && (flags === FLAG_UPPER || BestMove.lastScore - 20 >= score);

		if (BestMove === NOMOVE) { // first
			BestMove = { move, score, depth, flags, lastMove: move, lastScore: score };
		} else {
			BestMove.move  = move;
			BestMove.score = score;
			BestMove.depth = depth;
			BestMove.flags = flags;
		}

		var time = Date.now() - StartTime;

		var pvLine = '';
		for (var index = idx; PvLineMoves[index] !== NOMOVE; index++) {
			pvLine += ' '+FormatMove(PvLineMoves[index]);
		}

		if (score < -ISMATE) {
			score = 'mate '+((-INFINITE - score) / 2); // -Matt
		} else if (score > ISMATE) {
			score = 'mate '+((INFINITE - score + 1) / 2); // +Matt
		} else {
			score = 'cp '+score;
		}

		if (flags === FLAG_LOWER) score += ' lowerbound';
		if (flags === FLAG_UPPER) score += ' upperbound';

		sendMessage('info currmove '+FormatMove(move)+' depth '+depth+' score '+score+' nodes '+Nodes+' time '+time+' pv'+pvLine);
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function BuildPv(move, idx) {
		PvLineMoves[idx] = move;
		for (var i = idx; (PvLineMoves[i+1] = PvLineMoves[i+MaxDepth]) !== NOMOVE; i++);
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function sendMessage(msg) {
		if (UI_HOST === HOST_NODEJS) { // Node.js
			nodefs.writeSync(1, msg+'\n');
		} else if (UI_HOST !== HOST_WEB) { // Worker, JSUCI
			postMessage(msg);
		} else if (typeof console !== 'undefined') {
			console.log(msg);
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	var HOST_WEB    = 0;
	var HOST_TANKY  = 1;
	var HOST_JSUCI  = 2;
	var HOST_NODEJS = 3;
	var HOST_WORKER = 4;
	var UI_HOST = HOST_WEB;

	if (typeof WorkerGlobalScope !== 'undefined') { // Worker

		UI_HOST = HOST_WORKER;

	} else if (typeof process !== 'undefined') { // Node.js

		UI_HOST = HOST_NODEJS;
		var nodefs = require('fs');
		process.stdin.setEncoding('utf8');
		process.stdin.on('data', function(data) {
			onMessage({data: data});
		});
		process.stdin.on('end', function() {
			process.exit();
		});

	} else if (typeof lastMessage !== 'undefined') { // JSUCI

		UI_HOST = HOST_JSUCI;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	var uci_options = { 'Hash': '16' };

	var onMessage = function(command) {

		if (command !== null && command.data !== undefined && typeof command.data === "string")
		{
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

				if (command === 'u') command = 'ucinewgame';

				if (command === 'b') command = 'board';

				if (command === 'q') command = 'quit';

				if (command === 'p') {
					command = 'position';
					if (tokens[1] === 's') {
						tokens[1] = 'startpos';
					}
				}

				if (command === 'g') {
					command = 'go';
					if (tokens[1] === 'd') {
						tokens[1] = 'depth';
					}
				}

				// ############################################################################################

				switch (command) {

					case 'tankyworker':

						UI_HOST = HOST_TANKY;

					break;

					case 'ucinewgame':

						InitEnginSearch(); // Engine Init
						if (SideKeyLow === 0) InitHashKeys();

					break;

				// ############################################################################################

					case 'position':

						if (SideKeyLow === 0) { // Nincs HashKey
							return sendMessage('info string First send a "u" command for New Game!');
						}

						ClearForNewGame(); // Valtozok nullazasa

						START_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1';

						var arr = getArr('fen', 'moves', tokens); // FEN parameterek

						if (arr.lo > 0) {
							if (arr.lo <= arr.hi) START_FEN  =     tokens[arr.lo++]; // CHESS_BOARD
							if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo++]; // CurrentPlayer
							if (arr.lo <= arr.hi) START_FEN += ' '+tokens[arr.lo++]; // CastleRights
							START_FEN += ' '+((arr.lo <= arr.hi) ? tokens[arr.lo++] : '-'); // En Passant
							START_FEN += ' '+((arr.lo <= arr.hi) ? tokens[arr.lo++] : '0'); // 50 move
							START_FEN += ' '+((arr.lo <= arr.hi) ? tokens[arr.lo++] : '1'); // Full move
						}

						FENToBoard(); // CHESS_BOARD, BitBoard, HashKey, NN init..

						var arr = getArr('moves', 'fen', tokens); // Lepesek

						if (arr.lo > 0 && tokens[arr.lo] != undefined) {
							for (var index = arr.lo; index <= arr.hi; index++) {
								makeMove(GetMoveFromString(tokens[index]));
								BoardPly = 0; // reset after makeMove..
							}
						}

					break;

				// ############################################################################################

					case 'go':

						var fixDepth = getInt('depth', 0, tokens);
						MinSearchTime = getInt('movetime', 0, tokens);

						if (MinSearchTime === 0) // Smart search..
						{
							var movesToGo = getInt('movestogo', 30, tokens);
							if (movesToGo > 30 || movesToGo <= 0) { // Limit
								movesToGo = 30;
							}

							if (CurrentPlayer === WHITE) {
								var inc  = getInt('winc' , 0, tokens);
								var time = getInt('wtime', 0, tokens);
							} else {
								var inc  = getInt('binc' , 0, tokens);
								var time = getInt('btime', 0, tokens);
							}

							var reserve = Math.min(1000, Math.max(50, time / 10));
							time = Math.max(time - reserve, 0); // min 50ms for lag
							var total = time + inc * (movesToGo - 1);
							var alloc = total / movesToGo;
							var limit = Math.max(total * 0.5, alloc);
							MinSearchTime = Math.min(alloc, time) | 0;
							MaxSearchTime = Math.min(limit, time) | 0;

							if (fixDepth > 0 && MinSearchTime === 0) // Nincs ido + fix melyseg..
							{
								MinSearchTime = 1000 * 3600; // 1 hour
							}
						}
						else // Fix ido..
						{
							MaxSearchTime = MinSearchTime;
						}

						if (fixDepth > 64 || fixDepth <= 0) { // Limit
							fixDepth = 64;
						}

						SearchPosition(fixDepth); // Kereses..

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

						if (key === 'Hash' && val != uci_options[key] && val >= 1) {

							if (restBit(val) !== 0) break; // Hash must be power of 2

							HASH_ENTRIES = (val << 20) / 16;
							HASH_MASK = (HASH_ENTRIES - 1) & -CLUSTER_SIZE;
							uci_options[key] = val;
							InitEnginSearch();

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

					case 'board':

						sendMessage('board '+boardToFEN());

					break;

				// ############################################################################################

					case 'stop':

						TimeStop = 1; // TODO: separate worker needed for NodeJS

					break;

				// ############################################################################################

					case 'quit':

						if (UI_HOST === HOST_NODEJS) process.exit();

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

	if (typeof self !== 'undefined') {
		self.onmessage = onMessage;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function GetGamePhase() {
		return 24 - (
			  brd_pieceCount[WHITE_KNIGHT] + brd_pieceCount[BLACK_KNIGHT]
			+ brd_pieceCount[WHITE_BISHOP] + brd_pieceCount[BLACK_BISHOP]
			+(brd_pieceCount[WHITE_ROOK  ] + brd_pieceCount[BLACK_ROOK  ]) * 2
			+(brd_pieceCount[WHITE_QUEEN ] + brd_pieceCount[BLACK_QUEEN ]) * 4
		);
	}

	function Interpolation(mg, eg, phase) {
		if (phase < 0) phase = 0;
		return (mg * (24 - phase) + eg * phase) / 24 | 0;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function FormatMove(move) {

		if (move === NOMOVE) return 'NULL';

		var retS = '';
		var from = (move & 0x3F);
		var to = (move >> 6) & 0x3F;
		var prom = (move >> 13) & 0xF;
		var rank1 = 7 - (from >> 3);
		var rank2 = 7 - (to   >> 3);

		retS += Letters[from & 0x07]+''+(rank1 + 1); // honnan
		retS += Letters[to   & 0x07]+''+(rank2 + 1); // hova

		if (prom !== 0) { // promocio
			retS += ['', '', 'n', 'b', 'r', 'q', ''][prom & 0x07];
		}

		return retS;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function GetMoveFromString(moveString) {
		moveString = moveString.toUpperCase();
		var promote = 0, capture = 0, castling = 0;
		var from = SQUARES[moveString.substr(0, 2)];
		var to   = SQUARES[moveString.substr(2, 2)];
		var pieceType = CHESS_BOARD[from] & 0x07;
		if (pieceType === KING && Math.abs(from - to) === 2 ? 1 : 0) {
			castling = 1;
		} else if (CHESS_BOARD[to] !== 0) {
			capture = 1;
		} else if (pieceType === PAWN && to === EN_PASSANT && EN_PASSANT !== 0) {
			capture = 1;
		}
		switch (moveString.charAt(4)) {
			case 'N': promote = CurrentPlayer|KNIGHT; break;
			case 'B': promote = CurrentPlayer|BISHOP; break;
			case 'R': promote = CurrentPlayer|ROOK; break;
			case 'Q': promote = CurrentPlayer|QUEEN; break;
		}
		return BIT_MOVE(from, to, capture, promote, castling);
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

		BitBoard.fill(0);
		brd_pieceCount.fill(0);
		brd_pieceIndex.fill(0);
		brd_pieceList.fill(EMPTY);

		for (var sq = 0; sq < 64; sq++)
		{
			if (CHESS_BOARD[sq] !== 0) {
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
			if (CHESS_BOARD[sq] !== 0) {
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

		if (EN_PASSANT !== 0) { // En Passant
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

		if (CastleRights === 0) { // Nincs sancolas
			FEN += ' -';
		} else {
			FEN += ' '; // Szokoz hozzadasa
			if (CastleRights & CASTLEBIT.WK) FEN += 'K'; // White King side
			if (CastleRights & CASTLEBIT.WQ) FEN += 'Q'; // White Queen side
			if (CastleRights & CASTLEBIT.BK) FEN += 'k'; // Black King side
			if (CastleRights & CASTLEBIT.BQ) FEN += 'q'; // Black Queen side
		}

		if (EN_PASSANT === 0) { // Nincs En Passant
			FEN += ' -';
		} else {
			FEN += ' '+(Letters[SquareFile(EN_PASSANT)]+''+(SquareRank(EN_PASSANT)+1));
		}

		FEN += ' '+brd_fiftyMove; // 50 lepes
		FEN += ' '+(1 + (MoveCount - (CurrentPlayer === BLACK)) / 2); // Lepespar

		return FEN;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// FEN -> CHESS_BOARD
	function FENToBoard(fenParam) {

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

		var chessBoard = [];

		var Fen = (fenParam || START_FEN).split(' ');

		for (var index = 0; index < Fen[0].length; index++)
		{
			var value = Fen[0][index];
			if (value === '/') {
				continue;
			}

			if (isNaN(value)) { // Babuk feltoltese
				chessBoard.push(pieceValueMap[value]);
			} else {
				for (var j = 0; j < parseInt(value, 10); j++) { // Ures mezok
					chessBoard.push(0);
				}
			}
		}

		if (fenParam) // only for testing..
		{
			return new Int8Array(chessBoard);
		}

		for (index = 0; index < chessBoard.length; index++) {
			CHESS_BOARD[index] = chessBoard[index]; // copy..
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

		InitChessNN(); // Halozat inicializalasa
		InitPieceList(); // Babuk inicializalasa

		EN_PASSANT = 0; // En Passant nullazas!

		if (Fen[3] !== '-') { // En Passant csak ha tamadja gyalog
			var epSq = parseInt(SQUARES[Fen[3].toUpperCase()]);
			if (CurrentPlayer ? DefendedByBPawn(epSq) : DefendedByWPawn(epSq)) {
				EN_PASSANT = epSq;
			}
		}

		brd_fiftyMove = Fen[4] != null ? Fen[4] : 0; // 50 lepes

		GenerateHashKey(); // HashKey generalasa

		return CHESS_BOARD;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Sancolas
	var CastlePerm = new Int8Array([
	 11,  15,  15,  15,   3,  15,  15,   7,
	 15,  15,  15,  15,  15,  15,  15,  15,
	 15,  15,  15,  15,  15,  15,  15,  15,
	 15,  15,  15,  15,  15,  15,  15,  15,
	 15,  15,  15,  15,  15,  15,  15,  15,
	 15,  15,  15,  15,  15,  15,  15,  15,
	 15,  15,  15,  15,  15,  15,  15,  15,
	 14,  15,  15,  15,  12,  15,  15,  13
	]);

	// Huszar "orszem"
	var KnightOutpost = new Int32Array([
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0),
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0),
	S(  0,   0), S(  0,   0), S(  4,   0), S(  5,   0), S(  5,   0), S(  4,   0), S(  0,   0), S(  0,   0),
	S(  0,   0), S(  2,   0), S(  5,   0), S( 10,   0), S( 10,   0), S(  5,   0), S(  2,   0), S(  0,   0),
	S(  0,   0), S(  2,   0), S(  5,   0), S( 10,   0), S( 10,   0), S(  5,   0), S(  2,   0), S(  0,   0),
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0),
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0),
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0)
	]);

	var PawnPst = new Int32Array([
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0),
	S(-12,   7), S( -3,  -4), S(  2, -14), S( 14, -10), S( 14, -10), S(  2, -14), S( -3,  -4), S(-12,   7),
	S(  0,  14), S(  7,   8), S( 22,   1), S( 18,  -6), S( 18,  -6), S( 22,   1), S(  7,   8), S(  0,  14),
	S(-10,  12), S(  2,   4), S(  2,  -3), S( 21, -12), S( 21, -12), S(  2,  -3), S(  2,   4), S(-10,  12),
	S(-18,   3), S(-16,   0), S(  4,  -9), S( 14, -14), S( 14, -14), S(  4,  -9), S(-16,   0), S(-18,   3),
	S(-13,  -3), S( -4,  -4), S(  4,  -3), S(  7,  -1), S(  7,  -1), S(  4,  -3), S( -4,  -4), S(-13,  -3),
	S(-16,   0), S(  6,  -1), S( -6,  10), S(  3,   7), S(  3,   7), S( -6,  10), S(  6,  -1), S(-16,   0),
	S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0)
	]);

	var KnightPst = new Int32Array([
	S(-162,-42), S(-65, -44), S(-63, -22), S(-16, -28), S(-16, -28), S(-63, -22), S(-65, -44), S(-162,-42),
	S(-62, -32), S(-38, -14), S( -4, -22), S(-12,  -9), S(-12,  -9), S( -4, -22), S(-38, -14), S(-62, -32),
	S(-23, -34), S( 19, -23), S( 15,  -2), S( 16,   0), S( 16,   0), S( 15,  -2), S( 19, -23), S(-23, -34),
	S(  3, -21), S(  6,  -5), S( 14,   7), S( 10,  16), S( 10,  16), S( 14,   7), S(  6,  -5), S(  3, -21),
	S(-10, -15), S( 11, -12), S( 11,   4), S(  9,   9), S(  9,   9), S( 11,   4), S( 11, -12), S(-10, -15),
	S(-18, -25), S( -1, -21), S(  6, -15), S( 11,  -1), S( 11,  -1), S(  6, -15), S( -1, -21), S(-18, -25),
	S(-22, -39), S(-22, -23), S( -4, -25), S( -1, -14), S( -1, -14), S( -4, -25), S(-22, -23), S(-22, -39),
	S(-50, -35), S(-22, -37), S(-30, -24), S(-18, -18), S(-18, -18), S(-30, -24), S(-22, -37), S(-50, -35)
	]);

	var BishopPst = new Int32Array([
	S(-32, -17), S(-11, -17), S(-42, -13), S(-37,  -6), S(-37,  -6), S(-42, -13), S(-11, -17), S(-32, -17),
	S(-43,  -7), S(-20,  -3), S(-26,   2), S(-20,  -5), S(-20,  -5), S(-26,   2), S(-20,  -3), S(-43,  -7),
	S(  2,  -8), S( 10,  -5), S( 14,   1), S( -7,   0), S( -7,   0), S( 14,   1), S( 10,  -5), S(  2,  -8),
	S(-11,  -5), S(-11,   1), S(  5,   4), S( 12,   9), S( 12,   9), S(  5,   4), S(-11,   1), S(-11,  -5),
	S( -7, -10), S( -1,  -7), S( -5,   6), S( 19,   5), S( 19,   5), S( -5,   6), S( -1,  -7), S( -7, -10),
	S(-10,  -7), S(  7,  -7), S( 11,  -1), S(  4,   6), S(  4,   6), S( 11,  -1), S(  7,  -7), S(-10,  -7),
	S( -5, -16), S( 18, -15), S(  9, -10), S(  0,  -2), S(  0,  -2), S(  9, -10), S( 18, -15), S( -5, -16),
	S(-23, -13), S( -6, -11), S( -8,  -7), S( -6,  -6), S( -6,  -6), S( -8,  -7), S( -6, -11), S(-23, -13)
	]);

	var RookPst = new Int32Array([
	S( -6,  18), S(  4,  14), S(-11,  19), S(  6,  14), S(  6,  14), S(-11,  19), S(  4,  14), S( -6,  18),
	S(-10,   8), S( -8,   8), S(  3,   7), S(  6,   2), S(  6,   2), S(  3,   7), S( -8,   8), S(-10,   8),
	S( -8,  13), S(  9,  15), S(  5,  14), S( -1,  14), S( -1,  14), S(  5,  14), S(  9,  15), S( -8,  13),
	S(-16,  16), S( -7,  13), S(  6,  18), S(  6,  11), S(  6,  11), S(  6,  18), S( -7,  13), S(-16,  16),
	S(-24,  12), S( -3,  10), S(-13,  13), S( -1,   7), S( -1,   7), S(-13,  13), S( -3,  10), S(-24,  12),
	S(-25,   3), S( -9,   5), S( -6,  -1), S( -4,  -1), S( -4,  -1), S( -6,  -1), S( -9,   5), S(-25,   3),
	S(-27,   1), S( -5,  -6), S( -5,  -2), S(  3,  -4), S(  3,  -4), S( -5,  -2), S( -5,  -6), S(-27,   1),
	S( -7,  -8), S( -3,  -4), S( -4,   1), S(  8,  -6), S(  8,  -6), S( -4,   1), S( -3,  -4), S( -7,  -8)
	]);

	var QueenPst = new Int32Array([
	S( -8, -18), S(  1,  -7), S(  3,   2), S(  7,   3), S(  7,   3), S(  3,   2), S(  1,  -7), S( -8, -18),
	S(  0, -22), S(-27,  -8), S( -8,   1), S(-11,  20), S(-11,  20), S( -8,   1), S(-27,  -8), S(  0, -22),
	S(  9, -15), S(  1,   0), S(  1,   9), S( -9,  27), S( -9,  27), S(  1,   9), S(  1,   0), S(  9, -15),
	S(-13,  11), S(-14,  25), S(-10,  14), S(-21,  32), S(-21,  32), S(-10,  14), S(-14,  25), S(-13,  11),
	S( -8,  -2), S( -7,  16), S( -6,  11), S( -9,  24), S( -9,  24), S( -6,  11), S( -7,  16), S( -8,  -2),
	S(-11,  -3), S(  5, -12), S( -6,   8), S( -4,   4), S( -4,   4), S( -6,   8), S(  5, -12), S(-11,  -3),
	S(-16, -23), S( -2, -27), S( 12, -22), S(  8, -10), S(  8, -10), S( 12, -22), S( -2, -27), S(-16, -23),
	S( -7, -36), S( -7, -33), S( -4, -27), S(  7, -26), S(  7, -26), S( -4, -27), S( -7, -33), S( -7, -36)
	]);

	var KingPst = new Int32Array([
	S(-46, -79), S( 12, -44), S(-21, -26), S(-62, -33), S(-62, -33), S(-21, -26), S( 12, -44), S(-46, -79),
	S( -9, -33), S( -6, -16), S(-20,   0), S(-34,   3), S(-34,   3), S(-20,   0), S( -6, -16), S( -9, -33),
	S(  0, -21), S( 16,   3), S( -3,  14), S(-50,  11), S(-50,  11), S( -3,  14), S( 16,   3), S(  0, -21),
	S(-23, -18), S( -4,   8), S(-27,  15), S(-57,  19), S(-57,  19), S(-27,  15), S( -4,   8), S(-23, -18),
	S(-26, -24), S(-11,  -6), S(-29,  10), S(-57,  16), S(-57,  16), S(-29,  10), S(-11,  -6), S(-26, -24),
	S( 11, -29), S( 17, -10), S( -8,  -1), S(-32,   8), S(-32,   8), S( -8,  -1), S( 17, -10), S( 11, -29),
	S( 43, -38), S( 38, -23), S(  5, -11), S(-13,  -5), S(-13,  -5), S(  5, -11), S( 38, -23), S( 43, -38),
	S( 47, -73), S( 55, -47), S( 22, -35), S( 23, -41), S( 23, -41), S( 22, -35), S( 55, -47), S( 47, -73)
	]);

	// Extra
	var BishopPair  = S( 48,  39);
	var TempoBonus  = S( 33,  24);
	var BlockedRook = S( 47,  -7);
	var TempoMG = MG_SC(TempoBonus);
	var TempoEG = EG_SC(TempoBonus);

	// File & Rank
	var RookOn7th    = S(  0,  27);
	var QueenOn7th   = S(-15,  18);
	var RookHalfOpen = S(  6,  15);
	var RookFullOpen = S( 26,   5);

	// King Safety
	var KingShield = new Int32Array([
		S(  0,   0), S( 14,   0), S( 20,   0), S( 16,   0),
		S(  0,   0), S( 30,   0), S( 26,   0), S(  1,   0),
		S(  0,   0), S( 34,   0), S( -1,   0), S(  1,   0),
		S(  0,   0), S( 12,   0), S(  8,   0), S( 10,   0)
	]);

	var KingSafetyMull = new Int32Array([ S(  0,   0), S(  8,   0), S( 21,   0), S( 34,   0), S( 44,   0) ]);

	// Material
	var DeltaValue = new Int32Array([ 0, 100, 342, 340, 519, 1006, 20000, 0, 0, 100, 342, 340, 519, 1006, 20000 ]);

	var PieceValue = new Int32Array([
		   0, S( 81,  87), S(342, 315), S(340, 323), S(480, 519), S(1006, 1006), S(20000, 20000),
	    0, 0, S( 81,  87), S(342, 315), S(340, 323), S(480, 519), S(1006, 1006), S(20000, 20000)
	]);

	var PAWN_VALUE = PieceValue[PAWN], KNIGHT_VALUE = PieceValue[KNIGHT], BISHOP_VALUE = PieceValue[BISHOP];
	var ROOK_VALUE = PieceValue[ROOK], QUEEN_VALUE  = PieceValue[QUEEN] , KING_VALUE   = PieceValue[KING];

	// Threats
	var ThreatScore = new Int32Array([
		S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0), S(  0,   0),
		S(  0,   0), S(  0,   0), S( 67,  22), S( 63,  47), S( 83,   9), S( 70,  14), S(  0,   0),
		S(  0,   0), S(  0,   0), S(  0,   0), S( 35,  27), S( 63,  11), S( 54, -11), S(  0,   0),
		S(  0,   0), S(  0,   0), S( 18,  24), S(  0,   0), S( 49,  21), S( 68,  51), S(  0,   0),
		S(  0,   0), S(  0,   0), S( 21,  24), S( 23,  31), S(  0,   0), S( 82,  23), S(  0,   0),
		S(  0,   0), S(  0,   0), S(  5,  20), S(  4,  22), S( -2,  20), S(  0,   0), S(  0,   0),
		S(  0,   0), S(  0,   0), S( 13,  29), S( 17,  29), S(  0,  33), S(  0,   0), S(  0,   0)
	]);

	// Passed Pawn
	var PassedDistanceOwn = new Int32Array([
		S(  0,   0), S(  0,   0), S(  0,   0), S(  8,  25), S( 38,  52), S( 35,  78), S( 45,  96),
		S(  0,   0), S(  0,   0), S(  0,   0), S( 15,  21), S( 35,  39), S( 49,  67), S( 41,  62),
		S(  0,   0), S(  0,   0), S(  0,   0), S(  5,   7), S( 14,  12), S( 15,  12), S( 29,  37),
		S(  0,   0), S(  0,   0), S(  0,   0), S( -8,  -5), S(-10,  -8), S(  5, -17), S( 10,  -6),
		S(  0,   0), S(  0,   0), S(  0,   0), S(-12, -17), S( -8, -23), S(-14, -30), S( -5, -38),
		S(  0,   0), S(  0,   0), S(  0,   0), S(-17, -16), S(-12, -27), S(-13, -36), S(-15, -35),
		S(  0,   0), S(  0,   0), S(  0,   0), S(  9, -13), S(  5, -27), S( -7, -33), S(  1, -49),
		S(  0,   0), S(  0,   0), S(  0,   0), S(-15,  -7), S( -7, -24), S(  9, -30), S(  6, -48)
	]);

	var PassedDistanceThem = new Int32Array([
		S(  0,   0), S(  0,   0), S(  0,   0), S(-16, -29), S(  1, -35), S(  6, -52), S(  3, -65),
		S(  0,   0), S(  0,   0), S(  0,   0), S( -4, -11), S( 11, -24), S( 14, -42), S( -1, -49),
		S(  0,   0), S(  0,   0), S(  0,   0), S( 15, -10), S(  9, -15), S( 18, -20), S( 10, -13),
		S(  0,   0), S(  0,   0), S(  0,   0), S( -6,   1), S(-15,  14), S(-15,  45), S( 12,  82),
		S(  0,   0), S(  0,   0), S(  0,   0), S(-17,  12), S(-12,  37), S(-22,  79), S( -3, 109),
		S(  0,   0), S(  0,   0), S(  0,   0), S(-14,  21), S(-16,  51), S(-14,  85), S(  8, 113),
		S(  0,   0), S(  0,   0), S(  0,   0), S( -4,  27), S( -5,  56), S(-11,  87), S(  1, 122),
		S(  0,   0), S(  0,   0), S(  0,   0), S(-21,  26), S(-16,  54), S(-17,  86), S(-29, 112)
	]);

	var PassedPawnBase = new Int32Array([ S(  0,   0), S(  1,  13), S(  0,  14), S( 10,  26), S( 22,  40), S( 41,  66), S( 74, 106) ]);
	var PassedHalfFree = new Int32Array([ S(  0,   0), S(  0,   0), S(  0,   0), S( -2,   3), S(  4,   6), S( 12,  15), S( 18,  36) ]);
	var PassedFullFree = new Int32Array([ S(  0,   0), S(  0,   0), S(  0,   0), S(-23,  17), S(-13,  35), S( 34,  90), S( 56, 139) ]);

	// Pawn Evals
	var PawnDoubled       = new Int32Array([ S(  0,   0), S(-10, -20), S(-20, -11), S( -4, -14), S(-12, -10), S( 22, -14), S(-10, -20) ]);
	var PawnDoubledOpen   = new Int32Array([ S(  0,   0), S(-10, -20), S( -5, -28), S(  6, -21), S( -3,  -8), S(  4,  -3), S(  9,  -3) ]);
	var PawnIsolated      = new Int32Array([ S(  0,   0), S( -9,  -8), S(-12, -10), S( -4, -11), S( -3, -16), S(  2,  -8), S(-10, -20) ]);
	var PawnIsolatedOpen  = new Int32Array([ S(  0,   0), S(-23, -10), S(-26, -12), S(-25,  -8), S(-14, -13), S( -6, -16), S(-17, -20) ]);
	var PawnBackward      = new Int32Array([ S(  0,   0), S( -6,  -4), S( -3,  -9), S(-11, -13), S( -6, -15), S(  3,  -5), S( -8, -10) ]);
	var PawnBackwardOpen  = new Int32Array([ S(  0,   0), S(-16, -11), S(-25,  -6), S(-22,  -1), S( -8,  -3), S( -5,  -8), S(-11,  -8) ]);
	var PawnConnected     = new Int32Array([ S(  0,   0), S(  2,  -3), S(  6,  -1), S( 10,  -3), S( 15,   2), S( 22,  41), S(  0,   0) ]);
	var PawnConnectedOpen = new Int32Array([ S(  0,   0), S(  3,  -6), S(  8,  -1), S( 15,   8), S( 21,  22), S( 41,  51), S( 74,  57) ]);

	// Mobility
	var KnightMob = new Int32Array([ S(-27, -83), S(-17, -38), S( -6, -18), S( -4,  -6), S(  5,  -4), S( 10,   5), S( 16,   3), S( 21,   3), S( 32,  -4) ]);
	var BishopMob = new Int32Array([ S(-42, -54), S(-30, -48), S(-14, -29), S(-11, -13), S( -3,  -4), S(  4,   1), S(  7,   6), S(  8,   6), S( 11,  10), S( 11,   9), S( 14,   5), S( 31,   7), S( 16,  13), S( 24,  12) ]);
	var RookMob   = new Int32Array([ S(-42, -88), S(-19, -50), S(-13, -27), S(-13, -15), S(-12,  -9), S( -8,   0), S( -6,   6), S(  0,   9), S(  3,  11), S(  9,  14), S(  9,  19), S( 14,  21), S( 17,  21), S( 17,  23), S( 15,  25) ]);
	var QueenMob  = new Int32Array([ S(-200, -26), S(-19, -153), S(-22, -99), S(-19, -55), S(-18, -65), S(-17, -51), S(-11, -50), S( -7, -43), S( -5, -25), S( -2, -20), S( -3,  -9), S(  1,  -5), S(  2,  -2), S(  5,   5), S(  7,   7), S(  6,  15), S(  5,  20), S(  9,  16), S( 13,  24), S( 20,  25), S( 24,  26), S( 23,  31), S( 31,  25), S( 28,  32), S( 29,  27), S( 23,  24), S(  7,  22), S( 27,  22) ]);

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
// Chess Neural Network by Tamas Kuzmics
// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	var INPUT_NEURONS     = 768;
	var HIDDEN_NEURONS    = 16;
	var OUTPUT_NEURONS    = 1;
	var HIDDEN_HISTORY    = new Float64Array(HIDDEN_NEURONS * 1024); // Maxmoves
	var NN_HIDDEN_LAYER   = new Float64Array(HIDDEN_NEURONS);
	var NN_OUTPUT_LAYER   = new Float64Array(OUTPUT_NEURONS);
	var NN_HIDDEN_BIASES  = new Float64Array(HIDDEN_NEURONS);
	var NN_OUTPUT_BIASES  = new Float64Array(OUTPUT_NEURONS);
	var NN_HIDDEN_WEIGHTS = new Float64Array(HIDDEN_NEURONS * INPUT_NEURONS);
	var NN_OUTPUT_WEIGHTS = new Float64Array(OUTPUT_NEURONS * HIDDEN_NEURONS);

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	setTimeout(function() {
		for (var neuron = 0; neuron < HIDDEN_NEURONS; neuron++) {
			NN_HIDDEN_BIASES[neuron] = CHESS_NN.biases[0][neuron];
			for (var input_neuron = 0; input_neuron < INPUT_NEURONS; input_neuron++) { // reversed for contiguous increment..
				NN_HIDDEN_WEIGHTS[neuron + input_neuron * HIDDEN_NEURONS] = CHESS_NN.weights[0][neuron][input_neuron];
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
		return sq + 64 * (piece - 1) + 384 * (side === BLACK);
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function ADDING_NN_PCE(pce, sq, side) {
		var input_neuron = CHESS_NN_IDX(pce & 0x07, sq, side) * HIDDEN_NEURONS;
		for (var neuron = 0; neuron < HIDDEN_NEURONS; neuron++) {
			NN_HIDDEN_LAYER[neuron] += NN_HIDDEN_WEIGHTS[neuron + input_neuron];
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function DELETE_NN_PCE(pce, sq, side) {
		var input_neuron = CHESS_NN_IDX(pce & 0x07, sq, side) * HIDDEN_NEURONS;
		for (var neuron = 0; neuron < HIDDEN_NEURONS; neuron++) {
			NN_HIDDEN_LAYER[neuron] -= NN_HIDDEN_WEIGHTS[neuron + input_neuron];
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function MOVE_NN_PCE(fromPce, toPce, from, to, side) {
		var input_neuron_add = CHESS_NN_IDX(toPce   & 0x07, to,   side) * HIDDEN_NEURONS;
		var input_neuron_del = CHESS_NN_IDX(fromPce & 0x07, from, side) * HIDDEN_NEURONS;
		for (var neuron = 0; neuron < HIDDEN_NEURONS; neuron++) {
			NN_HIDDEN_LAYER[neuron] += NN_HIDDEN_WEIGHTS[neuron + input_neuron_add] - NN_HIDDEN_WEIGHTS[neuron + input_neuron_del];
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function InitChessNN() {
		for (var neuron = 0; neuron < HIDDEN_NEURONS; neuron++) {
			NN_HIDDEN_LAYER[neuron] = NN_HIDDEN_BIASES[neuron];
		}
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	function ChessNNEval() {
		var output = NN_OUTPUT_BIASES[0]; // biases
		for (var input_neuron = 0; input_neuron < HIDDEN_NEURONS; input_neuron++) {
			var hidden_output = NN_HIDDEN_LAYER[input_neuron];
			if (hidden_output > 0) { // ReLU -> hidden layer activation
				output += hidden_output * NN_OUTPUT_WEIGHTS[input_neuron];
			}
		}
		return output;
	}

// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	var CHESS_NN = {
		weights: [
			[
				[ -0.018735273226373698, -0.01918513211422074, 0.014526771585178332, 0.0010992823002687069, -0.018282042057352295, 0.020837864309391895, 0.011271036339462614, -0.003038760515372314, -1.2602738764342167, -0.35393689367431636, 0.9680319469311819, 1.4339647502871062, -2.4016330512250867, -1.0170716504377226, 6.427591228637733, 2.502239162711352, 1.0410112163343324, 2.0115348860274027, 1.6890559930622686, 1.5052690748495032, 1.0442964213940742, -0.7617105212851031, -2.575178451895159, 2.8545940346248826, 1.3154708874459962, 1.3754543290947177, 0.04297951279078308, 0.2497349675751228, -0.1658622252327305, 1.0138609225169048, 0.26910636358038986, -1.8471351715502473, 0.5869234413570856, 2.0376553243583615, -0.6490235011904546, 1.9731159831841385, -0.8112608833017514, 2.0259602914317774, -0.5895762565604193, 1.553279903661108, 1.4203403589268258, 0.8142658878006461, 2.3295138792335557, 0.01845026158814321, 0.9977678893923321, -1.378044685573155, 0.9232638211422546, 0.3733758798406521, 0.5758951105891827, 0.33053818615598995, 1.4367998592083284, -0.08811535834590603, 0.8441498669520077, -5.117327107151529, -2.7445426576640863, 0.14773912057040592, -0.00916580421788605, 0.01074810068231919, 0.00509201613102457, -0.01814651139761534, -0.001702692045519137, 0.01822569195771007, 0.0024255005013486155, -0.016887307808921923, 1.097175593320788, 1.8907263863505135, -0.46363771899922807, -2.3393057640572037, -1.0286063654009336, 0.305546294023943, -2.8830356218363065, 1.4213837089867316, -1.3018205586023928, 0.3810083701451865, 1.014719205744088, -2.293610027133101, -0.2227627997810557, 1.2557111959843403, -1.9348480493697884, -4.309876224677874, 1.1416727813302507, 2.1494251920176595, 1.0847597473246426, 1.1297358007491394, 0.18559239530633864, -1.9566452094725773, 1.0591971423658861, 2.7151028794719623, 0.7033620565008638, 1.3547102998984377, 0.4066441073486095, 1.3647660543464817, -0.7285421356242431, 1.0414596945564942, -1.2054968613282198, -0.5626172624863879, 0.9301584545786536, 1.259575425413385, 0.7538202583006391, -0.6913535166315847, 1.3868258178588542, -0.2750355250182822, 0.45796227137233364, 0.028778902471212387, 2.291263270317688, 2.3619381990911057, 1.4802842639750666, -0.3003898922509796, 0.8306139199197254, -2.708788128658759, 0.9398294511627523, -2.7727635668229484, 3.464630224259136, 2.9470450531421255, -1.9472635565157237, 0.6645506854992501, 0.25439229406498165, 0.5019769135488005, -1.040317590586169, -0.13927146656903228, 2.4207238184526907, 0.5341499793454593, 0.01553892293926197, 3.128250076518754, 0.7167788216071797, 0.2694359460826827, -2.5027623257087703, -1.1148494943169072, -1.4369376203522277, 1.2839012683652806, -1.5902825160440837, 1.469539557024234, -1.7761489332389937, 1.3290659813748145, -4.0727390277006625, 2.855865901914014, -2.104435445726338, -0.8486196685281289, -0.9696677949072489, -2.771786069546404, 1.829778700995186, 0.7488691959652207, 3.969121426934545, 0.7040916223514174, -0.9560887137138162, -1.066074798819268, -0.7953876113515469, 0.3387301671836154, -1.5504125676836829, -0.09370865186514038, -1.5175170479629303, 2.2560707403399674, 3.135550262780153, 0.05807594824141291, 1.500481195672823, 1.0496765271692319, -0.8424354750117079, 0.3406334426883828, 0.4788586481386439, -0.08646282727770843, -1.2289716887472426, 0.6025290421843923, -2.818954628578474, -1.2474944888745678, 0.36697800069994574, -0.6540207536224377, -1.6485636948917273, -1.0524967863572299, 2.525764620905459, -1.9956598099695284, 1.6295127580136501, -1.8856764998109161, 1.416909188696226, -4.69013948701267, -1.1371319451691047, -0.5733983243034806, 1.7963152077492044, 2.138266296184072, -1.7972382707791927, 1.8437045643843644, -0.8897571344249143, -0.6225705171383753, -2.656986153164913, -2.856908868621839, 3.326070323091501, 1.439743578318516, 2.121114762462311, -1.6985392647314965, 0.6832175716874445, -1.130724494295136, -1.822702997169882, -3.562040163433531, 0.9134283566942659, 0.5531372944965456, 0.5999841838345916, 0.28086158635741065, 0.14302201228297637, -1.427381861968884, -1.522130159516715, -1.2803874150819827, 0.46955519898312786, -0.7891662239294902, 0.449872183115693, -1.1688686384743916, -0.36440011671652617, 1.5574869286851447, -0.45280973657410345, -1.9581453187085358, 0.06984543443032593, 0.26042944267715723, 0.22367630193890356, 0.6691239209213362, 0.1636469900063926, -0.2619617754182663, 1.150367663465477, -0.058017409843570476, 0.510609802138673, -1.1796316494474548, -0.538891549386407, -0.08607482934976415, -0.25557232719693607, 1.0386917801574422, -0.6921688121707414, 0.5874602309801437, 1.9878712955885554, 0.9873801181262456, -0.26055525049486383, -0.12439314424416754, 0.7225941972805414, 1.2155715402356835, 0.49111618784710626, 0.431864333011049, 0.6593986669838839, 1.7429314939021243, -0.5817710556181455, -0.13409910379068046, -0.3473367852601074, -0.3298833431557264, -0.6613774063133301, 0.2427282924634451, 2.634563945251081, 2.2317198997986343, -0.44434813776933485, -1.153266563117538, -1.6482342639412173, 0.7629929959281934, -0.15181774562133976, 2.085843842470396, 0.5292398974454416, 0.40626033055601746, 0.23167704736197736, 0.4055764113117824, 0.5978765388500249, -0.44591328757177207, -1.2719173865209772, 1.3060258440682662, 0.620915226588988, 1.180056637495353, -0.08433658668147383, 3.0983513690192326, -0.7084346520104666, -2.8702302259565764, -2.1941428934644716, -1.513564540018068, 0.7648193625034574, -1.2187971264846897, -0.9298354411877967, -0.9835116407110511, -1.0463711635552533, 1.9230793834624218, -0.7585611848968749, 1.5373476740800671, 0.6112151071311319, 1.897559971430661, 0.5340557667230986, 0.958116211179822, 1.5722166512143307, 0.7905336372353556, -0.28028919703062377, -2.048624102540553, 1.1378714479595549, 1.3166670168532864, 0.32064681585554894, -0.3735938969529561, -1.095289656238803, 2.364585307792697, -0.414013818257341, -1.3396847213916605, 1.5239896681323932, 1.5818265236728604, 0.804685224273448, -1.8842724707438148, 0.1231464295670174, -0.3946793609829702, -1.3364449441260289, -2.2016473215261643, 0.9733250883787363, 0.5166071100975077, 0.17812424469212457, 0.5700329693952851, -0.6899837506870574, -2.082284381642743, -0.990451856078977, -0.8963755978086361, 1.0011278537690755, 0.2058313731039515, 0.043963908554434626, -0.7617159136420466, -0.9715659912930039, -1.2050925582580028, -1.5613484717750692, -2.3976829567825564, 0.7987388626368183, 1.0520447261668275, 1.2169577942815812, -0.9630386744909847, -1.3591587678211547, 0.4120892612173282, 1.0699561624791745, 2.067761798080569, -3.9203569277321852, 4.26345655516217, -5.883146407211672, -4.923489401571371, 1.4705392593408517, -3.6953914185635064, -6.165540136138815, 4.535650880641529, -8.241752459770488, -4.262507409061172, -4.252433711696319, -8.007617716613964, -6.8691869286035026, -3.0122996081068716, -8.083155899131631, 2.411207726407912, -6.563930897767463, -4.695338375767904, -0.07270937508566992, -1.0481292896401682, -4.975496355641743, -8.124639112481624, -2.7499995855585158, -6.965906429209547, -1.620249231550459, -0.6746330145168131, -2.268667575107864, -4.635473472989136, -5.017875396765773, -5.521371284169969, -5.564822656766972, -2.546012489665915, -1.5181859463704968, -8.776623916187178, -6.316793240240498, -2.0908800072515024, -3.2076455795925107, -2.358236050873142, -2.8219426690336573, -1.3891467800393893, -5.347554305659386, -7.048303252950606, -2.553304778045179, -2.5171772046965937, -1.3781907777833964, -1.617790413346466, 0.12653061946663618, 1.1750572381024569, -5.3588870489394465, -5.971401119826842, -2.0524466855554717, -2.1533650607975767, -0.07967042280495655, -0.19615066019891397, 1.5983645187775388, 1.6147454548875408, -10.422795353768445, -4.95014634871541, 0.11449404342358344, -0.10106130592563739, 1.6104626185909041, 1.5960640281670706, 1.9294887645727863, 1.7995001921861635, 0.01556711212205981, 0.017338522661880913, -0.012180971868059852, 0.0016905502018410108, -0.0006258984740285276, -0.010441120766109842, -0.00964017247592057, -0.0029985920192251297, -1.07423359465571, -1.735661401060653, -2.431835579328072, -0.330795341998452, -1.7568507823704096, 0.11628881132701158, 0.8070249023721529, -1.0379020807719508, 0.04426307407251446, -1.4064440017316628, -1.8187747204736833, -2.1994599711447624, -0.04003319130768737, -0.26472639328279535, 0.4149242171570938, -0.037622893600053484, -1.0960587743085106, -0.12761947705310214, -0.9973355784148384, -0.2791005921052248, -1.164659353310158, 0.3814097625500915, 0.982964647035533, 0.9938067913690463, -0.5532038984701658, 0.4270738928137069, -0.03798343842779533, -0.19309491408258747, 0.1801699003259538, 1.5826152950552559, -0.2683635604853311, 1.5499192588753163, 0.40328339041390404, -0.841690606642612, 1.6165518421572183, 0.5717700450160987, 2.515726650401731, 4.050916961443454, 2.0645119947622796, 2.6874296282634886, 4.658304036701935, 3.7114336739290033, 1.2578284361115646, 4.28180957543779, 2.928833952617007, 3.16292940203442, 2.5637492892102056, 5.2969779356138, 0.017585914391608656, 0.019406783063569452, -0.018109356956825445, -0.007381161643121595, -0.012856538837560048, -0.018961078584357877, -0.003817007010225861, 0.0012126154655289427, -2.4779554712552407, -3.027530179144324, -2.609523639305425, -0.7941941863118894, -1.9045160883280392, -2.4660234920006303, 0.9280834476600784, -5.5609993241506155, -1.0909349173699465, -2.476450995644811, -2.416012449253635, -2.565448001877227, 0.045521299480862025, -3.556889492650597, -0.4061111831754536, -5.914905690657322, -2.2691866180879376, -0.8208006404075143, -2.123188879114334, -1.1230122586825597, -1.2895199286497852, -0.21891852343483031, -2.3344362381011967, 1.576720448183962, -0.5357243029591359, -1.993808741848931, -3.2627236500800945, 1.5005894707014529, 0.6227332864020719, 2.533874995886589, 0.24461726744954862, 0.4588669785337182, -0.3442810861521019, -0.6453048022073541, 0.8268972093735701, 0.06987022045446327, 3.545055514611213, 2.7511828831486858, 3.1744016627466314, 1.031599920511844, -1.4695251011632395, -1.667453319326008, 1.764419407279025, 1.684427018329745, 1.9209170834728486, 2.594233250368724, 3.226718987376845, 1.3281115959140004, 1.6194307678118862, -0.5155487920496881, 1.6911818866501338, 0.9125294010561056, 0.33164445701646555, 0.7165792356101989, 0.15106768203994805, 3.2284220453588137, -3.9557595858265016, -0.29828821775466136, -2.6476246333108895, 0.011017808956106191, 2.5469881980159195, 4.0788180997930805, 1.6414126382203122, 0.4866526606992439, 0.325988271892465, 2.9233290580570213, -1.4858218994919536, 0.6779933197956163, -1.1363703427872687, 2.271777675472514, 1.6738927632031544, 2.298867129446593, 2.8944926915974176, -0.41025389262638706, 1.1145928552479873, -2.7075216721554978, 1.113675004534977, 0.3642960429506193, 1.1086010612443844, -0.24989216378820175, 0.6217698648867584, 2.3267552725447365, -0.5942821425209324, 1.907487108630663, -1.772752261551833, 2.6096124145907464, -0.8593451994820623, 1.9651937233670143, 1.9147073349335844, -0.08839101463403284, 0.7844602810216789, 0.5398989146868733, 1.9939151126493675, -0.03958281802290081, 0.1877139793002982, -1.7295388413553432, -0.8010612815434921, 2.4814669862019354, 1.4861491608526443, -1.1341993714341256, 2.5392197971431893, 2.4878291312791343, 1.1261643380134618, 1.3943821523914142, 0.6457289968722192, -0.48815216342958473, 1.699530687798229, 0.632065097773252, 4.0092612533624115, -0.1467254109650283, 2.7497636149823594, 2.581612002545521, 2.0645404043241595, -0.8854569360684532, -0.5406528106687621, 1.5916738916659452, 1.432291818632034, 2.044692543231371, -0.33836274567599955, 2.8779953878580704, -2.24956576744446, -2.1162079115271157, 3.5326664346951193, -1.218385126741179, 2.002831636603762, -3.284579330098775, -6.936881119472535, -3.2375559039797257, -0.5404910921041647, 0.7976543396176631, 1.0877738384446667, 0.49908801208202475, 1.0588425922922875, 0.025145851561557964, 1.7097692381944116, -1.405811446088125, -0.7900706525319208, 0.7466642525676978, 0.41991932896639134, -0.6043518577141475, 1.4548352572458902, -1.4208861201477916, 2.346933631973252, 0.06264273214920034, 0.8492311435481873, 1.0103518912409484, 0.345833755205257, -1.1046508516661369, 1.3268009502554712, -0.45535707388588714, -1.5541854138294868, -2.8060115274104747, 0.09263459527632995, -0.736365619745077, 0.33670187976503496, 0.3611792364227339, 1.5802140053661908, 0.7354736484406751, 1.3573321378599412, 0.9054863858382127, 1.8836416363183632, 1.2973676614576342, 0.7846856072550125, 1.3096628786091833, 1.867958613571193, 2.616635206278966, 4.822370448688868, 1.9136115649468703, 0.37079300770504975, 1.971757012168946, 2.2732877439479147, 2.0179107674227215, 4.113605227232788, 3.780222504077735, 3.1098065648880153, 3.494342554603986, 2.582586237768387, 2.4548180341387793, 2.7444926727319685, 2.6078617801115134, 3.8864726924309956, 2.7790523524615063, 4.496981090520717, 2.9194494445474897, -0.40399975409261313, 1.3598705857450542, 1.508100368891831, 2.01689188303987, 1.3078255851247524, 3.4137671678208004, 3.31787832014685, 4.027053680505604, 1.9342175718733379, 1.2009447598921998, -0.03862834293506383, 0.6401359238293137, 0.9926549003836752, 2.0694682906518, 4.379159431197858, 4.028742150817494, 1.227635454691734, 2.0681268083179662, 1.7795457616019863, 0.7862521009585469, 0.9165233033425367, 0.9252209930944401, -0.35556539887474786, 0.04439565003238446, 3.2424418861666418, 2.093614278441706, 1.803937120239255, 1.4479476464321415, 1.349106444432737, 0.11652158507237971, 0.743800962708363, -1.7130247027280858, 1.0445841173210384, 1.7959233183671721, 2.6926794608362457, 2.2196249483581356, 2.486505137045908, 4.446209073327089, 0.8970453781471773, 1.2490124817145598, 2.7672246830747205, 2.494038331546854, 3.1195524894039965, 2.4023014105204568, 4.784250506160268, 6.525147549765144, 4.655816478791757, 3.376527254134957, 2.924229138649627, 3.1951808473566072, 3.0660966286443228, 5.988673147926468, 3.8472683285543, 3.929287254507914, 6.864564008893365, 7.509850170293022, 4.219381445996213, 4.548511550205405, 2.6759028579159483, 4.232844494344874, 6.869190352563207, 3.844941461341299, 7.505374652577075, 1.8463023534827354, 4.1797719263444195, 5.197360969087548, 3.880882299654011, 2.1663723497125535, 2.82050751313712, 6.1826566787906385, 6.059257095165438, 8.63370629807823, 2.9862484618486596, -5.644791975826899, -2.3150864470783237, -5.6159903027169475, -5.199933805089429, -0.4688579253670458, 1.88965077469253, 0.9583437130029921, -4.835005342228304, -3.2424226599911017, -2.014386658017848, -3.6828184483555324, -2.6455144685658114, -0.09138984257039796, 0.2459516850095288, 1.6799499258686568, -1.6656607141464046, -0.39458101490065534, -2.411167513221713, -3.2930768791584133, -2.5732704136842246, -2.337193335226809, -1.0329292144492315, -1.219490245676775, -3.273530078363252, -0.7436193527947255, -2.274815962654213, -2.159589999678688, -0.8457190384044525, -0.15646511858988657, -1.8177558544106172, 0.09946679332637656, 1.119682771861546, -4.967517099076642, -1.6762378097241315, -2.8282372509514575, -0.9813706655640956, -1.834884130571673, -1.156989198657675, 1.6614626206599281, -5.174444164481558, -3.4857007351574905, -3.5978667941869813, 0.07753644902675831, -3.52776487523745, -2.765529251554892, -1.1441315610862723, 0.800407560181816, -4.198094473224136, -3.0927888834044586, 0.7587096235456815, -2.5725429038584737, -6.742548793860507, 1.0590334047904166, -1.1214274420310164, 0.24765974890711923, -6.882759901553824, 2.0600458273056708, 0.7705746885200493, -2.098568701023566, -0.36585588045563433, -0.45747988493669545, -0.5052029278687002, -4.0654611673826055 ],
				[ 0.01631592388286479, -0.0024022706514438387, -0.012082033949470985, -0.005642554419644166, 0.002174500958351744, -0.008592178066556308, -0.019029279612746006, 0.01611464201552918, -1.120571262422939, 0.27356052796399727, 4.105876510861741, 0.6709305421065975, 4.950753977492923, 0.4419469605261504, -2.2996026780641836, -2.275376301169572, -1.107244121180147, 2.2810821197426274, 1.272928030780422, 1.569295876439883, 2.2782435016526126, 3.433320569897012, 1.0119491828868605, -0.38283069508427736, 0.18432304467716082, -0.1865441014563899, -0.4478636896775162, 0.17468845151613135, 1.0252799451469647, 1.1269058680677753, -0.891467557234049, -0.2175895302591472, 0.7971193744858512, -0.44816810264921253, -0.5693719230727322, 0.4572856761692951, -0.8789524217731907, -0.48309265677418545, -1.1952273663350055, -0.29924851593391844, 0.40821084227849264, -0.18442851050900025, 0.43849792036469887, -0.4981451296122229, -2.1393939054817275, -1.5098665113582326, -3.9304988973761965, -0.5279997002512198, 0.5125392737862374, -0.49166856527322617, 0.5936081067914418, -2.480129781112728, -2.025450970691779, -3.000126856053588, -3.7136593668215325, -0.4412036979845277, -0.011710419761394374, -0.00010576519045342545, 0.004317856273305488, -0.005383400737213664, 0.005682196794955598, 0.007142964487207782, -0.018347150518059574, -0.014194295906384154, -4.369354322548064, -3.6495236395632653, 2.246619116611016, -3.2727809354710304, 2.0468442962791884, -1.2887859527720584, 4.822169870164444, 3.2114189866541047, 1.160445860488568, -3.7119144284921175, -0.400455019765503, 0.46395081251879633, 1.8929323011962174, -0.7730027943388992, 0.791631208956294, 0.3483917725157835, 0.15059387805383778, -1.1007192824391352, 1.9579403697013562, 0.40124242982737535, 1.8844917972565478, 0.8359088609071229, 1.106224955984592, 2.1441614221326404, -0.10045016611823021, -0.4293859736983794, -0.5110150526226032, 1.8760301160174524, -0.48037579521544677, 0.6840118458532446, 0.844183739938158, 3.0476953690889608, -2.355636349049433, 0.8347902774400413, -0.09157962180050427, 0.19925755859059296, -0.34755060281338207, 0.8223025757021643, 2.1631147503280923, 1.73377397387587, -0.3295688893037437, -1.6215041998031559, -1.2318767221551647, -0.8913325494732804, 0.26207998979282404, -0.30789704792602846, 0.7795023002957047, 1.7006701422314094, -1.0319152369175693, -2.055430891645836, -0.827877187485761, -1.2874288305595472, -1.2132286434916058, 0.9791572529484857, -0.2777149117030434, 1.2012398748097557, -3.723136300428719, -2.324673217384013, -1.8845595192158404, 0.23753453850389675, 0.1333719897302013, 0.8280792583909395, -0.16531116016206884, -1.5241756017877508, -1.0243236167724858, -2.0054102185525085, 2.6964045826245027, -4.965947889202963, -5.562241853230758, 0.4213499784709695, 2.367561609655647, -3.7436238305724654, -7.154362823400643, -0.11500451734332515, 0.35101293636343145, -0.03781155176721086, 0.5091580432294817, 2.0396022812912658, -0.1852900179454817, 2.854640824703497, 0.14701973148072842, 0.7050655997724159, 0.2443838303871099, 2.0629785250959616, 1.4838086173620098, 1.4320162045746618, 1.0999078971085774, -0.2573588801346601, 0.20180765577322307, 1.0577445175973867, 0.40804300931458176, 1.7351798268987342, 1.22416463294669, 1.7267503536351176, 1.3874382594764836, 0.6844487208348992, 1.1310268329231197, 1.11717667381196, 0.6200972333839405, -0.35746120477478716, 0.2779692193777743, 0.5103428472304077, 0.9375988775716468, 0.8273512668254535, 0.8509633595911671, 0.6277457435941531, -0.33212054014252, 1.5326026259749639, -0.06914080997010599, -0.6871676593081442, 0.27766372130856914, -0.5898166217398914, 0.900621667134123, -0.36543275592620406, 0.867119665106441, 0.37214440063920473, -0.16757524577716432, -1.431184057559947, 0.012069534002263715, 0.4380218388458137, -0.6046999014733092, 2.5585952922438913, 0.2526486510030412, -0.5598693373335032, 0.6313347861578044, -1.224014882489936, -0.49664981923377743, 1.024917412300358, 3.5092570404416645, -0.22274495235770625, 2.1251634734779437, 1.4799973180421786, 2.292957395091411, 3.761110409602861, 2.3395191761122516, 3.0156806115138055, 1.314500894085901, -0.6624540719147873, -0.4694672827224952, -0.8070683600115398, 0.30448553720935684, 1.1990834656409106, 1.3329261059722335, 1.3266851288397223, 0.8682261620988081, -0.8688741910120555, -2.290916609755896, 1.4747679842190973, 1.6085840027071339, 1.1748049819854347, 2.2209284352864147, 2.513473308569565, -0.16398351358386729, -0.9798848736320726, -0.07372573439558908, 1.1894552570097718, 0.8514101331093435, 0.9783460633479508, 3.2334877304998764, 2.155575452872262, -0.03703268694514659, 0.12946880722932633, -1.185932538906056, 0.5077114933606015, 0.618836237591146, 1.4199042167069837, 2.497471050971715, 2.4337934767345337, -1.1985679140879917, -0.20570326899153615, -1.2761346961343563, -0.14542026188607227, 0.35257774732532, 1.2017827370104253, 3.578263766131123, 4.542563056049076, -0.8454693950651464, -2.0309502905783066, -0.2318442024197282, -0.136127888308123, -0.03142343202557528, 2.30924938651533, 3.2176966584857665, 0.8352156047365414, -0.2337518637407895, -0.6648884959348255, -0.18223556774052804, 0.6762471045607915, 1.0592224613501606, 2.079811060284299, 3.4055923485828936, 2.1969187280018225, 0.593877977593638, 1.8590292875799368, -2.2141731636242943, 1.6340087583731506, 1.0352596364789572, -0.28168236964831406, -3.0364623344726156, 7.142492285272395, 2.955991847642876, 2.425992246161293, 2.0066894676145353, 2.252551511823889, 1.4243525950451263, 2.52610550823121, 4.609912429231536, 5.991217109870336, 2.0240430913343483, 2.3939881478940093, 2.9179786557590326, 1.7386163203637275, 4.2283501539784645, 4.332156885694793, 4.626899278123084, 5.493331551037935, 3.4139401970568906, -1.4455298581295735, 1.2215660592913713, 2.923275941889386, 2.743043623229314, 4.5324221161644, 5.701547003310946, 5.348374237931154, 0.5868725480438345, 1.5630867354637084, 1.8261591725341428, 2.033270825028462, 2.4779909884550704, 4.294172595751018, 3.1696413348229378, 5.166599703905596, -0.5248968478265507, 0.2674175330065645, 1.8737163621702058, 2.5246431279125607, 2.1681996417860256, 3.1474870946426132, 4.2604135517691795, 6.520299598394158, 1.41060536863356, 1.1732968319695594, 1.0954502356308728, 1.7527509360822286, 1.4809626222931827, 2.9439345259450005, 3.8485434824988936, 4.931934506038832, 3.127790074856604, 1.195766225822158, 2.8372978840514085, 1.122866957755188, 1.1123405090187843, 2.9726130762082574, 3.8683206275024604, 4.386330169213479, -2.6393642092998495, 3.6294879584680793, 2.2512730231871663, -4.363327676048792, 1.9533177856871071, -2.530630161581698, -0.3504107310748847, -0.7717915731123989, 5.05791239834877, -1.865757873663432, 1.6445858322965858, -1.0933265083653736, -0.6956985064871, -1.1890001091526914, -1.3701744021053397, -0.6414210770854291, 3.1738356592125463, -1.5197843352880338, 1.6647804127775434, 0.2598316915852355, -0.8871605204976383, -1.6037257715667015, -3.130886753282425, -0.9296369011020355, 3.21553119633881, 1.5936982082950224, 1.955398279492959, 0.42522883536803374, -1.0034551230098978, -0.5440583852137859, -3.138526900559234, -1.967415434591028, 0.9009204453800184, 0.6143836293852081, 1.3664056509193274, 1.2191317048370163, -0.6068761273245294, -1.3385706476784553, -1.7916984859416891, -1.9031966972360175, 0.7614490866521066, 1.2826502253910197, -0.6358738460097354, -0.6171373515838393, -4.713011407008856, -1.3748456730698226, -1.5179574308859216, -0.7169127346072423, -1.9530131975626321, -1.6571366337015154, -0.19171262455755247, -3.0609265364377003, -1.793494351676279, -1.6587989010945912, -2.8610974932391144, -1.2147568828333202, 0.49556866096904595, -0.07529251413887615, -1.0006356412104722, -3.663711023968328, -1.2859569865188203, -1.5081416806191479, -1.54200264917335, 0.9996709375830882, -0.012563769293713924, 0.012975934127314988, -0.010364382047286848, -0.003221729513221813, -0.008533454178026527, -0.006062055228377387, -0.00927310619084845, 0.0025313068817454983, 1.3544704346940812, 2.0015537465182627, 1.0711671449062337, 1.4881495138578076, 2.0053231548339006, 0.4821501869248103, -1.4662404784987768, -3.6425780475054967, 1.7072942131709652, 1.7620428138730748, 1.1623748024965395, 0.5606377302213476, 0.3286857731145907, -0.5944781974912007, -2.000626468315214, -1.7998691162593552, 0.9205874621820289, 2.0226912375456556, 1.2596627262234852, 0.5431278583900426, 0.12857203489188418, -1.986215651722136, -2.891396212126777, -1.2001413615275398, 1.1675064777849067, 2.2061288331818765, 2.631925113893486, 2.136499210830399, -1.3282519366550924, -0.7175564878017074, -1.68095032791854, 0.29033410002160986, 1.7043699385364612, 2.0372110079979993, 2.7385368801605714, -0.08320059491801027, -0.32904826189346714, -3.020868079348517, -1.0763736795827759, 0.6974289441091723, -1.5672669397696202, 6.900023895477661, -3.7943893501731494, 2.445117967388961, -0.550328634621266, -3.987847170184228, 0.5694103721408571, 2.125864173403562, 0.0008159303715951685, -0.008801880281476354, -0.011163663634947599, -0.0057769824354221315, 0.01762709415934424, 0.0007502593176963196, 0.002851131500958986, -0.012729545222088292, 5.781990650486944, 2.527874931383295, 1.794293436746747, 0.7961364577613625, 0.7003509606569996, 0.7010518982620295, 0.6600904131878446, 0.9037483661893863, 3.7331044214997298, 2.82368966035267, 2.159436833185695, 1.3964296132870508, 0.5772778678539304, -0.5061747431092402, -0.1465015275074573, 0.4352704312508289, 2.622023410015224, 2.950797529318811, 1.864048612469254, 1.0075108783064242, 1.0790547884216544, 0.7579513370256381, -0.14188327685067428, -0.7029559597717377, 1.4595746900230206, 2.0871766272891334, 1.6086569927658527, 1.3591589161291382, -0.20927770049461294, -1.898985510979859, 1.5577509497121655, -0.48440849888662874, 2.179591159532239, 2.2487130891895752, 1.4124291195192944, 1.5483881054155444, -0.5198301994902368, -0.9232569652825826, 0.6528379161301807, 1.1930087973482122, 3.872852097233978, 2.438679986816532, 1.9455566458526152, 3.0236180995458084, -0.5305626437340858, 0.5777720729393597, 4.419286953576053, 2.258813890100436, 1.0084110625804084, 1.978657555950115, 2.5358124645633913, 2.5436218574483163, -2.0980460650719284, 0.5776391941318545, -1.3288269438021016, -5.298125254129531, 1.6914861243382568, 1.6384627691660556, 1.7644207909324106, -5.739811094997518, 2.004459321787032, 0.3973209192490755, -2.241679931606305, 4.141906660963294, -0.7562682092081716, 0.9361547096309204, 0.46268632996488773, -0.20118193375577392, -1.0199656474851762, -0.12907550785450064, -1.0476121887675385, -0.39751862272450356, 0.7868720782314202, 0.8775007692851153, 1.147414675431378, 0.6419093307377467, 0.011174784763345165, -1.166951100026338, -1.0206178113049993, -1.4383142087325527, 1.0857017906673279, 0.0735343652939779, 1.1269860785700414, 0.45468583134044516, -0.23343691647451326, -0.23725663726733084, -0.930233723110534, -0.842118395701732, 0.06639734244202504, 1.0230798204055167, 1.2889640718259843, -0.2698730331790132, -1.343224927090622, -1.7672337950163277, -1.9382223483809335, -0.6781125429545828, 1.401215657414344, -0.3243980233192827, -0.2132612635644958, -0.5694241097884868, -2.275846757681716, -2.2297619221948284, -0.3376510986487145, -0.3099599714677781, 2.6498106063164615, -2.1301006905448925, 0.09258795795026194, -2.6653888175123255, -0.1353503230117858, 1.870231358321653, 1.4019205160089967, 1.1034450032426009, 1.405283560114576, -1.840826419623376, -2.2087556761263, 1.1203321465856697, 0.9057395530806664, -0.6331654783968343, -0.2973497897149676, -0.9201467924209953, 2.164174703063514, -3.278795434714016, 2.144848375586748, -0.2422020880917418, 1.599464360870997, 0.7582696237947549, -0.8157286609678354, -0.8661052676640113, 2.884918823044297, 2.9337430151595143, 2.469407628130899, 2.2517867728341936, 1.8820997467786975, 1.9341784276483989, 0.9312665891835664, 0.3693659958475226, 3.2792432104953098, 1.7872235205615934, 1.3008954779238315, 1.765176089103954, 1.9909419340954522, 0.8711903836930013, -1.00611664690473, -2.420308634315581, 1.461177778628167, 0.5556281556678181, 1.0426190469331422, 1.8313885614845324, 0.33191888242575096, 1.4387884205478285, 0.10914378415409302, 0.00815269775982073, 2.4766346162301165, 3.6347597818908013, 2.5078914836678523, 2.4731095706999087, 1.132049829899122, -0.0672951632935842, -0.3001103936076193, -0.9603746996346925, 1.9002089298757292, 2.2733069676555893, 1.4955219041831895, 1.459924173455292, -0.09185948347068858, -0.6613789703909166, -0.8873804940268674, -3.1027083804698554, 1.8344183645155268, 0.8021093693724224, 2.097611827787111, -0.6073104752866306, 0.2989074700278521, 0.148987761717068, 0.009977208671309447, 0.3714174754000317, 1.390846872188929, 1.7706782402983505, 2.357215824293196, 1.3820356657879085, 0.29874474319406163, 1.9331936742008948, -0.429760913214025, 0.30211063767891316, 1.7772746719582975, -0.18685302455189584, 1.1350303548625162, -0.6901921782351428, 1.6257026578023446, 0.5981737187721775, 0.5596356241713542, 2.3907457785970485, 1.2879495759791941, 2.151016652341755, 2.1758292441308953, 1.7657059233530124, 1.1834687259996497, 0.7847072018473089, 0.3037682422016676, -0.7655286459218791, 1.965278797788757, 2.2750755058170524, 2.297711209874095, 2.0338075370963598, 1.2701620691479458, 1.8041416943864095, -0.467455321785525, 2.1437542834325094, 2.1641940650577944, 2.2138868037644435, 1.5553030213079626, 1.3596230545026644, 1.1587362831228927, 1.9655390343119439, 0.9591241777729329, 0.026541488556095935, 2.4695041013219114, 2.122115148123615, 1.7933525459426876, 2.430459692203374, 1.6023730244371321, 1.9712508302210223, 1.0825017221578677, 1.849914345729822, -0.10096061269741191, 0.2721403944075009, 1.2535855852515079, 2.3677903829679994, 2.509906493055812, 1.9258452911168138, 1.5870985455271904, 2.993770281177941, 3.216527191068276, 1.908483739695367, 0.732982273260234, 0.4401645199014266, 2.416671099281466, 1.951262840073459, 0.09275606842397797, 2.9213008773532545, 2.102236984833203, 1.8137309416771346, 0.8484773539048144, 2.382595745253926, 1.4236406040991634, 0.9571962965842077, 2.981537630365831, 1.6955348351255184, 1.6561416186041502, 2.3229676406003645, 0.919432778204479, 1.6992505449527524, 2.375688675371072, 3.1820243094156475, 1.0692970851880734, -2.6780524651658553, -13.117756102134216, -10.124497428374449, -8.040174786060343, -2.94124831430893, -2.5871991270673957, 0.8602752216364511, 0.5298744607857966, -0.48912892190570356, -11.234358653727888, -13.888553619872631, -12.147015487513467, -1.7562639795957382, -0.5750237359195218, 1.152713141220332, 0.6163944646586864, 0.24002474844245694, -3.0964124977966168, -7.214358180806285, -9.381863373851516, -8.192768442457636, -2.6546357329395223, -1.3312715627607408, 1.4115395543678968, 0.4787329973498544, -4.555569112101322, -5.921675474872044, -9.003575456848601, -3.938238226586629, -2.034780303543401, -5.616206023268628, -0.6867781106058163, 2.417218083481098, -5.6113554045729135, -3.7674433662586013, -2.5724536920880476, 0.12474141841085694, -2.792201329174966, 1.2068765123391747, 1.154439996998185, 4.073810551940769, -2.143531272967245, -0.12860994826528332, -1.3520375222590482, -2.231692157208784, -1.1517625592564158, 2.9857889805822464, 4.440862306680434, 4.986601307050493, 0.6721200640999652, -0.5653191359835964, -5.030239489358714, -1.0465400861551386, -5.456613124271858, 2.607090153797284, 4.018839962761595, 5.172966015075556, -0.36060839253348487, -5.946658723454523, -1.4419115607768056, 0.28574602404336663, -3.2112771756130916, -3.148741509072427, -4.987708789053741, -3.624040299024453 ],
				[ -0.013050593390723125, -0.0021870936824212256, 0.002931658509088606, 0.011867516782472939, -0.01151063905894265, -0.013928714231518848, 0.018756627359996895, 0.012302905143804175, -6.197715411555735, -6.080693450103749, -6.6654333127117695, -1.4761898710819077, 1.7081943508212807, -5.545470316431721, 1.102254387584419, 10.243391987482612, -4.271070765849055, -3.410773322551872, -0.7739204256399336, -0.2839258244983332, -1.0130710725493401, 1.7417988507005624, 4.0705163946548355, 4.863766822122381, -2.6633922302911635, -2.004608511122365, -0.10521003608412004, 1.4660184504189533, 0.975089144246005, 2.481027839052204, 1.9929307321787932, 5.211059358271902, -1.3606524110977363, -2.6205632499741083, -0.586421017193234, -0.8754247688144408, 0.9945678094424686, -0.4132881678199974, 3.449721670235274, 3.2796794596115393, -1.4471498791823412, -1.8952391942031526, -3.0934516001990753, -0.027015573635662843, -1.4005666093434705, 0.17619356827848792, 0.480270643212314, 2.1485236459158155, -1.0489564110785932, -1.396136398917357, -2.716941266646217, -0.8694843841372372, -2.052325468414308, -0.472149691872453, 1.3013078152658337, 2.6940926301503354, -0.012308678588344838, -0.004697276232603697, 0.016507973922680715, -0.01693238238204874, -0.013760582852697595, -0.00417088457500705, -0.014911556101677355, 0.013178199120891118, 1.318148885949873, -1.6522564969049238, 1.750911423649821, -0.5147293248826308, -1.630289319185549, -7.575037474974623, -3.5459999373769935, -4.461766706909252, 0.7660947070345764, 2.0224701477755844, 2.441498328495602, -1.3073452698697619, -2.540724724155425, 0.7233551467077138, -3.7191806504133775, 0.020190077439912, 2.2445798025186603, 1.5268853439720995, 1.1168198739406447, 0.4286672627242245, 0.44375376307350284, -1.2368801738258515, -1.8543041792971098, 1.504519311519044, 3.118808708668979, 1.4644997332236203, 1.2620578940625242, -2.2512535519090475, 0.5354467633414131, -3.164047071622723, -0.3930507925304433, 1.6919610503739286, 1.317464820104374, 2.110855687244263, 0.40042646799378134, 0.6860876079099206, 0.4552390615717751, -0.3434235258894696, -0.2976788145024354, 0.026629372443720798, 1.6073684285126986, 1.486975395252153, -0.39730531819278747, -0.3280932701351895, -0.5374721000315034, 0.29099255160553084, -1.0938337391370059, 2.577178535005121, 1.235692472526636, 0.04832947245905885, 0.5705345319104677, 0.40851467415389664, 0.549017766293935, 0.1497811239480592, 0.10874475676805503, 0.8063089082859597, 1.9325282595739612, 2.2499493193995197, 3.611548425798522, 2.263175372476963, 0.9276503223079188, -0.834307296788346, 4.184717047546511, -3.3912914659960767, 0.023428504384925317, -0.2150313848540523, 0.23288708434183328, -1.4319752404691222, -3.123448644762206, -0.29874301794124286, -1.2645277203640122, -2.9589367209272424, -0.6815943421162506, -2.3527655354526265, -0.45002511036736953, -1.10002593721011, 0.12995884741890723, -0.12785180623952655, -5.6853919360246525, -1.599412823104244, 1.5514640228232257, -0.04543949527385051, -1.2451168559948353, 1.0224244792089396, -2.863463472897821, -6.727078084981846, -2.5526490752060096, 0.07573498957356486, -3.028819587458697, -0.12767265223316565, -0.07033299828235696, -1.3352256833524248, -0.29770838318138904, -2.687296457070381, 0.645812334759186, -0.34951950118003783, -0.3265483443043724, -0.8371758926464405, -1.1734158256692926, -0.7969040875594864, -0.5900934717028786, -0.11947453485151598, -1.0798427283291765, 1.550598395153356, -0.9845936746657535, -2.048478540409973, -2.928212896224597, -0.793542517289108, -3.2232489075402677, 0.27087290418389237, -0.8708180627498155, -0.2892872109428422, -3.2473093869218315, -2.539411637600767, -0.7474811112876967, -0.7135487280189425, -0.30979863166688837, -0.5748349451671045, -0.322126361359705, 3.1916618219780473, -2.663680414355085, -3.0041937305326156, -0.8055514121385561, 0.30218593202396654, -0.2579724942091424, 0.39465268982933366, -0.8203591052422995, 0.8063644499391056, -2.3577715736293587, -1.1902220977340046, -0.35009290920861214, -0.984867542509462, -1.2236075120334946, -1.046691971409122, -1.7187733812381687, -0.9316425842901854, -0.6289986292273243, 0.7374642561272046, 0.5386865326267617, -0.2702266904107267, 0.9383786874472094, -0.039159136381382846, -0.9551325887095425, -6.702112490800672, -0.6937328968460317, -1.0520325180176586, -0.28245806045533156, -0.46257491729385913, -0.416932652542502, 0.26373772868650097, -0.7312533741837447, -1.1602926021504332, -0.8273362624531337, 0.7492085441144435, -1.249149289090324, 0.6815124022354023, 1.4033097727971355, -1.391442644789344, 0.051371504811027494, -0.7830128596620816, -2.021907351277609, -1.0112809412535904, -0.7804415861895215, -0.685288674595844, -0.5797332813960403, -1.0928512566440645, -0.7785590676474392, -1.3040785183840935, -0.1356871519194998, -0.234005023094255, 0.18207677019433605, -0.28069405098407224, -0.3572877605067463, -0.9536268859115902, -2.373519160288438, -0.6384333639732794, -1.7404880645590433, -0.9634374266528943, 0.4297171254198895, 0.7703423778451073, -1.7016669503955724, -0.7729883700217413, 0.42985440104563527, 1.3857650892406486, -0.49696559919570293, 0.9947383661018592, 0.3159662383562865, -0.6488089541042596, -1.230592368149724, -1.3292743806460365, 0.12641700899267042, 1.5058491422293485, 2.3616731170114913, -0.0513763692672935, -1.7712350929523515, -2.4529693224061484, 1.2520311939379214, 2.1652007881482316, -0.8396521291115274, -2.7503766410105075, 2.67794176834263, -0.4873706626599408, 0.2191567863181007, -0.15820909849723622, -0.2016452888512809, -6.787996003972557, 0.6123153785864562, 0.0577866438826895, 2.5473340623183236, 2.3847482575314665, 1.121970254956016, -0.007479897236661209, 2.8048243180627934, -3.211385159839913, -3.3129324492020222, -3.453973699839995, 1.0887936355814178, 2.4316395394409103, 1.9545190988656955, 2.370576226329583, -0.22549733481183196, -4.850580288086141, -4.025925440515688, -1.907802719579856, 2.8353357615569927, 0.7066541021853677, 0.45420853796897, 1.2318165923952282, 0.5230685688089299, -1.1021948050304833, -1.059146479103287, -1.31806100108189, 1.4534974903848243, 0.029444374526034465, 0.7173323193486728, 0.44958954157844894, -0.4532595543590072, -0.5576081492885185, -0.9864678632171372, -0.6378761967010762, 1.0549467842937361, -0.5507590774439638, -0.5461217704430769, 0.3442389225647722, 0.3261381751280464, 0.49021514134284383, 0.3168730210864114, -1.3675291271985837, 0.747353623999922, 0.4247395808746328, 0.7881060261138529, -1.2361910636830011, 0.577477593939687, 2.9279454127005025, 0.8349904326785152, 0.3071916126664343, 1.1695256476550169, 2.352558900990506, 4.7658888818795235, 1.9172743075795005, -2.252933689844604, -1.2510062829586146, 1.6090970611396347, 0.4501707955582038, -0.8392196131174551, 1.192044658375761, 0.861506217781604, -1.5266594868273182, 0.1325759515182411, 1.7932208953988504, -2.0033628685956217, 0.6038693395315363, 1.3307841366675437, 2.008060707464908, 0.31654570204914584, -1.9461139655642756, -0.2867513707143993, 0.4161926517449421, -3.0457065795111675, 0.11140589320001387, 0.8953532175589332, 1.9777089710713194, 0.8681837487530049, 1.31373672774029, 0.33212017121541093, -0.2915003283997207, -0.4657212537621279, -0.723770381696966, -1.8831082522678824, 1.5963518925037767, 0.5999271489363752, -0.062179119527431874, 0.0361654677032053, -3.2972513655594664, -2.0621597741022857, -0.20889579768226776, 1.6865117302224553, 0.07482729876817998, -0.3663941437971778, 0.29037862149765037, -1.9550256781332438, -1.851208722966005, -2.163839949432412, -2.234839304254867, 1.1017156729211801, 2.3021969143826597, 2.7408495533264, 1.4233728969079729, -0.3219340839326031, -1.5057179418556281, -1.7125256294941928, -1.6872135514189115, 3.394413236465135, 4.3599803675165685, 2.8339522123717216, 2.550766830073277, 1.0691433894394586, -0.32640819285686395, -0.8712955799690619, -0.9558118236744209, -0.01715475876315953, -0.006426893735755399, 0.01093906123495798, 0.011858009050323186, 0.005826694800323305, 0.017026840085596268, 0.012106746463315516, 0.017685375554940354, -1.727419022501464, -2.740805919847202, -1.3262134450312872, -2.9148651094003677, -1.7383829275570977, 0.37326418528404715, -0.05528727317165951, -0.2565756438048536, -2.0455535345883704, -2.6805925869203113, -1.1785487945677375, -0.6028040713098144, -1.2940033711971033, 0.11561442361242788, -0.2650244808156063, 0.9121088977930063, -1.3281673040896207, -0.9807212525208954, -0.8142020228094523, -1.0772352163933396, -1.2200192657569435, -0.9440824762369441, -0.3048196124593497, 0.2952810523197718, -0.7499578764806816, -0.3068673516203265, 0.8036337420035653, 0.4289852367306782, -0.5848354515861491, -0.33640703760433566, 1.8704423934898429, 1.3777657498024949, 0.03443681893728742, 1.919104396264952, 0.7880455739501692, 2.0207397280344916, -0.6169166859579994, 0.3709817815217808, 3.0466526107791423, 2.9852487406771133, 1.9570873692518589, -1.0835437477739582, 0.21185514039959366, 0.9284812633532172, -1.1441021270243792, 1.907445132192914, -1.0992366461576561, -0.8846420019142397, -0.009212163735274, -0.006905286736710911, -0.003099783336012026, -0.012981605596849377, 0.00151730200582408, -0.011378689380026213, -0.01790863231876016, 0.021697085673874912, 2.5583276136584265, -2.748577087607399, -2.8756606578540103, -4.08349053271658, -1.268361578882558, -1.6537759959124145, -1.2242700307893246, -0.08275834941079657, -4.306959016268255, -2.8806350011821067, -2.323007408666692, -1.589415079773406, -1.520085771238688, -1.2205000754873772, -4.8796017473543305, -1.48400819567937, -2.3643729176185135, -0.6866718024279544, -0.9383554079962694, -0.2167087101833035, -0.686963094891135, -1.6578018578611509, 0.462342858833849, -2.407688603983378, -0.2474799067929192, -1.188563738624741, 0.9335813417083404, -0.14234789381543653, 0.6536942645384645, 1.306200014856482, 0.744440431672826, 0.9669930373343968, -1.0944191941160202, 0.8284999266910192, 0.37804605699303195, 1.3056198578488007, 1.0619478937400288, 0.9543791915639472, 0.9287821766569987, 0.6870090958626508, 1.098342214196692, 0.570790992288131, 1.3896128860755281, 0.9220235835913294, 0.24271009234770696, 1.356837372671163, 3.6508365448177624, 1.8003263013027018, 0.8536457829733681, 1.0162242572430342, 1.2251151373619837, 1.4411926868926421, 0.17703658365890526, 2.6007453579799944, 2.38195214372342, 5.431048822307347, -1.039887274617228, -2.3633782455224277, 0.3513902653211777, 2.6351200148990754, 3.2024462695443776, 2.4554329703630033, 5.293432325902638, 1.8000443473395258, -1.7001000553907388, -2.699569608577422, -0.8405714600820001, -1.8153735385998309, 0.5718378305530573, 1.8713769140635816, 0.8814457429889733, 3.669737143264336, -3.1732538223598596, -1.9271547438483239, -1.7614199573232179, -0.016894507898173282, -0.8645547066329348, -0.10531941577214554, 2.346384840983358, -1.2041904530739578, -1.3932708375349299, -1.3542775863107448, -0.5268874469426551, -0.005007354154430248, 1.1279715426773682, 0.15981997295406872, 1.9229638615801912, 3.047532504772529, -0.6868985869717976, -0.360724723867573, 0.5746697865155029, 0.7270935329287859, 1.6971293593539902, 1.859622146567558, 2.784172189441382, 3.5873046881239796, -0.6062073819460113, -0.4378595973632939, -0.7323501569061791, 1.0583182313643935, -1.2065147078839378, 0.6739162596744854, 1.1959027908580104, 0.338664028510556, -0.4220213044658504, 1.131880008069209, 0.941264185413391, 1.9844215202373778, -0.4248730726961935, 0.31952429852926517, -2.493661797439176, 1.864520311038747, -0.1533854123969417, 2.0925451621076885, 1.7935349012626889, 1.7303417290284198, 0.916049819097642, -2.793008489056081, 1.0670310179856137, 2.4655220280544845, 2.9593354539985066, 0.2683839139099716, 0.7332959175604472, -2.3311274617569695, -2.4017229123417025, 0.9971431144088403, 1.6334375437321902, 3.6250757226263066, 2.2522021512401413, 3.0929425307975444, 1.867478820203674, 2.848223941860071, 1.8356593927203875, 2.589698629347663, 2.2455124526638857, 0.018868215038463122, 2.354404884845704, 1.892212589184558, 0.9622158282155271, 1.4241939733737976, 0.48661582947403165, 3.125015793796831, 0.8113902143033723, -1.4916258164097198, 1.3546563322331824, 1.3533765648721066, 1.8734952158091607, 2.8364750264727014, 1.2737121038284678, 3.1598231511355426, 3.2478153032466244, -3.0404321681678166, 0.2810703696727633, 0.7997913551657057, 2.0920381172061786, 1.4870498865189983, 2.8403803509607557, 3.5445363583796583, 2.2095840819465202, 0.000761894514746921, 0.8778409486671286, 0.8907237486118091, 1.548458734827559, 2.528338776881653, 1.8783026855569824, 2.349553111554601, 1.8240232615582581, 3.1606150104186232, 0.5508741138083002, 0.3734893010158178, 1.0551976124481708, 1.3129364573804791, 0.09472025614997885, 1.5279898502473512, 1.6757099351783225, 2.8591578721171023, -0.27715489348984124, 1.373578168942324, 1.7283067757709967, 1.5476245342348898, 1.3261695542527818, 1.4712643022223146, 2.3566303294769266, 2.9342149494630245, 1.2889645858299799, 0.38726644884829603, 1.124589028051125, 0.5408133567178562, 1.8575776253838394, 3.1280205174593085, 2.854893686610296, 1.8595385929533699, 4.7665758237996485, 2.7557879407359898, 3.3393164292515185, 0.9622012543433028, 2.5308665468828067, 5.372111189953375, 1.6616556344897901, -0.42032275553463816, 5.222799847288762, 2.8039052063729035, 0.8911847043163498, 1.6816945588743892, 1.816048608734836, 3.1568378733594415, 0.9674254687766393, -6.570165653037575, 2.128418789318924, 2.0186525067169727, 1.1993707297528289, 1.3830686100763938, 2.6045025142716534, 2.3016714297277505, 3.0297536934524776, 1.581119749127529, 2.575846079684413, 1.6670546249715137, 1.8319972193386402, 2.209128398861629, 4.6010247143738265, 3.808442878487553, 2.8473384395153247, 3.8477342265130723, 2.2720725040296994, 1.7818553458028799, 3.080563046901885, 1.1184472085896586, 1.4857467006448248, 3.0548551153524643, 2.0201357050584168, 0.5922341188229046, 1.5836636685545236, 2.1808449036256587, 1.739336203404804, 1.5571635443071303, 1.5226784359570236, 4.760416546398344, 1.455786534250679, 1.191023008185961, 3.750855098988271, 2.827214738186413, 2.0889589382989424, 0.32752448003321977, 2.2661287780320056, 0.5964709687204152, 2.4643460400495254, 4.758635288693527, 0.8635776221249776, 3.4126691182071296, 1.1551257771397307, 0.48654391919807205, 1.3565378119322224, 0.47401828923287354, 1.9965909617218909, -1.3687888404325665, -2.781279890754705, -11.868123394361307, -5.208473821334536, -3.816953140183661, -3.5645934184389043, -0.5826038241970576, 2.3151803353825398, 4.3671304085999845, -3.811760288969461, -5.383005878596699, -2.280407208388407, -4.134934377831486, -3.60717913378275, -0.7694536615901131, 0.772591977827264, 2.3524156291514147, -5.7542325395389105, -5.384236640999779, -5.029149257656386, -2.4558678759757258, -2.456605365526621, -1.5437218808711304, 1.5402039913735857, 3.3567021095469323, -6.627688145615924, -6.730629889616465, -3.7535843225320837, -3.7218125373649826, -1.7121095082187947, -1.0536172325077917, 2.413885697054167, 2.308411388705591, -6.501430435388733, -6.618557422132113, -4.860686170872046, -2.7396146449923866, -3.410106307189851, 0.7063704574324172, 0.597734582434339, 2.5649064350062396, -10.72926751148231, -7.57595273673685, -7.370936843155809, -5.414559286655626, -2.276340299993594, -1.974641247423422, 1.9177279698691985, 2.300387267291226, -5.840848064797844, -7.005654921449199, -4.51672538565034, -8.070824811559799, -3.4656225873513615, 1.6535076344734878, 2.4886741746274565, 2.3845688705836485, -6.722891270551679, -6.226266276858615, -6.980118371027231, -2.023522300040331, -6.11856559579055, 0.18127425027547392, -2.588805396676091, -0.8072396099254635 ],
				[ 0.004073010860158723, -0.013890887317922547, -0.018083006306040542, -0.018614583699701207, 0.012169018627939378, -0.000027451652931741252, 0.00782508517906046, -0.014889372581381288, 4.920588282130923, 4.046226878994911, 4.174804055117252, 1.9558437738689527, 2.389795032414477, 0.6785373531363508, -5.788847613630761, -7.913560025648846, 3.8066398107979715, 2.4453015874911794, 4.53625013954796, 4.000724857763629, 1.3763157801586878, 3.1607582486953576, 3.6418146186702005, 2.348007341104782, 2.7963715608894155, 3.552975447993718, 3.300045267078029, 2.769175043077954, 3.28896700884505, -1.4981096620760241, -0.35291969826014263, 1.686704587368774, 1.9876878681365469, 2.5257451357441854, 0.7700725419869271, 3.7847183434631866, 2.148500698889256, 1.30342749719538, 1.067095744122195, 1.4446192551504562, 1.1342419021925019, 1.4750587883645814, 2.367017406537904, 1.0809945585322496, 0.452740579825342, 1.3760056882424698, 1.127915201176902, 1.2261037761647422, 1.0036191836462103, 1.6619424413300536, 0.7380394128946924, -0.2291418962842178, -0.9510422195690196, 1.1973070803392387, 0.776977110885717, 0.31656496172097753, -0.01700893337001466, -0.020358571979889727, 0.01782232576639182, 0.004394468625513449, 0.01521534299980309, -0.019469614505239347, -0.00847312844482779, 0.010327551287873002, 2.411813896100451, 3.161849243619762, 1.2151589530903502, -1.956379486430465, 3.808017739675291, -0.12738694630623873, 0.6800823470331869, 3.6435605992887896, 2.793829299926741, 1.0868441137605651, 1.3146194133063305, 2.058208297609937, 0.43695530081892625, 0.22200325363264298, 1.6958549387372608, 0.6589098688957243, 4.9828080848180365, 3.697421410185485, 2.9130633714309497, 1.042293131051343, 2.1303930291762607, 0.500109235875952, 3.0861142659691145, 1.1000279467724154, 1.1953419866150965, 1.5107021170198096, 3.311967355626161, 1.2040985285834573, 0.2612168947748202, -1.062529731543519, 0.9447132783538408, -0.8453196180889785, 1.171387140843631, 1.7739170936030288, 1.6889264100583183, 1.8606475214930003, 1.7543415690737536, -1.5957514973173204, -3.204974368896565, -0.24300956235093626, -0.7489510239113426, 1.5364843726079034, 0.633053728937823, 0.1707605366975482, 1.589177450314895, -0.061571921977081584, 0.7413520345629213, 0.4575425629325089, -2.1385586305397144, 0.44779682686825106, 0.8288182166758961, 0.379186896323965, 0.7915407276824333, -0.2893884458500264, 0.6197311233543027, -0.39183794127447047, 1.562731710631797, 0.02357685437423168, -1.2866660466134732, 1.785863959946695, 1.6004200871003458, 3.7124105610540847, 2.948910818238558, 0.9771318325727295, 4.52574553264657, 1.9684592414588753, -0.8892433414013518, -1.728941694673451, 1.1122307676906413, -0.17006572625235108, -2.981771995513021, -1.1377674702630818, -2.2360924890111598, 1.1880610574361978, 0.5497178907164885, -0.9219869496426771, -0.9138878320175428, -0.0020044783647871173, -3.00392734420379, -7.464231727177603, -0.06237688199668617, 0.5396395406599473, 1.5916997916111992, -0.05738715751635651, -0.5250204129896399, -1.4426568522014724, 2.784465228943891, -1.1477628876355814, -0.07185708748405058, 3.3043516452343145, 0.7558615379175061, 2.0947361476834656, 0.3125700721238192, 0.39712193692297504, -0.16936483088407828, 1.5559490284317539, -0.18687451069195263, 0.9408092416819568, 1.2090595177448693, 0.05722047161467595, 1.7126004215883097, -0.21796518184110403, 0.13386389491120954, -1.627124105479537, -1.047626158268438, -0.738164516769106, -1.1447901190481333, 1.8285887358098247, 0.3434222164035639, 0.08823829132344291, 0.37015911850933975, 1.5560922350816653, 1.4882392322716524, -3.830567287599687, 0.49909232798147346, -0.0172075881843672, -0.49036527994144247, 2.306341307718991, 1.0071928784612876, 0.586804872205362, -2.526198557066416, 0.29523729300768475, -0.10897798370532007, -1.1217861197460681, 0.7816067513558353, 2.842505542068245, 1.4825168867846403, 0.17392282888215713, -0.22118875462759138, 1.371925558724227, 0.8823489249946311, 0.8589520400536587, 0.7096830039417932, -3.2280044646541786, 1.725441661285784, 1.3748797282881904, 1.8839664880554345, 2.8677033009963155, 2.232650979828089, 1.2176911555387995, 2.284472891829333, 0.3137999207667049, 1.7756913757502204, 1.8506743167152044, 2.193572764991494, 2.2160116072123355, 2.6312996653230685, 2.861010170902613, 1.9409081432332087, 0.666560431852889, -0.28546266583845614, 0.45592199605732836, 2.655871624755766, 2.880371758262336, 2.505560877575351, 2.4596048504325325, 0.16494506299073797, 0.10638236218294315, -2.8361375336251813, 0.3946966124637792, 1.8634709714228066, 2.2427487293418453, 1.4444744729744254, 3.2203874735945113, 0.333503764398689, -1.4064892513225191, -0.5925183289303837, 0.6515493918304095, 1.6564482709023436, 2.3711851998102307, 2.5269914082438527, 1.4660698216086292, 0.36128250124140393, 0.9837651199761293, -0.8652675283153347, -1.3573307942732684, 2.5089175128874848, 1.614846962848561, 3.6600407382149864, 2.087647676744297, 0.7529295338045112, 1.5755822609131311, -1.8212956412311396, -2.3946914404436312, 1.8761270965568377, 2.0634944776909747, 1.4194098639871058, 1.5641312537183016, 1.1195364597379034, 0.6762191908139601, -1.0411680731186226, -1.7131762189052022, 2.632339217736227, -1.923688927245792, 1.5024595365026054, -5.0824029427840305, -0.6699824087593392, -5.7245825752934065, 0.12306336859942826, -3.185300556377756, 1.9022418334947444, 3.2287661150957385, 1.0594924314199214, 0.346739688804177, -0.8425654671409354, -5.391774845257763, 4.911472818964345, 0.1492695061871132, 3.0093926222978507, 2.315313909660773, 2.1522102371504164, -2.734444806312501, -3.63189679086176, -1.328453739773637, -0.33433372671838557, -5.707801873687732, 1.3620799696270276, 2.5972701758143923, 3.736354288321178, 1.313045988526849, 0.04395296614683761, -2.1481853061110003, -4.461864038472001, -2.480948215796033, 1.2850973987424315, 2.553001035177455, 3.130177473939492, -0.1450093904608531, 1.248848798829579, 0.6492999117519793, 1.3344698584154213, -1.5776216577790716, 2.6254057066931096, 1.1260392465110836, 0.07418111307099746, 2.1639474522943796, 2.5378129106143827, 1.109585908656965, -0.20838137169549728, 0.9356440750676606, 2.0092934919823557, -0.10396784513791951, 0.7468812391992157, 1.296404679983782, 1.4136514846031656, 2.7915453702306046, 0.820382418498941, -3.148799347652853, 1.3315164593997535, 1.5187280429332815, 0.9294775761483546, 1.9056361166759266, 1.5001981074145985, 2.926800189984842, -0.06542605370478083, 2.0063081762033126, -0.8950760420075009, 0.47913035960037403, 4.367336646734209, 2.523617714243683, 0.9998389375026628, 0.07389972720883402, -0.35523536248650656, 4.814255262634056, 1.4337456791441543, 5.151284114444117, 0.4909995811222535, -1.526109999542447, -0.7863864021800093, -4.193086787262415, 2.9900846781054837, -3.405164606135784, 0.9758994335455724, 1.1767384622468149, 0.5140207775120605, 2.2697837431532024, 0.761250676279842, 2.027744813181538, 0.32746822096718936, 0.4570272385535859, 3.691076274993652, 2.412359085169009, 1.694016352671218, 0.48053716900032906, 0.9146774955646715, 0.23412668429019204, 1.2498347832978092, -0.9380088787285858, -0.12222408104844337, 2.440895555994572, 2.366653661324833, 0.5491264850474763, -0.2814155542659764, -2.339357682448936, -1.9030192246012945, -4.151880709362688, 0.13513561095872534, -0.07413666049418868, 1.3336382605947408, 0.23293544077437986, -1.776488311871622, -2.290050374740156, -2.82788004840134, -2.8477456632715463, 1.5631244061533751, -1.0785592941040663, 0.6070703419979915, -0.6818128395230364, -1.1916803820855826, -2.268755826419081, -1.7498000687694317, -2.2625578617165565, -2.6794332367187734, -3.403733765226931, -3.156756383530733, -1.1522227483545981, -4.459284291024008, -1.166089018844031, 0.04561355566063872, -0.40065624713673453, -0.0001025199380195767, 0.007800176279970514, 0.01918340364902148, -0.0023987998932780133, 0.014973680638386206, -0.012150356402014544, -0.011454530804695376, -0.016895545263505354, -1.8147964694588483, -1.6959105589323675, -1.8864256928499863, -1.3452366980724775, -0.5598751230545964, -1.22773517069009, 1.224768955541832, 2.2232300108779217, -1.0200922467776838, -1.3194005416559904, -1.3666817412570784, -1.1342153971226627, -0.6946655869216135, -0.0876007807230565, 1.3969311910103346, 1.7646020205394966, -1.388160869272367, -0.8246863898847004, -0.11683964094196442, 0.07096223130686571, 0.6709349641899486, -0.878092261410551, 1.1195839031770536, 0.45805933579547337, -1.3598276307268147, 0.6430744372650546, 0.17962300815734827, 3.901687340751524, -2.089376268034235, 1.183634155563535, -1.2332837278535336, -0.060844030970684124, -1.1281408556895125, 0.05367896953640669, 0.42103861665817144, 1.2091856929211595, -4.707505634107107, -1.405410635310163, -2.8605469033703783, -1.7503914633551079, -7.303678860454152, -3.29154100845084, -4.539150075783841, -3.3900452536556696, -6.333711365824375, -0.6084406097009255, 0.15953141805965507, -0.6041964872985451, -0.00030864968319881494, 0.021204398746224186, 0.018000786214895207, 0.018595406231765213, -0.017295864647695343, -0.007507810472447431, -0.002455469800083941, -0.006622229249126829, 1.0986505885532238, -2.5171766242399687, -0.8317926930476471, -3.676753146989763, -0.42935325747280917, -1.441572687741537, -4.506421063917458, 2.352763257072861, -4.788926712081612, -1.7628306298125795, -0.7697677653698174, -1.793259306150552, -0.16506439846611656, -0.5874015516154373, 0.6950007454761862, -1.4136807404762848, -1.6094235246370958, -1.2855780660524936, -1.1294769879002093, -1.4329625956832415, -0.2920546698447466, -0.44612550375313853, 0.0004339997865019351, 0.34856106037610013, -0.61453110399274, -2.567234421770053, -0.0589094776989834, -1.4328408643983324, -1.1815536615092954, 1.1802669819152425, 0.5301102904106376, 0.9619806174750147, -1.418591770256209, -0.7464904638552936, -0.4898876266129822, -1.3756188596267358, 0.22819622422859986, 0.4244013088060106, -0.3560728215416694, 1.6323909020604688, 0.33572774425340074, -2.560973502870829, -1.4410585630680781, 0.15942345615466022, -2.68352433363634, 0.057414778004658405, -0.2587350466505445, -0.527673097110916, -3.0125059350593375, 0.0006697227415877662, -0.11475216876874869, -1.2451376233394726, -2.7066976239066576, 1.0439725547559608, -0.24467174504635747, -1.5288816879895066, -2.850997021390244, -0.9673113697763168, -2.9362453677751583, -1.4531815985665257, 0.8230000937316366, -0.6469927099779547, 2.761548591684031, -5.439047961779441, -1.865361829055783, -2.50486419087861, -2.422947697738446, 0.5016082787964794, -1.245229462878668, -0.7714425521560198, -1.3975143775422703, 2.9034901095118077, -5.149330243076182, -1.5507526955146727, -1.6331374776150474, -1.4016940180393975, -0.4352948895459142, -0.08106448249299421, 1.1882830979053907, -1.4522436505234497, -1.5140251197345125, -1.6656286171050059, -0.9680129491949228, -0.7907990449569607, -1.1423174812122971, 1.2998313799344017, 0.39534101070921335, -0.902188192860032, -1.9126763693415159, -1.5686623716307833, -1.556107631064317, -3.241180090728084, 0.8015137124527276, 0.37175561777094246, 0.6448671717497921, -1.2668540492569276, -1.8749476923130215, -2.4076412979833086, -1.0352153268303759, -1.2423942594150248, -1.8886205570221313, -0.6355459687677146, -1.2478859233474269, 0.9656020119449715, -0.11577740106689345, -1.3148220943096063, 0.07390005647001821, -1.505383307850851, -3.677995437511451, -2.2470346398051464, -0.8753279106524012, 0.1150812847255292, -1.8395593385532478, -0.4797224845574267, -3.4084549123439696, -1.0806867682697485, -2.209321289468499, -3.371907060408671, -6.21348358616486, -1.4013552936343439, -1.2826176482880063, -0.15227256518102505, -1.07226248032843, -1.3227594431130825, -2.5231986368572277, -4.790027329166523, -3.4076418871361915, -1.6097042328375364, -1.8405854907654782, -1.015838911982408, -0.7148046352048232, -1.5622322798952388, -1.2807501894763573, -2.3196981612980103, -0.9111953976760649, -1.9426740645127438, -0.8195009719503066, -0.8233325340997507, -1.9460029605840676, -1.9970852696490924, -0.7318622188731335, -0.2527189989280183, -2.6326136776301174, 1.0068718873746225, -0.7463730719910981, -1.186109302520179, -0.36049342643857896, -0.125440427941521, -0.9953217817586227, -2.6970363125158086, -0.6622128908243404, -1.5843106283853037, -0.8665812317789149, -0.2871408497875907, -0.7173211545671416, -0.30836966308262187, 0.2599629251726046, -0.05745141178953308, -0.8637269728112869, -0.9913524551143327, -0.0044749764804668515, -1.7891310705833525, -0.6885039376944376, -1.2858911202955636, -0.9136526154206835, 0.33493981454354926, -1.3239616781862704, -0.022716320160472897, -3.0556653368182567, -2.1882301378653612, -1.4970233373986845, -2.1310640649649155, -2.9689113924643897, -1.1032016792883024, -2.314678115348099, -1.944577083655907, -3.2632129031741837, -1.1563258169603945, -1.5284620182741053, -2.6636265495515583, -1.0066613327601202, -4.44267056593007, -2.121866525476231, -1.4253315751161408, -2.6787907556488824, -2.197190810036227, -0.7051615102495489, -1.5615205474508156, -1.3572091608074974, -1.5435998901966415, -3.1786869032482015, -2.801847150634418, -2.6586443783131446, -1.6132246276880535, -3.151762749617502, -4.0490872278058205, -3.300221748030216, 0.48076721329184846, -1.3213162228131488, -1.7025241314699577, -4.8259200147511025, -2.6359144095795193, -2.7659134598680315, -2.369498821574487, -2.489759480814084, -1.9646692009446673, -2.383995495677761, -2.4938128158900907, -1.7104408318978026, -3.01344899615835, -2.239847044196372, -2.1411932722010762, -0.22723991004880367, -2.820736021839346, -3.0061351594499492, -4.445328586502494, -2.2420793452082557, -3.674030082680046, -1.4001734345363475, -4.557713297504816, -1.2430790135783067, -1.0807428747665044, -1.2746505166212363, -2.382916468617406, -2.104978084674752, -3.549059733494913, -1.9026850057039282, -1.3592040398392424, -1.051314482479755, -0.9261018598136022, 0.16007632347239178, -1.8092226829837292, -2.9895543134847418, -2.6310465369512412, -4.053957750360441, -5.325170104946332, -4.0022541035247565, -2.4200260593552976, -0.16140235478985124, -1.4787825801120171, -1.237706788993475, -4.3442499556176815, -1.4496683609050511, -4.752046493057694, -6.027393505249503, -5.178241053494172, -3.2800145988361225, -4.137496222436294, -2.1984900819228312, -1.3241861883335302, -7.471142883395235, -1.1724415587273707, -2.2639273329412095, -4.995842982520551, -3.425930677574729, -4.625378819587171, 1.8670394648971658, 2.3588688552567794, 1.1928666689500915, -0.5482232326451718, 0.17132998833719246, -0.5161703082810717, -0.36090268873389597, -0.5594416295302231, -2.706641443500429, 0.4953351838413329, 1.5673250670103638, 0.008057756927449955, 0.32810270280171416, -0.7483236343286743, -1.122258731877144, -0.07685637153517484, -0.13666764752630348, -0.8034426461923212, -0.5756791893950083, -1.7735322521494887, -0.8604580295775162, -1.9541410700300113, -1.0112545997944289, -3.8413946142529936, 0.9986462222712773, -3.7891823009618215, -5.446389773157252, -3.038812273622635, -0.3125337951646531, -2.0791021156417466, -3.2604680174452887, -1.4216840628429155, -2.7086456409631947, -1.094728913372484, -3.2628343055962716, -3.5275025312639117, -1.9672921322829255, -3.8227837368641193, -2.315776550707679, -3.6456663768806545, -5.3036676851841875, 0.40958783144494365, -2.568387935994735, -2.861911995569666, -3.67468779857304, -0.9131261608588591, -5.949014975245573, -3.730989683397705, 1.463896254419755, -1.0491562949869042, -2.3098013520673573, -6.3650635679903385, 0.00363774011431204, -1.8916418490892097, 1.5344958312100878, -5.081528543318621, 0.8925489511771458, -5.539128870647195, 0.12946264958882625, -3.9122647755190836, -2.8380155105117635, 2.3518911029125715, 2.2005697926898664, 2.545914483842103 ],
				[ -0.017013533090283285, 0.020188511272838567, 0.009906528357001529, -0.004160755436193333, 0.0034369971938890097, 0.00951482716986452, -0.008635753409812843, -0.007892787402759225, 1.2741556512657388, 1.8901829984584138, 1.3798749388957927, 1.9573907839010138, 0.8834600275590099, 0.9117977051107137, 1.314057853839535, 0.6617785657219396, 1.6695183206932211, 1.9390468524818918, 1.9132049831523485, 1.5408107944974931, 1.3058570641147174, 0.9827816086569905, 1.2362775245310196, 1.0859776431510002, 1.3441447635559787, 1.3987767141106642, 1.2286527680055455, 1.545848433191219, 1.0659583978760867, 0.8352954270104155, 1.0905022704097287, 0.7895087345262016, 1.2975923591240301, 1.303725881634099, 1.3341878059073013, 1.2527472760072351, 1.2481948160934442, 0.8380647561323717, 1.0437729220853422, 0.9597457726151519, 1.157814649636809, 1.132438539835861, 1.2303931528219507, 0.8437879870378606, 0.9268496556712892, 0.7834922060199724, 0.781260622176715, 0.8322753084527854, 1.1764483161436265, 1.2192310934037442, 1.1513858248435431, 0.9320890792039073, 0.9583681509318384, 0.8496279013884688, 1.0063316887112683, 0.7995062908790327, -0.01888508968635972, 0.000655793372067103, -0.007947629694750812, -0.006207959331887435, -0.01067673776938244, -0.01475843693135429, -0.014030276132972468, -0.02088589305112142, 0.7030644333818136, 2.0418793673997784, 2.6842055642050235, 2.1882848464450957, 1.3597763854319966, 1.8913339026033251, 1.8908610097082004, 0.8500279154681828, 1.4507450283283438, 2.200806419393987, 2.1757573695441677, 1.8193273146630191, 1.7373404720459096, 1.6962332680344943, 1.796520986966325, 0.8950904972901904, 2.5107693677844987, 2.4102744862726175, 2.1239988586646747, 2.4520102156589885, 1.7101785215518863, 2.1610785408874547, 2.2079124061894317, 2.363485310260842, 2.3407934116998295, 2.169371875473333, 2.3039272365767105, 1.8707429348881752, 2.1057192981038675, 1.5305848713025074, 1.7914290083231281, 2.0586740921941056, 2.1292050409430163, 2.4845971647621514, 2.114287501541607, 2.0461608124593234, 2.0068237061999636, 1.9653811458784067, 2.2783159343052573, 1.2010594207843879, 2.324182058954308, 2.245213733951773, 2.1417291074959723, 2.0658006709143124, 1.9099087501442331, 1.5167797224604334, 1.781216066857877, 1.3605388629651878, 2.271240684920618, 2.5412279422433115, 2.004447131596147, 1.5549839770318314, 1.9326075729136998, 1.9833973151315638, 1.1799998818088593, 1.6848068406132204, 1.5106349088535527, 2.0549185156548924, 2.0205358154726443, 1.9888498451564047, 1.509861197750047, 1.6190216961340034, 1.6724274167431585, 0.6837832111733154, 0.3044890833740429, 1.3179269595991157, 1.6768283100391106, 1.543391211048563, 1.8067678910150082, 1.8027343969094956, 1.7387870454296666, 0.7965222030377467, 2.7344283473607423, 1.6587297632205642, 1.914889276454344, 1.3567271600612953, 1.785115179509076, 1.7824055152534304, 1.7647210067515633, 1.9744383674837627, 2.2405391693033185, 1.93590534838342, 1.942874936710954, 1.8384381319289695, 1.9307696780396968, 1.773455573988305, 1.6600718011261506, 2.169433105250151, 2.2610000605282132, 1.6108937187968217, 1.8380994480948674, 2.09438709347286, 1.7840852949520893, 1.942607804063853, 1.7337217584478308, 2.112552045848799, 1.8989930448430694, 1.6464762472074392, 1.8234230421808673, 1.9208601152776366, 1.7329067095719908, 1.642858021147373, 1.6099612567999422, 2.0114138836245443, 1.969077549215979, 2.231348919732184, 2.125719534524605, 1.8270696329832563, 1.5919574896499533, 1.8575381969336928, 1.793239878812312, 1.4241560233642938, 1.2411177583674775, 2.048519797747603, 1.886794927603846, 1.8137673984399576, 1.7306239622680082, 1.4650352014884382, 1.5632706091098554, 1.3874409668915093, 1.28859805272107, 1.7230759198874253, 1.892622901941368, 2.2691622321843137, 1.9426426781091592, 1.3401676369712796, 1.305962664293474, 1.4129218345483059, 3.0933249573594113, 3.2592437643434025, 2.9867619628955078, 2.92881201841381, 2.869007220827455, 2.624225899516324, 2.9942046044684747, 2.918955181590622, 3.728803691958523, 3.417042998567127, 3.416890105305828, 3.2015083645718176, 3.23941264966261, 3.0699710683451396, 3.3541657237600067, 3.325702887309969, 3.4411080694850695, 3.3274302574036967, 3.241076639265685, 2.845974115919583, 3.1334994540009515, 3.1533972742381504, 3.201996990298334, 3.2959405017180536, 3.060601443211492, 3.3124784503539506, 3.3044061901580615, 2.9515777557426244, 2.928371426263655, 3.105490803034094, 3.2635681254577094, 3.1387650820338964, 3.0193447316653916, 3.2180544345301842, 3.2172515084844746, 3.2092209891232413, 3.270932406600285, 3.3198938269913403, 3.1025866851279424, 3.1665524112556103, 2.9869749993911574, 3.4282231165933292, 3.4508951063131854, 3.0675785072418673, 3.091648331433076, 3.2801013390944576, 3.007169814187161, 3.123087631570412, 3.359151743821539, 3.377143030729724, 3.199266165857579, 3.3484470648466163, 2.896794158313774, 2.732381717440165, 2.740305836696584, 3.08723793056792, 2.8106155078827033, 2.932531232937082, 2.7483713947500155, 2.7608844242740975, 2.6399786014532487, 2.3478011699242076, 2.6724358408332427, 2.5151863065279025, -1.4288549610265366, -1.5522885330578968, -1.1407692823559148, 0.4605961688376041, -3.2715594780440957, -0.11239622676037266, -1.4629939426997616, 1.9947950127306733, 1.5366138427078169, 2.247545505448222, 2.114891900681943, -1.688538841039189, 1.2655744072947603, 1.1259208980628377, -1.1512995974929088, -1.399419745288291, 1.3138921440507085, 2.7061946603249614, 2.97645944885704, 0.945470382891189, -2.782354720364166, -0.3557835689910916, 0.3602890186732385, -0.2428261790306796, 2.7556732930613768, 2.1554519103340977, 3.3774326229406517, -1.5535698768968582, 1.6807865138725524, -0.12900932619616395, 1.1501070179865418, 1.1660432907656055, 3.025908817023792, 3.031671105908357, 2.9883222383921346, 2.3111998110110044, 2.1461500538680096, 1.9201460005634494, 2.240728806115685, 1.6349225572795232, 2.3997072774369386, 2.4185790663903823, 2.9273341913455218, 2.909079230404758, 2.5939245375389595, 1.9056317327774792, 1.3770384338416117, 2.3359709687487724, -1.449473474313667, 1.318104331234972, 2.2376811551717912, 1.1035904954763218, 2.3158117429040286, 2.6568673487635013, 2.5466696088461003, 2.588826576825749, 3.1714279132148646, 1.818356784230649, 2.7887508885012733, 1.6145051136284614, 2.1273817757388143, 2.8994440300270483, 2.164223850342381, 0.7157931022799794, -0.2278307204537934, -0.08823919320956286, 0.23817845347865443, -0.18968555550565414, 0.1359450025545792, -0.7991838941980927, -1.4166050045977863, -0.6732708779730447, -0.6000925643790516, 0.6011177033042263, -0.21247546261898614, -0.48335535810724656, -0.1040705706526149, -0.09499771549868201, 0.7167838674642693, -0.612224873540338, 0.13217592826718044, 0.5084358168500409, 0.4369382730779208, 0.1416538855272142, 0.23281663244791873, 0.051911305250836495, 0.1776619529302296, 0.37263048499375606, 0.3861781741438834, 0.47686958032809684, 0.6068113755264334, 0.2877652274817794, 0.2196880307441445, 0.21518661660350052, -0.15907913417425337, 0.37660185062274154, 1.0552665348704726, 0.35748052538155123, 0.2616841398176922, 0.4196558353531275, 0.38330388459143455, 0.16607344689682074, 0.0234851132808645, 0.0935456070102181, 0.16886326394811832, 0.11819413001937994, 0.5688588203685062, 0.43062634405908196, 0.405971491244886, 0.0629221221974554, -0.08641537869888284, -0.3329239540636085, -0.6382196502473316, 0.17504046812600824, 0.41513141158676764, 0.49278746272488716, 0.335970926739137, 0.16422754132875417, -0.3814226193122904, -0.5528402286849785, -0.41090555682537655, 0.4016832076561267, 0.31734475218153047, -0.06072402759584738, -0.2824385080478214, -0.14018591320752985, -0.7390321155586697, -0.6084623549571886, -0.004530628788755956, -0.006033837243157809, 0.003911101698131501, 0.011894712527738072, -0.017024692924662015, -0.016858060263753635, -0.002849235127811604, -0.017569554736022668, -0.27607930537027486, -0.4113024525008254, -0.3334652283561437, -0.2518287401828787, -0.7296316791729471, -0.20397251355500481, -0.3294148208521813, -0.5365087217909682, -0.2398158499138528, -0.33118815032412496, -0.23829671142941727, -0.5271701827046296, -0.4222400086930557, -0.3577082306996415, -0.33669656202816967, -0.7162785550024984, -0.11292539345245503, -0.144047647648871, -0.20910280653829783, -0.3961311491550299, -0.4759537071422909, -0.40335579443437125, -0.3194271169409096, -0.5326851207282287, -0.015830029924802265, -0.1399268723782588, 0.08496508132572608, -0.18924819584241304, -0.2935365068864071, -0.4371730625677889, -0.26038996134062264, -0.5696680766218564, 0.1456449585024463, 0.015552924091725614, 0.02550080010138517, -0.3551765353624788, 0.027021623558479924, -0.3791142791237633, -0.6456348961938183, -0.6467441871051777, 1.8424023682262884, -0.134153704444761, 0.5345143896745319, 0.1201574589422985, -1.6478232257004375, -0.889376415735783, -2.09364927658084, -1.095936587076723, 0.01920941067462461, 0.005578303884802734, -0.019884246181262118, -0.015316559213896906, 0.01697598956439595, -0.004017431464603442, 0.018209484227186667, -0.004176187394559817, -1.4786117489706712, -2.3582474288635655, -1.6967891141906528, -2.194881220743697, -1.7186147957564304, -1.182847983415015, -1.9735694956583236, -0.5723925821165279, -1.9072912654614986, -1.5408268979675568, -1.9594093352591053, -2.33521810871166, -2.2878714863493435, -1.867342017740043, -1.6607211723199655, -1.8514898835815345, -2.314910564588538, -2.1844042839922087, -1.9799824593668234, -1.988052232409524, -1.770059389533274, -2.157462782443813, -1.957494503683599, -1.9964049413150282, -2.0786417482615684, -1.864425841409173, -1.9333042561353093, -1.7374367299996303, -2.1008702758382514, -2.045059974579781, -1.851502892025624, -1.6764099712302027, -1.555393844779318, -2.116185054730445, -1.9222143985069235, -1.8068429873344627, -2.289787890661746, -1.5544832180937802, -2.075995946874988, -1.575378168294769, -1.728930596920195, -1.610558285370065, -2.0131894795531595, -2.0704148094393378, -1.8761030833384034, -1.970925213349903, -2.027654395321109, -1.7624153114948529, -1.5426013485418237, -1.2678575812357613, -1.668940943342217, -2.2772340483938134, -1.4644968974003525, -1.5397310926137313, -1.2276995858864617, -0.9338423959000619, -3.598382059869277, -2.9272664844625713, -1.5552079938758325, -1.0469268760213328, -2.3220687080615496, -2.207921040483593, -1.7295730156827078, -2.12644297864532, -1.1721760233733851, -2.3998554125360103, -2.1338080073152947, -2.295754800169804, -2.0285450522659025, -2.135034996158313, -2.077443201553187, -1.7532750099152572, -2.2613008799772873, -2.338048932753915, -1.9996350399121816, -1.9554803299643178, -2.2737399053916088, -1.9050160312486755, -2.425098749258553, -1.9535899948288027, -2.1180840246684527, -2.411194020042038, -2.154194273992869, -2.2021603864931283, -1.8261069887411983, -2.2774525014322444, -1.9507860851702994, -1.8522180479214816, -2.31987320332651, -1.9159586191253735, -2.0247573357519855, -2.049898572913829, -2.0991643938838718, -1.9714031649380415, -2.2913359128425443, -2.2332556420735505, -1.8052953150921283, -1.7764288801065562, -2.646902721187943, -1.904510111590018, -2.198688387681574, -2.4812166372926066, -2.3180650400392766, -2.3262772387398685, -2.2331531064402044, -2.1263237573947147, -2.5848241302856363, -2.16647207827086, -2.4478643311387698, -2.3441238880430384, -2.5370938939309737, -2.103186702696457, -1.8868665264079814, -2.5781367152729455, -1.8894740082963863, -2.4893483107096444, -3.2780768295737843, -2.698544430378072, -2.08863825252259, -2.26493015514457, -3.3167182756497127, -2.679587817961135, -2.900381420026226, -2.704077713848827, -2.4822126267533027, -2.388564756998297, -2.591013923651619, -2.537000286152033, -3.446914989618202, -3.224513279990186, -3.1055661017917497, -3.3191476158789492, -3.4967520246412733, -3.3808127464920426, -2.488882422310461, -3.355634491040914, -2.611666143809258, -3.2363951764230485, -2.9671244804040096, -2.7608305941020688, -3.017900516563381, -2.8498791196079147, -2.842085563682111, -2.7918530276827647, -2.874934635072454, -2.959512370277772, -3.139057517390886, -2.8898036963937836, -2.7885895281293047, -2.5297399234035667, -2.651463427202039, -2.334004876161369, -3.095067836539587, -2.9047645537656783, -2.986606857189976, -2.694834778152885, -3.0634174671351206, -2.7994876821746355, -2.88570228397824, -3.0012981077273615, -3.1058223345199636, -3.1392902833326652, -3.130978927715704, -2.876079860948847, -2.9934570907627056, -2.975812740988197, -2.701455855275126, -2.8449504946288657, -3.1202619032659213, -2.9742207758214967, -3.317171381038762, -3.2422223036128917, -3.001818061020068, -2.908904645927938, -2.850146358621518, -2.847068265163692, -2.825789147379822, -2.930283771879081, -3.1703846643126923, -3.2515052065800987, -3.337802074388335, -3.1193265171818734, -3.0940751699724163, -3.0232939112764203, -3.2019672350421717, -3.164287671460908, -3.4199539385639546, -3.1862916574960267, -3.383111558142825, -3.197133087177686, -3.340697277181429, -3.153501281978075, -4.493035079686753, -4.229477339113921, -3.562845477374357, -5.03893292989951, -3.968997261079083, -4.346771706603868, -2.194732484777822, -4.476252670015991, -3.969954027300556, -4.054721583195306, -4.2482272657153395, -4.2513018815800345, -4.824124953844426, -3.6731152312686146, -3.428382673159773, -4.300837769929048, -6.800571400164045, -5.967367809890729, -3.907819841465451, -4.518969510397485, -4.4191405012076075, -4.767149997640121, -4.317334611250335, -3.0046338880241086, -4.664035248121833, -3.3801907653828307, -4.4890823630653705, -4.0649464891216684, -4.638476590630096, -5.7115676431292455, -4.674133916209378, -7.097887480150523, -6.143606959805465, -6.095578287328838, -7.088163034728184, -7.486835218334581, -6.6300903361353525, -5.797480477477685, -8.217722943341215, -7.075235119052079, -7.766827270626039, -7.208015015359273, -8.028190861179944, -7.691194340441957, -6.631381155381689, -9.362067963886558, -8.68028933578533, -7.816818173674244, -8.041312837716267, -8.165841129593877, -7.454506702873008, -8.534917215210791, -8.376929712371282, -7.183461714964724, -7.8610929867474635, -7.938422762882565, -8.523835768223776, -9.20939568276684, -8.634968544579282, -9.498472288659716, -8.393729183774216, -7.1078691050622345, -8.576024656333118, -7.539980024723624, -0.12051674701558195, 0.06216568841588616, 0.005447613229457451, 0.019837750885805923, -0.06984818086646204, -0.05801282722829093, 0.03878721586407567, 0.519519332240945, 0.47928933396250695, -0.22449520033199438, 0.1416154344828367, 0.14227314890244988, 0.033181030583775556, 0.12242136726216915, 0.15168630199167862, 0.1623268845470403, 0.009798445122247323, -0.07161446729796102, -0.023875060331796996, 0.15594376769204185, -0.0053743353060702334, -0.08277662054473853, 0.09805265748792052, 0.13318497324853787, 0.4568420967366593, 0.18791511487046939, -0.2475566482842677, -0.034124196064515215, -0.10807161210390075, -0.27236875651689635, -0.16172443351515636, -0.01766993185714852, 0.6276291703861473, -0.7315770689882583, -0.2349524459453113, -0.4197231453706057, -0.47257470644964017, -0.21020757309872737, -0.17317320859104612, -0.29773204818187426, -1.0272352863986252, -0.4480841464567844, -0.500289051302571, -0.1881035405789, -0.33141440464968946, -0.721869082390955, -0.890989846650795, -0.1904587440779283, 0.39934899834063264, -0.9810712844449696, -0.6149512766793898, -0.8094715290210204, -1.7778201378330234, -0.4836490928670648, -0.96108710107721, -0.6042331904397802, 0.609270996322794, -1.0274938870421624, -0.5853863309789109, -0.6811626071913842, 0.6130810990877666, -0.6019797691487017, -1.8592865958888085, -0.06097326487558925 ],
				[ 0.004007733571819605, 0.015123298151569485, 0.0007077647321060979, 0.015611298055200623, -0.010857783450722963, 0.016561933285659112, 0.00986407779986741, 0.015537323536921109, 3.573652465280943, 0.9573773354133738, 1.0485147728755808, 5.076277860497204, 3.1430545483559085, 3.5219453246395207, 2.4891936346311767, 2.4888734583565655, 0.575938562872485, 1.064074498605084, 2.077842291049603, 4.459363331703595, 3.45776650628576, 3.5586465225523813, 2.6248844345246924, 2.439513800585641, 0.26854394479637367, 0.9339763634636362, 1.9896967636567653, 0.5206762758348287, 3.835803908924142, 1.9618591907391347, 2.1202162680904864, 1.4833543263276607, -0.5204697334780759, 0.3755428918821513, 0.3354827399158586, 2.5137359224793485, -1.062270764660409, 1.474390512892652, 1.161161060793408, 0.7811687705749915, 0.06627281449067236, -0.822552794155842, 1.1240692900652263, -0.14672964013236278, -0.1858956117711732, -0.817762362141636, -0.027434128771213116, -0.7191334686301035, -0.7926669594506855, -0.9033688051914598, -0.3053610343414168, -0.6322174713756584, -0.9361903517324484, -0.3544716901480219, 0.126844775352263, -1.0178020647772779, -0.004608309939171877, 0.015380588795886222, 0.003520340175772196, -0.0045216056182061145, 0.0037350284364886938, -0.017706455063649658, 0.009523755934650572, 0.015529605433493457, 7.116320276831096, 1.2988262830294952, -2.4383869975962926, 1.4324344327415717, 2.5866361095251045, 3.3658168423593158, -0.48155739622863303, 7.0592918990523, 1.6009444110955044, 0.6919725442598762, 1.9004460243420676, 2.8892011419585732, 4.299511993619106, 5.306417317134971, 3.7089316365852305, 3.9682583885890077, 1.7282479285654473, 2.7582407025306472, 1.6919281234682357, 3.0547235280425102, 2.8711722600330347, 3.3118098630588246, 3.0643315788497376, 2.3445845530128473, -0.9759329571593942, -0.227720128057391, 2.5327740646564014, 2.3082886896012798, 3.5895497846493836, 3.328647625034449, 4.137166445047537, 1.5987392207404914, -0.7225257021445692, 0.319919448198061, 0.7481314429674083, 2.389736799634083, 2.694917267063117, 3.091937833566765, 1.995709676470689, 2.5683327659976336, -2.8167827632405116, -0.9807259244890646, -0.01660610571395376, 1.333439257041485, 0.33965835019444596, 1.4105133217580275, 0.3664212764608071, 1.4365351389491534, -0.08108968836481582, -1.1866602824845847, -1.305993190669992, -1.4049438876747364, 0.20574878452783607, -1.787919798607412, 0.7412505041856411, -1.2078660907129115, -0.13099120843290477, -2.4130765786780386, -1.096858192223457, -0.7975616266535229, -3.409097911961039, -1.35172096027731, -0.24748704802311008, -2.1379016059015474, 1.8291781271666467, -0.6315844750322569, 2.8992477417678257, -0.6945687928293648, 1.1887719323957608, 1.8347062250762423, 3.58647274109153, -0.13419097462102356, -1.3850541319076928, 1.0885232924641763, -1.8994731595807868, -1.1354698579571587, 1.0071798490679338, 3.585381810410559, 1.8172609186653408, 1.676405022235947, 0.5687359144754629, -2.5927788597625216, 0.3685997794914397, -1.3343937486537805, 3.244983693783488, 0.3825820848490498, 1.6992880237944978, 1.151117672988436, -0.8976178488432264, 0.7496439156205565, 0.0001479424233393848, 2.0410577009975306, 1.305592683586872, 3.9627609015759186, 0.020506019955867535, 1.2471609177356457, 0.5491604191573791, -1.0824452774816427, 1.632124125288987, 1.3018792214920807, 2.796686130416036, 0.6974258593334867, 1.2674316267671564, 1.0691700275334965, -0.8040491070499897, -0.015876035146029668, -1.9089596061940728, 1.9746717443833735, -0.612773528043115, 0.5328740242474584, -1.2519170023064494, 0.543277646215678, 0.0929121379294471, -4.515555162260851, 2.0018261225839815, -1.4785077286692787, 0.5675231665299623, -2.4295318579119303, -0.12667360275637735, -3.53687828443222, -2.920402878759117, -0.0929899347658655, -2.214698023362103, -0.2952048711238299, -2.9277720390548527, 0.023530243729825442, 0.2832405952055462, -0.8980917499367956, 1.73656989754764, 2.564099973309987, 3.687587000988249, 2.732185981000492, 2.371456845354178, 2.396202841931645, 2.3916420569070733, 3.1735427273352377, 2.8016807741787386, 2.567427625948057, 3.2744947595620078, 3.460944173014159, 3.436542436449552, 4.518967870080738, 3.9980282986925806, 3.461355549320217, 1.2105535082183139, 2.607628928637354, 2.641529426081323, 2.6923572374273808, 3.2409429523965096, 4.232565389111902, 3.1568426561616523, 3.1193843029147463, -0.1757357410811799, -0.5548721075779718, 1.2826150368198264, 2.655340976301081, 2.7162926852738076, 3.3626190557830222, 1.7646285115208318, 2.7843531153550987, -0.7254529272701307, -2.1069185068851746, -0.017391918847550734, 0.6941912925662799, 0.022192981876396043, 3.2057205849947397, 2.094842067834649, 0.6736241314327376, -1.1636418597946425, -0.7674118832746957, -1.6553276182633887, -0.7539222232649606, -0.4308976338483004, 0.7526020200787398, 0.6464323233838789, 2.005138065054376, 0.5624808751664553, 0.19828741609670072, -1.864337427502066, -1.2465862039191318, -1.7888386997017185, -0.5843946099573132, 1.0365212916214663, 2.6688722180011792, -0.6712496026935617, -0.2898463626858687, -0.9865371117039372, -0.9067082256682538, -0.5643637140441515, -0.6578678364917904, -0.15129357728522236, -0.2702836489975841, 3.72913389660677, 5.692228138700123, 5.059550602787942, 6.3580324859176995, 8.656949150859687, 4.468461532747735, 7.459253162145705, 5.032838625426684, 1.8468810326686131, 2.8892540426199336, 3.169239665888064, 5.688736703704848, 6.951226517197471, 5.159510572217519, 5.3810383671665365, 6.212461919449497, 3.473362016039718, 3.8869271579161353, 3.663006946255414, 5.891100732905464, 6.338971043980043, 6.793699303049183, 6.3000849405457275, 7.972798721135411, 2.2620090086238105, 1.2502621589478993, 2.366615106524446, 3.787113001479866, 6.618638229873439, 7.155521221299628, 6.32532989833132, 5.401632096278706, 1.3218171019540872, 0.751225971197907, 1.4249317736776406, 2.977640409660278, 2.8278661898379918, 3.8953841513659166, 3.2843953188823543, 4.031156350199271, 0.9327505254718343, 1.623729733194721, -0.3159842568151932, 1.7215221475921814, 1.913770898341741, 1.648753006443655, 2.068568034739292, 3.9883621262028672, 2.4757919721193833, 0.9202712188627763, 1.5198806799234124, 0.7917679388788276, 1.5378183844422575, 0.12770814831519173, -1.4253485155980683, 2.152956100866115, 0.3788573598918487, 2.1279581580153324, 0.9099859469221041, 1.073260353349154, 1.6624871685698, 1.0846608097963344, 2.6601440495286317, 2.69080000257713, -2.085140940846132, 1.5389783049606314, -1.9018207907580582, 1.9009168678322954, -1.7403590682642776, -3.5725978150302025, -0.7001529221523167, -1.4257611960196936, -1.0847048070615792, -0.9198121758004716, 1.1078797003360445, 2.0914442236325614, 0.08830659288458613, -1.3411416967142649, -1.564011837249851, -2.413291536785472, -2.707206606633341, -1.534578785425374, -0.8888963060487208, 0.25724070191834, -1.1506612555604, 0.44134631192827367, -1.3948775257916688, -1.2739778464726235, -1.4495580460082074, -2.376029381496804, -0.6693208341287713, -0.631789937526002, 0.6460026614990559, -0.5314533279517092, -0.6656147774826809, -0.46189990937114606, -2.3562292965532086, 0.19368352165582928, -1.1028996233329598, 0.05597236657952526, -0.5856257422611556, 0.2383109815601239, -0.11711540697555539, 0.9134820623303114, -2.0471777465103074, -2.2285437346527637, -1.9491261223558058, -1.4140081381401308, -0.7462539114866193, -1.1927737378564294, 0.0940308035994332, 0.020778511848753373, -3.505397476427898, -2.1654852257549226, -2.3639189965127145, -2.0422820084056887, -1.4077424118608795, -1.256486079765019, 0.24204044523666246, 0.7972509145802715, -2.5531621871243626, -3.5546799314435287, -2.85260953510188, -1.5130596585591125, -1.7070481477826585, -1.5902818525356401, -0.7874892929713793, -0.6021713342026352, -0.01189410541026705, 0.014374446701863462, 0.02068181788224633, 0.017093729641137614, 0.012891790866269057, -0.013949589261348412, -0.0008672496444150988, -0.0004805978720045049, 0.9115492335718657, 0.3718163339901891, -0.32297228446959564, -1.2640893079543332, -0.21194281687705185, -1.3354550026615835, -1.5604088343125386, -1.1578256623807721, 0.9254532399672004, 1.1026035917469295, 1.1693903883021224, 1.030567777209246, 0.5798266969546798, 0.25761676481401663, -0.6450171820795321, -0.8670996561529556, 0.9808414390747147, 1.9935712366171363, 0.5376091588610665, 3.125892368180313, 1.8276854234759388, 1.423288313759905, 0.46902175608421126, 0.5208668818440408, 1.0326478013092713, 1.6693703161833193, 1.5302429405168334, 3.025718031107323, 1.877860438355901, 1.0182294819547906, 1.1981686139509198, 0.7962000425318267, 0.5599308361169465, 1.9674856312857831, 2.214042014411926, 2.24391645202878, 1.2894971743455828, 2.925459973441516, -0.3869412529297972, 1.6423012588401111, -0.8859792503659365, -0.862771132319356, -0.8316429175555945, 2.178714056768994, 0.3476151051902969, 1.077365818856201, 1.1596257348380434, 0.09606162823071669, -0.011445472182154465, -0.002838976003669292, -0.005490148855144314, 0.015342986694074098, 0.002048448336704678, 0.019427924311312406, 0.014272164283650579, 0.00012925039242467595, -1.4467505678223178, 0.6224460685208583, 1.8186219428850803, 2.3029213058644524, -1.467203503733792, 0.3670125473424864, -0.7130531920525948, -1.0267762592725609, -1.084820205124821, -0.5012271281697905, -0.6724142061878177, -1.1198240645377577, -0.9150854213165645, -2.1201555928539713, -0.6520508767389359, -2.476353424006923, 1.904079723789774, -1.1055354057804272, -0.81337166054428, -2.5656360973085928, -1.1846354422560887, -3.8530804605154763, -1.9598771978723517, -0.8750248015746513, -0.09062920671892914, -0.1858196373452596, -0.9029522904381261, -2.268680775884448, -1.2542488368130138, -2.1344158254776766, -2.398926314008016, -1.9337461993279264, 0.36828309734450504, 0.42409129902333337, -0.02409664645245211, 0.1219131487314342, -2.3931620014851136, -0.6422961505734078, -3.9578396655157064, 0.7101913599405657, -0.7797379497086173, 0.43258887956767067, -0.1081070937796065, -0.691539427905835, -0.8640314886801141, -4.168749378758463, -1.3033657824005673, -6.807273142871437, -1.0141116769946024, 0.6318489810868364, -0.9868242266859718, -1.104602796818581, -1.0301569135538544, -4.124577004039477, -1.7067421206227424, -2.9766292674465764, 0.4500742331807043, 2.7865988171602942, 1.879276407936525, -3.2211937059884077, -1.9516077220916208, -6.773487745398706, -4.521938725693196, 2.9993139934769224, 2.191516950101011, 0.17760885208592198, 1.7413543321782998, -0.6863413452808044, 1.4208442658334042, 0.4870710644320467, -0.07433652277178203, -0.8064527822180922, 2.998043279879757, 2.187590173744787, 0.04165464690265909, 0.9450284072764814, -1.475724227601725, -0.4476998814737453, 0.05287098432977782, -1.335569530476669, 2.322779392442446, -0.41517291447894505, 1.1214085464860342, -0.6514433797287685, -0.5529608724544041, -0.9688279663021188, -2.1318871546280618, 0.5935535057260442, 1.242538171431983, 1.4757412586844563, 0.609786665443914, -0.4077876288934287, 0.5263943837284197, -1.735355474228913, -1.1375341483887167, 0.0016215584563993959, 1.2725142341132956, -0.7425690799853872, 0.637169407080219, 0.07352409932702754, -1.5661425042891643, 1.303459916454135, -0.8935007936057504, -0.17742900491786498, -1.236869868184975, 1.4793078982253793, 0.019209053129747907, 1.068994221660488, -0.34564672910478156, 0.06741863112590324, -0.11257214740701087, 1.2584759409750472, -2.5586251683997716, -0.5160310133534227, 1.149870400946975, -0.8010067344635448, 0.6137124806553871, 1.5463177735421965, 1.1774978941958443, 1.5898284067194264, -5.967631231228167, 1.7734054337585698, 0.7634500575900762, 0.5573010944470616, -1.3999979382413297, 0.19985777496936116, 1.3636095355105298, 1.4613527148479797, -0.17180139736381014, 0.28929633360253765, 0.44783285974568254, 0.45363558470548737, 0.32977082698684895, -0.19921463807041997, 0.08798674505835302, 0.41039431770359186, 0.44889647793566356, 1.4378631124747683, 1.4862344396486433, -1.046499182079245, 0.5145150008597076, -0.3101724425993169, 0.44170889442293604, 1.604981459431061, 0.8178063166903653, 1.7824171241623037, 1.425901563206575, 1.0951536410710352, 0.7808078005135923, 0.18983655449859807, 0.74649217583141, 0.5508503890432459, 0.1428733975327159, 0.44313260188875886, 1.1102468789066473, 0.6727944012762607, 0.25281415974298643, -0.9721469752142755, -0.27541410415667056, 1.9812979711530179, 0.31467387085329845, -0.05459398667951976, 0.33044315984854905, 0.41571572229214426, -0.09732328557260173, 0.28734465495803563, 0.19708775746690288, 1.9672968095893535, 0.7663610304212599, 0.4090266137169135, 0.4403024632843999, 0.7731032332017936, -0.5428696847902811, -0.7507035538751835, 0.368871770865121, 0.6534700764526844, 0.07029233437723321, 0.5794903439807599, 0.5490396906031042, -0.22197736262396472, 1.2958189371460473, -0.7864152002025903, 0.8098923962064366, 1.4405338325289923, 0.27345251499769957, -0.011204490048352953, -0.2675127612560902, -0.257998013736479, -0.8234062410711611, -1.100871729854954, -0.404239528210306, 0.1872160452200217, 1.6022598158271495, 0.7565256889304226, 0.804814903991873, 0.451876587490774, 0.08164527405464864, 1.3425503397433216, -0.935936164940909, 1.021877327169787, 1.8491816671035226, 0.7305920515990774, -0.2679672920761242, -0.17741060885278304, -0.31654296871779813, -0.7986937677921787, -0.20782647607767177, -1.4056493608441714, 1.7736291050146298, 1.2979488572017384, -0.05885769416527324, -0.9226868660280784, -1.4075912610698633, -2.338071706630277, -0.7514541931447515, -1.7554452804280947, 0.622393339970437, 2.015023147989016, 0.024018507221842844, -1.0595844188938721, -0.8561451717396885, -1.8613701245300975, -0.8463256882280208, -0.7095394032480125, 1.8384496232475358, -0.10516532947122251, 0.5791799829273321, -0.15818274254109344, -1.2169215793637544, -0.74395293631159, -3.49859009571628, 0.008547828315151256, -0.11526214753165508, 1.0294204569254333, 0.2491079356798845, 0.23491878567402943, -1.3301461961590249, -2.7278290491087356, 0.3597982871359683, -1.1826172090632792, -0.18931302940006997, 0.7783962747613833, 1.1891244468865498, -0.08220523141225854, -1.458852230249041, -1.2774949403284659, 3.040560349024727, -2.7446878860249466, 0.8926404807967366, -0.519314577150912, 0.8796120019079295, -0.5459157987664822, -2.7588483333787654, -3.2131692387226827, -0.7557917917150805, -2.823576431092797, -1.444305917315434, -3.7408051972130605, -1.1881952508995584, -0.7424570983818507, 1.770889909216308, 0.8088781067304921, 0.5215030862592109, 0.27555108272522116, -3.1029888238922916, -2.0914269166465935, -1.2899044429247593, -1.5980192528804484, -0.9146617099359945, 0.5562121465926567, -0.015814758717148533, 0.5968419347200833, -3.0374076562800556, -1.670090269219653, -2.3599885193684695, -1.684309067669202, -0.9108963308506082, -0.1899841285618497, -0.8695305104683567, 0.20277124046905276, -6.093564817531071, -4.430015504080332, -6.2248706401759035, -3.696505580521422, -3.4930548214406207, -1.9834392589638314, -1.7102674978553958, 0.004221247384705773, -2.235819016278835, -4.925701764894449, -4.860577593535419, -6.1943840697977235, -8.641888666311747, -3.8849128138858813, -2.031984101764576, -2.6428677371133498, -4.0140365599199574, -3.99273263272722, -2.7773038072453833, -5.198215624754875, -8.972687863911556, -5.145643129688341, -5.555234420715497, -4.367522985657403, -4.546612993896375, -6.444194649782824, -7.97799767582466, -7.1353294853101215, -6.5315925559408905, -8.833477677349235, -2.743877939432896, -0.8445246804580874, -0.11787289301229148, -4.966375198009779, -5.759466939881948, -6.216606683429334, -2.665398007873023, -5.899234114772982, -1.6198311834164687, -3.9654597880159335 ],
				[ 0.01076461564234167, 0.01734666712160892, 0.00904731739391123, 0.015706899427389787, -0.004838318173090915, 0.001242582242418682, -0.018981175493034585, 0.003055357592844159, -6.231055597044168, 1.7831103786839677, -1.6200251661266303, 3.441492265167328, 1.358832653863525, 5.635746199868518, 0.15574046840835667, 0.10860799832466754, -3.4019077102458612, -0.23866832315841272, 1.3331464740411507, -0.37520723504427483, 1.235679787364839, -1.8428335872354098, 2.7120736662367655, 0.707007976639673, -1.949885311610847, -0.5069830187595323, 1.78702356556679, 3.5573210262578514, 0.456086861401898, -0.8928328761920381, 1.9304017832768348, 0.10133142966706767, -2.2400497456049977, -0.9455986683231984, -0.04574056503433151, 0.9931982837203588, 0.9405743401393011, -0.06465588086789104, -0.10410848616873088, 0.8535877394715597, -1.7565804945966133, -0.7030006997528252, -0.8900100867640833, -0.11894389365175181, -0.9219317083160026, 1.5372411433610944, -0.5784223533937748, -0.34782523213058464, -2.0644355380658994, -0.9154432179145249, -0.6013104818949838, -0.41531289462719456, -0.7705240498813875, 0.5746239971831683, 0.4937719368815546, 0.37841044580734456, 0.005238115132803738, -0.017213714362653322, -0.014099771110440425, -0.016285486935195888, 0.015240889366581906, -0.012441723219973983, -0.008617391760403253, -0.014777567870535697, -8.083846336635956, 3.7838837286816216, -2.6103085576263676, -3.1265112678976488, -1.086156014304584, -2.387166159099554, -5.186685962809248, -1.3724349225485564, -1.8635037268548535, -5.487051008813879, -1.0562058497722429, -2.8349317005032497, -1.3999297445849688, -0.4681212769196984, -0.5607277796337261, -3.515211517973361, -3.6375500840617105, -1.4675490185495879, -1.715109347407238, -2.039320187716257, -2.6323981496354194, -3.7173771326336698, -2.014290700613027, -1.9213023628145807, -6.826466670242492, -0.8465965156563371, -2.1514145339890662, -1.7337616814595642, -2.026966938048817, -4.073688301535098, -2.3450573338596827, -2.402516236564633, -2.673267419730677, -3.0979482800564164, -2.0273980653902286, -4.380668443254558, -3.2267797461175367, -0.9998970042052607, -2.4005539573040378, -2.70481249873325, -2.4194894457776313, -2.919546467532983, -0.6764242277464465, -3.5349459111917945, -1.2083283373935736, -2.85985626612194, -2.1242098981759336, -1.70194128615885, -5.915679537479173, -4.589583392124236, -3.055130268873459, -2.411271831943326, -2.04689459448202, -1.681998681815952, -7.50195222683913, -4.031138518448592, -0.4215411714482488, -3.4530396043305958, -2.7898011486085537, -2.7547763681428448, -4.979381038532392, -2.792408891405054, -3.5842643710851387, -3.219726674965003, -0.6064622025669013, -1.6989803439122368, -2.020097845800485, -3.938243411649036, -0.12874619177941612, -2.31883395397691, -2.9512401059529254, -5.134073270822975, -5.259484001769308, -1.192946146241357, -1.4425391263811644, -2.653119206725854, -0.4677755986039037, -0.7838546939610821, -2.1135593313348298, 0.37958385126199073, -0.26127621661328365, -0.6017369629387398, -0.04843591453769427, -2.9129192019681898, -0.9271727914299657, -2.273901428896768, -0.25998154915109856, -1.3494559046987833, 0.6632394566071041, -0.25923181713938026, -0.8737156467071198, -1.3112668325154484, -0.9184803471003203, 0.4453772915017901, -1.813872503416389, -0.4970349772774696, -2.1329163709353556, -0.6499057436578631, -0.7580877088552976, -0.7230169870842754, -0.7245950783796311, -1.4202219027115348, -3.005150758392936, -3.2749438390949184, -1.2784184854611884, -0.6681447397757303, -0.09590094267528716, -0.5414442634661653, 0.06396337015484665, 0.013641689828638849, -1.5699182995048664, -2.9681387018102576, -2.1135879722381694, -0.003418202896790571, -0.7756846876272708, -0.6447440951426526, -0.5137309550214443, -0.7361468220418739, 1.9131819160786387, -3.616928498899215, -2.1557064413131446, -1.183722712557559, -1.3346320086951626, -0.5322106771739711, -0.7432185882794822, -0.8456731841700309, -0.9013174428088302, -1.4747189673463101, -2.9337681422775717, -2.5267006255575573, -1.159400443490563, -1.5809158249340627, -1.3240687187202074, -1.7656672713400694, -0.9593133843908008, -0.8107566309489539, -0.22730852470879698, -1.31540277309702, -0.9426141744046581, -1.6461723220849047, -2.288456270063513, -1.0563199765608347, -1.199605096976979, -0.6606704494981593, -2.15364163799486, -2.0858767432890057, -1.4897914039003801, -1.7995911762314372, -2.2323677342295984, -2.8321381320401424, 0.7162661726918895, -1.8236336861862321, -2.087935192724014, -3.0710902224670855, -2.102634287282411, -2.5569389515336454, -0.6954623182858157, -0.5522811202103627, -2.2183901425902723, -1.9521194093394585, -2.096555068458618, -1.435333583975071, -1.4378082974790185, -2.3497025017730078, -0.20242597972751342, -1.916272905286597, -1.037252687336607, -1.1797426934803097, -2.4012467545745304, -1.6220845512400357, -2.253947703750575, -1.3632817614851072, -1.2155588007048008, -1.0909379739451441, -1.5080658234231592, -1.0390877693328016, -1.2007924097898326, -1.113189163236826, -0.6460891558192761, 0.10466501355333283, -2.6942430923440726, -1.0761174840930061, 0.3496957134589095, -3.335046532950319, -2.011390898355719, -1.3700138156606745, -1.373929230060746, -1.6904171433964323, -1.567177545779765, -1.799121601313424, -1.179309812057385, -2.4481807574165826, -2.415519567111017, -4.0626622726049515, -1.7369771222002364, -2.8269895227528976, -1.965066241478731, -5.537180511078341, -5.606258372148174, -6.399574562675719, -2.3530150641977468, -4.132168867770262, -1.9002801013574309, -2.9691435867615774, 0.3323915566625604, -1.3799026228869054, -10.434006539748301, -4.68652839787891, -2.930216432429416, -1.1642518499370598, 1.3718886884453694, -1.1568092532481757, -1.7192337883436926, -7.044646126780579, -1.8811233714134967, -2.5194685457712764, -0.40424737166865615, -4.057238099067337, -0.38413371365832283, -3.353201202245393, -3.7407486743156912, -3.8665741240821343, -3.2471383433203664, -1.9135498580502788, -3.596086774420178, -0.9533770345519496, -1.9459099084544529, -3.8865593960172666, -3.5855797525056405, -2.429755613976489, -2.91088787695109, -2.920713696189985, -3.403751855409861, -2.4778012128009546, -2.705115594965916, -2.6021509782163763, -1.6946568776895812, -3.458709354966205, -2.4274225940412664, -3.484486836794741, -3.3919563872950413, -3.4382318221805175, -2.3140912802211937, -2.621469568559919, -2.6931101342251558, -1.8888801678116793, -4.185270415145651, -1.4728971292695294, -2.92696265206194, -2.295147549122012, -3.196564312886505, -2.551104190145795, -2.2740419441097868, -2.0279833431976964, 0.024988087616284602, -9.535312779075259, 3.639427437927503, -0.3586971786464009, 1.0616529048977394, -4.197609794613831, -3.668422673997119, -3.5683964139522897, -3.140722024103926, -3.140415428097769, 0.6762938116106936, 1.2620366109700278, -0.6172511955223197, 1.973401905284888, -2.1704895839156135, 0.16206931527092766, -4.196576383169792, -2.233285071402539, 0.44690214487995455, -1.0167013511750342, 1.652500277672185, -2.6594283079545717, -1.6781656375492582, -2.6098994922613716, -4.713912895890534, 2.2081240217136795, -0.650394684737054, 1.046246439412022, -1.4338418989797024, -0.6158183810926214, -1.9376120394343768, -0.38486254682835497, -0.6662899725130577, 1.1801042022377255, 1.3826754570259088, 1.2716810876648563, 1.2775522172122158, 0.4658377943981854, 0.3274612711935458, -0.7866114464320633, -0.7796665336163462, -0.2540463509775581, 2.7086062339585886, 0.225383367994006, 1.6931337652884895, 0.3660654401815873, 1.0837216588897682, -0.17928734041358704, -0.17219569379024735, -0.4808437264924818, 0.48285473388796585, 0.35464078221772444, 0.6578841207248285, -0.3147566807531959, -0.5970038299164476, -1.2636165576113414, -1.2200174993039836, -0.07184262756451903, -0.4723497226348004, -0.9291039245602716, -0.6464105522851842, -3.276976011944313, 0.007881747059047527, -1.8363114591695278, -0.1822636068458896, -1.297653353997912, 0.019506245562509916, -0.009165748579986118, 0.0007877823118666025, -0.002505180309994023, -0.009612410813712292, 0.007667712829683888, 0.01655093384367704, 0.013240470003764103, 0.8391962799265222, 0.3217687958757065, -0.20433024463887636, 0.8236518058731794, 0.025699656993716343, 1.4866996158306032, 2.0450331449531287, 0.8921572498270566, 0.8915810062968172, 0.3500618164351567, 2.8677018392833094, 1.0888182730173852, 1.6718102321898871, 1.1951437223235535, 1.9625039362444503, 0.999656127528441, 1.1188276607889744, 1.7249857522230043, 0.5590718975352382, 4.955861827314122, 1.4555295825911385, 2.3033837570217686, 2.222432468182207, 1.605709937657811, 1.7554061142614725, 1.1826225451971675, 1.7331723517227107, 1.3953489479334502, 3.7461335121173485, 1.6860660838444994, 0.43675272934351467, 1.2478256147138205, 1.0863577599423793, 0.8519607079136376, 0.4880791002990618, -0.9144425737363021, -0.3758980679432212, 2.6430196551374117, -1.7232116720194348, 1.4002455896051362, 1.5238365587266347, -0.5871310918870914, 1.1873443596965514, -5.197325514046445, -0.5615003521254055, -6.237753927879415, -0.7105680470246653, 1.159850132589301, -0.02038709418888108, 0.01087404530273225, -0.002293055684579411, -0.007969995816910052, 0.014139145137184282, -0.0159521152377857, 0.015561505449797381, 0.013596297412771515, 3.7253520412709533, 2.2703866074199546, 3.088707300092674, 0.953853493294535, 2.8282249231002243, 1.4265587461203468, 1.9070861487327515, 1.0383211339313119, 2.6452136355020897, 3.6720014318744867, 2.2307746028575517, 0.9523515666535016, 2.4283203028157567, 1.3504150479612196, 4.525518634105163, 2.2347061557329417, 1.9512703349528335, 1.2470937189792, 1.924022883439606, 2.5649408974567027, 2.838373427386854, 1.370511553169351, 1.8751438702658867, 2.6842216691356384, 1.8078906660440803, 1.655127649194794, 0.5993582722163471, 2.855139525101412, 1.8881053972253403, 2.3453214785050913, 1.3510003919629356, 3.060553219819157, 0.479579413927086, 0.3927108656917964, 1.3394048451640843, 0.7346105454522572, -0.5615300357148515, 2.2597857531169265, 1.0996394858941814, 3.4015133705321423, 0.5985162606463713, 2.2257968183034373, 0.6467304093938143, 2.1683411656540597, -0.977717802901523, 3.0469210525699135, 2.1312239703078326, 1.2844715279061638, 0.8599138055259533, 1.7111920330137882, 1.7710317222069263, 2.0075094331069216, 0.8133590605590375, 1.7502221778262288, 1.6998891930155713, 0.8009781218968683, -0.49064742639329756, 1.0278496554215817, 2.179760759291373, 0.5195311929238657, 0.572671390063643, 2.6116467198231255, 3.5823233803128636, 0.051990214547697346, -6.677059919822603, 2.2997281845820994, -1.7107005767009145, 0.9905194293424783, -0.7616863098692472, 3.4525675441422887, 0.5508321825054162, -1.8852008239666744, -0.6960236268029953, -8.300934335967712, 0.9984761569391621, -2.046508596529175, 2.007245505857634, 0.7325219900644275, 2.482651360242399, 1.2568975189620175, -3.1790081677307374, 0.21343908340166964, -6.426545478926925, 2.301888853406191, -0.6710925738351716, 2.2346408607881685, -1.5123374323335443, 2.1814985819546475, 1.983822730095669, -2.263691539038881, 0.24124987454017904, -0.21959858970823765, 1.1197934397231448, -0.7750178144187906, 2.770915818788759, -1.5846229490495463, -1.8284470906717247, 2.305107590800217, -1.9935602319968373, 1.7825784355901142, -2.67913965073042, 2.7513793844888808, -1.7210721930785853, 1.7807315539461674, 1.6274073291044864, -1.8192938762113091, 1.025672924824687, -3.3352218186923714, 0.8644740105967545, 0.9256137320860796, -0.17662579375151288, -0.9272839109876808, -1.2011235195823988, -0.4845102388678451, -4.029666825788747, -1.7672373705490374, -5.041791802479357, 1.901013436527576, -2.486999841605625, 3.7329470420762876, 0.7396376006919192, -3.2369848950396665, 2.0832983755209318, -0.3525425642869981, 0.5737485230143743, -2.5055307789179735, -3.450342169978061, 0.6760161369382875, 0.8746045923320661, 0.8071309173595643, 0.6079400560889153, 0.8222002526777459, 0.18514465759526932, 0.2503569054638738, -0.674033316115468, 0.41431357426386767, 4.2602104898542414, 1.6804384816685338, 1.179604611902339, 0.49961806258283203, 2.159138189768767, -0.047326487172750495, 0.20931685120816163, -0.031105415837688204, 0.8858230582918654, 0.9578452848570242, 0.9651736269358259, 0.7328287613451632, 1.5446114407005538, 1.7034708594944779, 0.13549574582396476, 2.0625706516416473, 0.9627300643899972, 2.012504359079241, 1.8011966843284524, 2.2688255962104105, 0.7290167316365456, 1.0285814966893476, 1.9877367602298004, 0.46076775840185563, 1.6947566877516604, 1.1062155340322166, 0.3922197090712738, 1.3744028506688246, 1.0882556080930552, 0.8891495040770482, 0.5076349201627601, 3.110813106343593, 0.3254784846277982, 0.8896414260908099, 0.45679323947086503, 1.620990478009375, -1.0068595192430103, 0.5996551275405245, -1.903009544155436, 1.7360504240730004, -2.583245145848034, -1.8525192957683343, -0.7172624022146249, -0.5498413019459409, -0.27420737616837115, -0.49987393258093643, -0.30003042612439157, -0.6503881494261515, 0.1233142805332806, -1.6671497603607361, -1.0483893871532846, -0.4225760288510601, -0.2040650944089218, 0.7669952005860539, -0.2506152912574446, 1.9729889192559686, 0.031832115350573904, 2.2847531453669494, 1.9749609348570922, 0.7887806731454247, 0.12148680601677028, 1.4188634947892464, 0.05923366927398291, -2.7229234831333686, 2.420385317748312, -0.5669070918281249, -0.07108375536721802, 0.7457483560086786, 1.1395293409009424, 1.3785847396096378, 2.23082806374792, 3.4681091294681603, -0.4646906176866776, 1.4602676404052988, -1.3955569144084035, 1.674878548214193, 1.7981608145582277, 1.7076468203140522, 0.6917694315247298, 0.5486227710960886, 1.097713639986647, 0.3959376252531246, 0.8948014143622063, 0.23220295529584176, 1.7510899547027297, 1.31946456224692, 3.101896974283043, 0.7512887088345165, -0.6170828865663243, 0.7953423824752444, 0.013800691537431551, 1.8326811578265474, 0.6244435814745286, 0.6093629067316807, -0.003472874475099786, 2.0716126502422822, 0.21712695711939928, -0.32107656586508276, -1.6555207577348292, -1.945113337444368, -1.43149475672686, -4.285628628762596, -1.2070358775103043, -0.5595376850431873, -1.1782666548084761, -2.8153036843096966, -0.1244613238638175, 0.21694998026395618, -1.3791579370176812, -0.9330235680235873, 4.612150428480175, 1.9961022716538666, -0.22788007885747838, -0.6754388628329921, 2.1340790734167565, 1.5692800411572936, 1.9657103301896541, 1.615549034766436, 3.760568461392041, 1.5899904424023252, -8.76508029338266, -10.409298330495428, -3.795374114141862, 0.2865927250330963, -0.11684789373594102, 0.7870116122145425, -0.44452816440618886, -1.659109445662273, -6.556431687490591, -2.542629919695425, 0.2033286545418075, -0.6302057631806147, -0.05975080832002256, 0.8653054680350643, 0.3571123605933897, -0.23581877953748615, -3.7113788358833917, -1.6983247668593502, -0.782634770677995, 0.061731300765550556, 1.2719991488819216, -0.01894765457465043, -0.8611190236791618, 0.08307215660717844, -7.579956525609477, -2.958986216737064, 0.4984407018009633, 1.2261474663428655, 0.6007602704678933, 0.7986621065561897, -0.9567241055253547, 0.5043793376891509, -1.2848652136518715, -1.2594657300159744, 0.3543014409442257, 0.22880101659866406, 1.657114271644602, 0.7727465819571248, 1.7227194823052365, 2.010424810602295, -2.8669603312662386, -2.5217775461472507, -1.2212115196502933, 0.6062205640639478, -0.32888940394169874, 1.086732805356344, 1.2149675678781493, 2.7985956470956532, -1.2420236049966416, -3.649360167148807, -2.606508883428056, -1.4516534830383856, -1.6138244289766293, 0.03916983338203797, 2.73738404395715, 1.6298125494388922, -0.39049919176562076, -2.0605346813428125, -1.3717472802917992, 1.5499979445525334, 1.7103056652577184, -0.710254488155172, -1.8591289634828938, -2.4584914655401127 ],
				[ 0.013828796572016163, -0.0009612325284756617, 0.012306680433032577, 0.01369379414959261, -0.020937510559293278, 0.01741000367552092, 0.018998743982852007, -0.02023377188234037, 4.580510309335956, 0.6390314961282629, 0.9267495201061949, 3.6698950521748777, 0.12689811542579496, -2.2619380076045816, -1.2761764286716024, -3.236804100169343, 0.5832243502087502, -0.6698161323714401, 0.596950146772238, 1.4733458200142833, -1.1341253021851676, 2.9507927496204256, 1.1807944300829878, 3.4716235852256787, -0.34083985524205335, 1.8313487881221184, 1.1055578268912423, -2.3311501537887094, 0.43373738009073587, 2.82890368417351, 0.9386122459206575, 0.8438032927407845, 1.005037778685202, 0.9891017583750663, 0.34484917420377703, 0.1268321450205558, 0.4746086087355111, 2.0874302775154763, 3.1349650835696576, -0.7817585958385641, 0.5027784251349505, -1.4068512356848377, -2.135236495372841, 1.8709586419838624, 1.924488416253473, 1.5897404740373993, 1.3825600858822726, -0.1607694211782256, -0.2021296161515492, -2.7715143472067614, -1.449431012803935, 1.4660745487896858, 0.23831906543735454, 0.6889846916091991, 1.2563975090032513, 1.5953078877615514, 0.01951672066650334, -0.01824376807980182, -0.0024156362651659683, 0.013779313458584373, -0.006779995136721568, -0.017246190492106187, -0.010104245595582489, 0.013038827576252127, -0.9493273582854916, -0.26182087009251265, 1.4784403267750497, 5.036066470184077, 1.8302853273882627, -0.3024338299059099, -3.8122168566601156, 7.341401066626749, 1.0851899063021917, 0.43992461716991244, 1.345013464362326, -1.0481627566272962, -0.7336491498600667, 3.0691841727306004, -4.958770855881741, 4.532861036350155, 1.112955159717264, -3.959670974068948, 2.332503086654003, -0.8512885975465794, -0.16907796186035193, 1.628949734712204, -2.079729609575192, -0.6578082467918709, 1.2383746522775714, 0.12440771980478982, 2.7283666085379505, -0.25773918207136115, -0.18095871651985876, -1.0668428847941518, -1.9583564582517525, -0.03377754255302252, 1.8491192250962218, 1.0559285594206074, -0.042161870498766685, 1.7538720527792304, 1.6792431334600482, -1.1396949460866392, -1.023103899085241, 0.17383586487725303, 1.798575447296791, 2.4515725561810444, 0.08874323332202122, 1.265381999606805, -0.023891114509012133, 0.304001339595899, 1.1325910117548608, 1.3393950691389949, 0.0746145048237562, 1.8283685918462893, -0.13092215361190945, 0.7782597730308679, 0.9338270050005935, 0.6319142537594014, 2.5884056721144906, 2.271988237962184, 2.611535853827222, 2.0199591752470725, 3.239648735385366, 3.1640811226452725, 0.2765505632743585, 1.6258966093508413, -0.09465940945250821, 0.07971206926142023, -0.2991942981026794, -1.1733065452851825, -3.4629251067623277, -5.463514162450075, -1.9498398664250023, -0.7321549084489234, 4.833934031939307, -4.901691945743189, -0.8597063245425359, -2.755867028365295, -1.2646462948277053, -0.6095526241681165, -5.434747164573812, -4.383860863251725, -5.7722142462015, -2.0055097753042763, -1.4517887248355401, -5.223712651809885, 0.8107573993637118, 0.5199832693178849, 2.715482307623852, -6.034639179817059, -2.798505083785559, -4.844914318310671, -2.0791532958422336, 2.738579798821558, 1.2544240842720353, 2.263734966913727, -2.866682453780464, 0.04809878054715746, -1.5375159571352186, -0.36967641451686756, 2.3083115334774478, -1.8028979050601437, 0.5607173106079424, -2.1283464859987387, 3.015350533017469, -1.434020944303127, -0.03365168823741506, -0.4549504558166058, -1.0190448284914084, 0.5990526411041983, -2.832547705134859, 0.7184369138781698, -0.8708181966123003, 0.928912687051651, 0.6627421622609313, 1.47896661160089, 2.177614757039065, -2.08772563768152, -0.5552916183676526, -1.2768678142723522, 2.175030218314577, 0.8943899664956658, 0.9179918879033349, 1.3102111014483613, 4.395846231040786, -0.08548877881199989, -1.6887551436487231, 0.18831572165635044, -0.912554069514216, 0.7983038042983098, -3.507427537039265, 3.8909155184785855, 0.19786684725615492, 0.3261028770899213, -0.22516756095961174, -3.5374755593727887, -0.1463923728880156, 1.1570216845876653, -1.3697005032514589, -3.9623402357955375, -2.344825984501218, -3.5244883347180247, -4.2538764971818654, -0.686752560316421, -0.7169696841058444, -4.563524703079292, -1.7381718754157256, -4.6012280933924865, -2.7588362379789695, 0.12511287622486716, 0.4762628004038885, 0.4035354268550478, 1.0727578313112967, 1.3798731070495827, -1.25369753179108, -0.17605948018069287, -0.6115252795377594, 0.6100046431720274, -2.102710470165797, 0.901150235140407, -0.13810777137728894, -2.5147739104240356, 0.44641409048708397, 0.1556638070006797, 0.5104379636640494, -0.5848226616336172, 0.4770538862843579, -0.3486193700863536, 0.754426818867874, -1.3062272193853013, -1.0031140358084543, -2.2184655863843132, 2.233017613750482, 0.5127385725765415, 0.18493814193669272, -2.779161034432554, 1.8854783401987858, -1.564339934792289, -0.01786798342097508, 0.7778755988139571, 2.0648801604230123, 1.6198156947642148, 1.4165765610451984, -1.0651123845287962, -1.1006136409203644, 0.24550603338528246, 2.371096392600871, -2.058619299648109, 1.2453867066042523, 1.880306001206168, 1.9659027328237122, 0.03924166022376995, 0.571529564414777, 0.5690794624593284, -0.1332373672995492, 1.2887013852411437, -2.26396133958965, -1.2491230724999647, -0.9751808047133481, 3.995554787109469, 2.5116138607297964, -1.2555843562113613, -2.8347543968842124, -2.9984584423405076, 3.203980748384239, -0.9374683917391053, 1.7169705591830289, 2.4623715251896128, 0.8490973117692265, -0.7578403120244203, -2.3070481459974537, -2.843311306273955, -0.6134215198024419, -1.3127777237742697, -0.6963785270217702, 0.6289558073006598, 1.4101966437864975, 0.2517768028058847, 3.620608300082305, -3.361213161808467, 1.7708945540195866, 2.2855745415941677, 2.3140154894417035, -1.288432986573336, 0.8629579725119462, 1.3923525776963084, 0.6384124518308747, -0.525328333496385, 3.1205634281339107, 3.8288463250762246, 3.0920009113908686, 1.1897570987846111, 1.5832677773263344, -0.1535595487809049, -1.0919732511290345, 1.4885101799552327, 1.3798736738945703, 3.893346676436776, 3.760373862204826, 2.888290678884317, 2.153547224829371, 0.6927254474878499, 2.2949302367803086, -2.886459708783991, 1.5181391727791702, 3.236969406606964, 2.8969545903853002, 1.2357975994694095, 1.8356352072956388, 0.5303835625072659, 2.801096605444542, 4.3172041008861575, 3.2212169383849596, 4.124682956074122, 3.499799649134249, 2.005301617267075, 3.190760943218887, 3.403397878216368, -0.6317057114042997, 0.984229221107875, 0.8813881540101616, 1.453059371038137, -0.5263921572165633, 4.8335582945204285, -2.9730613723195627, -1.2949489967691374, 5.380586839207753, 6.308730715931526, 4.038067728361735, -0.3860060387006826, -1.134331984280777, -1.2483979868824138, -3.777272658539468, -0.29289542195011475, 6.13239539599869, 0.16437871728693837, -8.556621909961574, -1.88432105671084, -2.7349608389898257, 2.151453381073899, 0.617339527154776, 0.6587765440952752, -3.3061950040801245, 1.098693789752268, -2.287370285731905, -3.953371338297688, -0.59399967721923, -4.742893144646666, 0.5869111557930433, 0.11848878011873301, 1.7519609146578907, -3.359433848976217, -4.352152692581784, -3.6192132831119843, -2.20696601514133, -0.21494239087364736, -0.31637212094596456, 1.2469424929186383, 0.4416868119925409, 1.3072648805931133, -3.588380303300437, -4.607941445825963, -3.7528912272338633, -0.46002090026246695, 0.9684376909109896, 1.220257859831983, 1.7229630842267623, 1.384814074858381, -3.2603371596381625, -7.597333096301681, -4.275454620767612, -1.7507192027096001, -0.13874006423490726, -1.3529341276461906, -0.30494216106427835, 0.4277033989627099, -3.348211954758696, -6.482388089334567, -6.290495487136566, -6.999486043202226, -1.9660158555010088, -2.365226256180366, -2.171074683599522, -1.8222913211332135, -0.01619281311658771, -0.015661138111793965, 0.005784010900132518, 0.012441786496720054, 0.0157544290219746, 0.015298666669118626, 0.016262364461586815, -0.00717043647887294, -2.5053164705489346, -0.17570118361783035, 1.855879009349245, 0.7053032365704314, 1.6240858011424912, -0.261624415031993, 1.2304976522768851, -0.5534529111673611, -1.9130534477801908, -0.8290771207615397, 1.8519747547288963, 1.730995110597492, 0.8463116428110142, -0.7752585056556286, 0.724845464991544, 0.5705925765012192, -3.460413566428476, -0.5517258352314134, -0.3582459445297687, 1.1135161143807457, 0.7557674257990701, -0.283373461512947, -3.5330850998076913, 0.05816323167865681, -3.3632883974248564, -1.964640270353651, -2.178830423725085, 0.6900877217565778, 0.9591613555087094, -2.6131892933113683, -0.5911827226541393, -2.03839342405031, 0.24614611051406857, -3.2708266661980376, 0.16569892076006823, -0.9659107653527674, 1.26780649900105, -6.208012010296719, -0.06638600904340643, 2.326965974696381, -5.663802191863052, -7.623530220976519, -5.823322174359601, 0.08778343936410166, -5.327222747276048, -4.203059637250229, 3.6325327910684644, -1.2596411936127672, 0.016105603218995936, -0.004160596394882232, 0.016964185379854103, 0.005608423073798274, -0.004012609674688819, -0.006415720274883909, 0.016782991334163624, 0.003089180295906209, 0.821085467898538, -1.3333371195739223, -1.7236967681048294, -6.428353163756665, -0.6468326221122389, -0.8060567704900778, -1.9701328905371716, -9.047315420450536, 2.123363086289067, -0.8654309540398784, -0.5101648285551638, -0.6393599253555804, -0.7279930947686595, -1.813110248749206, -1.274924636219365, -0.9793761123761757, -1.9654849552187812, 0.047165927832636616, 1.640104883251667, 0.4938231258923213, 1.8585498476186368, 0.6818910850281176, -0.5672531165809136, -1.612232769196783, -2.0684509989586646, -0.7629594928220478, 0.2716085447106653, -0.9785134956655035, 0.6138803292183957, 1.0598861379139144, 0.28257442443545644, -0.20413198680601363, 1.0319087112388483, -2.080226097581835, -2.5217064603108823, 0.9316146961916101, 0.9254438854205317, 1.1774860099887776, 1.3755859423628976, 0.610561242230184, -0.6444633934841107, 3.147591270083288, -1.1361686864193812, 1.5839532410133512, 2.2953573398727145, -3.6243366732717703, 4.969874907103676, 1.1918355749791594, -4.724465013708608, -0.9223988892389013, -2.754831552234433, -1.2824450931312426, 0.49665581000388875, -0.8044409181252723, 1.1642898567313338, -1.4959741751853588, 1.7171203787013156, -0.2677056770385201, 2.7160832460268547, -3.7100614033848953, -0.006481202694332715, 6.308411078183151, 3.314412485097931, -4.640093736157152, -4.717053156600698, 1.091556240126426, -0.34630273737844414, 1.0265089450474632, 1.7269263991425483, -0.8819807889251626, 1.0988046317089724, -3.0210971163364047, 0.45261819722598196, 1.275531922526316, 0.5630247355063883, 1.0000590311484763, 1.6603060414129125, -0.5469245995882616, 1.7150330977811714, -1.5412362453426935, -0.14276941791966058, 0.9832216806818921, 0.3526564305418502, 1.2021092868614387, 1.1567748137365392, 2.521826040761509, 0.04725547518465835, 0.6736333419288254, 0.004376486124275853, -1.2865441792657184, -0.7910218595964248, 0.21050691177541417, 3.3002479404534313, 1.6107609650803818, 0.17383214356264867, 2.9016638957693, -1.0470301284862793, -1.5595045330320914, -0.08664607482287279, 0.0721818734376401, -0.4672112016368773, -4.025983702740061, 1.0158062854894494, 2.2179225479662894, 0.2951530126455866, 0.2644312129556164, -0.8047334481842605, -0.045534630916272446, 0.5676483875025088, 1.8782948135732944, 1.2857423986471344, 3.02820331711858, -2.747046956826847, 2.5770627740577323, 0.6598034403716843, -0.5424960113518085, 0.9855563706471306, -3.031576267508915, 5.29226728614844, -0.22838408104512437, 2.7759303649519387, 1.1971968196628595, -0.02383634042203676, -3.710655836154683, 0.07973298082016059, 2.158232330320975, 2.811315188847814, -3.5189769575517125, 1.2636459630200338, 0.6796004012987804, 0.4057188209480373, 0.9957587575749312, 1.2319759368234562, 1.0973286284544108, 1.1894582161132827, 0.09201200614831102, 1.5570626072528524, 1.9113907510180128, 2.1826361556328995, 1.674688907613092, 2.111676543710386, -0.16044207880157174, -0.4918740503313326, 0.6835485201542226, -1.149759048901013, 2.3649439317733156, 2.8580996543671353, 1.2914722354741297, 3.6625876587587913, 3.234443500918998, 0.33821007886622967, 1.0780236554261746, -0.24501497367423097, 3.114843425843351, 0.29574158699952124, 0.40431912331888, 1.2868429403005262, 3.678481209861959, -1.1616443497088722, 0.92858511627287, -0.32189576720593194, -0.731811295473215, -0.4198030883257982, -1.64412472215113, -0.8840456648939535, -1.7939343122622333, 1.4952808562139073, 2.8388709694072434, 1.676746014569558, 0.3704930855070823, 0.830060387403639, 1.2444265215962655, 1.0868981189401399, 2.762406379992663, 1.090934270659736, 2.46675744380588, 3.0935488809328358, 0.9794603737548359, 1.668186451032435, 0.4123844485643232, 1.264471417430245, 3.2368187448728905, -8.451784456197174, 0.459446316741571, 0.4430233843439309, 1.8254172591115059, 4.400412664758602, 1.1650781360965043, -1.9557946489741005, 4.553408574442213, 1.0384508572864117, -3.4771654518493658, 0.04144210799397284, -2.6906767301338252, -1.0006297244873155, 0.45316760089641994, -1.9140904281963644, 0.5049904145578373, -1.89477994400845, -4.061046431038777, -0.08087825034402858, -0.8114177817459383, 0.18285013020809157, -0.13388885351204197, 0.27207201282976134, -1.6078206590599087, -4.645163301605037, -2.490442522143692, -0.44854047178947076, 1.2222028760923704, 1.229811505216016, -0.18194884217710555, -1.7861217315024236, 0.4663272319215395, 0.5884075544433428, 0.2701252549294663, 0.7975917512557744, 0.9422154086789827, -0.3590776414718193, 0.6431851669597182, 0.08582738782917233, 0.5579387742203895, -1.2007884344649278, 1.6977090693725407, -2.8807873429461273, 1.5300989741020627, 1.4325990064693845, -0.4049863832584903, -0.7326283741142159, 0.2055149218520377, -1.4741569534790555, 0.9033722296151089, 3.8451115576410673, 2.8625464361312942, 4.7918634735559476, 0.843419747528504, 1.018183502950895, -3.1983938633590503, -1.3895826288913948, 4.287426734706449, 1.2577359127364887, 2.786661909783094, 1.2956066260223054, 1.4209619271975065, 3.8205350004868346, -7.612807746730925, -2.9175756494008223, 0.3176070305109991, 1.106614507129458, 4.069279754802687, -0.705372626247771, -1.3621121945815584, 0.2895813040001041, -4.610086694096363, -4.183091869454484, -3.60839206040837, 1.0026475030250122, 0.647385658426963, 0.33419040485062307, -2.4679597346417728, -4.600836803407706, -0.6556136671572811, -1.0037073738697995, -0.9160552385225214, 2.0642635846790536, 2.990761394570733, -4.856702222414313, -1.8156484747519221, -3.3917638279478517, -1.554116926220061, -1.5093654016998337, -2.2732933623561027, 4.280547630858277, -0.49584410875327006, 1.7201913493896501, -5.487446578224802, -7.4812623399120985, -3.8106613851942774, -1.258070016862975, -2.850006630405155, 0.7111493609782814, -3.333959849950613, -3.50688708855295, -4.022887560591862, -4.390255213909325, -0.953299611957078, -5.695193643666534, -0.08368440870719861, 3.2723448967010285, 2.290728129384336, -0.4981525904184267, -6.338982911762069, -0.898933972493441, -8.178806143579035, -2.32040166755156, -0.6652584647346564, 2.3862331776507113, 5.199469653195252, -5.7504761500328945, 3.1211291468790203, -2.9100286251408147, -7.841731098483094, -2.522834757404594, -5.364893285577471, 4.793244760090843, 6.3610313599531585, 4.8894256291837115, 2.557559840253636, 4.320982892295304, 0.6069691659486054, -1.292507553087002, -5.024546106946876, 0.26589286069682355, -0.777044025237226, 3.973830839469303, -3.4949350118463895, 2.0493913549448695, 3.8702227243308003, 1.4386026742123865, 1.0525958133557152 ],
				[ 0.008591615955552575, 0.013538497213028468, 0.01065312897039599, 0.003690219743335566, -0.011021537386398437, -0.020798927693125698, -0.017353828724163807, -0.013400232958199587, -0.2152621623657235, 2.142492199768372, 1.5306975073787195, 1.3719336440113792, 1.0889636924353039, -2.8286524921453693, 4.027488848919008, 2.863081703523879, 2.807320678669838, 2.2742240772003313, 1.521431077468415, 0.9937059666125925, 1.5737011197860198, -5.694267777094253, -1.2522846208381697, 0.25904134911975846, 0.8963796845730603, 1.9726410933848713, 1.928775470837874, 1.7382529812998755, 0.11367629785200599, -1.6171396625875964, -0.994516539626984, -0.4772576046478487, 1.0540699862248573, 2.060512062467864, 1.6584998106695885, 1.5627249987027205, 0.818465869671303, -1.2420367532500671, -2.743566011910992, -1.324180235497208, 1.7664534885698333, 2.445651428980619, 1.9878582345266804, 1.208714856592735, 0.4089859665958875, -0.7820335828744092, -1.763544426934537, -1.8855678457659146, 1.3457888870590689, 2.0769546763471487, 1.4592299630068908, 1.0694732624058245, 2.1303721812927505, 0.7679800105066024, -1.58975052138041, -3.3324582046360915, 0.01826250437683412, -0.019318530048849016, -0.005490507684708472, 0.00717553150221062, 0.01986425200258279, -0.0017597909205391458, -0.021490559904527758, -0.012008470223396921, 2.131549691516746, -0.1732372394207814, 3.2404050785419614, 4.705752591174791, -1.1259921691222892, -1.196797800957731, 6.256984396328502, -4.086269340800244, -1.0867282368935378, -1.0976449022635846, 2.524454879035316, -0.10711878935385422, -0.7898822866928615, -3.8770363162033776, -1.7025975706632013, -3.6191478975385394, 4.718810898343181, 3.6333665061225755, 1.7476825977772952, 1.2628165158706877, 0.17611628131533963, 1.482302992912259, 2.9178818157735016, -1.1319594042214765, 2.8277530515399123, 0.806900700191119, 1.642229219897866, 1.449004769143581, -1.5784694144463214, -0.007522887143229785, 1.3971877988222414, 1.3490266818360779, 1.5563692031435874, 1.2506022287099907, 2.0677990679631857, 1.0055716394875467, 0.3917344263336503, -0.6908534695180703, 1.459724590910039, 0.04329392322195904, 2.0365689722277964, 1.958166359362586, 1.3271253763155877, -0.1962547087123689, 0.8022001430795722, 0.6666706726007526, 0.511138581929855, -0.6822393763752874, 1.5624629393261673, 0.3194916705684986, 1.5111832008864619, 1.2627173398381497, 0.5542458785974372, -0.3684923025656502, -0.6310785754006083, -0.1536202114818251, 5.727201825624376, 0.855375674723798, -2.6978177983941074, 3.04682790959637, 0.5536453347446021, -0.25332078508403616, 0.20509799274776705, -0.09127798377764058, 0.8307492014215457, 2.9598761924155546, -2.1658564908111955, 2.7403270989133484, 1.4216425184454418, 6.333548281996429, 1.1403429938159109, 1.235605480406976, -4.668759776592586, -0.08152220272839718, -1.249636140755913, 0.3181947460162492, 1.0572065643903694, 0.4192200570330764, 4.097867743650796, 1.3659283564172986, -0.11441901442933324, 2.5315360785089567, 0.09574092284043534, 1.5974007746292271, 0.5527628355843229, 0.8055085143032713, 1.6213478128399708, 3.6722026990453833, 0.8326274887508727, 0.7862435980711001, 2.3160740649317253, 0.4364962872064641, 0.16409171919000937, -0.4377444201669645, -0.5736564797758709, 1.6153456423383015, -0.26069578059877835, 2.3581092008051776, 0.23434410666127317, 1.3250353857198993, -0.6567937715338941, -0.932055232602891, -1.961207962403653, 1.2524097813687127, 1.717336211900125, 0.8019726831579371, 0.97466210615626, 0.28742655410542356, 0.8071948300309916, 0.18668550229628164, -0.8287815333950389, -0.8520954162073852, 0.28756106269104864, 1.6539927787838038, 1.4705659331228274, 1.6226553714582643, 0.7981843690481192, -0.3537105733951894, -0.140288187579431, -0.1937196994823024, 0.4644696396882544, 0.26331761457783825, 0.9380578052873403, 0.7363568400123167, 0.24189638820470213, -0.45285105787949537, 2.9227869463054024, 0.0039209618982689, 3.0824585574339953, 2.9730751131098265, 3.278621970392715, 2.6990073172102087, 2.21634537283541, 1.4566401879362025, 2.5824553922685376, 4.420079976255202, 2.728518634433544, 2.3449926865294675, 2.716995931942135, 2.5596487153732816, 2.294332954649278, 2.5332759614465092, 2.320969307199171, 3.3870281960121513, 3.0792440530653513, 1.4783664877951972, 1.7662796506998282, 0.6253340263696384, 1.518844338231352, 2.889841649087947, 1.25819071443683, 2.234639959955837, 2.7862343176105844, 2.1774336131469347, 0.5991756482080374, 0.7998648356961926, -0.2490102638928183, -1.0782487538308807, -0.7515204488347706, -0.7036020436419644, 2.8799543387702218, 3.2273657934589584, 1.836488183720985, 0.9878423974844077, 1.9594423215895742, -0.3032992050092558, -0.19689012128772654, -1.1636625662567348, 3.2757777967827146, 1.963404051668003, 2.0061978023808575, 1.3472258055322333, 1.125403663445452, 1.5017609512821455, 0.10290572792555026, -0.03297441858488196, 2.1840141522285825, 1.9013776890082108, 2.0965223180046952, 2.293648670673178, 1.6777613821699362, 0.5921576908848176, -0.5605648409866297, -0.7168306933887989, 3.281129364202921, 2.899187199601345, 2.5913752499071343, 2.6932520001439233, 2.8210035481483526, 2.140777257416635, 1.1572965457514182, 0.05961748025057941, 1.8935598582308535, 1.7801623054057463, 3.9028636421422256, 1.6784960502664303, 3.9186762524322067, -1.5394215766378614, 2.7771143408020684, 2.149217791736357, 2.526605033871209, 4.288758616489686, 3.4676875415201422, 3.238855861575986, 3.5392453065504035, 2.992235457096705, 1.7059720118146782, 3.4688376469465343, 5.303386655510702, 2.174419061684784, 3.4081871217663684, 3.2080619323611557, 1.9995741146421813, 1.9063522574206624, 1.7863367933796237, 4.120688436143048, 1.158511881691733, 1.2814024587360604, 3.0944133486587377, 2.2302320654985266, 1.7092333509371374, 0.12384592008608142, 1.5527406196699032, 3.0022707094898067, 1.0395373845470415, 1.2233760459613172, 2.9221627439290994, 2.018088597297833, 1.0766415658332833, 1.2643214752898302, 0.6658061770972121, 3.040270212800245, 2.085415874552814, 2.069048765395166, 1.1009849940397392, 1.901329903604328, 0.48145126893102574, 1.3766542753515816, 1.2591881735698716, 1.4053979501346072, 0.45760358801936224, 1.8571308555449644, 2.2765000581925614, 1.8348138164586636, 1.9947178846008615, 1.49243432534748, 1.1437362657435068, 0.37367869019742395, 2.837378760877359, 1.8505927373666902, 1.7600131394588236, 1.8033365591495387, 1.8668846431549586, 2.419378897399215, 0.019787931907466704, 0.2897583546069145, 4.630906816295866, -4.234861358192311, -2.5696794856294516, 0.24003299460329264, -5.162793675146445, -1.0015211162251176, -3.0677023386133255, -4.995270261423684, 0.2337789857505807, -2.5370551203088167, -4.851388299517627, -8.075545000610518, 1.1907676342630709, 0.1556429223246683, -0.2706996560960633, -1.0512109473206301, -2.0442909501879583, -2.2303402408067727, -4.159929832555368, -2.829800649387011, -4.878932784717646, -2.2598165580645, 3.6124903174271727, 4.541817345205265, -4.196708108661905, -7.597697828710413, -3.1126773685934066, -1.4399654617997002, -5.29645255408859, 1.0977051360032901, 4.257217894973899, 2.0190348289498754, -4.627864853588435, -10.320975483496023, -8.266964255745824, -4.104571076882031, -4.034617474250392, -0.2710293124605642, 0.5947604291863473, 3.2220675993581676, -9.180429352484909, -10.231517874624677, -8.47067641934306, -5.138620234021198, -0.994379122611982, -0.4396185504788706, 0.9869619652047235, 1.07209472301158, -16.0293260508618, -10.806046938328377, -10.734277399626144, -3.3510964195176007, -0.4037638995475701, 0.5182150291512131, 0.10280076425174359, 0.0839267636165077, -12.156866046650391, -11.463140951235513, -11.372850343089796, -2.3814943850353543, -1.3074061851164034, 0.7684977787637322, -0.024299388244762823, -0.7247630649506703, -0.0033601283626450156, -0.02026545690629331, 0.02134632804034265, 0.0032494863253703533, 0.018408337509480337, -0.005502773451200411, 0.018317958477583735, -0.01968883884130731, -0.7038179038853816, -1.2573926860300766, -0.7498624817070663, -2.428618454503309, -3.2873691724858087, -3.1815982477170586, -2.560655793405023, -0.010794688191357251, -0.8249492018372692, -0.9218625736282826, -0.9050922057163081, -0.38978920872181055, -1.8922375705353285, -1.8058673376421288, -2.5791018509812766, -0.5742535956398289, -0.20669415134143088, -0.5335612083674182, -0.6101444847552644, -0.7271249512485044, -0.781423383148372, -0.16194446738970025, -1.0468638667437913, -1.2125552705091398, -1.5869625595271695, -1.65152494894949, -0.8501094566642278, -0.024302545452332167, 0.9741906998777531, 1.6860457705921168, -0.8048923336634977, -0.347223657484209, -3.1104572302661313, -3.0987236101315707, -0.2789506881507511, 0.9126724314900935, 1.443815890174298, 2.67660535728613, 1.937188912121065, -2.430248688390828, 1.56032609891804, 2.1258280516398194, -2.307887104764154, 0.783980564975396, 3.045761253564685, 2.49115341376757, -3.600020559213687, -2.0304824053084323, 0.0014860194831693688, -0.013216648454691502, 0.003957784143848305, -0.02166277985964905, 0.013098472930612134, -0.008007691039848917, -0.005745212490454793, 0.017747750512422517, -0.8092013602203482, -1.0450566489922495, -2.368054293305451, -0.32633606210543126, -0.09351858679434066, 0.8944937950648495, -0.2609767113688695, 1.7405415974962322, -2.1553099054659204, -2.1948669853976197, 0.5540424216213251, -0.7791612824984578, 0.38969350127105395, -0.2315517977787524, 0.8609320537457832, 0.6454417280603767, -1.1012309103329556, -0.9605787322287753, -0.8763239112684161, -0.24542998471827782, 0.13602284740666948, 0.5401898502205179, 0.9373684133094045, 2.0969965334284386, -0.8659678437312109, -0.5040111748845303, -0.19046174471829577, 0.5872965692507135, 0.5746188713536725, 1.1042020856015913, 1.6989522302253082, 2.2839964048178523, -0.9736939698917226, 0.2352480272550015, 0.08210589386071912, 0.586831483409078, 0.05379279874359655, 2.256407014044364, 0.2196187626130815, 2.1964348666214635, 1.3050084072509298, -4.16258915318634, -0.8484362048589059, 0.1815195227057482, 0.8280087014700602, 3.893996222569217, 1.1968138515161777, -0.5966784038103156, 2.4819219309252487, -0.8306322005184613, -2.8521003739832396, -1.0319315014994583, 1.1354814267070117, 1.9085428217657396, -2.7548778910804956, 4.589842727462372, -2.125730403893272, -1.5723057652917465, 1.8978653567473978, -1.8485579573888649, 2.0974702455683163, -6.492164809055531, -3.7610930315999367, 3.3449118363706405, 2.2077534366799156, 0.8315397447222646, 0.3331486871979005, -0.4850278902488046, -0.48190582094877943, -0.7136094207113853, 0.9171094668727326, 2.9660379657224443, 0.17530519469209646, 0.0810927816320425, 0.08902912698506867, 0.6247041845086261, -1.1879288419038616, -1.5245227438038969, -0.5011711504699041, 1.5303354224940524, -0.2296401413176811, -0.2279815277123102, -0.03570405516396193, -0.07153878832760731, 0.27783925213355953, -0.6563235284402558, 0.7874987738501485, 1.09090089958083, -2.0132523616079117, 0.22800837632890542, -0.6680128123265973, -0.41024585589479784, -0.13554866949234604, 1.3523098061271999, 0.23615250413540048, 1.254036987086973, -0.7998409621284563, 0.78290888538261, -0.2507485407057413, 0.8419482556782194, 1.3646604504731892, 0.5159970072205543, 1.4175317421166223, -0.829975442934853, -4.436182867469074, -1.7670761663778098, -2.732666871655093, 0.40189505633376904, 1.532783028428024, 1.259457045267686, -0.007870749552020948, -0.9572428253777843, -6.7154925529394065, -0.46789736580967256, -0.520953683999621, -2.840360601901032, 0.5083613198034249, 1.426100228072269, 1.3711442640978908, -0.5032359112008493, -6.552352070615573, -3.2468088326264115, 0.03735548650883771, -0.7148014071919284, 0.15810134381644889, -1.6466366742562357, 1.905348013822153, 0.10528645418670246, -0.6209088972366789, -0.703873755975758, -0.06297579596958704, 0.3066923109675775, 1.106446327434444, 1.712853370283242, 2.402875537544794, 2.142910721141024, -2.6608624850603357, -0.7981189320092595, -1.0722461146924553, -1.6039040769161326, -0.4564966079139121, 1.4315418869398226, 2.3700458422775768, 2.6383861751910027, -0.27068431799522547, -0.3260494559408469, -1.936619453353925, -0.2380147628844377, 0.44291466803577634, 1.2177579606265554, 3.1295551559102592, 3.7257828790665033, 0.25562642802487784, -2.6240387161301686, -0.7422209882017564, -1.3474960583303186, 0.1884989982167645, 0.45009236617438025, 2.365113576734073, 1.9267677335156188, -0.07233568296679284, -0.7043462603335725, -0.4862578249669803, 1.148200983393451, 0.9936001525800794, 0.9468599924028163, 2.1478253587769296, 3.0694821805264905, -2.09662500172129, 0.11102314496073887, -0.5056731729178391, 1.9973338234507472, 0.8945333259299374, 1.2100269946402953, 1.0228756971433437, 1.337255751052065, -1.4913984712040318, -1.7036910020875147, -0.7182049578172188, -1.5992278552825914, -1.1018803950243896, 2.301499392609423, 0.10253705006122123, 1.8921650024414545, 0.5619384327666483, -0.6297784883041893, -0.45805737481562064, 2.4097803443252714, 1.1160357540159174, 3.763313695464524, 4.206554731704292, 2.856364100916474, 2.8569255534530873, 1.7872526476309067, 3.1868885032239334, 2.680828388094599, 2.4894355513101063, 3.3811614483413717, 1.829572506469398, 2.39723689239912, 0.18448590033406478, 3.563872010168405, 2.131645657916286, 2.5636738266869408, 2.5001303390384115, 3.520437586032099, 3.5971784085863834, 4.075857731531917, -0.32853644301110807, 1.6298298664419142, 2.5813937621270138, 2.926331019264851, 2.4003679928363852, 3.632107668944237, 3.859755508430333, 4.249543659960535, 1.6507209110330456, 2.1831748828638133, 1.4980483749869276, 2.6169055088924766, 2.936758163475465, 4.317447958272094, 4.135863823155159, 3.5694879800828914, 2.3779746367152006, -0.14311207923620434, 2.8816315992004577, 4.045985359205994, 3.9803502470540217, 4.210604519745672, 5.7810148641842405, 5.70294373047005, -0.4835282423440151, 0.4346970615936468, -0.10909365281403782, 2.099701800995107, 2.875202251844861, 6.1494517895213265, 3.6007320678462666, 4.872818002375176, 0.5219126138929653, 1.127617788140337, 0.3135407254642452, 2.282368244902716, -0.16959967539910425, 3.51498581390332, 2.978875759348934, 6.385650321227365, 0.7310766403313128, -3.0675384394887986, 2.3696727474925847, 0.02064938085584681, 3.177827235335508, 1.547478926735993, 2.177899704803466, 5.04932736684485, 0.0487425570571654, -1.5464862689866803, -1.3979503272886225, -2.1627049605257262, -1.2428312771455843, -1.9486839706195422, -1.2904098990629342, 1.2695681102603873, -7.138329521223219, -3.661086038903031, -3.5304568374041136, -1.9173591555975316, -2.482636690129039, -2.2767236774457027, -1.5697692401727816, -0.36709488488774905, -0.6683025086621808, -1.9868596984883264, -6.446861976998192, -3.2321566084961835, -1.2172558118790884, -1.2509572086951257, 0.25653866982450074, 0.25164861416648976, -4.836066044335008, 0.633117755207821, 0.840033478673749, -1.0517010459625828, -1.0917592071513225, -1.3306948635440787, -0.35041352950322074, -2.0806368470038286, -4.046632142015916, -1.593717655480414, 0.4624263303870521, -0.3358899502041049, -1.744637833760619, 0.2931511079389989, -2.6801895535491895, -1.2392791973906243, -2.4439165579667987, -2.1230429289076143, 1.6709551633794089, 0.42770110243792914, -0.8637381143308767, 0.4825115810782849, -2.601977438581643, -0.8286554614531817, 0.9690198962838033, -0.8668414094402884, 0.12248365165916415, 1.7326611206163303, 2.5749724215430887, -5.532277173024419, -2.082882772568599, 0.7159727689632268, -2.1495217943704596, -2.042305710792365, 2.106270113866552, 2.7339270462873957, -1.6296455174445934, -5.168932739930096, -0.3090541068001936, -0.8270362868003054 ],
				[ -0.003381796714226472, -0.005168742604306641, 0.014874665824101872, 0.015292489333140933, -0.0040926236819790645, -0.010520026898456103, -0.01945325808565791, -0.003912551981627806, 10.697439545959515, 9.381479703748747, 2.783609558514048, 7.840611457802256, 3.599536328122629, 6.813964407048177, 3.892260390048632, -1.821662461918904, 2.390971304947085, 4.7090558634137345, 5.759402111367361, 6.157747872487376, 3.692754671148394, 3.9226599648899794, 4.029900104836005, 0.07745341084582415, -1.4295013773544767, 2.5633153443122683, -0.6037176887915183, -2.390231804610921, -0.13201698920063162, 0.1153338628794421, 0.14136478318623708, 0.31726235793247376, -0.8757739359255491, -0.5520728222563366, 0.9619734707919877, -0.12829915320725688, 0.14784534503371632, -0.6895290750421479, -0.27343519546418715, -0.1362989079966215, -0.5620616397732023, -0.34948393814706524, 0.695252812319388, 2.053429083921208, 0.002032088663065826, -1.7040477250660846, -0.658633355375448, 0.609211273320222, -1.0947601848916884, 0.04621288134100336, 1.168757970945885, 1.2306146476285398, 1.0737190073367835, -0.3689027236191546, 0.7767876673849081, 0.31972592883574724, -0.007302434523653596, -0.009873156923327442, 0.007156424467185479, 0.01044488931903294, -0.0032933457265919364, 0.014197378884076255, -0.008796448687697895, -0.01937868623159344, 1.8644918936351491, -1.6258838842443706, 0.6311305924740809, 2.475783160558114, -1.2836720227280185, -3.0950586273417895, -6.649619174796856, -2.6208921336894155, -3.3467739887111403, 1.101346344588809, -3.1688704709663655, -0.17926129085714101, 2.7335583046505336, -1.4934511738510587, 4.090107470835587, -3.0379786719679296, 2.8549078934654357, 0.23053629902363568, -0.3578522835410892, 1.5970356135632158, -0.6056140829176636, 0.18960832378234113, 0.28100995896270037, 2.2030861706517864, -1.3806952891335806, -0.42225441152518106, 1.4463740451633234, 2.107415992767067, 3.24606049568376, 0.46095249831172463, 1.8044399356261285, -0.2349694412078563, 0.5237886830416665, -0.33391209559098983, 2.563683959584779, 1.0241977356544811, 0.8923941899591606, -0.37830462364175726, -0.9290913469396354, -1.945472854194711, 0.2675638521945119, 1.774590639558711, 0.9802484862919705, 2.08370561453579, 0.5393574371645331, -0.6268208011868937, 0.3336124944445131, -1.282502560123522, 1.059744291473096, -2.7051235428204037, 2.4047646928759128, -0.6354009877182144, -0.2884569086968218, -1.2681048168621278, -0.31400661734206575, -3.4400238955932063, 0.30796056741151423, -0.5857481160376976, 0.11148940207333395, 0.42570692527301823, -3.0675814846638083, -2.8460341273271776, -2.164223203247633, -0.21109829466758748, 1.3223653237170183, -1.2870922299113348, -1.52160500404423, -2.077977980716889, -1.6096232024976753, -2.3497323603054965, -0.28959783989279564, -0.7225216027329603, -3.1135192656051087, 0.9046011210688805, -3.794878941372541, -1.9449969877608935, -1.4771217503793597, -2.8288140129666983, -0.36480386904700157, -0.9530852018079671, -0.06709485803184378, 0.35762714396269296, -2.4714257215609927, -2.0728740654530755, -1.0894799931082084, -3.0078350450483184, -0.8365910642495711, 0.3589864972102589, -3.861803530648503, -1.645111818655557, -0.741323825737243, 0.20286073256991072, -0.29206497071805165, 0.6081299075658879, -1.1097169994177616, -2.5653211067985904, 0.5000175549692231, -1.3198952917990139, -1.8384068692589903, -1.0936899200206953, 1.2094988781729872, 0.09939884895763663, -1.4377456926446164, 0.22244570558700189, -3.377055937830175, -1.0678912052427112, -1.6313852958211439, 0.17233023751604284, -1.4487292980772812, -1.837960341868979, -1.6757562374376107, -1.8689495460678256, -1.5640113651162604, -0.8041626595924176, -1.1648313272778397, -1.418452050148511, 0.3876958458306545, -2.4097555895480185, -3.6344880101638433, -5.2323932269231666, -2.3139900142950984, -2.5554195225022527, -3.258613512790625, -0.27651156637419805, -1.254925679658402, -2.575320266319556, -6.925660236558611, -6.773533993708237, -2.559470972564391, -1.9041428732647534, -2.57503709757203, -2.192019090054082, -1.7521609826867108, -3.1964550896413906, -3.1287499548853552, -2.5675235040563495, -0.14285592950430545, -0.029390404982544006, -0.5542950865453875, -1.5717032488867688, 0.5910230575655072, -0.5268579998198516, -0.8095468583901609, 0.4162260729632287, -1.6659695539645798, -1.4275193940173163, -2.3526638326651526, -1.9495206687195148, -1.0466176428335612, -1.7359312122673871, -2.481454651042066, -2.5106151475659524, -3.487795770168147, -3.8273333632832154, -1.5236928787100115, -2.8723068664169147, -1.3507245013959523, -0.9394931555270014, -2.0702145224752244, -1.7611033118580512, -2.033632308536126, -1.6222903155336321, -2.4225536487122943, -1.8273330776811123, -1.91782320955723, -0.5212935592382604, -3.341499216132658, -2.609941787423154, -1.4172477481611223, -0.287338226572026, -1.3400809464669374, -1.0105393726962222, -3.226515689485829, -0.6937286805850915, -2.109264960977389, 0.5012039003198611, 2.8080175084440966, -0.9455800598835354, -0.9452770590376315, -0.8528162168417723, -1.9313213454355767, -2.3796797018550477, -0.12047646069783256, -1.769494661867392, -0.3647346098635479, -1.0869280653360827, -1.2330057022705116, -0.26351994782737254, -1.7249253945637488, -1.2023069592784403, -0.26420918066472554, -1.6984667279319616, -0.6753341521438212, -4.099189749298287, -4.33568614927002, -0.5465060292137187, -1.8989126809020211, -7.190023734383167, -2.1929853854014127, -0.6538698635516011, -6.223567442998914, -2.249022367748914, -3.3395065383998506, -2.6851316907160894, -1.3560533730045377, -4.311683570540647, -3.4651686138944124, -4.796964420631075, -2.5686783036631216, -3.1620752302515003, -4.941494357104464, -3.6871084099563567, -0.9758503602182056, -2.070207811383183, -3.8467969562727955, -0.8546929436162518, -2.713420437680238, -2.4468827871025245, -5.014196410933442, -5.143594765903729, -1.6964387623163184, -3.3289504288959644, -3.973362987507035, -4.256328664736804, -2.070774925378534, -0.9297452026531727, -2.141920641983954, -0.14743822540039975, -2.974104632253307, -1.3791952820376263, -3.7472293660139044, -3.0941963891972173, -1.7926392608695843, -0.9061457131041037, -3.894297662817819, -1.1903239472785232, -2.2970571740572505, -2.2305900175207714, -3.0489843405104295, 0.04334781310543215, -1.5225300317160044, -3.220554355836447, -0.7935581015395764, -2.4130235530985975, -2.6930419804529477, -1.9376356893585838, -5.631070100718737, -0.49108982692128766, -2.7742755405494766, -3.539557124683258, -2.956246369385868, -1.4410933616630905, -4.208749071434761, -1.9924840177721421, -2.5802319896620767, -1.784331496985778, 6.245836267767965, -0.35430067236150037, 1.617593070787952, 1.6632116659946987, -3.9316145875678017, -6.509117570528546, -6.181650461090009, -3.2638799920826953, 1.1181712860065152, -1.2386274167063172, 2.073901950308025, 1.7763644137692836, 0.9013301413840465, -6.8721067662149755, -7.6049143160813095, -1.3489334985683994, 1.884784474794919, -0.8508247371975713, 1.7834694097000425, 4.116303687106973, 1.5953492850114173, -0.24928841797657372, -0.945279371941922, -2.5562338634959048, 1.6129634883475137, 1.6961542766011164, 3.6762140992155543, 1.7105429741380196, 2.896490367784364, 4.6376098190079675, 3.6629555062963064, 1.1018676716738458, 1.0677733895672696, 2.242679252611967, 1.2073536490649202, 2.3736677840492484, 1.06735693364894, 2.6375925632538606, 2.6038423065107548, 0.016277453217710503, 1.0703676148971835, 0.016130339250122975, 1.831886413831661, 1.5506998035276662, -0.4176900043966633, 0.629419908316561, 1.7725375000631134, -0.03807611300975488, -1.4928463445772377, -1.2483659607118889, -0.10726483187500939, 2.338473963963368, -0.25960042080117307, -0.6023289445928532, 0.28814590426482567, 0.20750309366543643, -2.9936170035363245, -3.6688484281067404, -3.012813722932264, 1.271963566024541, -1.7345948391021935, 0.055462221503707596, 0.5109997133310656, 1.5802877041318422, -0.01982850403960166, -0.00047435494289336887, -0.01947064884157736, -0.011467955862324783, -0.01879072300468615, -0.005664588064317217, 0.010388931580849707, -0.015071682933710799, 0.6669112982479393, -0.6554612631642669, -0.6768545244243429, 1.484948410248784, 1.2409886705568387, 1.49106710225246, 1.3258231188563294, 1.4857627609536403, 1.019257735043532, -0.030012425668469067, -2.124636310296878, -0.515640151091561, 1.2602447277314972, 1.3522100547379485, 3.5429077548947006, 0.89109449070991, 0.45040273824743887, 0.851391157542913, -0.11876300937188718, -2.94563921928053, -0.38966799192278406, -0.04781860542082772, 1.1139500954180097, -0.043620362734458046, 1.6267593826785034, -1.0235712008908064, -2.908241800945694, 0.36500760542777955, -4.836755467068693, -0.4982175589280234, 0.6248015433651567, 0.023468880767270422, 0.4402420090020981, -3.9696246159821973, -2.5602975633864467, -4.28456335569288, -2.4676640997372545, -2.9610813109590794, -1.3286095824707038, -1.2915424650919707, 0.5197281055308407, -0.22180533387799445, -2.413867570393097, -1.4724478973968274, -2.3830591661971106, -5.307142526759655, -3.416805364791109, -7.205920506840064, -0.01577916140536089, -0.018901109153833574, 0.0007859626901962867, 0.006678100574927192, -0.0012808113943800228, -0.004337668112922269, 0.00495946198312689, -0.01096921179079959, 0.003820631230578934, 1.265715263481386, 1.0435562268029057, 3.7477908336566554, 2.3059449380783708, 6.459880582557481, 0.48623608562253834, 2.6716252362510446, 3.114920652182546, 4.099568815807411, -1.4744700630537235, 0.26595313815768035, 0.23204660352676545, 1.1150534392639613, 3.112386021484207, 3.282616518066397, -0.36117574603396885, 0.4935197204194617, -0.2608040756084052, 1.0420225661216493, 0.5589704305239237, -0.5225466634720235, 2.6993955757891515, -0.2127528549164657, 0.9918338540319478, -2.4376410955560353, -1.300471868939627, -0.5146240220038502, 0.8577946020533346, -1.3316062054626274, 0.6829830134384677, -1.5751802575716518, 3.0452133997314323, 0.18597408478068733, -0.18638659097149488, 0.8927316178950737, -1.070041242900615, -1.8417568005341804, -3.1774287133974037, 3.6761597600718514, -0.3171025283565516, 0.2649018800039341, -1.6699840217936797, -1.6141852921600008, -1.703127935312958, -0.6784507388552364, -0.4617641477684137, -1.6436617353570337, 0.11296628030172597, 1.5422513028631224, 0.8545358280741902, 1.2652094178110478, 1.347482520865746, -0.558308575944356, -0.3714504530178255, 0.8173338570278682, 0.4545983584767465, 3.647886399857467, 5.185628449497608, 0.8652048666609351, -1.2923999974048148, -1.169771350748728, -0.4951208428543752, 0.258835641192461, 8.741489793880994, 1.203830768282786, 1.6071513848303134, 2.717396891086538, 1.7782332914047352, 0.9785921618452627, 0.4019108419609019, -0.5673762705681847, 1.5644408574307562, 2.6877936777690836, -1.9160662359883094, 1.1029749980726513, 0.4207208997438052, 2.328675936438721, 1.3173516209111393, 1.8174362874284202, 3.785538706192026, 0.6563330764244559, 2.2202853236419946, -0.42837939180893736, 1.6091447269658754, -0.46932659727008863, 2.5630484666993287, 1.1793671797002758, 0.8057387248531434, 1.2916350108194377, 1.3642486743669644, 0.054620104397352, 0.0930900825551357, 2.013742933539616, -0.8885422481237474, 0.3906015871776382, 1.6891694522972065, 1.0125838273911507, 0.6010187216689222, -0.5860530518257796, -1.4667548695816517, -3.613432509345052, 1.1700614279948847, 1.7968234416076403, 0.9878049641492673, 2.1785110930528937, -1.4011813153149775, 0.649129212566085, -0.3675812988448129, -1.062991723148288, 0.6399170942740653, -2.2162541231728983, 1.4681979043664355, 0.6127272823679637, 2.003608910387284, 1.6334254456244697, 0.9453942110199303, -0.9457046072515243, 2.7487958320450874, -3.2903413290154155, 3.2788723661511465, 3.321520223887135, 2.2454037994385665, 1.9744676514733535, 3.703607100030077, 0.9833690156651712, 5.963995502724762, 2.348650621989024, 0.35998287394248374, 0.04456639768218598, 1.199731660120291, 0.05449017406447798, -0.3850446402794532, 0.018823840039291988, -0.8468696072613319, -1.4315273855904755, -1.536056482841487, 1.6464499122722591, 0.46564695712015386, 2.163702575399352, 1.191712627380051, 2.0428366152775097, 0.47791483607385443, -1.4232150449541328, 0.9743999771316447, 1.2007114845771474, 0.8937114869350197, 2.0401365691787223, 1.9593571303320716, 1.7168793074190858, 1.7979691189608638, -0.6108092954181668, 2.7006927774768936, 3.1881148654051543, 1.1153097062017434, 0.565085180315714, 2.2453610204099275, 1.5655461281938174, -0.14638228613734042, 3.701343894614348, 2.0239259428718617, 2.1734649644627906, 0.6838962118929283, 1.4629381306209222, 2.5082496401395855, 0.5574631087150511, 1.6006552697676533, 0.4051560145884851, 2.7745491120799235, 1.3962181466567862, 1.3842683344790805, 1.0563906703429755, 0.7582732881692982, 0.7588793954740547, 0.3428236442293838, 0.4415601094777622, -0.14354735225054605, -0.06670146592847603, -1.674404690520191, 0.6877050970005977, 0.45621444399746686, -1.635111948849555, -0.9339978760623879, -2.001018416328866, 1.0173931429716352, 3.9215034187432463, 1.6302696672090895, 0.12697122030831412, 2.4966666986048702, 1.7101715913332811, 1.974009173940486, 1.8750601765053847, 3.2782941433596613, 3.3552175533693767, 1.790281237200862, 0.896350754274013, 2.1420618588634466, -1.0721771365617638, 0.6379453194304878, -2.898874353572617, -1.8623362667930643, 3.7473546367666986, 1.0095426240426308, 2.7206420146258545, 0.866804414979182, -1.4634175567179055, 1.5746675698704604, 1.2114249578527736, 1.2486346871394132, 3.114697727875796, 4.538345092513555, 1.5080139405848598, 3.105830338087408, 1.5209346886358128, 2.1780671146806068, 1.0776369883804953, 1.9299009336745412, 1.4691575731098032, 1.5058329387328002, 3.312578923581636, 0.8967302912925631, -0.6747130106896843, 1.7723310850758032, 0.8232342384421477, 2.0601170215370277, 1.6732531642252668, 1.3240255383389217, 0.6220234973421522, 1.4706818262643646, -0.5504463055349496, 1.3452497046877947, 1.069047666612206, -2.3464203393903995, -0.7662308777615761, -2.059983861943139, -0.0821375672456392, -0.028357904787255923, -0.754125567991858, 1.5805276700216893, -0.19620471228335545, 1.5433771449165383, 1.5959387171991262, 0.6620032446947781, 1.22963715893896, -0.08493931679895483, 0.22145048340868437, -1.7739720829998602, 3.539989971181447, 0.6922598490902984, 0.8021210765127337, 1.4189132117801666, 1.2050409840698133, 1.3188685203423223, 1.2405118598127598, 0.5119386779408078, 0.07493597216554122, 1.2461608297358422, 2.7772900722191003, 7.312153508261416, 0.34237575908074824, 1.42466373306511, 2.903512241318396, 0.28360063614452863, -0.4966892941326483, 0.38936651956027046, 2.568448853511314, 1.3562840425697364, 1.0215819751655804, 1.201874735908446, 2.157446538628776, 0.8731866136024394, 0.024237507442330525, -0.2703375349417096, -1.3725216653859433, 0.34657542809774927, -1.1462287678353633, -1.0231100862241487, -0.6118810957849674, -0.8186702120848383, -1.0526382343851182, 2.7008911634758546, -2.708915841751588, -1.4386503995432331, -0.753596006745241, -1.1615165479957426, -0.14099030351542163, 0.5461018225422182, -0.2016873233907944, 1.099621583808199, -2.3456536716019896, -0.6905943954361429, -0.26540366025829243, -1.6105763810978155, -0.9263173018584441, -1.0440670026743606, -0.07597700042499712, -2.487880033150086, -1.057263591723651, -0.512489688946969, -2.5471962084372057, -5.592125463012305, 0.515650267614897, 0.4759821639934034, -1.6756828990399162, -2.069623211511597, -3.9785726030318553, 0.07106398271370598, -1.2689891681570513, -4.252251548056486, -2.02852393303981, -0.7195300421531663, -0.3507985657496439, 0.098581876847285, -7.798484724597838, -2.627216090300497, -1.7061606720398736, 1.7162821760631015, -2.0704999232357046, -0.5661775223766643, 2.497126582731463 ],
				[ -0.0065576523614673905, -0.01930555617753047, 0.017899161660555992, 0.020786591535327706, 0.005767778343980692, 0.0066061644676988366, -0.02052475813670105, 0.015911207617114786, 1.7003830535142956, 6.294662981195204, -1.6239702540178484, 4.228739078651347, 1.4250579559353271, 5.441156110262165, -4.190993184284471, 3.9337440432671404, 1.924501915404838, 0.392443295303062, 0.4724012382215149, -0.5202031620235327, -0.009230300366010687, -0.6594476684977715, 2.2351313389324874, 4.337475279292102, -0.7076159806148898, 0.11489246116555744, -1.0160141743911333, -0.6302641393434022, -3.1766118751926347, 0.28146000395438703, -0.13583267208805647, 0.6170104791943274, -0.601286242022181, -0.6862042163300267, -0.7304953521447053, -3.107178108368789, -0.8334453335706108, -2.094238056011148, 0.055110010632563954, 0.39724470904534087, 0.40652885067521993, -0.5024403907108846, -3.801085063891182, -2.4457634102222, -0.2761167832271091, 1.3668817285910801, -0.20390117801485602, 0.1425148799901005, 0.43795865316901017, -1.5788243331733525, -1.1654436713933791, -1.9249355943442814, -0.7998327223811467, 0.2392500627631128, 1.3647036469904803, -2.054459602119701, 0.016622081440994255, -0.00419679035191935, -0.0013512471818441457, 0.004309572439708379, 0.01954690894909901, 0.0018556665752051085, 0.004069906691549084, -0.020826220206806228, 2.427237547107911, -1.1386635077391867, -2.7006047313068215, -0.48388798099895763, -1.5622562676163585, -0.5848883612599133, 2.440128655392853, -5.668884077606316, -0.057892654171650494, -1.2866495497397274, -0.29117998930229017, 1.3577040441858523, 1.2352057155230118, 1.8551026384505844, 2.645403421003923, 3.4929313105617874, 1.191984644784908, -2.710332668167685, -0.6330116918914073, -0.7555727448501632, 0.3558708950978416, -0.10782038581963928, -0.20958862123677818, 1.0445036525570437, -0.7876298231524305, -1.440870922215064, -0.18716544122153814, -0.7468193579562259, 0.9244410148806594, -2.876705970853182, -0.1566179660194605, -0.15169415965163952, 0.1874101179718912, -2.3665798106640556, -1.1321599579876662, -1.276921424400407, -1.5581677597621162, -1.488984984920673, -1.8730531593953932, -3.142224807458472, -3.4755689964974357, -0.36222498065260517, -2.1497436309399327, -1.7285211518419497, -2.3086140370408095, -1.4790977094741826, -1.889090908867967, 0.09926756343963176, -4.823227887635082, -1.06294267752243, -1.9996905333884125, -1.722032289593749, -0.9956753260724326, -1.4066259973224664, 1.10715001805903, -2.213036679012222, -0.4090349726910445, -2.2327317543189413, -1.632541088081743, 0.905205464315879, -0.05170295592232702, -0.2904018287662283, -1.8930894906213265, -4.26715526239343, -0.7328509560503846, 1.138431568299123, -1.056657573756949, -0.1217845753018064, -2.4442597537384176, 0.7673865274497493, 3.006260626289981, 4.554379413712556, 2.219822770895281, 0.13232683568316383, 0.7620819307240893, 0.795590713991184, 5.266627476369628, -1.3130435145305963, 1.5968891756278751, 0.8925898327940069, -1.7453488759478537, 3.204743804495533, -0.12324841642447029, 2.9730204881390048, 1.0869786517330318, 1.2071853441149165, -2.56542440742059, 3.2918545790914218, 1.6666425749487326, 0.29885077970128954, 2.2505446616760305, 1.1148447679017817, 2.0206279997182572, -2.5653369796791616, 3.0543470086065168, -0.646203269586363, -1.350668283493873, 2.283994792628472, -0.8501288525879913, 1.0454824372626685, -1.825901315991871, 1.4169786661373152, -0.9691756994741445, -0.6038282239693625, 2.7861865643299937, -0.4304543606354064, 2.7673425274597583, -1.337243015827153, 0.6272288541857862, -1.3729854902513605, 0.09127706124917075, -0.7098240400292342, -0.3972199445469963, 3.582305889168956, -1.7626610073325608, -0.14748112088403317, -0.8495747280230611, 1.139718971809466, -0.6767956875925581, -0.514461719201794, 6.079120400282696, -2.0376108117406857, 0.8850375482793053, -0.6709269318433212, 2.8111757361342926, -0.20016341119057365, 1.7237742594408578, -3.4668734453731513, 1.110006855424439, 1.9264691633340452, 1.001540122412746, 0.4176489968911461, 0.913960548754881, 2.0413820941403715, 6.035689610626985, 5.551828528827026, 3.405301000744215, 2.2668014658366977, 1.7941660632726808, 1.200354001812999, 1.0635267420618786, 2.104494293810024, 5.629945128322827, 4.765080177281597, 2.2431660598010446, 0.6103096722700337, 1.5057037043289503, 0.9387285482179588, 3.3621705165330793, 3.8117494597411192, 3.234559091008938, 1.0180514574686905, 1.7447051654232777, -0.21776297805932981, -0.5244800212036924, 1.5178754305279234, 3.043091656062722, 2.9519407085883884, 2.3412694770952327, 2.1979942613719388, 1.5127182360416207, 0.7702169314790386, 0.24057239182736695, -0.7726181502763573, 1.7088718887873562, -0.10243849670088517, 0.5820638794442523, -0.7208778079753304, 0.05984637596459742, -0.5391410718605245, 0.06867317733154892, 1.2167027246948825, 0.995240574982821, 1.8519790306860775, 2.32041148885141, -0.6845768261336086, -0.4513253147109393, 0.7871919674505408, 2.0739793410584633, 2.0871391501038294, 1.0321270087741725, 0.9984320509971208, 0.2582497602973194, -2.8488918609657583, 0.48039538270844895, 0.8889419459168404, 1.2365502177654881, 1.5284944132962357, 0.7615903809577652, 0.0009294604733097474, -0.8423618022741574, -0.31688742698198746, 1.3615197857427577, -0.16726036817040107, -1.2946234777135193, 2.397583663695399, 0.4888782517120536, 5.098965538270041, 0.5256682162118859, 8.237373082646176, 3.9478021196971085, 3.355766041321145, 2.6467978419901788, 1.380888496690523, 4.787695582459252, 3.4387758292035917, -0.6703934009121667, 4.958090249084265, 1.6675743621240868, 2.2582044552879865, 1.2542145150782662, 0.7051542763642379, 1.422483250182361, 4.6436178800051096, 3.375919684116757, 0.21424212245007906, 3.3028913106134623, 2.787265617019302, 1.6113508367391642, 2.098756378195508, 1.5901047980628669, 2.799194599100547, 2.203417413612908, 1.653090864101272, 0.5615259807030674, 1.7812348920042118, 1.3314185445618467, 2.986783621204225, 0.4219460009711082, 0.9377752807574128, -0.2356248555262664, 3.1699356484928556, 1.2891254122367732, 1.7656037956574822, 2.0112013279609005, 1.5546334969464326, 2.0696128197554575, 0.39148172590433855, 1.9476061766487542, 0.17663790959006218, 3.5281388264273423, 2.4913051061616143, 1.2762310846714382, 0.6758982030967075, 0.49341865490387005, -1.035687167741835, -0.9073524893435917, -0.26535676256226126, 3.5956161443542296, 2.460432947452856, 3.0541105145474634, 0.5067084707332411, 1.1322049279348383, 0.8197674227345526, 0.48210042772305284, 0.9383147041404845, -5.276340683520285, -0.1679997309481762, 0.6465738315005782, 0.77363585128316, -3.8687000227922845, 0.843078251789256, 0.6306645131033154, -1.9921529103661946, -3.8677521969373005, -3.019628989117419, -0.007046848311336749, -1.7197508260421162, -4.302482737886819, 0.9530179903486773, -1.326521585754606, -5.412201912384175, -3.9455231442642664, -5.193797784102744, -2.546384760100438, -1.3509133234121995, -2.1590607806144417, -1.3608120781926236, -2.030299190889382, -1.2219664337647733, -4.265922099062698, 0.04021588168755113, -3.0361977159023135, -6.627723059842292, -3.492914264258432, -0.5144670725346993, -0.6995495050467775, -1.4191769892776853, -7.2261319674031075, 2.0939760882238434, -3.321666255746275, -5.607241605856984, -3.2028077756784734, -1.4513557028124002, -1.6511076096097057, -2.1236127150488566, 2.5127220252045572, -6.709179854317322, -1.7843774671717407, -3.9909909347532286, -2.3665724198315594, -1.5550587692141977, -1.4214967619841852, -1.660721428120697, -2.405148212394361, -1.954270274276134, -2.5104882181675015, -2.6415667808385033, -4.17913403501839, -1.5404613716718358, 0.10948810744453688, 1.6453489181441274, 0.5278767575556453, 2.1471275659774522, 1.494371908534963, -2.084010738554413, -2.3003339980013506, -0.3379133351056395, 2.256654476161451, 1.929201209130575, 0.0020901298107322917, 0.0016865161858838505, -0.008888476275833028, -0.014305046313200747, -0.013874515910863484, 0.014569051716466504, -0.014761301354210103, -0.017324485556586507, 0.6189316975493574, -0.5031842149057819, 0.8010737297277056, 0.3347281612940182, -1.8820525576530887, -2.537067772900544, -1.0875160150599794, 2.3208483937284736, 0.9240380076067563, -0.2550972138002074, 0.8213463846462146, 0.29116628289757934, 1.0684506321764708, -2.5678378838329414, 2.5832623496185643, 1.7696012164477946, 1.129507970638542, 1.287618737991117, -0.8979742323367436, 0.44804327605369826, -2.2506820021029825, 0.684247866474426, 1.2102335550910601, 1.2196056895911893, 2.3219257993330165, -0.43726382940470054, -0.8225552084404614, -4.048980995048986, 0.15501544752996985, 1.3045387171877343, 1.7182089706721675, 0.24956840980906586, 3.128624099167487, 0.25438197732857615, -1.8986621764195046, -1.0272269715981952, -2.239877231316148, 1.8945088382968063, -0.8824141634102582, -1.0397468108667698, 5.409487780129872, 1.893381128703131, 2.678875920613986, -1.151515782890095, -1.9859755340959548, -7.050976460239194, 0.9097208083515274, 0.4302017001932019, -0.007144675606542585, -0.011260058140217995, 0.005670635213408431, -0.013242912250608883, 0.014011602769707513, 0.002397571059450179, 0.020703136836960054, 0.000045204390914640586, 4.610082711096345, 2.0332757109466972, 3.459522751968063, -0.31753066191112855, 1.4754327171399717, 0.17071341337037962, -0.5896345401268516, -6.245599264550769, 2.134107652302229, 3.2921482634335595, 2.410195948957211, 1.1347222774455672, 1.7407769814553753, 0.2865365063127391, -1.0775475066725737, -0.7744393675260974, 2.684721782535594, 1.4170442291142644, 2.0565463668045827, 1.9859042472437998, 2.062977286546621, -0.15521004095786925, 0.29885487887394235, 0.9833897015862129, 2.449793640108745, 1.9692827352346929, 2.4664693787463796, 2.130167346076168, 1.0699597252259876, 2.0443775255483274, -1.1393324041501995, 0.5767671255945984, 5.425131512442334, 2.3858829253833846, 1.3890870487639368, -1.136487046478563, 1.1838286159531899, 0.9070238033305899, 0.6273637945923369, -1.1997663777715821, 1.782981680285362, 2.5854040535764566, 0.3015717600429388, 1.0339446232790155, 0.7166053727176331, -0.10210883187519176, 0.695819828719119, -0.8743752541729267, 0.7951744488701072, 1.7075462778306394, 1.716526688801348, 0.33787855422512514, -1.416559177681268, -2.345758649601778, -3.242217373084174, 2.3460789069380574, -2.0104491667989097, -3.068266691510384, 1.7458905208328537, 1.1421927980860174, -0.35625626067292965, -0.37880084211270454, 1.0231673547610107, -2.4901936719255615, 1.1166350421892428, -2.133906111692794, 1.2842037527123833, -3.631647130849295, -0.32803955157694026, -4.208678057649527, -1.0669371926233255, -3.0729175381911547, -4.825711425242985, 1.455489223504691, -2.6006513037119845, 0.27291595237141486, -3.4475647509768286, 1.0511631240317658, -5.417538245537111, -1.2760306356154874, 1.5596613562675092, -2.3860070600381036, -0.08403553154493215, -3.7156287094831333, -0.2958393845480292, -4.197225131181255, -0.8441452663481134, -3.1235463248977178, -1.5120799431428098, 1.4512708089307516, -3.327282494408979, 0.003225621507386028, -1.6313774633368734, 0.5287482647675451, -4.442398512169032, 1.480204539176054, 0.5917721753736367, -2.0465837474750326, -0.078552575355019, -3.4944903662826694, -0.7277217745792407, -2.412906157488794, 0.3899392213774511, -2.966638045642878, 0.7503327533923029, 0.13232161407064785, -5.63852486407423, 0.15906223026567531, -0.34813098768902484, -1.7984436145152716, -1.1702412411443044, -2.0822569369285815, -1.2940049026515967, -5.616484216938437, -0.0644984526764897, -2.588509485675451, -0.276235231021131, -2.3443933180011123, 1.721279448488546, -0.3036615714864231, 0.42684185387125545, -2.116461859422429, -3.0828971217579992, -0.8181509638669169, -0.8686644064166, -0.8543212145790546, -7.892507130029893, -2.9283698223857364, -0.09163671021443685, 0.30731882581673875, -0.9588333207718124, -0.7798983453619429, -0.5454838062144515, -1.7966896326360096, -0.44946324897998197, 1.5220103999811345, -0.6310106829162737, -0.3941116465981731, -1.3978460821625496, -0.47686760293959396, -1.5024154499620792, -1.5499055931648456, -2.476723404170181, -0.6707025520962733, 1.0420617622723585, -0.4138529571268538, -2.3092929656978143, -0.7146322823865527, -0.46352794858884133, -0.4018957714877496, -3.090546924126452, -0.36052018368813327, -0.5834499042157127, -0.7454216664952145, -1.4291531238216595, -0.8359631302154806, 0.22512087891640015, -1.1247544872450712, 0.21067504848547286, -3.1519717506391807, 0.5671716686705373, -1.018930872694199, -0.8389236294346, -1.5406677556400143, -1.147163017086055, -0.283061386174188, -0.07984036852401694, -1.4345628640944144, 0.07430972077796562, -0.47039253816058196, 0.029822417017303576, -0.9692064852617963, -0.08267664256855659, -1.7654221009370852, 0.59425790358684, 0.8831525796119511, -1.052325517716206, -2.2519970004687937, -1.628604231352346, -0.6105278468767225, -0.9948557171251304, 0.13573850090457212, -2.029445787522203, -1.6678568342975482, -1.5938374874274024, -1.7508060367728457, -2.151675237300073, -0.8942122995203823, -0.046403610905484116, -1.2023626883229879, -4.707964249025154, -9.141770088559934, 0.42850467816043164, 0.5648587457128369, 0.03053637667990947, -1.1007322873288095, -0.6056933445689987, -2.8579286435046156, -2.1487635393139266, 1.0554878973460864, -0.5089082275610148, -0.799305385377705, 0.2937185827883781, 0.42844232336520033, -0.6370670670078316, -0.4323957823615771, -1.1569289338651925, -1.8877335751557467, 1.1784382042310941, 0.6994964555096354, -0.42347244582069304, 0.46859722127525855, 0.09485782240642064, -1.0196750403978063, -2.8580822714136263, -2.7048580024850293, 1.1269509073530806, 2.397369234523496, 1.8862659332446003, -0.5413389663916229, 0.8494491426013565, -0.04167722114054956, -0.0830041634851483, -3.507334295447629, -0.20925268451041218, 0.5414548165510618, 1.5197293024042724, 0.9262882336846117, -0.8648263449520828, -0.47767080503332365, -2.3865854868566947, -3.583360770674415, -1.8059312852862317, -0.7378914402932262, -2.0606024026244, -1.5160878137263858, 0.0862495729535378, -1.4653347038082207, -6.788348641613434, -5.1737232662226145, -2.4155232573107006, -2.3896833493972114, -0.6617896864388764, 0.6942658277070568, 0.448017522824436, 0.30395030217122654, 1.522704055256583, -2.1150409529382936, -1.2761505565277558, -0.22037574985704125, 2.012013150294251, 1.1128943154391733, -1.7814719328830892, -6.302644522533134, -0.10171069561017937, 0.6146605335254236, 0.053797451843522935, -2.972245228639935, -1.0829764651581817, 0.59132342927327, -0.6065141154957641, 1.331803152489607, 1.6157207838212555, 2.519159826751155, -4.339260325485772, -2.9434380219904153, -2.9049246368171127, -0.3811936175405265, -0.796102056328824, 1.0549324406578156, 1.9968887567688351, 1.1073577917703263, -2.0557799315868572, -3.398384814937684, -1.6145950336052362, -1.0294226163169833, -1.6758554014637566, -2.5149069955540972, 0.0736966700038829, -0.07619364025405359, -2.0653742737944136, -4.189619212316925, -1.6076728117959769, -1.3176006787554413, -5.752799442008585, -4.699293427802178, -4.407465168821748, -0.7166202640539896, 1.566178336949603, -3.3684277106384477, -2.1488375223154343, -3.0761669678206776, -1.7448903521599277, -2.6370105770497623, -1.5746199657614774, -2.848903209168163, -0.2839262501164985, 1.9854207108622908, 0.10200421377535147, -0.543034460234492, -2.8936535856323116, -5.072850232391997, -3.9340623071594463, -2.304647999333432, -1.369238138007133, -1.9392099328628607, -0.29157230315608096, -5.891484766845385, -2.406976681457249, -2.965893618689734, -5.118181124791988, -0.2452295362431408, 4.2561946861428845, -5.532545542177156, -3.9705679044192843, -0.7524994950796478, -1.1127100793560802, -1.2563782814804816, -3.2581672649232294, -2.376659875713975 ],
				[ 0.010830113089373107, 0.014522908498025434, 0.00880041787157982, 0.019905613593608262, 0.000004874916579390573, 0.021403106589195853, -0.0021224223685316424, 0.0036107283447473592, 3.441251080704848, 2.7768470730522004, 3.279601397214124, 1.5984264414869342, -1.191623053133297, -5.029104609613477, -8.030729615229433, -2.066907687327886, 3.0891836690968844, 2.9442295316031313, 3.352985852967896, 1.9108006097284045, 0.3675248160768806, 0.739503109707121, -0.2979458737600984, 0.45825290264073787, 1.9304290076067145, 1.8267096460321735, 2.246833530216095, 2.30833247682217, 0.6932627781543367, -0.10871049814013757, -0.6010718429081084, -0.45096750617249404, 1.84837193458119, 2.1729388868476396, 1.871152603561417, 1.291337842093145, 1.1491874845788688, -0.43380757944850407, 0.26228570246816313, -0.41359291648044627, 1.5639699820824402, 1.2871813198789868, 1.1129338712527521, -0.3100992447575355, -0.050691522530790886, -0.5924129962252412, -0.8751982152649848, -0.9381015176253478, 1.631821669478565, 1.2218878490858065, 0.625895333735241, 0.7370490743461775, -0.9950091676331212, -0.4774118890473586, -1.0839523681192766, -1.4187961549741426, -0.006189830569944847, 0.00953023781364562, -0.003923414950401215, 0.016115555356448395, -0.015557831638013674, 0.0054869105846400675, 0.006034820865435731, 0.004634054336760709, 3.6820650421303656, -2.393452497946409, -2.422342589541513, -1.582893589254501, -1.0832905943812545, -1.135346793046848, 3.5083816658183613, 3.788377053662336, -0.44771971812924327, 0.6983375168956499, 0.22189527793680885, -0.5610256933577173, -0.026776881856658594, -1.5565183181147013, -0.33519142406384317, 1.6244350205241185, -0.16053143144347456, -0.5207635105236532, -0.8969561574064114, -0.37598650611411427, -2.662292514766872, -1.5878144533410115, -2.6184307875918873, -0.5509981622296061, -0.04354546881976119, -0.04140013868273665, -0.8418374697695773, -1.9862613750315348, -1.7612849001924296, -2.8803273475318343, -1.9200173048030724, -0.9562182313088335, -0.0620019256509459, -0.028999800268124706, -1.041639134706726, -1.8706036597342892, -1.8730642731623224, -2.4421980009753974, -1.6707122223502158, -2.070298143736335, -0.08361045127522088, -0.7972346768846813, -1.5849196712427536, -1.9586243605794118, -2.353618441072812, -1.917075433941362, -1.4596772318419906, -1.3459551198261943, 0.6701726045746902, 0.3295759882662976, -1.6251410450323496, -1.8431481551339104, -1.518504897486486, -1.9414171641648201, -1.1272097372789076, -1.9327654341325544, -1.2727476173183716, 0.3231158291182222, 1.4230379922229413, -0.03548694109043593, -1.3437879570597764, -0.21419284305004588, -0.31923157360756105, 0.00181284201905512, -4.605505357915237, -3.7234479766419186, -1.9818750135916647, -2.564477897563038, -3.7293144647142022, -3.861101466694258, -0.9052621793816267, -2.5303885521662877, 0.08236130448568169, -2.486078103096364, -1.5819848355406283, -3.6655005146369484, -2.1154393842248567, -1.4379392658363248, -2.371844917421792, -0.8588504387232112, -0.551413114859549, -2.0259565434165787, -1.669441768344478, -1.8404347366020766, -1.620368378690484, -2.4419265013535303, -2.539262745230892, -1.5167341322897465, -1.990561823604914, -1.8594258767526852, -2.210823335572115, -1.8120775998706242, -1.8537802269465817, -1.5768804075148601, -2.6225694094597385, -1.3900189020683376, 0.38589394781343833, -1.3440243952802557, -1.1474408685805806, -1.5492980073559381, -2.5979370956097254, -2.3318289985565825, -2.147968177976776, -1.5222253501601855, -0.4758439508651974, -0.4819994307749609, -0.9912301543382849, -1.1777321638542821, -2.4276399998544336, -1.2133084647338332, -2.9057751140888546, -1.950359846360442, -3.515220173062791, -0.6344077904153216, -0.663716502111399, -1.850974353370988, -1.5446048043161789, -1.9584939498761642, -2.073086095048345, -0.5526153840142324, -0.023572605904345813, -1.005660406630015, -0.1860128976654865, -1.1349791433039664, -0.678774001181633, -0.8484835203741, -0.4073602427800225, 0.45004202481462185, -1.28703706298093, -1.9885083515627946, -2.328125808164414, -2.0448029197849484, -2.604665089056161, -2.1403781503024004, -2.0439770344468178, -2.0324868884123592, -0.7421017665776819, -1.0084897573734404, -0.6210639227127874, -2.043264088525519, -1.8281597415366053, -1.1030110864483684, -0.8946556402428983, -0.7574552497305675, -1.6106944317803837, -0.4779188822515498, -1.5971284098962557, -1.2156369397430435, -1.6093555218694675, -1.9221458167536423, -1.425006878636946, -0.6659960837226019, -1.03412208973851, -0.5352963052148935, -1.374590615043094, -0.6634929715020215, -1.3753831275972912, -1.808179578200703, -0.4544617028236226, -0.5365782995039834, -1.2515360098139814, -1.0877730438790825, -1.180690362019993, -0.8430557584304288, -0.7197016899954808, -1.4524813151786211, -0.709912357047997, -0.7818450500049767, -0.41284978790951177, -0.5824456760344716, -0.37884732206523913, -0.8856252655675395, -0.7923304969512542, -1.192837262265945, -1.4581089728962682, -0.48565215818013036, 0.17788894141944558, -0.1021261421213377, 0.20694506174026417, -0.07518380448869702, -0.14337621476239581, -0.5374040451913049, 0.07646649392418545, 0.6617381976610813, -1.2349715902124134, -0.448211808652698, -1.2061154698915708, -1.3352279360861885, -1.7779863529429718, -2.2077291322079917, -1.190759021759785, -1.6641519561695322, -6.0694034918877975, -6.97160376566976, -6.648270833859303, -5.909061036415027, -6.804337274803911, -6.4745756967334955, -11.466076503864912, -5.647134979917852, -2.651361577409878, -4.611697585226371, -3.760189383637555, -6.5115061923199224, -7.260205557099783, -7.718027744007469, -2.935801653332025, -5.440079448462615, -3.439853565594606, -2.066281106422845, -4.220067351340605, -4.595603920497739, -6.179513795677595, -7.759639211030468, -4.590529252499151, -4.580685348757826, -1.887316940932125, -3.236326919989639, -3.8106486601946266, -3.9534812202938947, -3.0979350642449797, -4.907850132895423, -3.9072481849855136, -3.639843304531884, -0.46437723827050836, -1.7069597098414564, -3.5621914964769026, -4.3273279302609895, -3.510472314959739, -4.661236998321208, -4.552682918873266, -4.785058625825411, -0.7851327336209925, -2.4649244502451926, -2.521137999994734, -3.072360067964285, -3.293656726255844, -4.147839965008295, -4.03925460655685, -2.1784154541181793, -1.569769998185154, -3.070006371627068, -2.216495897902044, -3.448844937153032, -3.734866871283705, -2.4488772753902146, -3.3945426001920693, -2.474718056011543, -1.4000078141547383, -1.84620767952035, -1.235695591751469, -3.0198293541062435, -2.3988454432123136, -1.306920114284315, -1.5612479819381169, -0.7165151951298918, 2.267726372063434, -0.5620858872323279, 0.7832823612919917, -0.8095833745325431, -1.3755454201092314, 0.10214299894581741, -0.13762175290628959, 0.026782843901582715, -2.8281754145118247, -5.685989705783014, -7.068920710239616, -3.278700490265695, -5.015374248300588, -0.4650884040135088, 2.7312742410126667, -0.3523253084435575, -2.977313212832847, -3.2999444230816395, -5.24016445236944, -3.4071847692437385, -4.194790112129775, -1.1553421662262477, -1.544606290718188, -0.8446951944371922, -3.661663404339375, -5.925622561014106, -5.432379835517605, -3.3531191037376957, -2.9634100574895936, -2.9022460682743136, -2.139982561431061, -0.5799815941905188, -3.4334782752108817, -2.824308274353553, -2.0438563226720254, -2.660039685271834, -0.9126839789290343, -1.2588351922563634, -0.8029884838109776, 0.32567629897862416, -3.530229947466954, -1.4058064779433803, -1.3644197466118893, -0.6950799702418207, -0.41758861108113954, -0.07338425368306145, 0.00804505269970001, 1.1953952929628486, -4.097453105739382, -1.8979948735225383, -0.852195591809064, -0.4568676140845142, 0.6277557967808237, 0.23314718683418237, 0.3278723335630404, 0.351237580755391, -3.5144541401766216, -2.5294805261912585, -2.293087569717448, -0.7965646824997187, 0.441175914744214, 0.606952823011823, -0.11465691893630171, 1.163472571100124, 0.006253918526286937, 0.009957370449769977, -0.011361847723237511, -0.010248282647268906, -0.02071417201672558, 0.011078143361415244, -0.00685926704728974, -0.006273137918037007, 1.2472130312195675, 1.2106364508390586, 1.5646765457178065, 0.37700365329926094, 0.47671052058534535, 0.9461853206496085, 1.0566026697710644, 0.7689847754690424, 0.9302031520514099, 1.5587072900762582, 1.4634873710583582, 1.5715062212799478, 0.45134857062775424, 1.165557067909038, 0.8513458512965132, 0.6705361892615487, 1.565270847121593, 1.6207300117537031, 1.9020614798325703, 1.6887898014458878, 2.219765597152943, 1.039361654695003, 1.8815427910502494, 1.300150712588076, 2.0253696960674805, 2.0489442388569103, 2.2242290785897376, 2.8011357660844194, 2.87893335560019, 2.9891971104623187, 3.1059855186780876, 2.130591450761777, 2.305943927490116, 2.3451004525937114, 2.9909177782985203, 3.2450032276982466, 4.8319680976887724, 3.3606432263530843, 2.9223958867071915, 2.5398168871427664, 3.3155727711461758, 2.00515043018241, 3.0171160990461963, 5.098362284525622, 1.3901347572815048, 2.8053386134119593, 2.031652898123789, 3.4975494326182304, 0.003082647481514641, 0.0037872995261768283, -0.019694375864437626, -0.021061330202768937, 0.00504461766164218, 0.021203347197725927, -0.008105018034665366, -0.0008985132734273181, 0.007418686301150621, -1.4917975593178043, 0.5977559993323112, -1.412130867263617, 0.2793059119243026, -0.01185462302330613, -1.1678702499666398, -1.56762149107535, 0.2503017173579798, 1.6835564154303158, 0.4228744441030231, -0.40710175520600844, -0.14047665987590646, 1.1448598648503567, -0.045973235767412635, 1.4225359240443278, -0.1473339151737323, 0.36746044465054123, 0.3861498746421427, 1.5025075488017416, 2.1315424786362613, 0.030818639430520215, 1.6773352676067228, 0.30835931367617014, 0.8730779806290501, 2.1208105284827723, 2.6211316035709333, 2.0800862570045453, 2.501852420346098, 2.1013917204633525, 2.7348597876584915, 2.1067111941767296, 1.2384461436126861, 1.1433252764366335, 2.7764589758052582, 2.544040072464239, 2.563832487407586, 3.518938811925098, 2.595683031527032, 2.8781786518640375, 2.991684883532944, 3.864274431831476, 3.311571228736193, 2.1251346866694387, 3.0633733850188194, 2.698685251356861, 2.2110735392835603, 2.5892256089062236, 1.6843880896895178, 2.8848065841030524, 2.4727943958641716, 2.3237816205824933, 3.7609055530738225, 3.5656970562895642, 3.499724634825392, 1.4750774902495285, -2.2910655258470305, -1.28949729712329, 2.684242337293536, 3.002747151677586, 1.7524057290653112, 2.9031147860927122, 1.7230872346538986, 0.45955978055520924, 1.0000064011986254, -1.3275868798833008, 0.5914368023319392, -0.7929997502517193, 0.5330077442653675, -1.8287313011071058, -1.14860109313146, 1.5003925881341242, -0.8262065012512169, 0.3489152305982344, 0.6074336294509336, 1.4853589924430388, -1.3823363478723905, 0.27390857518551753, -1.976905986797697, -0.6571252136003382, 0.8865230819876596, 0.4319846654435045, 1.6908335429262524, 0.718179154407223, 1.788315578225606, -0.15828613826617577, 0.3506258099667231, 1.216607426061585, 0.05307705641010371, 2.311320723720218, 1.4716522426974492, 1.711983687187469, 1.66507050833013, 2.0595336996080755, 1.1884820696002665, 2.2639244920061055, 2.331500842196104, 0.5878378556976995, 1.5816815725162494, 1.5593771066658926, 2.1599563158442256, 1.4000437180159555, 1.7796615666250595, 1.7097404667891807, 0.7726087457283005, 2.749100756889544, 0.76759745505857, 2.5464068648819684, 1.1947136541839858, 3.2758031580502958, 1.1455045650065225, 3.106830995770164, 0.696200871510456, 0.8256095778072544, 1.3799781990973772, 0.7785776580667717, 1.7988477298028784, 1.059245133962233, 2.6036521735526086, 1.6403354118908253, -1.9314916644792766, 1.5041328332405686, 0.7202585403974984, 1.2918511731192983, -0.5071272151344866, 1.8772059190693937, 0.5688554316856281, 3.633002005741448, -0.7111645483826066, 0.5035328261741013, -0.619044238248955, -0.11914062378569315, 0.21816885275377249, 0.2807409588620291, 3.307473353994163, 1.146975616089381, 0.9417780854410708, 0.086129481576869, -0.11178249183658671, 1.2826815592507743, 0.8135739207572585, 2.1495939605591174, 1.4568208649016656, 3.3853551961633443, 0.7159732512256134, 1.9889442718219081, 1.3227346484058562, 2.2207773604281775, 2.2088555129045897, 2.3136797718243014, 1.9637662290089475, 2.656232455749842, 0.7018476606834352, 1.957508889414922, 2.735780326545751, 3.494509946290428, 2.1290769559737317, 2.922530893487093, 2.3931936272579346, 3.0456833861917993, 2.8622940421246077, 2.7083671569378884, 2.516966554081127, 2.8313788964247095, 3.098261336661779, 3.5580314636139967, 3.3186851640284654, 3.13168671601312, 3.4303087215596313, 3.3304502559978224, 3.4400039512229714, 3.603976394530723, 3.468205639669844, 3.6748838166497713, 3.420173375143837, 3.6891583753489567, 3.8133359646905984, 3.8763118013560787, 3.5114024405484336, 3.7036569859894684, 3.1112255837438045, 3.621369266130126, 3.078680305435723, 2.834524698573888, 3.4819395653661824, 2.8223399904009376, 3.039535721195412, 2.6386841357507254, 2.2993523810058973, 2.4812817500743685, 3.085376263486396, 1.9026522374121468, -1.0210684447232345, 0.861563378922764, 0.6643216239360985, -1.4767362637506514, -0.2020410097595028, 0.8835254531461164, 4.237778923762081, 1.0910426483581237, -1.3304258112458085, -1.0075152395388622, -1.1638959245334393, -0.18392747507423826, -0.7133858869131748, -0.49947594056186634, 1.0335276881354967, 1.6151320627581454, -0.6507774060965843, -1.7734623773996294, 0.5409918277579416, -0.5317488281575056, 0.9612893034785193, 0.08165239975239844, 0.07730465728680551, 2.8150258813313696, -0.4471531543481195, 1.7357044003526434, 1.92835393782851, 1.5575709216960192, 2.4227844351317356, 1.3730313798776426, 1.793766006990567, 2.4523082937207783, 0.2740083499334188, 0.42912789290939385, 2.077557518884224, 2.9709366157299417, 3.04676293569592, 3.649070422241022, 3.1781403909105186, 1.0853325213341087, -0.19372549378315485, 1.1828597254740882, -0.6929918998335169, 2.1704746140549784, 3.535271592520604, 4.349266098986643, 2.9717845741017994, 2.604455498828779, 0.7781410305133304, 3.366813779342906, 2.380886791981227, 2.6897833878042947, 4.168606970187276, 4.1472896021201615, 5.520222796876316, 4.107346957505312, 2.9113109092387863, 2.34396765027271, 1.0933998002904375, 3.723752098930946, 1.2926128032053321, 3.079158622623745, 4.134846876876374, 5.086510315217098, -0.4630503633221233, 1.4997679846699707, -0.17419781714414903, -0.9910304859488969, -1.6143961068194925, -0.9494310856834378, -2.2815172555857512, -2.2097717323837203, 2.13355969142052, 0.051610533433817614, -0.07065957888821314, 0.57981292607476, -0.9757149861029054, -1.066510441867596, -1.1346971127702183, -1.2903284468795444, 1.5372566978658178, 1.0382502847297888, 0.8211524527050298, 0.5950008750654484, -0.6422786685650398, -0.7540235509754386, -1.4944999453321604, -0.933926561937745, 3.435736309960477, 1.899566696558055, 1.2163718479162795, 0.4649095279247944, -0.24315127248478954, -1.2581541040783428, -0.5028186367842405, -0.9955369455593192, 3.9756910839718196, 2.717146400276731, 2.0934715445980574, 0.9496534436837508, -0.2015840610011617, -0.9056530377926566, -1.6907176310654444, -1.2648617046340669, 1.6396373732779785, 3.518505139577549, 1.47091347771105, 1.65118822217219, 0.4271319287825931, -1.1592021652389812, -1.975992084293327, -2.2541657477130816, 2.9170923526795938, 4.488507659131379, 1.155531975483274, -1.7726917896729635, -0.6388922592407794, -2.3541838433144076, -1.715027210525013, -1.166709411594602, 0.2507651317366377, 1.6711263393049596, 0.4736721724989365, 1.7600121643898516, 2.273872457615015, -2.086327248094443, -2.884629824851358, -2.0902055316933317 ],
				[ -0.0026610312233421697, 0.008838883611587524, -0.010562330008430291, -0.01080893830904338, -0.003975711793488953, 0.015996137608306017, 0.01068500083327592, 0.01479277606105116, 3.216840995136048, 3.5464228446160857, 3.827238935274518, 3.265251602211102, 3.409163909018336, 4.0687729470842315, 5.3918725971305195, 2.8194817098113814, 0.3585070857461554, 1.3462294512972544, 5.088282069424278, 3.5064018799166563, 3.3882693836702353, 1.208341608158033, 3.2610987542743834, -0.14364047530733684, 1.1063157004280246, 0.9347128851329807, 1.2287688827452747, 3.9800813803141124, -0.15916476461551687, 2.7243481655771253, 2.112942703910322, 0.9646059389785927, 0.45532252659651345, -0.40191976632317095, 2.3097054955474143, -2.6510938381259974, 3.536967012433031, 1.105493048284999, 1.5185909893550376, -0.03099458439448136, -0.6011790158377193, -0.005196302874349075, -3.466219618602945, 0.3959562103095965, -0.23033622631013154, 1.2176545083786474, 0.03343066111933356, -0.18254023509542067, 0.3875244632637314, -1.1446815475833647, 0.048716236415527345, 0.10165499931021538, 1.1374350243764464, -0.6579992492299688, -0.3558489883300158, 0.020701872933554185, 0.00309272456256671, -0.02017523834791007, 0.003550677924964971, 0.014175541607209281, 0.003901893754994816, -0.0019206132660793203, -0.0063398090758577195, -0.009666654746503911, 1.911650686609675, 1.761178312573402, -2.0288174654927107, 2.0391439961078803, 2.5284187300410297, 2.7101152570369553, 6.489935143718963, 0.48828454378873876, 1.4477095621490117, 2.8857363982183513, 2.352023675140056, 2.775319788090465, 3.3271270930483117, -1.839879121309762, 4.561807370807678, 3.4487413295475045, -0.8483016856214639, 2.670883149251581, 1.418855125295003, 3.090805957149333, 3.144537611685738, 4.885053193709214, 2.732266201254462, 3.205554647347958, -0.5574949541532307, 1.054765709852024, 0.7313769280559943, 3.7015486628174674, 1.735662160261283, 1.8511858311695526, 2.009744842760443, 2.319775518096188, 1.6877816324806636, -0.7813902221412554, 3.4543862428064376, 0.6386622063105548, 2.240936499817917, -0.00465832432370536, 2.5136131747478005, 2.311910183324545, -2.211433187058633, -2.3357385372010984, 1.4293353798652189, -0.948302505629986, 1.9457992963760848, -0.011641754576586899, 1.9578010398816996, 0.7015000851857381, -2.410548890986086, 0.6734032582409232, -2.5472638209787886, 0.8168818420954919, -0.9351620923287663, 0.38502867436268623, -0.530265372958835, 0.4678793959336763, -8.214160530417065, -1.1646992046300342, -3.3111781883608606, -1.495111344780429, -0.04743453401937309, 0.08971773269584807, 0.6370116393513966, -2.4515972164835413, -1.1208093664507546, 4.998149545713955, -1.3145916280787076, 4.721919021861378, -3.9983467565381394, 2.5023870457977955, -7.360913403382548, 0.7024270181900361, 0.4071536366921655, -1.247066187503265, 1.663249055527152, -2.035330186770617, 3.1108978464982044, -0.6164722325697853, 1.679488718451602, -0.4755327686579614, -3.172818146240731, 3.810543503191562, -4.105109860950395, 2.7605354164859177, 0.9472566024081265, 3.839926561529692, -0.9222334570561903, 3.3589243080857054, 1.1382857842083582, -2.398325661173554, 2.898669900764333, 1.5020434600283652, 2.426268040854919, -1.652328674035596, 2.678239651018083, -1.5038754992870924, -4.8684957596559855, 3.4630406784869225, 0.5137928916303076, 0.7251564114871686, -0.11091059890754394, 3.1354224286863492, -3.307719031638931, 0.990390670578204, 2.3979366469385015, -2.046669581676775, 4.196577829877938, -2.111947744027012, 2.5358838606161256, -3.3015270714445646, 2.189569393872054, -1.2103407819656573, -8.491530318888431, 3.5021197977842715, -3.655102869896018, 3.1599398573349213, -2.8253208168769706, -0.06024032173083717, -3.98097705052181, 3.7133009221756614, 3.1994602989509766, -3.6706072081345926, 1.6528015994063563, -2.8042053642868408, 1.7225915116034705, -3.2054608189433296, -0.7131620618662207, -2.5571392997753706, 1.7746457999026473, 3.678839872431204, 1.7403976608508045, 3.2072278740444085, 3.637030343046972, 2.8299328427864867, 3.0703807502101674, 3.1893427093493085, 1.9996115590788455, 2.116349368333918, 1.6125573950986996, 2.4850785262535573, 3.017645486826904, 3.801192389173827, 3.1969234163599727, 2.8233750865726424, 2.5187789144763197, 2.803452515462346, 2.2218814187173406, 1.7592681710952573, 2.6569572051098276, 2.2401306796185008, 3.0103640345053675, 2.2876478446219854, 1.9721469623707502, 2.4402782720496545, 2.085627320082262, 3.2357369508277762, 2.906413711681664, 1.993277221083289, 3.20692809036576, 2.746196637690217, 1.1621062562467672, 0.982854148224955, 1.1022650014552158, 0.3284300646331494, 3.11536781580604, 0.7827653611511922, 1.580957608526384, 0.07869414752876329, 0.7150891622682856, -0.39056447363780056, -1.2278559458438167, 1.1577143835584354, -0.3326049423515775, 1.7234150791865033, 0.17695401094519456, 1.856176613776156, 0.17884983789519499, -1.926600668374159, -0.17381403130067177, 1.1683461205845824, -0.6388191503003697, 0.7347641408696077, 1.2028923036052408, 1.0932781429057803, -0.7697360751104785, -0.14247651297744723, -0.11409114266072304, -0.15464105289260469, -0.39467119723888294, 0.4204186952895814, 1.3809555195760979, -0.6615130969275721, 4.986553999182225, 0.20035032165273206, 5.267280994043408, 2.9174968475001823, 0.34521049588264363, 2.7531288785611365, 3.42870791360743, 2.6350663666146508, 3.230670794956174, -0.06321843475524504, 2.4912100181248893, -1.175375299483634, 1.6078292829898813, 2.525754563269416, 7.42696692142966, 1.9416226414625835, 2.7608083075228893, 3.408245489253223, 1.3491776512542886, 3.8330527136055923, 4.848592475484867, -1.10914194643751, 3.8160738174089963, 2.4627112674078395, 1.522313205395153, 2.4032894324100114, 0.2733109970837238, 5.287635110574559, 3.530033559728277, 3.9720188790681483, 0.7220896193035564, 3.8912474645372273, 3.089587025234533, 3.4054228827308126, 1.1860439431125704, 1.2609101940494962, 3.5449333792223214, 4.319091826668478, 2.628432264490029, 1.3748220485332503, 2.2931012288973904, 2.0124420070132287, 1.8100843826332504, 0.25140212612676743, 1.018844228408322, 1.6432415013875454, 1.3184017089762905, 3.725105419466942, -0.43678003018995804, 2.2271137380546047, 1.2093773818274272, 1.2876551736913766, 1.3982675078732973, 1.1228384075341173, -1.5638436963611464, 1.6624187079664081, 2.079737020004735, 3.649936057688326, 0.14558537241124878, 1.3723335676311075, 1.8275118513038728, 1.7409648333708299, 5.048479932604187, 1.493792203521595, -4.778252881770003, -0.9194113558414547, -3.869101794946015, -5.030444818895713, -0.2680420495282773, -0.5124945166540639, -2.4298438103936113, -1.3814599838949035, 0.596049947890584, -1.1145742992605863, -2.3100612839022547, 1.4161118456120307, 0.29873156544324553, 2.0384598108151435, 1.8530982009338104, 1.6932338044389852, 2.6550278718047537, 0.8819945917994854, 1.706825113737647, -0.5208864543239932, 0.4511790903506182, 0.599283948453319, 2.1397289898382548, -0.17371897318359086, -4.124355496291141, 0.72655069805937, 0.6435398478900074, 2.4777150663514855, -0.16447748352515684, 1.0994939855450345, 0.46424339581559704, 0.7840684880048734, 1.5994420320465121, -0.5724675090434463, 0.9713753594890014, -0.4764455058468431, 1.5751277645903488, 0.6971158238989653, 1.871141829898916, -0.3446305339201717, -2.9354299214474584, -2.6573016448819047, -0.27293301753621174, -1.1688369811915469, -0.38451313180062363, 0.47531063851727245, -0.4546228882075784, 1.0458368788506862, -2.2094932762687587, -1.9827720131372535, -0.6023676097664018, -0.43699173811493236, -0.8635523036643638, -1.4063853769356527, -0.9955389796768846, -1.6970080460641208, -3.9041177168265144, -3.1303134918972724, -1.7725641597577284, -0.49054128194460783, -1.5737516441608563, -1.7254859552990969, -2.426725820210064, -1.4834844073345035, 0.002415410353673559, 0.011792369122780701, -0.017709128796595856, 0.018198261084191467, 0.011269250881238656, 0.016934667154598616, -0.020283117310379076, -0.010930875788025462, 0.8095678453332693, -0.11873907984675326, -1.2933451420858326, 1.4161257415865989, 0.5792168415975807, 1.0833431899918458, 0.2713744771845485, -0.8224839436218989, 0.42492320131820666, 0.6565967469183164, 1.2074521301893537, 1.3851795108092204, 0.849695823614415, -0.5867204737350389, 0.6342536804886626, 0.17192531211161804, 1.4613951485853602, 0.6773543578186144, 2.7919930803257813, 0.6821768439737853, 1.5753816227124804, -0.2558937574447387, 1.2296788661332854, -0.12006827654238476, 1.069889874758884, 1.7079345765931464, 1.5006167814901488, 0.8125330712385653, 2.631893877033203, 1.5371884923331656, 0.5051223483186082, 1.03789608002657, 2.555853074678388, 1.2222294714215678, 0.5943349306905003, -0.07679498410737816, 1.2390026443556479, 1.7349113339423137, 2.3052458724548663, 0.7896820106042018, 0.8888698432967249, -2.959753403875775, 0.43939898741334155, -0.6695888064954095, 3.650454231904012, -2.0040239605829875, -2.688367910593623, -2.869235093794619, 0.010620798360301902, -0.017646823717697938, -0.003185309696931431, 0.018756764956668077, -0.017070077135495767, -0.01740460933973981, -0.014397783617084716, -0.013327527483896932, -0.06506956557345697, 1.4295798673737385, 1.947742062086062, -0.383679064408068, 0.1950726075699897, -0.40837698691985613, -3.1167561708922156, -1.1561340263012365, 1.9687338012892506, 0.39811855378057565, -0.4362913625517955, -0.9302117976616924, -0.25366051677512225, -1.9290343383162984, 0.7005802190815497, -1.168435051920943, -2.6567716656146705, 0.09877739891089221, -4.152915960454387, -0.2172609084142703, -2.787508350379783, -0.3133412272974454, -1.4305721848020787, -1.4725459841869009, 1.741334318701943, -0.2593835125441456, -2.1944730337891327, 0.06244382583957454, -3.0434020712330905, -2.6251188233644247, -0.26824874110924923, -1.5810307329946585, 1.097896765533375, -1.4074435194131316, 2.1241314281669355, -3.129455996393727, -0.4451178143124229, -1.2006143506704838, -2.5924063544014, 1.6672166728806836, 0.640927632988821, 0.7933213779341582, -0.017169667200927136, -2.1840504872838227, -3.38336905716729, 0.9048119992863505, -6.083801070634633, -2.9068958586439817, 0.7952377772520064, -2.4861429688939123, 1.2133173110516389, -1.735172439513263, -3.280707545615148, -2.1924137398708905, -4.385522756229969, 1.5620103637626905, 1.8875325877056066, 0.1579738096268011, -7.4266641226115055, 1.6760534359974393, -2.1353601216323708, 1.339922096706756, 0.4241548757013623, -1.577326214962099, -1.8106437297646212, -0.3576728521194108, -0.865970325237716, 1.9110355738177092, 1.0083480710720854, 0.9257503167021081, 0.007826552104223283, -1.200502751323314, 0.4815730737661332, -0.4782287994954828, 0.1949288424811793, -1.8116277455080967, 0.45625457645748646, -0.6918504970005103, -0.2851715461623414, 1.7293050343948002, -0.028656627888150012, 1.7319917361621682, -2.072756486874844, 0.3329926554861437, -0.5737769295607418, 0.17123330610684656, -0.3572659115811091, 0.8590370424308782, 2.7686369814561536, -1.699803561872652, -1.922088022256552, -0.08405061804354833, -1.9884337563025338, 0.16344578247515756, -0.03509144015927778, 1.1940070347291505, -0.3042207667990559, 0.3392668188417847, -0.3657623813211661, -2.8463460936938385, -0.5464520294336473, -0.7110053227319816, -1.1875269077604238, 1.5475065386049425, -0.2354879929044998, -1.665269531539139, -0.4585126748466023, -1.325245687472769, 1.637787187458531, -1.216406022108775, -0.9493053437812171, 0.4490864245324261, -1.8448221402046845, -0.77463018257603, -0.8992757201224454, 0.8109735802932804, -0.279752563712431, 0.19514431881661187, -0.6955025209904546, -1.964138435074337, -0.2850486776698518, -5.118502699302597, 2.8231764103083465, -4.814409471518869, 1.3170552509157447, -0.20987386623082013, -1.243760377642193, -1.1693950329075027, 0.29726182458159767, 1.891970358109591, 0.07062296581959937, 0.7207409085775223, 0.4007381238854066, -0.01834923528603473, 0.11694441658818149, 0.12711477822046705, 0.6395462501229129, 1.9827719813540947, 0.6851430469433625, 0.8437195574290087, -0.041889844026098084, 0.9191138905148878, 1.3858280482601326, 0.5199920821485531, 0.5369563896167393, 1.6373823035823432, -0.37421936796105904, 0.2509387729189242, -0.02844726826492478, -0.048799020180566796, 0.5359210012231246, -0.06016392730673942, 1.8802719583105305, 0.3829604085832756, 2.110552389763, -0.23972037827346235, 0.4188126302549666, 1.1910344562927127, 0.7587281331192193, 0.08661718180977862, 1.4604793689046531, 1.3000891491939344, 0.9548046993902792, -0.022582695606827238, -0.48808764564645846, 0.6944531260709118, 1.8390572854208647, 0.6140475405824419, 0.38005982166609176, 1.066831286449957, 0.4380116445308346, 1.1945792442713372, 0.32115314589315924, 0.924014609817895, -0.44852478172716453, -0.7481375162148574, 0.2946410008546214, 0.4242101038835498, 0.029132900711315465, 1.4370553615753408, -1.0039471627198622, -1.5001108935222476, 1.1024668341600887, -0.5825085204336559, -0.15894415082187163, 1.1695293727073464, 0.10925947046798937, 0.0836240056763715, 0.5105962347741342, 0.3330235751683273, 0.5677395845582344, 0.5335592103074477, 0.3006864951584636, 0.5966983126080295, 0.5185668372817077, -0.9032346662387666, -0.6680561489736562, 1.6176367236595595, 2.581541761475864, -2.71679544371093, -1.0967603629717153, -0.5254904705699367, 0.18242941030716767, -0.6238351690892208, -0.4582380796118502, 0.23382827150909452, -0.7867710066949998, 0.2091087351119613, -0.15557973334334207, 0.8178701579822146, 0.23463520428549334, -0.39557835701861516, -1.0998596891184997, -0.2893235481185578, -1.0464556114626822, -0.6425053202628132, 0.5564934550877112, -1.5085434908120632, -1.8102166608176928, 0.5958020326071779, -1.1777419385807617, -2.5434798372796155, -0.5414580944555457, 0.2594416707692718, -0.4951739785808378, -1.4423523851570106, 0.7343303268586076, -2.283607319027133, -2.2307102152914795, -5.305270000015604, -1.1569183305126525, -4.082848804155103, -0.4410345058475028, -1.3714973359981968, -3.418872692928693, -0.458854569647648, -3.40681269803829, -6.368555708091212, -3.532709258154316, -0.5884040538080947, -1.4681103480673119, -1.916929973471301, -1.2715488590298691, -1.0467541417944966, -4.595459958652896, -5.084515480478023, 0.42472961052046637, 0.10217529767025, -1.7675830847733607, -3.5373648777017714, -0.5349616691162847, -4.725211055792268, -7.227551557800457, 1.347264657554405, -3.004044313083803, -1.9400860635912562, -3.328533490138183, 0.35112954914493766, 0.1333442693852454, 0.6417958859843894, -0.6865829063961135, 0.17971536058176663, -0.9155164763278695, 0.6658742350765262, -3.0844056457820104, -0.06617926854255039, -0.40918826388809026, 0.119676916585465, 0.34810204354293084, -0.6264124258118351, -0.8079754200944876, -0.5801024822106061, -0.9721741072388368, -2.8007423491292527, -3.4048131534227255, -0.8905865398668786, -2.7030165596249898, -0.9011277848475708, -1.1214586469966914, 0.32329168117218243, -0.30304029881656336, -5.276659134006288, -3.47327452610089, -10.525686495398126, -4.055731854774469, -1.7578888369990409, -2.2928189438597637, -1.5086293586586903, -1.9153731617295462, -2.1655954873507146, -5.820278237558553, -4.9571779512900775, -3.1404748406490373, -3.4729330670188356, -3.553924492631883, -1.0927396837250924, -5.958948327110125, -4.42039741215393, -9.709143901339326, -3.556940618686868, -5.059461558789787, -3.1699502316164647, -4.429339578361352, -1.2362094241062147, 1.5244801324996107, 0.8782219345045996, -7.120611487060404, -4.852208131657661, -2.0513053522733267, -5.633903959228883, -0.5047975279003372, 2.432544317233929, -3.1827722193169556, 3.5986022802119697, 2.847435933562733, -3.725297465984857, -0.5183570083122536, -0.9591224579196908, -4.707666293098661, -1.2787296920039244 ],
				[ 0.0031243297515674744, -0.01829207366953183, 0.009197379698922125, 0.01761593797164054, -0.01141812295957678, -0.00873904538341216, 0.017029754683598335, 0.019545031424011646, -0.7543262876903188, -1.4319938398812868, -0.4279476966014339, -0.5056325599826076, -1.710241730611782, -1.6766648088911131, -1.355394964259211, -3.664198316367533, -0.7327804062902008, 1.449756588223135, 0.6994555648629239, -0.4913696165593303, -0.2670036477807854, -1.1522802833572707, 1.3494869070893316, -1.4338637339554545, -0.3235821039365658, 0.29361109582794914, 1.6484026176121296, -0.9419873613454021, -1.916901669190225, -2.0966480521404836, -0.336874749859334, -0.5067510029517253, -1.343002005557303, 0.28470735867755526, -0.22243656367944253, -0.15751123478519355, -0.7373006581441393, -0.5711913797713578, -0.7264583867949161, -0.11365447186143736, -0.8760354810444084, -1.0704982351551395, -1.7128281733324797, -0.5835867645727412, -0.2941607205714601, -0.2436437885957363, -0.7513158305246983, 0.47884510099655997, -0.5572530796900131, -1.6182293182336436, -2.300909687220197, -1.5035442732923743, 0.0928311736281356, -0.06473681500239893, -0.5407041087507315, -0.601318222971672, 0.010307881262364267, 0.0012551336023505838, 0.0056268013670060305, 0.015281223445523863, 0.0036081341772696658, 0.011583075948411257, 0.015606561983650583, -0.00430776063466987, 2.0710135555095217, 1.510253761930569, 2.411179770485023, -0.39514424264395165, 1.7322580040290168, 2.035234058493692, 0.9017563637009058, -0.35338884177471624, -1.4298129595158167, 0.15173359691428298, 0.847197376134585, 0.018128414631040597, 0.30893377755095386, 0.05285825206557391, 1.7814728236239263, 1.683999538747388, 0.620795762241025, -0.8143079920673073, -0.9367767877798094, 0.8264917769011858, -1.0197652074848846, -0.9031246716700031, 1.8114192656129953, 1.3855013502768674, -0.5308248120188767, -0.8027625084893569, -0.08781905290480986, -0.9021731857258402, 1.1338032060294563, 0.3210182939650025, 1.045724140119422, 2.9320860193459573, -2.8474335640624906, -2.29702941829258, -0.19432433664788432, 0.538589177135859, -0.06737311904672677, 2.546113494940648, 1.2054265296499063, 0.417252648816043, 0.7758705743616907, 0.21133719747580396, 0.49795644128764943, 1.1014682764488022, 0.2715758494656889, 0.2992858637329514, -0.38376001147284505, -0.27276281920636297, 0.4453611683701348, -3.3397185327383316, -0.41962424370197965, 0.42815826836358173, -0.009355078137619486, -0.17546816455676353, -0.9590709946995465, 0.2867371683027356, 0.9935050303366253, -2.9099521621782922, 3.131632160156033, 2.6499887169778296, -0.42250243701602197, -0.8352590672361927, 0.04164052601753903, -3.1800910283087096, 4.626809151256489, 0.6400021564185111, 2.8415253104872247, 1.360175098729543, 2.274985875408318, 1.0552232944769062, -0.4089467740580997, 0.5209082800408441, -0.7691015958933597, 2.8438162656648376, -0.3437022046306882, -0.7266431893906637, 0.32132017022239795, 1.3257886220390067, 2.150594700534526, 0.008382535479988577, 3.4469329352757465, 1.0980575410748523, 0.0440900253048769, 1.0369822257691736, -0.9970129606772145, -0.8730439007345804, 2.6345559656805677, 1.43555586668923, -0.5275766310216791, -0.912128906788638, -0.4076388595481952, 0.0832353368562545, 0.6898986455747522, 2.2016145562012106, 2.488819265768762, 1.2237337584126944, 3.388536912579539, -0.17680334094692002, -0.21072107109028015, 0.548016347221541, 2.7223952771261137, 1.3920339437823122, 2.219776941805789, 1.461243246937261, -1.564534841545848, 0.3720879315884798, -1.6616794320652968, 1.5516818289070244, 0.867614092023623, 2.331677995750597, 0.31045540367307367, 0.06290609619621941, 1.1259950624398103, -1.5925294303790394, -0.06911656031885408, 0.7954882151812389, 1.3574867003511488, 0.5442200835902388, 2.0066152500858006, -1.0354976929451014, -2.808739444343186, 0.29566256379899525, -0.6891656724019838, 1.5314185426184819, 1.9360676929261698, 1.135143557176534, 1.7200945532854066, -2.8195494756556583, -0.5233614668761528, 1.1518473381035998, 2.0042276031665485, 2.732605582018132, 1.443405740936554, 1.8935485015230864, 0.3508634459810011, 1.465185487942679, -0.19003871414549164, 0.16310997272941966, -0.2926524994368682, -0.6466637131861332, 2.3046368729037443, -0.06633802261620986, 0.8994667722379287, 0.449342336989207, -0.8752751614665342, -0.6376333313358998, -1.2699863640077633, 0.072847021195466, -0.7967885077432709, 0.5806305080750048, -0.5487607409824327, 2.4591508484072446, 0.4005075283063024, 0.22374993426059814, 1.049205996890891, 1.9755528730917606, 2.190351746419599, -0.14823417394434468, 1.2011791187770902, 1.6460745928073952, -0.02280163496546719, 1.2985847538346045, -0.015198434476419094, 1.5923672560482687, 2.7451389074744474, 3.079917237010705, -0.3318171401905125, 1.5802646989873916, 2.5229074441512203, 2.5606261858548764, 1.0781781944887774, 0.34445405561146397, 0.7967920558535941, 2.541979232690851, 0.8665290595058672, 1.0187862956635967, 3.6139977097392153, 1.8145712818908524, 1.1608400622043884, 2.2155750822581797, 0.5028297939528986, 1.7543283106896663, 2.539850055654917, 0.44731593155610894, 1.5982534552151069, 2.404274542183069, 2.0517830594725397, 0.8645412476316852, 0.4182726779413721, 0.7479691680493742, 0.8547225346810438, -1.983953366406457, 3.8224081387089903, 1.6698719990411077, -1.6512409528615806, -1.3003258709874994, 1.502435896215045, 1.1362768201500317, -0.22840350151324773, -3.968242785014025, 1.9234364916972122, 0.007060224776624762, 0.2733611864902383, -0.06610396573824429, 1.8870838100668457, 1.910977928472147, 1.5074237239708022, 2.561646508813942, 1.753061013740791, 1.177748976783732, 2.345961955873498, 0.762313214234014, 4.334364412140509, 0.4605942579094572, 0.6472139118669304, 3.7319585829340496, 0.8143448378354134, 1.3234354378041766, 1.3100293695578595, -0.6110104267408315, 0.20439250096770986, 1.3869651395013747, 0.697529888418269, 1.7851716540164495, 2.84353484851329, 1.7488991902871853, 0.42014856023738023, -0.3934173860191169, 2.3725464215280923, 2.150679207008405, 1.3852746389468684, 1.0004578685245122, 1.6880116139930477, 1.3968015656986734, 0.5833289691443205, 0.9764663168437286, 1.5051968301376726, 1.6995954999989444, 2.4237518244094454, 3.2342282798249915, 1.9783964253162498, -0.16409088800795796, 1.3918539515743853, -0.17903270010847136, 0.5539262259036533, 0.6013378196576359, -0.3562147717995406, 1.0590374316706679, 1.0990048496214184, 0.5446265511117697, 0.38697334410249057, 0.5086878302500125, -1.0594287141387417, 0.7744531577140835, -0.7287127353927655, 2.4105342527819094, -6.489361383779902, -6.881939296791425, -9.898482643143977, -6.923216554598873, -5.781467347557849, -0.46401015205983703, -3.5464063921657716, 1.3748561100110337, -10.180717725407815, -13.29482414154147, -11.446118331798631, -6.971326401697013, -5.76853027510957, -0.5063505798086758, 0.8529381542505247, -0.08712149107177468, -14.276688955513915, -11.310638324330577, -13.250268089337148, -6.338203813494039, -2.495486454174802, -0.5590476922054836, 1.1638400732810497, 1.726333797061642, -8.479294407072102, -6.791507831366576, -8.612861945245903, -4.808851040853266, -1.4954298105472799, 1.8606065045796436, 2.889111731489383, 3.240613276219209, -7.934142651713069, -6.199256847862134, -3.444548395849411, -1.7783675757579753, -0.3024769127633574, 1.348023058068912, 2.7452484379976028, 1.784921114720611, -6.424893655576228, -4.432624967516237, -3.382417824159616, -1.793663894714235, -0.5363273311176575, 1.082731556770779, 1.4278150581546347, 2.329141635091886, -3.4278745214267436, -4.012279144616193, -1.099088814071989, -0.8465354726392154, -0.3801960423552414, 0.593762185574499, 1.736971144281067, 1.9260175985239154, -4.30794595670688, -3.630623883026841, -4.305864950824673, -0.782289727047783, 0.20639207569247844, 2.6892104864885007, 2.0962295276879295, 2.8282910836535615, -0.017938562786988094, -0.015032797400975649, 0.0009253396813522959, 0.0018844741504728353, -0.010199565709126812, 0.004726475762438427, 0.005335715649189552, 0.007769825977927527, -2.4610920682607906, -3.7206154413098806, -1.5973426939132291, -2.228606332429187, -0.8219914598486455, 0.987073463015431, 1.899890273073525, 2.7585299244253716, -2.902295100849913, -4.573521264132246, -3.3260499477470455, -0.24957742479578038, 0.1470759320935551, 1.5494514852854848, 1.689426525454799, 2.244143821810054, -2.454119668381423, -2.9490320366715435, -2.0133325580373027, -0.5921413181254097, 0.6867261006844808, 1.0147136374130952, 3.5239155158707565, 3.1226485826866037, -2.450222844652438, -1.7646549448655175, -1.639976234690688, 1.6654103232778792, 1.5265296074088648, 4.3068157761949495, 3.73130427046885, 5.264614345327436, -4.927392684686058, -3.290886611141088, -0.15221902451801045, 1.0399602755988056, 3.0128816501892226, 3.121568763180931, 5.770939714567292, 4.924519626832609, -4.478075493042795, 2.901434399637096, -0.6098350228194664, 5.198379737045608, 3.019861178976866, 3.1485407234583693, 0.10529968516302327, 8.132111281893165, -0.00016576880038721828, 0.002797889978127877, -0.012708851789314463, 0.015458100233758907, 0.012080029794835278, -0.01038017681187353, -0.013538033625291778, 0.0032052987130822973, 2.955068473374581, 1.0792033827499776, -0.30608155468822956, -0.27599198522015866, -1.349212955588009, -0.39705199910189914, 2.199257482991612, 1.578247642710491, 1.3838916579079137, 1.1610799624371126, -2.047628699042083, -0.779267845743097, -1.3747745430040001, -1.2292630302814453, 0.11890523497516893, 0.6572763119846463, 0.736631535338965, -0.7203831163262149, -0.6629258189895965, 1.0761038492453536, -0.3535454529958472, -1.357596922885137, -1.196970219288869, 0.3684796190193159, 0.6020023797472561, -0.14335395077392082, -0.5431073957744641, 0.07239365198505128, -0.43952991993819523, -1.5268187897204293, -0.359908025345116, -1.3664480091643565, 0.8516694186720798, 0.22933059747813317, 0.6362585087141032, 0.013710691525774192, -0.7799876087696246, -1.2399911366618843, -1.6588962040184905, -1.0753190524798812, 0.6044184914715415, -0.4735280797961271, -0.28717998395541944, -0.45054711170987566, -1.8079789068847916, -0.931452570200231, -2.3469011207589685, -1.4329569893603846, -2.620268925373026, -0.38333246538025983, -0.7946407187768281, -0.030704109615489063, 0.825149793840655, 0.03070533402140522, 0.1870757221037043, -0.6979374527407658, 0.9143571241038524, 0.8720146813700625, 1.4192179641158258, -3.001104608245284, -1.5857544211699643, -4.357240028877383, -1.6132469970639673, 6.01252934220802, -0.6359450444287684, 0.2720811029735326, -2.413304418191147, -1.9402709056934966, -1.765168210881019, 1.4936984615971995, -1.0166151261922796, 1.3701515813485352, -1.4301703009354496, -3.2179345227390237, -2.5942464585749816, -2.037789449078682, -0.6347617124884919, -1.4527970133623682, 0.4730559930295434, 1.3154073185428892, -1.5305416477102451, -2.732667759543766, -2.921410767012882, 0.05938826571961803, -0.4974934270443907, -0.37739109127917647, 1.4943903581705607, 1.3139681931526763, -0.07932909373441153, -2.644900543627292, -0.13046332899342272, -1.3091112739811437, -1.030541036662446, -0.623571958403324, -1.1887019484280632, -0.2450005814106541, -2.3444966309398336, 0.3177290971717575, -0.7059309470249965, -0.8073045562258411, -2.051919165743265, -2.2068953095158643, -2.1378597670731456, -1.7581917193909617, -1.0679208449058868, -1.5556570996302432, -1.1853938416887655, -1.1688136241316378, -1.774532636314034, -3.1872554333043217, -5.257111719012142, -2.120230659864172, -2.726519832920612, -0.9665594229117245, -1.4784391716430918, -2.7322824898962192, -3.025820852909412, -1.9711490224051718, -3.9840411161304994, -1.031950120473129, -2.622179056620128, -1.2957303535552682, -0.7773532510877498, -1.517474484671996, -0.7867578491010067, -5.298835621119349, 0.164955143292081, 0.2558175155278003, -1.5215305034267932, -0.926698444960428, -1.168877298402692, -0.881790871483193, -1.249168432945738, -1.5759504340602015, 0.6322585594732241, 1.2038445944065417, -1.224115347978526, -0.007954377529133328, -0.7354620104244884, -1.3674173033619181, -0.8859799684638168, -0.03197985305185486, 0.16645082721467108, -1.4927800527117894, -2.059564391913774, -1.0389877185778271, -1.2254286529055713, -0.6403165207968351, -1.2876296912869116, -0.4527260637231484, -1.5819452057027938, -0.981322175102241, -1.5057097182229262, -0.9793415516657555, -0.44919019878164335, -1.383047957807047, -0.9375328107442639, -1.3936462168213672, -0.8508802257717614, -0.2786548656175891, -1.3644652340115966, -0.516766672472397, -1.1919709726659962, -0.6206429785042412, -0.5860059234539733, -1.1210665599957328, 0.26824905847286973, -1.1620403025718036, -0.8271947382678312, 0.26446405533772105, -0.46047591807990707, -0.4324856872230519, -0.6343925106222774, -1.7383533550601877, -1.54809116769094, -1.9782482335778766, -1.737775733343962, -0.18942425831046822, -0.5339996210211262, -1.8106366080626797, -1.367521533206342, -0.19866970068497114, -1.8003253633305767, -2.327201393747021, -2.3045955984364856, -1.7951165402843767, -3.6060065051691694, -2.7918818235975515, -1.7804617481072949, -0.47329971792332337, -0.8602490740183472, -1.178092574660997, 0.0971149261480659, -0.6724520597384495, 0.3630142134745702, -2.5370954898444267, 0.3458453311450025, 0.046924712936525524, -0.7706792983104894, -4.43546888620813, 0.09056077370978018, 0.34036246244919727, -0.7406499537878551, -0.0485148849957692, -0.5512675523638292, -0.5311482059466149, -0.03580123259214555, -3.0142400350095624, 0.778413906220623, -2.2727381074920605, 0.6948625225968355, -0.32219905929162374, 0.22534925653260351, -1.3889405080188606, -0.05318186585792956, -2.1308355694778505, -1.164458727899257, -0.3273086743307218, -0.5282050397010543, -0.7407395409099745, -1.6444830719040229, -1.366368393169242, -1.3146605059234053, -3.2165672520253366, -0.7501869547423955, -0.5065629268362585, -0.9209940674086433, -3.76097839444714, -1.0885140214797115, -5.260178234725982, -4.928145768277644, -5.878417870964453, -0.4874416456827039, -1.9104788061660078, -1.536588565401405, -1.7519234426561057, -1.0496937358951386, -4.7696948338949, -3.8546143751459896, -5.416951252089291, 0.3245035947024568, -0.07067558111757091, -3.151941379179119, -3.171033743633056, -3.2248488323325835, -9.4723556845761, -1.0692051390124004, -4.0427678614449345, -2.2591708974552676, -0.7460226672694684, -1.2686601535107815, -2.8549796172378614, -5.944659641841682, -6.146701388945792, -1.2510224898205855, -1.5077588002276476, 3.3730966638706152, 4.630241061582584, 4.225657417495225, 2.0929873566305814, -1.1700573889062782, -0.9844261200843996, -1.8936011575242053, -1.1843851730184618, 0.9146993972593558, 2.511919341313723, 2.026461102637823, 1.5395418556993206, -0.13172524345031056, -1.6408772797058246, -2.19896908128676, -2.1139403255832656, 1.6160840716654272, 2.727555010077634, 0.46777948476890685, 0.41839372198721925, -0.24962505365435728, -1.969107366362411, -1.4037453690483475, -1.2306079385794324, 4.313081922564437, 1.1930857373681425, 1.642465104083993, 0.921538766845171, 0.4317453594423825, -0.15469442336961986, 0.9625177194188245, -1.2858396621303825, 1.7693932405228001, 2.6443954509921435, 2.623261667196862, 4.102213421933424, 1.2835506619371204, 0.7641397814217933, 0.24729899980550388, 0.18291394219523485, -1.0131232947594897, 0.3071339265151949, 3.339303715596191, 1.9229219808632687, 0.14977516543230804, -0.1335249856705126, -0.8938377826185925, 0.4817423924640587, 0.3958892584214941, 2.483953822925273, 3.453116435878389, 2.9335366530952083, 0.04737286696302518, -1.2492395554021078, -2.14715407892044, 0.887207593377674, 4.587574839741659, 3.320061660080777, 1.5740234435376501, 1.4644560090927787, 1.7015366827968645, -4.305636657022323, -3.837869136023094, 0.3563381275881462 ],
				[ -0.020438788448832474, 0.012334087920390334, 0.009671348990939903, -0.01785073142337476, -0.0021504271356269926, 0.018798775621480048, 0.0016237900937398598, 0.00038354773348405, -2.712835891048157, -4.533582128382473, -2.789310386077869, -0.823331147627357, -3.6395198013173533, -0.8542641042898498, 0.7528910337306467, -1.5658395325831194, 1.4481353773455268, -0.5077838235614968, -0.9141344641170884, -1.1733242335668683, 0.7410758382368813, 0.13429245272289547, -0.5900230070528923, -0.3365769338175273, 0.6335954441168299, -0.8691592900448586, 0.20136631718147666, 0.31936141479810315, 1.935920686479101, -0.1874845647279774, 0.38326820366293923, -0.5769121640241949, -0.605402025385089, -1.4062142992178175, 0.7715254758707755, 0.1254889382185208, 0.9559649420477397, 0.505798097298749, 0.1707421795488042, -0.025328298631662596, -1.4161703264194527, -2.227603963078021, -0.03977460536251585, -1.0431149015947563, 1.1097133797462673, 0.3554088639374907, 1.9732065355758053, 1.6643911340120658, -1.960126842359574, -1.891147674603198, -1.163669613727836, -1.8055188120704837, -0.28483101265799243, 0.2947300049880573, 0.9651348591385635, 0.4230045688987448, -0.007733738532757446, 0.017478907310857425, 0.005355395364744377, -0.004868169547413695, 0.013236979563120447, 0.010829968492532824, -0.004248851264503161, 0.011267914679877249, -0.08520816645119632, -2.6152034641429447, -0.34656485947211063, -3.375088456832075, -2.26909267172796, 0.12205265975601808, -5.14116142018605, -4.118163695857233, -6.242255957668192, -3.3484283804799433, -1.725948377152838, -4.730824021432813, -1.913989102276902, -1.7961045907471274, 1.9517513217659197, -4.25240613414323, 1.534612500504576, -1.5505084125662998, -2.0183370062944013, -2.5476033190744936, -0.03724624665164228, -1.3011678319543825, 2.703534663210151, -2.2947119549949244, -0.3689154913396423, -4.320318264407708, -1.264275803685151, -1.1569022190724942, -1.046898790705119, 0.24830568379301896, -0.3548741837166077, 0.5842455887979158, -2.1162694708858036, -3.874231242241309, -3.090726824291153, -0.45457310264345274, -0.6227027432552603, -0.1563587918401109, -0.7444947303808692, 0.21080735008137297, -2.1484516468939434, -1.5953620561246074, -1.0249459413769075, -0.29165264582105777, 0.022431955167074743, 0.15429461748841394, 0.30935929170102383, 1.8502522873162157, -1.14169518530465, -1.13378448186054, -0.8817078304479466, -1.0338408078254095, -0.19018844127792625, -0.8306616127887012, 0.534491539178041, -1.2133154029739996, -0.05478822025965497, -2.1626372127340785, -4.177766352293504, 0.049870230410451216, 0.1755927721931394, 0.43507511136453614, 0.5255661299138858, 2.615599904012606, -0.2328924745575007, -2.309950973478751, -0.7606272164229114, 0.005980394504502181, -0.6512142409993354, 1.1311149763328285, -5.92661687060739, -3.1568850932609354, -1.439055206661991, -0.9288890391659964, -1.96003262806167, -1.519158923919337, -1.3326762762903823, -3.921389876614008, -1.4734172617861387, -1.1863341580437174, -0.6905393974656086, -0.9108235486768094, -1.1809235990308884, -0.7305049343890111, -1.641664063877125, -1.403932630491752, -0.854916809326577, 0.0858201088622618, -1.709786266590203, -3.1863507931820974, -0.7714898791236982, -1.2497474409448668, -0.16070766631034505, -2.2226490761687736, -0.5930852126494752, 0.5930890841371023, -1.4711129448558196, -2.8198167897279798, -1.952353218797826, -0.4469225288991879, 1.3010161893113423, 0.7393037993840305, 0.6408942876550584, 1.0945705655489844, -0.7946837623587014, -1.0814725702733534, -0.3134712253676273, -0.4813995258101092, -0.3783875082622879, 0.30818545186113727, 1.7086505926603797, 0.00773981926659818, 0.9735147294738359, -0.3493625020731465, -1.4240225920061809, -0.9215566875694408, -0.1082044250892528, 0.8862695175958147, 1.2694309631294753, 1.493713447789683, -1.5033121858685683, -1.4995200006597365, -1.0408307286994845, 0.5414236114430883, 1.097982243024319, -0.49176777839073593, 2.8272043319974225, -1.1961675204882254, -0.3717323553177719, -0.06442887356887997, -0.3731585617412218, -0.25349239136044327, -1.5385503081538656, -0.9044133978688385, -0.5966825082583684, -1.483377296212783, 0.09201498263776839, -1.0381343157865668, -0.7132135699035859, -1.7556691796109165, -0.0492054176207329, -2.905064957547642, 0.7435346999024545, 0.04488353279025632, 0.3194519437202138, -1.218040029005081, -1.396679073491989, -1.1539873858373138, 0.18409005916466573, -0.09230640600982114, -0.03105576461550981, 1.2105075652524948, 0.275682399920334, -0.5400544130132925, -0.2872158399339437, -0.2894364330036906, -0.41528964273259483, -1.0381595546012334, 0.29186732578677793, 0.3732558523593279, -0.8515812188228882, 0.5468493875377143, -1.0586208062043467, 1.0976415945799405, 0.14408960056626924, 0.07041924205621686, 0.5885667052240487, 0.2553996069818114, 0.4350455959450131, 0.8675687484738434, -0.041671994825703745, 0.9407462876749985, 0.47807330304400186, 1.5975166973372237, 2.0903537243394528, 1.9027061350446934, 0.03194552366282259, 1.2347131215920886, 0.8465128921921077, 1.8682424190347922, 0.9965043764020813, 1.5475493535100735, -1.136926768735145, 0.11418890473831872, -0.4553074290083483, 0.41873690910904704, 0.07757589264746176, 0.2102928912003723, -0.1646944549312535, -0.34210011288259157, -1.069745107044426, 0.23132666106884922, 0.23744407372021464, -1.2553830032940871, -3.3153787980513045, -4.1024856235223055, -2.306555049545841, -4.606394802391144, -5.938033958979833, -4.213985062303165, -1.232787308494052, -3.1557361502039263, -3.0494966742937635, -1.309800389338512, -3.2208333029168754, -0.7645788954784027, -1.07555378469279, -3.9633117095957284, -0.22314160320665874, -1.458141709764554, -0.7505537632733716, -2.404244548841006, -8.062011895318555, -2.978303494031838, -3.611764324198019, -0.06690323005140043, -2.6679954179818024, -3.2898842795714454, -0.9831274346660133, -2.7724881980937535, -2.209820948880393, -1.2121692269145188, -1.7850521211669257, -0.46257175939867734, -3.0384022311390897, -1.7949402129772771, -2.024915015602822, -3.5827054058336434, -1.9471887744049492, -0.7728063722289643, -0.9791879433366345, -1.2675933754432198, -2.596387114823074, -1.3482230280957428, -1.8856509212033914, -1.5387189660882814, -1.6770378245803534, -1.7114501605272925, -1.049495132222344, 1.6244961641342097, -2.645249162362845, -1.558430251857324, -1.023459943299713, -2.423656610166809, -1.5966711672640952, -0.29872755769239967, -2.04356017858451, -4.28347096483935, -1.3584122667170526, -0.07698853804075222, -1.5805099292278038, -1.7727368651186768, -0.530721365606525, -3.3690678163615875, -1.864353878829011, -1.9067640930279721, -0.828344317996309, 4.698744270400309, 0.0215525665998904, -3.5829200518477555, -1.7505631038990792, -3.9681565375905565, -1.5546709103586622, 0.10078002555043211, 3.644948696818682, 3.2662682381469192, -4.370699528737124, -6.023835937645872, -5.395025010123471, -1.961572743215847, -5.167985265941133, 0.671925062821044, -3.7031211491044163, -1.9005748724516949, -2.565415304284841, -5.2718520623591125, -5.386609941067609, -3.3661821994164263, -2.5337328831333297, -1.8040673417545066, 0.5840410750632563, -0.8477601120769199, -0.8813513107410959, -2.433441895313499, -3.5896896813804027, -3.459115160050479, -3.7998683451033255, -3.751641485463982, 3.987409616836323, -2.051938460965609, -3.6381355871817354, -2.2521989238187916, -2.704738633333824, -2.706555210570493, -3.2280136727387467, -2.805123471051117, 1.3990536594220688, -0.9451257123651688, -0.8617446248762454, -2.335936503947782, -3.13933584256531, -2.4678532086950997, -2.575095315325202, -4.909243594787122, 2.40811342304599, 0.6245744563922638, 1.6510304466289671, -0.21284987985941015, -2.3331370582043314, -2.016596166629017, -1.6895567957623876, -1.7156979662938783, 4.582756814017564, 5.815457008387702, 3.3706479740398105, 0.2839597257951913, -2.3038098506300617, -0.8542558385377882, -2.132401010797612, -1.6131808381714796, 0.021305091403133646, -0.01741471940963102, 0.01277489122386679, 0.007878791354428899, -0.019828952567091735, 0.0214603089163779, -0.007227508730134252, -0.02125068937754603, 0.2316744269457057, -0.839760846220536, 0.01394780488281584, 1.7530412581360664, 1.6290658823890323, 0.8193230520589203, 1.1697199206716287, 1.9299376829247252, 1.08821089787808, 0.09100791061920324, -1.1637195071073057, 1.5853078623306884, 2.04354326556731, 1.9060064437371746, 1.2691818796353262, 1.4938525490794128, 2.0428815293892053, 3.246314142688173, 2.479717784900459, 0.9138290667441228, 2.5693359328482974, 1.6524585138326366, 2.296655690862581, 1.7259216067533412, 1.7168616163396067, 3.902967309139152, 4.062239884747169, 4.141336649636215, 1.8166925162890295, 2.7194522385951605, 1.9126428701894043, 1.869700426687212, 3.538921868604706, 4.576262319093415, 5.33552723831539, 4.378962016385271, 3.1373934972918844, 2.938859542184027, 4.067076182442378, 2.7501755469154436, 5.277402275775103, 5.789991039682929, 5.457248897101549, 4.280980599452619, 2.6311498027869717, 3.363290451532776, 3.6350452679645446, 3.033312504560851, 0.005932189433319748, -0.0033589835437821645, 0.021653145925330214, 0.01188240474946868, -0.01810353790862886, 0.020550355837200482, -0.01334601281511637, 0.01338071933530361, 2.582533363549077, 0.38950937068130403, 1.9623587010006176, -0.7924735021010222, 1.9678155496637446, 1.3342247562631517, -0.5097862552904221, 5.3568370696330065, 1.2515230582574182, -0.8214540474059775, 0.543019227170441, 1.1786962440805298, 0.02926821786231492, 0.14905362578456147, 1.3918533698900788, 0.8704127348421643, 1.2881459187681559, 1.5973713815938715, 0.4165462000302553, 1.1820640964627904, 0.9842401271296572, 0.417791762074318, -0.5597181030117602, -0.13548325993927965, 2.4207030482831464, 2.573024260731393, 3.390667305224528, 2.891448316053664, 0.9350489456272767, -1.636308913309197, -0.8901401090917734, -1.136759480971708, 4.831657021511997, 2.909529465497141, 3.6112483851285972, 2.450167396549203, 2.115022538019141, 2.371904841889844, -1.184444497719355, 0.09597214497228307, 3.6976572028968135, 2.3803047855849706, 3.342454487463226, 3.086353484033263, 2.3389375388141125, 3.5634244283559435, 0.5074255713777227, 1.0251612550370626, 2.5108625454408204, 2.03564764544156, 1.481104067068321, 1.5781187350543133, 1.9310069891585964, -0.5039399638154232, 2.6928408075834582, 1.7480875511442189, 0.3339182061591396, 3.9332942408841567, 3.2977892177585635, 2.8924456455375855, 3.7117207576444593, -1.8486737395283097, 5.5330743065510415, 4.244163041133341, 1.1368452271117573, 0.9547357201667108, -0.5460198430406693, -1.0434117877741784, 0.7838653795281105, -0.2709452965027361, 1.7898215898170788, 0.4366190149913638, -0.9277491954140564, 0.11564662113281736, -2.8556495855156414, 0.7842487405353926, -0.09104677781721456, 1.6559850583420377, -1.6375424082306136, 2.965015218987849, 1.6569588947151732, -0.03352443296422333, 0.44124469525793947, -0.22478817264965978, 1.4317439664179121, -0.60780840611841, 1.7624520016914291, -0.034850364452735046, -0.21222545087346234, 1.5640388124533042, 1.62512982399582, 0.9681160128137902, 1.2837222370313786, 1.881979630142706, -1.842628071850306, -1.0756970155567893, 0.8765988743797887, 2.4402818570041886, 2.372147321637981, 0.8628236390019872, 0.7772959242597351, -0.9981916783327814, 0.8824192345445204, -1.146983447637343, 0.6403840793508505, 0.4670984892535283, 0.004332119508014884, 1.652817634056606, -0.1065482355344297, -3.097833860102257, -1.702478726026187, 0.20522599676759098, 1.004744389292274, -0.5359194888464216, 2.3547162896056273, -2.811732112999592, -4.624191077079082, -1.4630010186422702, -2.2460579616497527, -1.5649674583541167, -2.904011860212184, 1.991310353480673, -1.5118903826697798, -1.7853257814051013, -0.12265715546988311, -1.4829668411440373, -6.7558823938716746, -2.0999203945541085, 1.145938651598318, 2.740427214738512, 2.3649749196553564, 0.7784887651209206, 0.744828367978651, -0.05819120988189702, -0.5243303319648448, -0.3915124900948929, 2.3462600446974236, 3.3227618141017317, 1.9111253813915736, 0.1504124238420735, -0.9423535105057202, 0.27161850822125955, 0.8185079067260886, -1.2851798359225284, 2.8989038371314706, 2.7662104876725206, 2.640415328347571, 0.8450853706055911, 0.44539885280050306, -2.108591997414513, 0.38895537705474315, -0.5503536939420778, 2.5288069047694055, 3.686773104045353, 2.633859186907867, 2.1682260806482376, 1.4980740873675138, -0.6330510169253539, -3.3389001817180213, -4.057073904293168, 2.7757093059167883, 2.730151782754765, 2.8362865716985066, 2.500740298199417, 2.551843038781507, 1.408079298363042, -2.961121889591924, -0.6670516305745822, 2.0175811561049377, 2.9999816194250597, 3.1063021069062917, 1.585117915532199, 2.3378511371270774, -0.6640251695439874, 2.707925367872163, 1.7677472467044222, 2.705213126905672, 2.8608704851202607, 1.567935702859213, 1.2901718914160079, 2.164231624021766, 2.4657750736486306, 2.5987871633006208, 3.354772609417412, -0.08555373487243902, 1.8726884934613597, 1.0756912761722575, 2.298540394061992, 2.689234769109423, 2.424603951789992, 2.6452495943558687, 0.5121023894955331, 0.1576796132120498, -0.9466351390896026, 1.4002355171799816, 0.6323420428058657, 0.3740676645629729, 1.074178758434088, -2.076671895005481, -3.605293732051998, 2.005577323992157, 0.6752664914529124, 1.2413268693508037, -0.12402253873593808, 0.870260903487021, -0.1008252861575322, -0.050008029327013696, -4.892300955112751, 2.5743974335108426, 1.5601871104357714, 2.4569544238931216, 1.0882272486312274, 0.7569989129337147, -0.13450266500750752, 0.11835224980215374, -2.0720586295879326, 3.1339669811982414, 4.084941980670005, 3.293343043746532, 1.6775558887942117, -0.6977055620887035, -1.4899254004488933, 0.2627603636235136, -3.9434922954985177, 2.3374129616178396, 3.202757766583923, 2.1056837425100814, 0.8682498351782372, 1.8746970635872093, -4.647448309496862, -3.11860259154586, -2.7718903658967258, 2.114768573807451, -0.19213369274222258, 2.3879574148846, -0.7250475990729963, -5.716320298564566, -6.79752631965982, -5.918482152848636, -4.894714057531749, 1.4051111486700298, 1.4139021663553375, 2.1512078599666538, -2.533595859955805, -5.746919937586967, -4.403678038309867, -3.288389559093661, -1.2759490186684632, -1.7317002210799073, 1.294199251556301, -2.6888902088697453, -5.5059198850228634, -3.9267913350654307, -2.506795133192883, -5.7598716508722685, -3.554250615080285, -2.5942822397443863, -0.491991087492544, -1.2097911106195913, -0.8325373694859385, -1.5546085963194891, -2.3702988996436125, -2.219188930312128, -2.1743715933059216, -3.0133720088825884, 0.38588739230123303, -0.7251681168713568, 0.17632080247534357, 0.40776075673600604, -2.124610002962465, -2.4900284936354895, -2.6459568812265877, 0.052678974085423304, -1.9915988735078067, 0.6350370009671293, 0.6339905643740834, 0.7491093620670851, -0.4188815951907799, -1.7321515304481907, -2.3756592687446236, 0.12448545516223482, 0.39860373292370394, -1.0576836824541584, 1.2947421547716094, 0.9112054566543988, -0.4861014795082656, -1.1079914832518303, -0.5946126497996108, 0.4145015050396499, -2.105795612869606, -0.2062831612115828, 0.9979460016407421, 2.1663703556221994, 1.8127995005174036, 2.3563435356517535, 0.09019849776972455, -7.070647957591879, -0.35956218165746645, 0.1782014486114305, 1.3652473614842056, 1.2819745065621282, 2.6003217612266765, 3.1978180939891674, 2.4080470612386673, -7.494855484769199, 2.3765022921788947, 1.4661015616120394, 1.6935536204934958, -0.46245115859047514, 1.2088960550172598, 5.39860924123767, -0.6059232975670212, -8.292333238865726, -6.032497255431216, 1.0969578076986675, 1.1084940331883655, 0.2531014374370231, 2.6412336230126843, 2.5919776860402854, 0.7477055518274854 ],
				[ -0.0006351766741542865, -0.002271389909960661, 0.016772608236703665, 0.013570007433011323, 0.0006973599723710464, 0.004351046400665675, -0.0030898966603126236, -0.0012684545689823766, 3.2734915449406503, 3.2853799175280907, 3.6346735655722076, 1.301743757096466, 4.1603109740513275, 3.358642121884119, 0.9051145131201963, -2.430016898883823, 1.6515693549030228, 3.152700814362214, 1.546517517937301, 2.955081403268792, 1.7736396805458126, -0.08751040040130133, 1.6198495000097664, 1.1965074668779607, 2.480156687023366, -0.04000170858472397, 2.325855958766464, 1.931713180320381, -0.30264382340831925, 0.1273893561357138, 1.6392131821444833, -1.3707628050545313, 1.1326790161446496, -0.43324061959729987, 1.301918914571555, -0.29648369174529965, -2.5654105934971216, 0.44567418720295404, 0.34571438116463077, 1.8446167470090253, 0.23679173923415828, -3.3613798709305827, 0.5058287991879835, -3.550846344314144, 0.6912817221815355, -2.0670808569119044, 0.9860494001146733, 1.2551821001610537, -0.5471936321313876, -1.5733600413407607, -0.9211185771578699, -0.591175842266777, -1.0399405944042024, 0.9837887165423629, 0.776586113089198, 0.706876737246333, 0.019136011936258485, -0.020166389898500798, -0.02045093899541002, 0.0038931602057325106, 0.006671956375271374, 0.0034836582160841854, 0.010637278042656266, 0.0035327507628528875, 0.7705748899535134, -0.7854521923911488, -0.9584472052405748, 3.7935630797045254, -1.8866125115791206, -0.4664387524927825, 3.0183346541413685, 0.5549650402356356, 4.445544959306917, 1.2961908422526944, 2.0921367925855594, -4.695909127497329, 2.2486676548810034, -1.1050779863581497, 0.15527632664734278, -2.004710832926639, 0.17525989069391676, 2.880939395044232, -0.11538917332987274, 1.2226787287367373, -0.7722591960452564, -0.7237170411102479, -1.729209963639143, 4.329918811653897, 3.0722827537642643, 4.114383050869047, -0.8131216762405232, 6.198194822443247, -0.9874401479202162, 2.7589848137953683, -1.4249863341517073, 1.1634928953692387, 0.8864041404315747, -0.08301124989127229, 2.28862618343937, -0.5007046257978307, 2.205923895083936, -0.14066620483927433, 1.1739404862950593, -0.055339574648859094, 0.3265335155998357, -0.581850520945333, 0.7741467281021366, -2.842768259579607, 0.426901001738859, -2.6783128950977266, 0.6917192343092364, 0.20725641292651328, 3.7627658836573, -0.5163124820988685, -1.209516046870779, -0.7698517208526522, -1.0282490065014525, 1.392091322883221, 0.7433761217634632, 0.3187513737639251, 1.6728140419541737, -1.0545607626754272, -1.2144006548382462, 1.8231370247779564, -1.1354200060677413, 1.6429154035594853, -2.016943379302525, -0.9053525155601494, 1.5808280098670946, -4.9692843399602316, -2.3397941155375652, -2.7134135740612257, -0.22475404608069907, -1.5153340942671327, 0.06772070919492199, -5.44625400072626, -3.6110675025438854, 1.0892565372814302, 0.8653752721473177, -1.436928179956922, -7.452335282055649, -3.7809864755656672, -6.6283810381232255, -0.8459875290232699, 3.8751876688083753, 2.675768203850362, 3.144996726420648, -0.16403053792518568, 2.997254972374276, -1.607072588217021, -0.1642244794183246, -1.7483482951873839, -1.551075484067018, 5.176482959139828, 0.21762207455918273, 3.8889699416605366, -1.5432118656022313, 2.0205914444065054, -4.1139925644627295, 1.6215805917544306, -0.4000726206532356, -1.0258129473279916, 2.9565804018974076, 1.024254662537123, 0.9781272292602594, -0.5239961823376117, -1.440466296239118, 0.5875140214803465, 0.006889387421765039, 3.7659391650385707, -0.9508847097703049, 0.19762132655407375, 0.6187065988285828, 1.9560491310529633, 1.0618258317361595, 2.132582606026763, -0.4250213392120455, -2.024524622728611, 1.287659515770717, -2.0385082145049327, 2.680755660833674, -3.0396406385938675, 3.4275094266082116, 5.109250813069006, 0.4241522660739768, -0.05956604015284974, -2.4877670305015607, 3.871594539088212, -0.8346885335044516, 2.2091551141062267, 1.4923188020948999, 6.642002825513437, 2.0499451264722954, -0.655185154315848, -0.31372003935607795, 0.7408722080519801, -9.487716593422233, -6.004896765889708, 0.32255678116591885, 2.190412099790374, 1.9210222703028075, 0.8460317217861725, 2.694181445159338, 3.077826970661517, 1.4653230823933823, 0.5423237296448127, 0.13409437216750805, 1.59495570580425, 2.781744894363738, 1.2066924734431514, 0.02177023307283752, 2.680522739170552, 2.9319751193322605, -1.5104717554390483, 2.518063108853282, 1.0744548593929424, 0.5011004521950766, 2.4018815268575486, 1.7449029405566512, 1.4339415448418436, 3.1925379577095017, 0.009809228149232352, -0.8228916321253984, -2.1791728829804975, 1.4495872849697022, 0.8501327485016215, 1.3987516016782713, 0.016108622211077804, -0.1107719171133731, 1.7629273495004731, -0.9856227579836323, 2.075198413318001, 0.6297447799273715, 2.875916891494145, 0.22118005836789792, 1.9396599902898723, 0.30593896249719627, -0.06041225375652088, -1.0911632527486, 0.22908628397856476, 0.6890607158724847, 1.4958363127572005, -0.16648158695221543, 2.1285796562366635, -0.4033642619034786, 1.7660885838437221, 2.090833085502549, -1.3518099563558983, 1.5168682635036181, 1.7969316539034819, 1.2240039403866974, 1.5381951829256368, 1.0371342536098143, 1.3722826797430259, 0.9382117013779963, -0.7368403838190807, 0.7131258698784408, -1.8374515671696765, -4.616854561081961, 0.2736439430361064, -4.569305975732426, -0.386147337256665, -2.9035509847031404, 2.601078021218988, -0.35091414407677135, 0.02122102358542259, 2.792527763176714, -0.8841535769628653, -3.6303324312786205, 0.5974445907313082, -1.1388589181335316, -7.3724243475913696, 1.1442632101070955, 3.1305142409881075, 4.114165439252952, 1.7233352145539673, -4.044822736065589, 3.0771678345545586, -2.17634711571578, -0.026667676164105193, 2.5566185156314605, 2.5215979847855508, 0.7167289994011274, 2.701562783290358, 3.083150116484906, 0.768036055587087, -4.223971922370683, 1.8439662880495782, 1.2732809308115072, 3.2271440861279443, 1.3468168445837871, 4.8327786111986875, 0.5561601241550806, 1.7435608100059559, 0.8383363219705946, -1.0218507680378013, 2.8448675402343278, 2.295030226954496, 2.0107888200978676, 1.4391400082099668, -1.2082223276121469, 2.088355101780274, 1.1912569152633725, -0.7516447711202741, 3.002413080819897, 2.2062467600405453, 1.9111072948911396, 0.8801173923689394, 2.1822808320686353, 2.794631450074282, 0.928512667402955, 1.0503845284903708, 3.119965693767783, 2.5571367003539582, 1.2410018401398606, 0.8819603916326958, 3.7773199079458357, 3.570830426501998, 2.370740310269034, -2.586271695048688, -4.113878393994035, -3.5469545660996467, 2.074341590649107, 3.76732346287467, 0.9012723898250606, 3.181434702489448, 3.104669279960383, 5.411275092462453, -2.2779209637694797, 0.8160501281722424, -6.872525127092615, -1.5751267063203558, -3.1956029255691276, -6.363609387911726, -3.6453716155632354, 1.0288915507064917, -5.549093418829025, -5.840687843797731, -3.8397830726596816, -1.4376002462720412, -2.906252238142154, -3.8616572950692016, -3.1633675882747085, 3.4158391226131255, 0.26935601582503005, -4.52083926150185, -0.8394681394315148, -0.4185232400844789, -1.5957872336828345, -0.8702264118243959, -1.011970544406251, -0.8157043829537703, -0.01849573333028126, -2.2755122705299766, -2.864851769549268, -1.0041606327569248, -3.6353454386866475, -1.610684103402383, -2.8871188395762517, -0.07677941468394779, -1.6104857901384375, 1.08069640416801, -0.7209614455496024, 0.5414618026275495, -2.025321956554624, -3.181666414054389, -1.8269785464688155, -7.874794650318414, 0.2795509568003569, 0.37261905067502377, -0.581102991533528, -1.6430125701055183, -1.9758920050136666, -2.0943290799874354, -1.5988622757848154, -1.390761867504756, 0.5748099887128251, 0.7313988841804163, 0.16886631355226545, -3.773113559208371, -0.08293745964130342, -0.7684797575258785, -0.3033801368989611, 0.2083045591738405, 0.014764742278730298, -0.02089838743725203, -0.011558688071065847, -0.01799391944830464, 0.017658567395506936, 0.01930002521056856, 0.009177696805317999, -0.011694371407231547, -0.9270344843802345, 0.21895621588219946, -3.7988481704728843, 0.6094149139776888, 0.40247631156530217, 0.037397481493027386, 0.4453900454414413, 1.2687017229771245, -0.769071215097831, 0.1097478651595934, -2.852475781879182, 0.21574413037274054, -1.6354554525376983, 1.686325028915426, -1.7530825816582154, 0.3291804756530222, -0.2072910183711187, -1.3626454825338004, 0.9463287753158708, -0.7910667189067493, 0.9734609489519761, 0.08541473877499177, 0.2848171005215289, 0.6790917336633204, -0.3470660392383815, -2.1990055274938283, -0.027787033797190167, -3.740554622872769, 1.402329567004209, -7.507632042054889, 2.3636798707026085, -0.6543134622568247, -0.16808043395993558, -3.59192482671959, -1.756153119636067, -1.994791076386862, 0.8973363530525567, -13.408114237089398, 0.4758347055149189, -3.0433888699703053, -8.256932277326237, -10.440843732168174, -6.322794100580641, -3.0814167464449227, -4.107728288321301, 1.3063000252951786, 3.119021001797022, 6.341743777919155, 0.018704106916863326, 0.002006338472721756, -0.01136238498345043, 0.008582118646841578, 0.013564121978390992, -0.005115938290998578, 0.019870351505562985, 0.009431581114789096, -1.2742915039638836, 0.569914333210653, -0.641811357423631, 0.8105434914834052, 1.0226415879097515, -0.6059235945608661, 1.4167909360980566, -2.642407285945569, 0.4015029579790146, 1.5192219299141578, 2.1920559337546113, -0.20128895241393033, 1.0718360857835512, 1.1224930183296082, -0.8138634021812843, 1.9468769801233168, 1.0305970464382193, 0.40759117521467625, -0.8923816267417692, -0.025042290275171145, 1.1589467858121492, -0.333360377588492, 2.996530118277982, 0.851529431480886, -2.7829253460607797, -1.067982419181387, -2.3578560736036995, 1.603362053675231, 0.49915699061362073, 0.880148823577285, 1.12412465557614, -0.107006229359758, -0.49980015903291775, -0.8693290812870736, 1.4308603391787098, -1.1316562553229332, 0.01267704975638882, 2.4111450895810935, -0.3384405309029944, 1.105585014590856, 0.40178817609855044, 2.4321230572575394, 1.6697995493958833, 0.2037059065987269, 3.686351111314952, 1.1560594933335333, 3.419716738623522, 0.5965207322351245, -2.6185201173608363, -0.8869694842638915, -0.7372975936685322, -1.781652621423664, -1.1542434732791298, -0.5022102030233563, 2.6967612625450226, -1.257886735152517, -4.242643547276461, 1.0594703918266737, 4.457090260191611, 2.6927624278842512, -7.428042650499256, 2.5522070965188504, -0.14433034321283006, 4.195649534587031, -2.394329083369176, -0.7568070651085872, -1.3332046493596426, -0.11108762793663121, -0.6321499727706201, 0.3905042758368048, 1.634411509917336, -7.382637633585025, -3.5008822150160275, -1.6708712465773874, -1.790058823347212, -1.873624423063204, -0.061700787829481366, -0.9106207358872364, 0.8581097267457134, 0.7209851289922066, -2.4673312984565605, -0.05966091557347636, -2.844303892234074, -0.45311902177401947, -0.6671586269714994, -0.5983481304762039, 0.13343479240801345, 0.3643658943851498, 0.3263771624510696, -1.9867879060177716, -4.113976546245319, 0.6415803109647497, 0.5946015084999017, 0.6765199639445507, 0.8847026973024024, 0.12116949029906716, -0.8497101288275635, -1.4768390353910743, -1.6787701675179034, -0.2031200893886072, -0.49344380631161894, -2.112617003748328, -0.7505828254367167, 1.6931751016802685, 0.9116836458186549, 0.20139649186832712, 1.1225254369304332, -1.7454006217256914, -1.32776558057455, 0.3087017574654716, -7.222745527619233, -0.45876657593955417, 1.1189480898406514, 1.4207428590717308, -2.324324832982504, 2.076745409779294, -0.17122775427050324, -1.0294461410655917, 1.4796054741986737, -1.0277089470804472, 3.9064695905524576, 1.3455233785424126, 1.7455108214973452, 0.870548432402806, 1.245899803907994, -3.2550931060518944, -2.7393720579994616, -7.06441812512919, 0.6066867750608668, 0.9743706114305595, 0.09496074934589342, 0.6767001585362316, -0.0851488722687812, 0.5731840035893689, 2.65097907540381, 0.7382917646203287, 2.3020220090273495, 1.7619615619817952, -0.854415237043485, 1.8487662865842858, -0.19584000309977911, 1.9045491552439884, 2.8683788442157026, 2.650859429876299, 1.5128623893792335, 1.7681428953090321, 1.338239147673076, 2.2307360100600415, 0.3169112519111064, -0.772700933731362, 1.874901483748927, 2.3078411149860933, 0.8694610053671118, 1.5875240366874916, 1.8959536642228414, 0.5083367247290387, 0.5989857594118161, 2.005561717282401, 3.491879887547868, 3.8993115035446606, 0.11979272331176377, 0.1092132404231728, -1.0158657041893062, -0.06792190058044344, 2.443808297529487, 1.2235349991147924, 1.0019997794111042, 1.5507523936908274, 0.8173771222541659, -0.6238321787730893, -2.120384238531103, -0.35727155156764834, 1.0198906895256767, 1.1105238737184884, -1.5044922961387337, 2.2440354487057377, -0.07119346741583729, 1.1011814935889213, -0.32372212735392997, 1.9695553153224084, 1.8282973291870337, -2.29924519371116, 1.415596091306096, -1.6773686491678776, -2.236017438063843, 0.019423768671265433, -1.1495086689463399, -1.5548203540196177, -2.0595747762827794, 2.341792523185522, 2.9930688956707527, -0.01269241476345985, -2.067301824696606, -0.2292690335988974, -0.06260489382761607, -0.4072554091590012, -0.7688072380972848, 2.4610776653042308, -4.820008507844298, -0.731461451027645, -0.12948361162799968, 0.7011061955202613, -1.205977759002701, -0.1044694652464672, -0.38520921683533765, -0.24433002451443386, -2.039020703223609, -0.09731699772676922, -1.9026489928840706, 0.48032337866061137, -1.1269782464599527, 0.7871068896310248, -0.8315762523837177, -0.2813971223638817, 1.0523816062416473, 0.6594700635551946, -0.1902994201369374, 1.6914292212530513, -1.2977708357510684, 0.39154910616001826, -1.174126168445913, 1.7880105856427357, 1.8766327332981407, -0.22499875069726283, 0.7916272560075461, -2.714228049383974, 1.0237840808532714, 0.39992166210241914, 0.8995189121713673, 0.11878687644934204, -0.06337101963751977, 2.0181326170759544, -0.12330809915999523, -0.4766036106580403, -1.8711231290601407, 4.810963474240182, 1.1889252042911835, 1.6219236847988312, -9.100657931292933, 0.33241058151480185, 0.3067762948737498, -1.3526602538394479, 1.64797444431421, 0.28697316202544887, 5.066661021972426, 3.9982997097754924, 1.9285521246607071, 3.6779657697011023, 0.7815457830479557, 0.09917495285075414, -0.6213797715946981, 2.2862890217840053, 3.185000133779942, -8.08605997428212, 3.377614094552691, 0.49214105141642883, 1.5071266470956883, 1.9230573328972402, 1.1925034578375457, 1.6679192034831956, 2.0592419564687514, -0.7294796107893208, -0.8208266449546543, -2.4264751328580205, 0.49675825842327, 2.4019183688862213, 0.32965332336107334, 2.019227420138619, -1.4984119800517208, -2.4491069195363737, -3.272167230241928, -2.513426089956345, -0.2091743625465316, 0.8820350214775489, -1.161323648598673, -1.664861432416831, -3.727866392262277, -2.679458496777993, -2.552740265108671, -1.0730814705145344, 0.8592905567963379, -4.092731453726481, -3.5983867616187055, 1.6268617033689994, -6.513605728663898, -1.9951683912610343, -3.5650997900356325, -4.583724711110016, 1.3779106932259024, 1.960051169757662, 1.3537078272793177, -4.978240810039245, -2.450657168201792, -2.8854530321835115, -2.049745791876728, -4.160952300324705, 0.7902684152114552, -7.713731233821741, -4.379170138048745, 1.3653360162545034, -6.825662971649188, -2.7483560719470903, -1.869853143064271, 0.8143887885698666, 1.749813226552996, 2.573382289083049, -1.4140568356751653, -3.0842923907023305, 0.18826630772404937, 2.8566599138494975, 0.11110839371952579, 0.7489669214632596, 4.60692123867424, -2.6644351771703785, 1.4791136844167736, 4.153200510043967, -4.799586843937418, 1.3470234986250242, -2.68703444501557, 5.605990467181245 ]
			],
			[
				[ -4.220475452664129, 7.5849352387515685, -4.330964583008609, 4.157154256047814, 24.201361136154716, 6.188349195547214, -4.222727542812749, 3.3751288773926826, -7.200408674087074, -2.807460283785701, 3.931539924021513, -7.629350982405115, 4.3675362807517475, 4.542816920158758, -4.651773641695766, 3.4596658631211583 ]
			]
		],
		biases: [
			[ -2.9614180358117452, -5.279520564454454, -0.920408879895549, -3.7883658598776706, -1.4819045349693947, -5.2959594596634485, -1.5518593366665399, -5.592412439909098, -4.831531599910079, 2.829587286462337, -1.0618608476112166, -3.969095462436552, -5.612672633345479, 0.9925983455536938, -6.081622231074628, -4.0226689193028236 ],
			[ 5.658213934191964 ]
		],
		activations: [ 'relu', 'chess' ]
	};
