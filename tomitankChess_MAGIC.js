/*
 tomitankChess 2.0 Copyright (C) 2017-2018 Tamás Kuzmics - tomitank
 Mail: tanky.hu@gmail.com
 Date: 2018.07.11.

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

// Valtozok
var VERSION         = '2.0';
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
var LeastWhitePawn  = 0; // Leghatso Feher Gyalog
var LeastBlackPawn  = 0; // Leghatso Fekete Gyalog
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
var brd_PvArray     = new Array(maxDepth); // Mentett lepesek
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
var MOVE_HISTORY    = new Array(); // Lepeselozmenyek
brd_moveStart[0]    = 0; // Hack: Lepes lista index


// Allandok definialasa a jobb olvashatosag miatt
var WHITE           = 0x0;
var BLACK           = 0x8;

var PAWN            = 0x01;
var KNIGHT          = 0x02;
var BISHOP          = 0x03;
var ROOK            = 0x04;
var QUEEN           = 0x05;
var KING            = 0x06;
var EMPTY           = 0x40;


// Feher babukat 4 bit tarolja
var WHITE_PAWN      = 0x01;
var WHITE_KNIGHT    = 0x02;
var WHITE_BISHOP    = 0x03;
var WHITE_ROOK      = 0x04;
var WHITE_QUEEN     = 0x05;
var WHITE_KING      = 0x06;


// Fekete babukat 4 bit tarolja
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
var PawnDoubled     = -10; // Dupla Gyalog
var BishopPair      = 50; // Futo par plusz pont
var PawnBackward    = -8; // Hatrahagyott Gyalog
var PawnIsolated    = -10; // Elkulonitett Gyalog
var INFINITE        = 30000; // Infinity / Vegtelen
var CAPTURE_MASK    = 0x1000; // Leutes jelzo maszk
var DANGER_MASK     = 0x3F000; // Fontos lepes maszk
var CASTLED_MASK    = 0x20000; // Sancolas jelzo maszk
var TACTICAL_MASK   = 0x1F000; // Utes, Bevaltas maszk
var ISMATE          = INFINITE - maxDepth * 2; // Matt
var PAWNENTRIES     = (1  << 12) /  1; // Gyalog hash max ~1 MB
var PAWNMASK        = PAWNENTRIES - 1; // Gyalog hash maszk, csak ketto hatvanya lehet
var HASHENTRIES     = (32 << 20) / 16; // Hashtabla merete 32 MB / 1 Hash merete (16 byte)
var HASHMASK        = HASHENTRIES - 1; // Hashtabla maszk, csak ketto hatvanya lehet & MASK
var CASTLEBIT       = { WQCA : 1, WKCA : 2, BQCA : 4, BKCA : 8 }; // Sancolas ellenorzeshez
var PawnShelter     = [ 36, 35, 32, 27, 20, 11, 0 ]; // Gyalog-Kiraly Pajzs (RANK_8, RANK_2)
var AttackWeight    = [ 0, 0, 0.5, 0.75, 0.88, 0.94, 0.97, 0.99 ]; // Kiraly Tamadas Sulyozasa
var PawnPassed      = [ 0, 0, 0, 0, 0.1, 0.3, 0.6, 1, 0 ]; // Telt Gyalog elorehaladasi pontjai (RANK_0, RANK_8)
var MvvLvaScores    = [ 0, 1, 2, 3, 4, 5, 6, 0, 0, 1, 2, 3, 4, 5, 6 ]; // MVV-LVA Babuk erteke (P, N, B, R, Q, K)
var SeeValue        = [ 0, 1, 3, 3, 5, 9, 900, 0, 0, 1, 3, 3, 5, 9, 900 ]; // See Babuk erteke (P, N, B, R, Q, K)
var KnightMoves     = [ 14, -14, 18, -18, 31, -31, 33, -33 ]; // Huszar lepesek
var KingMoves       = [ 1, -1, 15, -15, 16, -16, 17, -17 ]; // Kiraly lepesek
var BishopMoves     = [ 15, -15, 17, -17 ]; // Futo lepesek
var RookMoves       = [ 1, -1, 16, -16 ]; // Bastya lepesek
var Letters         = [ 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h' ]; // Betuzes
var START_FEN       = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -';
var nonSlider       = [ 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1 ]; // nonSlider (P, N, K)
var PieceDir        = [ 0, 0, KnightMoves, BishopMoves, RookMoves, KingMoves, KingMoves ]; // Lepesek tomb
var PieceValue      = [ 0,  80, 325, 325, 500, 1000, 20000, 0, 0,  80, 325, 325, 500, 1000, 20000 ]; // (P, N, B, R, Q, K)
var DeltaValue      = [ 0, 100, 325, 325, 500, 1000, 20000, 0, 0, 100, 325, 325, 500, 1000, 20000 ]; // (P, N, B, R, Q, K)
var RANKS           = { RANK_1 : 1, RANK_2 : 2, RANK_3 : 3, RANK_4 : 4, RANK_5 : 5, RANK_6 : 6, RANK_7 : 7, RANK_8 : 8 }; // Sorok
var FILES           = { FILE_A : 1, FILE_B : 2, FILE_C : 3, FILE_D : 4, FILE_E : 5, FILE_F : 6, FILE_G : 7, FILE_H : 8 }; // Oszlopok

// Typed Arrays for better memory usage. (16 byte)
var hash_move       = new Uint32Array(HASHENTRIES);
var hash_flags      = new Uint8Array(HASHENTRIES);
var hash_depth      = new Uint8Array(HASHENTRIES);
var hash_score      = new Int16Array(HASHENTRIES);
var hash_keyLow     = new Int32Array(HASHENTRIES);
var hash_keyHigh    = new Int32Array(HASHENTRIES);

// BitBoard
var LOW             = 0; // Also 32 bit tomb index
var HIGH            = 1; // Felso 32 bit tomb index
var RankBBMask      = new Int32Array(9); // Bitboard sor maszk
var FileBBMask      = new Int32Array(9); // Bitboard oszlop maszk
var SetMask         = new Int32Array(64); // Bitboard Mentes maszk
var ClearMask       = new Int32Array(64); // Bitboard Torles maszk
var HighSQMask      = new Uint8Array(64); // Bitboard HighSQ maszk
var BitFixLow       = new Uint8Array(64); // Bitboard BitFix maszk [LOW]
var BitFixHigh      = new Uint8Array(64); // Bitboard BitFix maszk [HIGH]
var IsolatedMask    = new Int32Array(64); // Bitboard Isolated maszk
var WhitePassedMask = new Int32Array(64); // Bitboard Passed maszk Feher
var BlackPassedMask = new Int32Array(64); // Bitboard Passed maszk Fekete
var WOpenFileMask   = new Int32Array(64); // Bitboard OpenFile maszk Feher
var BOpenFileMask   = new Int32Array(64); // Bitboard OpenFile maszk Fekete
var NeighbourMask   = new Int32Array(64); // Bitboard Neighbour maszk Kozos
var WCandidateMask  = new Int32Array(64); // Bitboard Candidate maszk Feher
var BCandidateMask  = new Int32Array(64); // Bitboard Candidate maszk Fekete
var BlockerBBMask   = new Int32Array(64 *  8 * 2); // Szelek kizaras maszk
var AttackBBMask    = new Int32Array(64 *  8 * 2); // Tamadas tombok maszk
var BehindBBMask    = new Int32Array(64 * 64 * 2); // A mezo mogotti maszk
var BetweenBBMask   = new Int32Array(64 * 64 * 2); // Ket mezo kozti maszk
var MagicRAttacks   = new Int32Array(64 * 4096 * 2); // Magikus Bastya tomb
var MagicBAttacks   = new Int32Array(64 * 4096 * 2); // Magikus "Futo" tomb
var MagicRShifts    = new Uint8Array(64); // Magikus BitBoard Bastya eltolas
var MagicBShifts    = new Uint8Array(64); // Magikus BitBoard "Futo" eltolas
var BitBoard        = new Int32Array(30); // Index: color/pce << 1 | Low/High

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

		if (SetMask[1] !== 0) { // Mar inicializaltunk
			return false;
		}

		var f, sq, pce, tsq;

		// Sor + Oszlop nullazasa
		for (sq = 0; sq < 8; ++sq) {
			FileBBMask[sq] = 0;
			RankBBMask[sq] = 0;
		}

		// Sor + Oszlop feltoltese
		for (var r = RANKS.RANK_8; r >= RANKS.RANK_1; r--) {
			for (f = FILES.FILE_H; f >= FILES.FILE_A; f--) {
				sq = (r - 1) * 8 + (8 - f);
				FileBBMask[f] |= (1 << sq);
				RankBBMask[r] |= (1 << sq);
			}
		}

		// Bitmaszkok nullazasa
		for (sq = 0; sq < 64; sq++)
		{
			IsolatedMask[sq] = 0;
			WOpenFileMask[sq] = 0;
			BOpenFileMask[sq] = 0;
			NeighbourMask[sq] = 0;
			WCandidateMask[sq] = 0;
			BCandidateMask[sq] = 0;
			WhitePassedMask[sq] = 0;
			BlackPassedMask[sq] = 0;

			// Tamadasok + Kizarasok
			for (pce = KNIGHT; pce <= KING; pce++) {
				AttackBBMask[AttackBBidx(pce, sq, LOW)] = 0;
				AttackBBMask[AttackBBidx(pce, sq, HIGH)] = 0;
				BlockerBBMask[AttackBBidx(pce, sq, LOW)] = 0;
				BlockerBBMask[AttackBBidx(pce, sq, HIGH)] = 0;
			}

			// Mogotte + Koztes
			for (var sq2 = 0; sq2 < 64; sq2++) {
				BehindBBMask[BetweenBBidx(sq, sq2, LOW)] = 0;
				BehindBBMask[BetweenBBidx(sq, sq2, HIGH)] = 0;
				BetweenBBMask[BetweenBBidx(sq, sq2, LOW)] = 0;
				BetweenBBMask[BetweenBBidx(sq, sq2, HIGH)] = 0;
			}

			// Maszkok Feltoltese
			SetMask[sq]    = (1 << (sq > 31 ? 63-sq : 31-sq)); // SetMask
			ClearMask[sq]  = ~SetMask[sq];                     // ClearMask
			HighSQMask[sq] = (sq > 31 ? 1 : 0);                // HighSQMask
			BitFixLow[sq]  = (sq > 31 ? 63 : 32 + sq); // Also bit fix?(63-Igen)
			BitFixHigh[sq] = (sq > 31 ? sq - 32 :  0); // Felso bit kell?(0-Nem)

			// Mezo kulonbseg
			DISTANCE[sq] = new Array(64); // ARRAY[SQ1][SQ2]
			var rank1 = TableRanks[sq];
			var file1 = TableFiles[sq];
			for (var sq2 = 0; sq2 < 64; sq2++) {
				var rank2 = TableRanks[sq2];
				var file2 = TableFiles[sq2];
				DISTANCE[sq][sq2] = Math.max(Math.abs(rank1-rank2), Math.abs(file1-file2));
			}
		}

		// Bitmaszkok feltoltese [0 - 64]-ig
		for (sq = 0; sq < 64; sq++)
		{
			tsq = sq + 8;
			while (tsq < 64) {
				BOpenFileMask[sq]   |= SetMask[tsq];
				BlackPassedMask[sq] |= SetMask[tsq];
				tsq += 8;
			}

			tsq = sq - 8;
			while (tsq >= 0) {
				WOpenFileMask[sq]   |= SetMask[tsq];
				WhitePassedMask[sq] |= SetMask[tsq];
				tsq -= 8;
			}

			if (TableFiles[sq] > FILES.FILE_A) {
				IsolatedMask[sq] |= FileBBMask[TableFiles[sq] - 1];

				tsq = sq + 7;
				while (tsq < 64) {
					WCandidateMask[sq]  |= SetMask[tsq];
					BlackPassedMask[sq] |= SetMask[tsq];
					tsq += 8;
				}

				tsq = sq - 9;
				while (tsq >= 0) {
					BCandidateMask[sq]  |= SetMask[tsq];
					WhitePassedMask[sq] |= SetMask[tsq];
					tsq -= 8;
				}
			}

			if (TableFiles[sq] < FILES.FILE_H) {
				IsolatedMask[sq] |= FileBBMask[TableFiles[sq] + 1];

				tsq = sq + 9;
				while (tsq < 64) {
					WCandidateMask[sq]  |= SetMask[tsq];
					BlackPassedMask[sq] |= SetMask[tsq];
					tsq += 8;
				}

				tsq = sq - 7;
				while (tsq >= 0) {
					BCandidateMask[sq]  |= SetMask[tsq];
					WhitePassedMask[sq] |= SetMask[tsq];
					tsq -= 8;
				}
			}

			// Kozvetlen szomszed mezok
			var r = TableRanks[sq];
			if (r > RANKS.RANK_4) {
				NeighbourMask[sq] |= (WCandidateMask[sq] & RankBBMask[r-4]);
			} else {
				NeighbourMask[sq] |= (WCandidateMask[BitFixHigh[sq]] & RankBBMask[r]);
			}

			// Mobilitas: A Gyalog tamadasokat a NeighbourMask adja!
			var from = to_88(sq); // 64 -> 120
			var from_64 = sq; // Hack
			for (pce = KNIGHT; pce <= KING; pce++)
			{
				for (var dir = 0; dir < PieceDir[pce].length; dir++)
				{
					var to = from + PieceDir[pce][dir];

					while (!(to & 0x88))
					{
						var to_64 = from_88(to); // 120 -> 64

						AttackBBMask[AttackBBidx(pce, from_64, HighSQMask[to_64])] |= SetMask[to_64]; // Tamadas mezok

						if (pce == BISHOP || pce == ROOK)
						{
							var flip = -1;
							if (from < to) flip = 1;

							if (TableRanks[from_64] == TableRanks[to_64]) {
								var inc = flip * 1;
							} else if (TableFiles[from_64] == TableFiles[to_64]) {
								var inc = flip * 16;
							} else if ((from % 15) == (to % 15)) {
								var inc = flip * 15;
							} else if ((from % 17) == (to % 17)) {
								var inc = flip * 17;
							}

							for (tsq = from + inc; tsq != to && !(tsq & 0x88); tsq += inc) { // Koztes mezok
								BetweenBBMask[BetweenBBidx(from_64, to_64, HighSQMask[from_88(tsq)])] |= SetMask[from_88(tsq)];
							}

							for (tsq = to + inc; !(tsq & 0x88); tsq += inc) { // Mogotte mezok
								BehindBBMask[BetweenBBidx(from_64, to_64, HighSQMask[from_88(tsq)])] |= SetMask[from_88(tsq)];
							}
						}

						if (nonSlider[pce]) break; // Huszar, Kiraly

						to += PieceDir[pce][dir];
					}
				}
			}
		}

		// Szeleket kizaro tomb
		for (var from = 0; from < 64; from++)
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

		// Magikus BitBoard "Fancy"
		for (var from = 0; from < 64; from++)
		{
			for (pce = BISHOP; pce <= ROOK; pce++)
			{
				if (pce == ROOK) {
					var MagicShift = MagicRShifts[from] = 32 - PopCount(BlockerBBMask[AttackBBidx(ROOK, from, LOW)]) - PopCount(BlockerBBMask[AttackBBidx(ROOK, from, HIGH)]);
				} else {
					var MagicShift = MagicBShifts[from] = 32 - PopCount(BlockerBBMask[AttackBBidx(BISHOP, from, LOW)]) - PopCount(BlockerBBMask[AttackBBidx(BISHOP, from, HIGH)]);
				}

				var MagicLow  = pce == ROOK ? MagicRLow[from]  : MagicBLow[from];
				var MagicHigh = pce == ROOK ? MagicRHigh[from] : MagicBHigh[from];

				var b = { Low : 0, High : 0 };

				do {

					b.High = 0; // Hack

					do {
						var attacks = AttacksFromDebug(pce, from, b);

						var index = ((b.Low * MagicLow) ^ (b.High * MagicHigh)) >>> MagicShift;

						if (pce == ROOK) {
							MagicRAttacks[(from << 13) | (index << 1) | LOW]  = attacks.Low;
							MagicRAttacks[(from << 13) | (index << 1) | HIGH] = attacks.High;
						} else {
							MagicBAttacks[(from << 13) | (index << 1) | LOW]  = attacks.Low;
							MagicBAttacks[(from << 13) | (index << 1) | HIGH] = attacks.High;
						}

						b.High = (b.High - BlockerBBMask[AttackBBidx(pce, from, HIGH)]) & BlockerBBMask[AttackBBidx(pce, from, HIGH)];

					} while (b.High);

					b.Low = (b.Low - BlockerBBMask[AttackBBidx(pce, from, LOW)]) & BlockerBBMask[AttackBBidx(pce, from, LOW)];

				} while (b.Low);
			}
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


// "Magikus" Szamok
	var MagicRLow = new Int32Array([
		0x04A09061, 0x00808806, 0x0AE1043A, 0x10842112, 0x0404A029, 0x00A04012, 0x0090E262, 0x08816301,
		0x01800080, 0x00018600, 0x01194A00, 0x30800810, 0x42900280, 0x00100410, 0x08805080, 0x00230020,
		0x082C0102, 0x18010200, 0x08A20084, 0x00808200, 0x2580800C, 0x06202000, 0x40001000, 0x20001000,
		0x08800380, 0x20800200, 0x00802E50, 0x00800488, 0x00800B00, 0x42020042, 0x00804004, 0x40200020,
		0x0082C204, 0x08740200, 0x02840498, 0x14C80010, 0x00A02900, 0x00A10410, 0x00328100, 0x02118140,
		0x08A84244, 0x008E0890, 0x16811018, 0x00110811, 0x02816014, 0x10044024, 0x48924000, 0x48402008,
		0x28886882, 0x58810004, 0x02144020, 0x0030400B, 0x00CA0081, 0x46802B08, 0x40802B10, 0x02801800,
		0x08800420, 0x00900210, 0x00420540, 0x08800850, 0x08880004, 0x20008009, 0x0111B008, 0x00802404
	]);
	var MagicRHigh = new Int32Array([
		0x02800023, 0x00004902, 0x00885052, 0x00C0300A, 0x24210010, 0x4134C40A, 0x01002011, 0x0000A090,
		0x12004141, 0x0800048A, 0x04005046, 0x0800100C, 0x60002008, 0x02040020, 0x42400060, 0x61401080,
		0x00880451, 0x08020205, 0x10408816, 0x40080284, 0x10515008, 0x0180320C, 0x001EA088, 0x00088040,
		0x48140461, 0x10A08401, 0x00918004, 0x01008008, 0x40808738, 0x009C00E2, 0x214A8030, 0x41809048,
		0x15808241, 0x08810081, 0x60881002, 0x40881D01, 0x18411001, 0x08406001, 0x00004125, 0x0480842E,
		0x01008101, 0x04208402, 0x00800202, 0x40040101, 0x10C82202, 0x54801020, 0x10012020, 0x00800040,
		0x00230001, 0x40810102, 0x04080404, 0x00A40824, 0x22008010, 0x01008010, 0x03808050, 0x00900408,
		0x00200841, 0x00800081, 0x20401802, 0x00810004, 0x00808010, 0x00841004, 0x02400060, 0x40804080
	]);
	var MagicBLow = new Int32Array([
		0x20C05100, 0x104200C1, 0x02842900, 0x20204100, 0x40A09821, 0x01028801, 0x10A41002, 0x00842580,
		0x048A1400, 0x02040000, 0x14044120, 0x12020000, 0x208A0002, 0x50C40840, 0x14C60128, 0x04902A00,
		0x120000C0, 0x0C200100, 0x08400020, 0x0C800040, 0x20800510, 0x08843000, 0x08051600, 0x40802010,
		0x00020588, 0x00446441, 0x00420140, 0x0C048882, 0x00110140, 0x20820880, 0x00822881, 0x40045000,
		0x04412802, 0x00480400, 0x3E208420, 0x46200404, 0x00820040, 0x21080501, 0x04080881, 0x44102400,
		0x298C0100, 0x00908881, 0x08884000, 0x41088100, 0x14871400, 0x140540C8, 0x08020050, 0x10840180,
		0x00921019, 0x51A09028, 0x44202000, 0x10004400, 0x01400043, 0x20D12040, 0x02AC4208, 0x10988A4A,
		0x008C8400, 0x02210002, 0x48000021, 0x04800010, 0x0880002B, 0x25C00104, 0x00882100, 0x04842440
	]);
	var MagicBHigh = new Int32Array([
		0x06882004, 0x00822404, 0x00044040, 0x00800002, 0x60400020, 0x00010002, 0x04000344, 0x02120042,
		0x208C0504, 0x000810A1, 0x10A00420, 0x12800014, 0x00800002, 0x0908005A, 0x20850401, 0x20014808,
		0x00080889, 0x10820845, 0x00069084, 0x04094003, 0x00021014, 0x1300484A, 0x008400C6, 0x13424104,
		0x009C8081, 0x01130801, 0x00012041, 0x01C00501, 0x00041048, 0x22001406, 0x4801100A, 0x02A60840,
		0x02026020, 0x40410200, 0x0D880028, 0x01881010, 0x10404A00, 0x00840200, 0x02122850, 0x20150402,
		0x00004401, 0x08908002, 0x00002101, 0x00104004, 0x40008004, 0x000A0050, 0x00040022, 0x03C02014,
		0x08000141, 0x00000B65, 0x00A02A92, 0x00800A0A, 0x00804242, 0x10101001, 0x008A0428, 0x40803004,
		0x18804228, 0x00010802, 0x00820114, 0x00920210, 0x04840502, 0x00444802, 0x44902408, 0x20A0810C
	]);


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

	function restBit(b) {
		return b & (b - 1);
	}

	var BitIndexLow = [ // Mezok 0-32-ig
	31, 30, 3, 29, 2, 17, 7, 28, 1, 9, 11, 16, 6, 14, 27, 23,
	0, 4, 18, 8, 10, 12, 15, 24, 5, 19, 13, 25, 20, 26, 21, 22 ];

	function firstBitLow(b) {
		return BitIndexLow[((b & -b) * 0x077CB531) >>> 27];
	}

	var BitIndexHigh = [ // Mezok 32-64-ig
	63, 62, 35, 61, 34, 49, 39, 60, 33, 41, 43, 48, 38, 46, 59, 55,
	32, 36, 50, 40, 42, 44, 47, 56, 37, 51, 45, 57, 52, 58, 53, 54 ];

	function firstBitHigh(b) {
		return BitIndexHigh[((b & -b) * 0x077CB531) >>> 27];
	}

	function PopCount(b) { // only 32 bit
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
		var Black = 0;     // [W/B]Candidate Elottunk/Mogottunk van
		var White = 0;     // NeighbourMask Mellettunk van, ezert..
		var sq_1 = sq + 8; // Kozvetlen vedo tarsakhoz LEFELE lepunk (NeighbourMask)
		var sq_2 = sq - 8; // Kozvetlen szomszed tarshoz (WCandidateMask), valamint
		                   // Kozvetlen Tamadokhoz (NeighbourMask) FELFELE lepunk
		Black += PopCount(BCandidateMask[sq] & BitBoard[bPawnLow]);
		Black += PopCount(BCandidateMask[BitFixHigh[sq]] & BitBoard[bPawnHigh]);
		White += PopCount(WCandidateMask[BitFixLow[sq_2]] & BitBoard[wPawnLow]);
		White += PopCount(WCandidateMask[sq_2] & BitBoard[wPawnHigh]);

		if (White >= Black) { // Tobbsegben vagyunk -> Jelenlegi tamadok/vedok szama kell
			Black = PopCount(NeighbourMask[sq_2] & BitBoard[BLACK_PAWN << 1 | HighSQMask[sq_2]]);
			White = PopCount(NeighbourMask[sq_1] & BitBoard[WHITE_PAWN << 1 | HighSQMask[sq_1]]);
			if (White >= Black) { // Gyoztunk
				return true;
			}
		}
		return false;
	}

	function BlackCandidatePawn(sq) {
		var Black = 0;     // [W/B]Candidate Elottunk/Mogottunk van
		var White = 0;     // NeighbourMask Mellettunk van, ezert..
		var sq_1 = sq - 8; // Kozvetlen vedo tarsakhoz FELFELE lepunk (NeighbourMask)
		var sq_2 = sq + 8; // Kozvetlen szomszed tarshoz (BCandidateMask), valamint
		                   // Kozvetlen Tamadokhoz (NeighbourMask) LEFELE lepunk
		Black += PopCount(BCandidateMask[sq_2] & BitBoard[bPawnLow]);
		Black += PopCount(BCandidateMask[BitFixHigh[sq_2]] & BitBoard[bPawnHigh]);
		White += PopCount(WCandidateMask[BitFixLow[sq]] & BitBoard[wPawnLow]);
		White += PopCount(WCandidateMask[sq] & BitBoard[wPawnHigh]);

		if (Black >= White) { // Tobbsegben vagyunk -> Jelenlegi tamadok/vedok szama kell
			Black = PopCount(NeighbourMask[sq_1] & BitBoard[BLACK_PAWN << 1 | HighSQMask[sq_1]]);
			White = PopCount(NeighbourMask[sq_2] & BitBoard[WHITE_PAWN << 1 | HighSQMask[sq_2]]);
			if (Black >= White) { // Gyoztunk
				return true;
			}
		}
		return false;
	}

	function WhiteBackwardControl(sq, rank) {
		var sq_1 = sq -  8; // 1 sorral fentebb
		var sq_2 = sq - 16; // 2 sorral fentebb
		if ((CHESS_BOARD[sq_1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
		&& ( NeighbourMask[sq_1] & BitBoard[WHITE_PAWN << 1 | HighSQMask[sq_1]]) != 0 // 1 sorral fentebb mellettem van Feher Gyalog
		&& ((NeighbourMask[sq_1] & BitBoard[BLACK_PAWN << 1 | HighSQMask[sq_1]]) // Kulon-kulon vizsgalok also es felso 32 bitet! Osszekapcsolom "|" ==>
		  | (NeighbourMask[sq_2] & BitBoard[BLACK_PAWN << 1 | HighSQMask[sq_2]])) == 0) { // (1 | 2) sorral fentebb atlosan 1-1 mezot nezek! Nincs Fekete Gyalog
			return false;
		} else if (rank == RANKS.RANK_2 // 2. Sorban also es felso 32 bitet meghatarozza
			   && (CHESS_BOARD[sq_1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
			   && (CHESS_BOARD[sq_2] & 0x07) !== PAWN // Elottem 2 mezovel nincs Gyalog
			   && (NeighbourMask[sq_2] & BitBoard[wPawnHigh]) != 0 // 2 sorral fentebb mellettem van Feher Gyalog ("FELSO BIT")
			   && ((NeighbourMask[sq_2-8] & BitBoard[bPawnLow]) | (BCandidateMask[BitFixHigh[sq]] & BitBoard[bPawnHigh])) == 0) { // Nincs Fekete Gyalog
			   // ((3 sorral fentebb atlosan 1-1 mezot nezek)   | (1-2 sorral fentebb atlosan 1-1 mezo "FELSO BIT")) (rank == 2 miatt also vagy felso 32 bit)
			return false;
		}
		return true;
	}

	function BlackBackwardControl(sq, rank) {
		var sq_1 = sq +  8; // 1 sorral lentebb
		var sq_2 = sq + 16; // 2 sorral lentebb
		if ((CHESS_BOARD[sq_1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
		&& ( NeighbourMask[sq_1] & BitBoard[BLACK_PAWN << 1 | HighSQMask[sq_1]]) != 0 // 1 sorral lentebb mellettem van Fekete Gyalog
		&& ((NeighbourMask[sq_1] & BitBoard[WHITE_PAWN << 1 | HighSQMask[sq_1]]) // Kulon-kulon vizsgalok also es felso 32 bitet! Osszekapcsolom "|" ==>
		  | (NeighbourMask[sq_2] & BitBoard[WHITE_PAWN << 1 | HighSQMask[sq_2]])) == 0) { // (1 | 2) sorral lentebb atlosan 1-1 mezot nezek! Nincs Feher Gyalog
			return false;
		} else if (rank == RANKS.RANK_7 // 7. Sorban also es felso 32 bitet meghatarozza
			   && (CHESS_BOARD[sq_1] & 0x07) !== PAWN // Elottem 1 mezovel nincs Gyalog
			   && (CHESS_BOARD[sq_2] & 0x07) !== PAWN // Elottem 2 mezovel nincs Gyalog
			   && (NeighbourMask[sq_2] & BitBoard[bPawnLow]) != 0 // 2 sorral lentebb mellettem van Fekete Gyalog ("ALSO BIT")
			   && ((NeighbourMask[sq_2+8] & BitBoard[wPawnHigh]) | (WCandidateMask[BitFixLow[sq]] & BitBoard[wPawnLow])) == 0) { // Nincs Feher Gyalog
			   // ((3 sorral lentebb atlosan 1-1 mezot nezek)    | (1-2 sorral lentebb atlosan 1-1 mezot nezek "ALSO BIT")) (rank == 7 miatt also vagy felso 32 bit)
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
	function from_88(sq) { return (sq + (sq & 7)) >> 1; }
	function AttackBBidx(pce, sq, bit) { return (sq << 4) | (pce << 1) | bit; }
	function BetweenBBidx(sq_1, sq_2, bit) { return (sq_1 << 7) | (sq_2 << 1) | bit; }
	function LineIsEmpty(sq_1, sq_2, pieces) { // Szabad az ut ?
		return (pieces.Low & BetweenBBMask[BetweenBBidx(sq_1, sq_2, LOW)]) | (pieces.High & BetweenBBMask[BetweenBBidx(sq_1, sq_2, HIGH)]);
	}

	function Behind(sq_1, sq_2) { // Mezo mogott
		return { Low : BehindBBMask[BetweenBBidx(sq_1, sq_2, LOW)], High : BehindBBMask[BetweenBBidx(sq_1, sq_2, HIGH)] };
	}

	function GetAllPce() { // Osszes Babu
		return { Low : (BitBoard[WhiteLow] | BitBoard[BlackLow]), High : (BitBoard[WhiteHigh] | BitBoard[BlackHigh]) };
	}

	function PceBlocker(pce, sq) { // Blokkolas
		return { Low : BlockerBBMask[AttackBBidx(pce, sq, LOW)], High : BlockerBBMask[AttackBBidx(pce, sq, HIGH)] };
	}

	function PceAttacks(pce, sq) { // Tamadasok
		return { Low : AttackBBMask[AttackBBidx(pce, sq, LOW)], High : AttackBBMask[AttackBBidx(pce, sq, HIGH)] };
	}

	function AllPceByColor(color) { // Babuk szin szerint
		return { Low : BitBoard[color << 1 | LOW], High : BitBoard[color << 1 | HIGH] };
	}

	function AttacksFromDebug(pce, from, pieces) { // Tamadas (Based on Senpai 1.0)
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

	function AttacksFrom(pce, from, pieces) { // Tamadas (Magic BitBoard)
		if (pce === ROOK) {
			var masks = PceBlocker(ROOK, from);
			var index = (((pieces.Low & masks.Low) * MagicRLow[from]) ^ ((pieces.High & masks.High) * MagicRHigh[from])) >>> MagicRShifts[from];
			return { Low  : MagicRAttacks[(from << 13) | (index << 1) | LOW], High : MagicRAttacks[(from << 13) | (index << 1) | HIGH] };
		}
		else if (pce === BISHOP) {
			var masks = PceBlocker(BISHOP, from);
			var index = (((pieces.Low & masks.Low) * MagicBLow[from]) ^ ((pieces.High & masks.High) * MagicBHigh[from])) >>> MagicBShifts[from];
			return { Low  : MagicBAttacks[(from << 13) | (index << 1) | LOW], High : MagicBAttacks[(from << 13) | (index << 1) | HIGH] };
		}
		else if (pce === QUEEN) {
			var RookAttack = AttacksFrom(ROOK, from, pieces);
			var BishopAttack = AttacksFrom(BISHOP, from, pieces);
			return { Low : (RookAttack.Low | BishopAttack.Low), High : (RookAttack.High | BishopAttack.High) };
		}
		else {
			return PceAttacks(pce, from);
		}
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
			makeMove(BIT_MOVE(from, to, CAPTURED, PROMOTED, CASTLING));
			var inCheck = isCheck(currentPlayer);
			unMakeMove();
			MOVE_HISTORY.splice(moveCount); // Elozmeny torlese

			return !inCheck;
		}
		return false;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function isPseudoLegal(from, to, currentPlayer) {

		var fromPiece = CHESS_BOARD[from];
		var toPiece = CHESS_BOARD[to];

		var from_64 = from; // Hack (64)
		from = to_88(from); // 64 -> 120
		to = to_88(to); // 64 -> 120

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
				if (direction == 0 && CHESS_BOARD[from_64 - 3]) { // Queen Side: All square is empty in this direction?!
					return false;
				}
				if (toPiece || CHESS_BOARD[(direction ? from_64 + 1 : from_64 - 1)]) { // All square is empty in this direction?!
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
			} else if (diff === 32 && (fromRow === 0x60 || fromRow === 0x10) && !toPiece && !CHESS_BOARD[from_64 + (direction ? 8 : -8)]) { // double move from start
				// valid
			} else if ((diff === 15 || diff === 17) && toPiece) { // capture
				// valid
			} else if ((diff === 15 || diff === 17) && !toPiece && EN_PASSANT !== 0 && EN_PASSANT === from_88(to)) { // en passant
				// valid en passant
			} else {
				return false;
			}
		}

		if (!nonSlider[fromPiece]) { // sliding piece
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
				if (CHESS_BOARD[from_88(path)]) {
					return false;
				}
			}
		}

		return true;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function GetPvLine(depth) { // Fo lepesvonal
		var count = 0;
		var move = ProbeHash();

		while (move != NOMOVE && count < depth) {
			brd_PvArray[count++] = move;
			makeMove(move.move);
			move = ProbeHash();
		}

		while (boardPly > 0) {
			unMakeMove();
		}

		return count;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function StoreHash(move, score, flags, depth) { // Hash mentes

		var index = brd_hashKeyLow & HASHMASK;

		if (hash_keyLow[index] == 0) { // new
			hashUsed++;
		}

		if (score > ISMATE) {
			score += boardPly;
		} else if (score < -ISMATE) {
			score -= boardPly;
		}

		hash_move[index]    = move;
		hash_flags[index]   = flags;
		hash_depth[index]   = depth;
		hash_score[index]   = score;
		hash_keyLow[index]  = brd_hashKeyLow;
		hash_keyHigh[index] = brd_hashKeyHigh;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function ProbeHash() { // Hash kiolvasas

		var index = brd_hashKeyLow & HASHMASK;

		if (hash_keyLow[index] == brd_hashKeyLow && hash_keyHigh[index] == brd_hashKeyHigh) {
			return {
				move  : hash_move[index],
				flags : hash_flags[index],
				depth : hash_depth[index],
				score : hash_score[index]
			};
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
		brd_hashKeyLow  ^= PieceKeysLow[ (pce << 6) | sq];
		brd_hashKeyHigh ^= PieceKeysHigh[(pce << 6) | sq];
		if ((pce & 0x07) === PAWN) {
			brd_pawnKeyLow  ^= PieceKeysLow[ (pce << 6) | sq];
			brd_pawnKeyHigh ^= PieceKeysHigh[(pce << 6) | sq];
		}
	}
	function HASH_CA() {
		brd_hashKeyLow  ^= CastleKeysLow[castleRights];
		brd_hashKeyHigh ^= CastleKeysHigh[castleRights];
	}
	function HASH_EP() {
		brd_hashKeyLow  ^= PieceKeysLow[EN_PASSANT];
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
			DELETE_PCE(PROMOTED_PIECE, from, currentPlayer);
			ADDING_PCE((currentPlayer | PAWN), from, currentPlayer);
		}
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function isMate(Score) { return Score > ISMATE || Score < -ISMATE; }

	function isCheck(Side) { return isSquareUnderAttack(brd_pieceList[(Side | KING) << 4], Side); }


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function isSquareUnderAttack(target, us) {

		var bb, from;
		var them = us^8; // Ellenfel

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

		// Akivel lepunk
		var PCE = PROMOTED(move) ? PROMOTED(move) & 0x07 : CHESS_BOARD[from] & 0x07;

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Gyalog Sakk?
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
		HighSQMask[from] ? xPiecesBB.High &= ClearMask[from] : xPiecesBB.Low &= ClearMask[from];
		HighSQMask[to]   ? xPiecesBB.High |= SetMask[to]     : xPiecesBB.Low |= SetMask[to];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Sancolas
		if (move & CASTLED_MASK)
		{
			switch(to) {
				case SQUARES.C1: var RookFrom = SQUARES.A1; var RookTo = SQUARES.D1; break;
				case SQUARES.C8: var RookFrom = SQUARES.A8; var RookTo = SQUARES.D8; break;
				case SQUARES.G1: var RookFrom = SQUARES.H1; var RookTo = SQUARES.F1; break;
				case SQUARES.G8: var RookFrom = SQUARES.H8; var RookTo = SQUARES.F8; break;
				default: break;
			}

			// Kiraly torlese + Bastya Mozgatasa
			HighSQMask[from] ?
			 xPiecesBB.High = (xPiecesBB.High ^ SetMask[to] ^ SetMask[RookFrom]) | SetMask[RookTo]
			: xPiecesBB.Low = (xPiecesBB.Low  ^ SetMask[to] ^ SetMask[RookFrom]) | SetMask[RookTo];

			// Hack: Bastya tamadas!
			PCE = ROOK; to = RookTo;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Direkt Sakk?
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
			HighSQMask[epSq] ? xPiecesBB.High &= ClearMask[epSq] : xPiecesBB.Low &= ClearMask[epSq];

			// Mogotte megnyilo mezok!
			Beyond.Low  |= BehindBBMask[BetweenBBidx(King, epSq, LOW)];
			Beyond.High |= BehindBBMask[BetweenBBidx(King, epSq, HIGH)];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Felfedezett Sakk?
		if (Beyond.Low != 0 || Beyond.High != 0)
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
		HighSQMask[from] ? xPiecesBB.High &= ClearMask[from] : xPiecesBB.Low &= ClearMask[from];
		HighSQMask[to]   ? xPiecesBB.High |= SetMask[to]     : xPiecesBB.Low |= SetMask[to];

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var Beyond = Behind(King, from); // Babu mogott megnyilo mezok

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// En Passant
		if (PCE === PAWN && CHESS_BOARD[to] == 0 && (move & CAPTURE_MASK))
		{
			var epSq = us === BLACK ? to-8 : to+8;

			// Ellenfel torlese
			HighSQMask[epSq] ? xPiecesBB.High &= ClearMask[epSq] : xPiecesBB.Low &= ClearMask[epSq];

			// Mogotte megnyilo mezok!
			Beyond.Low  |= BehindBBMask[BetweenBBidx(King, epSq, LOW)];
			Beyond.High |= BehindBBMask[BetweenBBidx(King, epSq, HIGH)];
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Felfedezett Sakk?
		if (Beyond.Low != 0 || Beyond.High != 0)
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

	var mob_score = new Array(29);

	for (var i = 0; i <= 28; i++)
	{
		mob_score[i] = -30 + 16.3 * Math.sqrt(Math.min(i, 14)) | 0; // was -20 + 13.0
	}

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
		var mgWhite      = 0; // Kezdo Feher
		var mgBlack      = 0; // Kezdo Fekete
		var egWhite      = 0; // Vegjatek Feher
		var egBlack      = 0; // Vegjatek Fekete
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
	//							   DONTETLEN
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

		var mobS = 0; var mobE = 0;

		var attS = 0; var attE = 0;

		var kingS = 0; var kingE = 0;

		var rooksS = 0; var rooksE = 0;

		var pawnsS = 0; var pawnsE = 0;

		var queensS = 0; var queensE = 0;

		var knightsS = 0; var knightsE = 0;

		var bishopsS = 0; var bishopsE = 0;

		var trappedS = 0; var trappedE = 0;

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var xPiecesBB = GetAllPce();
		var wAttacks  = { Low : 0, High : 0 }; wPawnAttacks(wAttacks);
		var bAttacks  = { Low : 0, High : 0 }; bPawnAttacks(bAttacks);

		var wPassedPawn = new Array(); LeastWhitePawn = 0x88888888;
		var bPassedPawn = new Array(); LeastBlackPawn = 0x11111111;

		var hash = brd_PawnTable[brd_pawnKeyLow & PAWNMASK];

		if (hash != null && hash.pawnLockKey == brd_pawnKeyHigh) {

			pawnsS         = hash.scoreS;
			pawnsE         = hash.scoreE;
			wPassedPawn    = hash.wPassed;
			bPassedPawn    = hash.bPassed;
			LeastWhitePawn = hash.wLeastPawn;
			LeastBlackPawn = hash.bLeastPawn;

		} else {

			var eval = EvalPawns(wPassedPawn, bPassedPawn);

			pawnsS = eval.scoreS; // Hack: Pont atvetele!
			pawnsE = eval.scoreE;

			brd_PawnTable[brd_pawnKeyLow & PAWNMASK] = { // max 168 byte
				scoreS      : pawnsS, // 8 byte
				scoreE      : pawnsE, // 8 byte
				wPassed     : wPassedPawn, // n* 8 byte
				bPassed     : bPassedPawn, // n* 8 byte
				wLeastPawn  : LeastWhitePawn, // 8 byte
				bLeastPawn  : LeastBlackPawn, // 8 byte
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
	//							   BABUK ERTEKELESE
	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Feher Kiraly
		var wKing = brd_pieceList[WHITE_KING << 4];
		var wKingRank = TableRanks[wKing]; // Kiraly sora
		var wKingFile = TableFiles[wKing]; // Kiraly oszlopa
		var WKZ = PceAttacks(KING, wKing); // Kiraly zonak
		var wKingAttacks = { Low : WKZ.Low, High : WKZ.High };
		WKZ.Low  |= WKZ.Low   <<  8;
		WKZ.Low  |= WKZ.High >>> 24;
		WKZ.High |= WKZ.High  <<  8;
		WKZ.Low  &= bPawnSafe.Low;
		WKZ.High &= bPawnSafe.High;
		WKZ.Low  |= BitBoard[wKingLow];
		WKZ.High |= BitBoard[wKingHigh];
		mgWhite  += KingMask[wKing];
		egWhite  += KingEndMask[wKing];

	// Fekete Kiraly
		var bKing = brd_pieceList[BLACK_KING << 4];
		var bKingRank = TableRanks[bKing]; // Kiraly sora
		var bKingFile = TableFiles[bKing]; // Kiraly oszlopa
		var BKZ = PceAttacks(KING, bKing); // Kiraly zonak
		var bKingAttacks = { Low : BKZ.Low, High : BKZ.High };
		BKZ.High |= BKZ.High >>>  8;
		BKZ.High |= BKZ.Low   << 24;
		BKZ.Low  |= BKZ.Low  >>>  8;
		BKZ.Low  &= wPawnSafe.Low;
		BKZ.High &= wPawnSafe.High;
		BKZ.Low  |= BitBoard[bKingLow];
		BKZ.High |= BitBoard[bKingHigh];
		mgBlack  += KingMask[TableMirror[bKing]];
		egBlack  += KingEndMask[TableMirror[bKing]];

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

	// Gyalog fenyegetes
		threats += PawnCapture(wAttacks, BLACK);
		threats -= PawnCapture(bAttacks, WHITE);

	// Kiraly fenyegetes
		threats += CaptureScore(wKingAttacks, wPawnSafe, KING, BLACK);
		threats -= CaptureScore(bKingAttacks, bPawnSafe, KING, WHITE);

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
			if ((bb.Low & BKZ.Low) | (bb.High & BKZ.High)) {
				wAttackCount++;
				wAttackPower += 4;
			}

			Phase -= 4;
			mobS += mob_score[mob];
			mobE += mob_score[mob];
			mgWhite += QueenMask[PCE];
			egWhite += QueenEndMask[PCE];

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
			if ((bb.Low & WKZ.Low) | (bb.High & WKZ.High)) {
				bAttackCount++;
				bAttackPower += 4;
			}

			Phase -= 4;
			mobS -= mob_score[mob];
			mobE -= mob_score[mob];
			mgBlack += QueenMask[TableMirror[PCE]];
			egBlack += QueenEndMask[TableMirror[PCE]];

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
				if (IsOpenFile(File, BLACK) == 0) { // Teljesen Nyitott
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
			if ((bb.Low & BKZ.Low) | (bb.High & BKZ.High)) {
				wAttackCount++;
				wAttackPower += 2;
			}

			Phase -= 2;
			mobS += mob_score[mob];
			mobE += mob_score[mob];
			mgWhite += RookMask[PCE];

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
				if (IsOpenFile(File, WHITE) == 0) { // Teljesen Nyitott
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
			if ((bb.Low & WKZ.Low) | (bb.High & WKZ.High)) {
				bAttackCount++;
				bAttackPower += 2;
			}

			Phase -= 2;
			mobS -= mob_score[mob];
			mobE -= mob_score[mob];
			mgBlack += RookMask[TableMirror[PCE]];

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
			if ((bb.Low & BKZ.Low) | (bb.High & BKZ.High)) {
				wAttackCount++;
				wAttackPower += 1;
			}

			Phase -= 1;
			mobS += mob_score[mob];
			mobE += mob_score[mob];
			mgWhite += BishopMask[PCE];
			egWhite += BishopEndMask[PCE];

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
			if ((bb.Low & WKZ.Low) | (bb.High & WKZ.High)) {
				bAttackCount++;
				bAttackPower += 1;
			}

			Phase -= 1;
			mobS -= mob_score[mob];
			mobE -= mob_score[mob];
			mgBlack += BishopMask[TableMirror[PCE]];
			egBlack += BishopEndMask[TableMirror[PCE]];

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
			if ((bb.Low & BKZ.Low) | (bb.High & BKZ.High)) {
				wAttackCount++;
				wAttackPower += 1;
			}

			Phase -= 1;
			mobS += mob_score[mob];
			mobE += mob_score[mob];
			mgWhite += KnightMask[PCE];
			egWhite += KnightEndMask[PCE];

			var outpost = KnightOutpost[PCE]; // Huszar Orszem

			if (outpost && DefendedByBPawn(PCE) == 0) { // Nincs fenyegetes
				knightsS += outpost * PopCount(DefendedByWPawn(PCE));
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
			if ((bb.Low & WKZ.Low) | (bb.High & WKZ.High)) {
				bAttackCount++;
				bAttackPower += 1;
			}

			Phase -= 1;
			mobS -= mob_score[mob];
			mobE -= mob_score[mob];
			mgBlack += KnightMask[TableMirror[PCE]];
			egBlack += KnightEndMask[TableMirror[PCE]];

			var outpost = KnightOutpost[TableMirror[PCE]]; // Huszar Orszem

			if (outpost && DefendedByWPawn(PCE) == 0) { // Nincs fenyegetes
				knightsS -= outpost * PopCount(DefendedByBPawn(PCE));
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

			if (Rank >= RANKS.RANK_4) {

				PassedMG  = 60; // Alap Pont Kozepjatek
				PassedEG  = 90; // Alap Pont Vegjatek
				PassedEG -=  5 * DISTANCE[wKing][PCE-8]; // Kiraly Tavolsag Sajat
				PassedEG += 20 * DISTANCE[bKing][PCE-8]; // Kiraly Tavolsag Ellenfel

				if (!bBigPieces && UnstoppablePawn(wKing, bKing, xPiecesBB, PCE, WHITE, File-1)) { // Megallithatatlan

					PassedEG += 800;

				} else if (CHESS_BOARD[PCE-8] == 0) { // Szabad Telt Gyalog

					var unsafe = (bKingAttacks.Low & ~(wKingAttacks.Low | wAttacks.Low)) | bAttacks.Low;
					var front  = { High : WOpenFileMask[BitFixHigh[PCE]], Low : WOpenFileMask[PCE] };
					var rear   = { Low  : BOpenFileMask[BitFixLow[PCE]], High : BOpenFileMask[PCE] };

					if (FreePawn(unsafe, front.Low, rear, xPiecesBB, PCE, BLACK, LOW)) { // Szabad
						PassedMG += 40;
						PassedEG += 60;
					}
					PassedMG += 20;
					PassedEG += 30;
				}
			}

			pawnsS += 10 + (PassedMG * PawnPassed[Rank]) | 0;
			pawnsE += 20 + (PassedEG * PawnPassed[Rank]) | 0;
		}

	// Fekete Telt Gyalog
		for (var idx = 0; idx < bPassedPawn.length; idx++)
		{
			PCE = bPassedPawn[idx];
			Rank = TableRanks[PCE];
			File = TableFiles[PCE];

			if (Rank <= RANKS.RANK_5) {

				PassedMG  = 60; // Alap Pont Kozepjatek
				PassedEG  = 90; // Alap Pont Vegjatek
				PassedEG -=  5 * DISTANCE[bKing][PCE+8]; // Kiraly Tavolsag Sajat
				PassedEG += 20 * DISTANCE[wKing][PCE+8]; // Kiraly Tavolsag Ellenfel

				if (!wBigPieces && UnstoppablePawn(bKing, wKing, xPiecesBB, PCE, BLACK, File+55)) { // Megallithatatlan

					PassedEG += 800;

				} else if (CHESS_BOARD[PCE+8] == 0) { // Szabad Telt Gyalog

					var unsafe = (wKingAttacks.High & ~(bKingAttacks.High | bAttacks.High)) | wAttacks.High;
					var front  = { Low  : BOpenFileMask[BitFixLow[PCE]], High : BOpenFileMask[PCE] };
					var rear   = { High : WOpenFileMask[BitFixHigh[PCE]], Low : WOpenFileMask[PCE] };

					if (FreePawn(unsafe, front.High, rear, xPiecesBB, PCE, WHITE, HIGH)) { // Szabad
						PassedMG += 40;
						PassedEG += 60;
					}
					PassedMG += 20;
					PassedEG += 30;
				}
			}

			pawnsS -= 10 + (PassedMG * PawnPassed[9-Rank]) | 0;
			pawnsE -= 20 + (PassedEG * PawnPassed[9-Rank]) | 0;
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (wCanAttack)
		{
			wAttackCount = Math.min(wAttackCount, 7); // Max 7 tamado
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

			if (castleRights & CASTLEBIT.BKCA) { // Sancolhat Kiraly oldal
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

			if (castleRights & CASTLEBIT.BQCA) { // Sancolhat Vezer oldal
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
			bAttackCount = Math.min(bAttackCount, 7); // Max 7 tamado
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

			if (castleRights & CASTLEBIT.WKCA) { // Sancolhat Kiraly oldal
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

			if (castleRights & CASTLEBIT.WQCA) { // Sancolhat Vezer oldal
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

		var materialS = brd_Material[WHITE] - brd_Material[BLACK]; // Anyag ertekelese
		var materialE = materialS + (wNumPawns * 10) - (bNumPawns * 10); // Ertek atadasa

		materialS += mgWhite - mgBlack;
		materialE += egWhite - egBlack;

		var evalS = materialS;
		var evalE = materialE;

		evalS += mobS;
		evalE += mobE;

		evalS += threats;
		evalE += threats;

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

		// Linearis interpolacio kezdo es vegjatek kozott
		Phase = (Phase << 8) / 24 + 0.5 | 0;
		var Score = ((evalS * (256 - Phase)) + (evalE * Phase)) >> 8;

		Score = Score / Draw | 0; // Ketes dontetlennel nem 0-at adunk vissza!

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (ShowEvalForUI === true) {
			return '\n'
			+' Eval term |           MG           |           EG           |\n'
			+'-----------|------------------------|------------------------|\n'
			+' tempo     | '+evalStr(tempoS)   +' | '+evalStr(tempoE)   +' |\n'
			+' pawns     | '+evalStr(pawnsS)   +' | '+evalStr(pawnsE)   +' |\n'
			+' knights   | '+evalStr(knightsS) +' | '+evalStr(knightsE) +' |\n'
			+' bishops   | '+evalStr(bishopsS) +' | '+evalStr(bishopsE) +' |\n'
			+' rooks     | '+evalStr(rooksS)   +' | '+evalStr(rooksE)   +' |\n'
			+' queens    | '+evalStr(queensS)  +' | '+evalStr(queensE)  +' |\n'
			+' king      | '+evalStr(kingS)    +' | '+evalStr(kingE)    +' |\n'
			+' material  | '+evalStr(materialS)+' | '+evalStr(materialE)+' |\n'
			+' attacks   | '+evalStr(attS)     +' | '+evalStr(attE)     +' |\n'
			+' mobility  | '+evalStr(mobS)     +' | '+evalStr(mobE)     +' |\n'
			+' trapped   | '+evalStr(trappedS) +' | '+evalStr(trappedE) +' |\n'
			+' threats   | '+evalStr(threats)  +' | '+evalStr(threats)  +' |\n'
			+'-----------|------------------------|------------------------|\n'
			+' Total     | '+evalStr(evalS)    +' | '+evalStr(evalE)    +' |\n\n'
			+' Total Eval: '+(Score / 100).toFixed(2);
		}

	// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		return currentPlayer === WHITE ? Score : -Score;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function WhiteKingShield(File) {
		var bits = 8-File << 2;
		var mask = 0xF << bits;
		return PawnShelter[8 - ((LeastWhitePawn & mask) >>> bits)];
	}

	function BlackKingShield(File) {
		var bits = 8-File << 2;
		var mask = 0xF << bits;
		return PawnShelter[((LeastBlackPawn & mask) >>> bits) - 1];
	}

	function WhitePawnStorm(File) {
		if (FileBBMask[File] & BitBoard[wPawnLow] & RankBBMask[RANKS.RANK_6]) {
			return 60;
		} else if (FileBBMask[File] & BitBoard[wPawnLow] & RankBBMask[RANKS.RANK_5]) {
			return 30;
		} else if (FileBBMask[File] & BitBoard[wPawnHigh] & RankBBMask[RANKS.RANK_4]) {
			return 10;
		}
		return 0;
	}

	function BlackPawnStorm(File) {
		if (FileBBMask[File] & BitBoard[bPawnHigh] & RankBBMask[RANKS.RANK_3]) {
			return 60;
		} else if (FileBBMask[File] & BitBoard[bPawnHigh] & RankBBMask[RANKS.RANK_4]) {
			return 30;
		} else if (FileBBMask[File] & BitBoard[bPawnLow] & RankBBMask[RANKS.RANK_5]) {
			return 10;
		}
		return 0;
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


	var attacker_weight = [ 0, 0, 4, 4, 2, 1, 4 ];
	var attacked_weight = [ 0, 0, 1, 1, 2, 4, 8 ];

	function CaptureScore(attacks, pawnSafe, pce, enemy) {

		var weak = { Low  : attacks.Low  & BitBoard[enemy << 1 | LOW]  & ~BitBoard[(enemy|PAWN) << 1 | LOW],
		             High : attacks.High & BitBoard[enemy << 1 | HIGH] & ~BitBoard[(enemy|PAWN) << 1 | HIGH] };

		if ((weak.Low | weak.High) == 0) return 0; // no threats!

		if (pce >= ROOK) {
			weak.Low  &= pawnSafe.Low  & ~BitBoard[(enemy|pce) << 1 | LOW]; // Not equal and not defended by pawn..
			weak.High &= pawnSafe.High & ~BitBoard[(enemy|pce) << 1 | HIGH];

			for (var piece = pce+1; piece <= KING; piece++) { // ..or greater than us!
				weak.Low  |= attacks.Low  & BitBoard[(enemy|piece) << 1 | LOW];
				weak.High |= attacks.High & BitBoard[(enemy|piece) << 1 | HIGH];
			}
		}

		var sc = 0;
		for (var bb = weak.Low;  bb != 0; bb = restBit(bb)) sc += attacked_weight[CHESS_BOARD[firstBitLow(bb)]  & 0x07];
		for (var bb = weak.High; bb != 0; bb = restBit(bb)) sc += attacked_weight[CHESS_BOARD[firstBitHigh(bb)] & 0x07];

		return attacker_weight[pce] * sc * 4;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	var p_attacked_sc = [ 0, 5, 28, 28, 45, 95, 0 ];

	function PawnCapture(attacks, enemy) {

		var weak = { Low  : attacks.Low  & BitBoard[enemy << 1 | LOW]  & ~BitBoard[(enemy|PAWN) << 1 | LOW],
		             High : attacks.High & BitBoard[enemy << 1 | HIGH] & ~BitBoard[(enemy|PAWN) << 1 | HIGH] };

		var sc = 0;
		for (var bb = weak.Low;  bb != 0; bb = restBit(bb)) sc += p_attacked_sc[CHESS_BOARD[firstBitLow(bb)]  & 0x07];
		for (var bb = weak.High; bb != 0; bb = restBit(bb)) sc += p_attacked_sc[CHESS_BOARD[firstBitHigh(bb)] & 0x07];

		return sc;
	}


// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


	function EvalPawns(wPassedPawn, bPassedPawn) {

		var PCE = 0
		var scoreS = 0;
		var scoreE = 0;

		var pieceIdx = WHITE_PAWN << 4;
		PCE = brd_pieceList[pieceIdx++];
		while (PCE != EMPTY)
		{
			var Open = 0; // Nyitott
			var Rank = TableRanks[PCE];
			var File = TableFiles[PCE];
			var bits  = 8-File << 2;
			var mask  = 0xF << bits;
			var lRank = (LeastWhitePawn & mask) >>> bits;

			if (Rank < lRank) { // Leghatso Feher Gyalog
				LeastWhitePawn = (LeastWhitePawn & ~mask) | (Rank << bits);
			}

			if (BlackOpenFile(PCE) != 0) { // Dupla Gyalog
				scoreS += PawnDoubled;
				scoreE += PawnDoubled * 2;
			}

			if (WhiteOpenFile(PCE) == 0 && WhiteMostPawn(PCE) == 0) { // Legelso Gyalog + Nyitott
				Open = 1;
			}

			if (IsolatedPawn(PCE, WHITE) == 0) { // Elkulonitett Gyalog
				scoreS += PawnIsolated + PawnIsolated * Open;
				scoreE += PawnIsolated * 2;
			} else if (WhiteBackwardPawn(PCE) == 0 && WhiteBackwardControl(PCE, Rank)) { // Hatrahagyott Gyalog
				scoreS += PawnBackward + PawnBackward * Open;
				scoreE += PawnBackward - 2;
			}

			if (Open) {
				if (WhitePassedPawn(PCE) == 0) { // Telt Gyalog

					wPassedPawn[wPassedPawn.length] = PCE;

				} else if (WhiteCandidatePawn(PCE)) { // Jelolt Gyalog
					scoreS +=  5 +  50 * PawnPassed[Rank];
					scoreE += 10 + 100 * PawnPassed[Rank];
				}
			}

			scoreS += PawnMask[PCE];

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
			var bits  = 8-File << 2;
			var mask  = 0xF << bits;
			var lRank = (LeastBlackPawn & mask) >>> bits;

			if (Rank > lRank) { // Leghatso Fekete Gyalog
				LeastBlackPawn = (LeastBlackPawn & ~mask) | (Rank << bits);
			}

			if (WhiteOpenFile(PCE) != 0) { // Dupla Gyalog
				scoreS -= PawnDoubled;
				scoreE -= PawnDoubled * 2;
			}

			if (BlackOpenFile(PCE) == 0 && BlackMostPawn(PCE) == 0) { // Legelso Gyalog + Nyitott
				Open = 1;
			}

			if (IsolatedPawn(PCE, BLACK) == 0) { // Elkulonitett Gyalog
				scoreS -= PawnIsolated + PawnIsolated * Open;
				scoreE -= PawnIsolated * 2;
			} else if (BlackBackwardPawn(PCE) == 0 && BlackBackwardControl(PCE, Rank)) { // Hatrahagyott Gyalog
				scoreS -= PawnBackward + PawnBackward * Open;
				scoreE -= PawnBackward - 2;
			}

			if (Open) {
				if (BlackPassedPawn(PCE) == 0) { // Telt Gyalog

					bPassedPawn[bPassedPawn.length] = PCE;

				} else if (BlackCandidatePawn(PCE)) { // Jelolt Gyalog
					scoreS -=  5 +  50 * PawnPassed[9-Rank];
					scoreE -= 10 + 100 * PawnPassed[9-Rank];
				}
			}

			scoreS -= PawnMask[TableMirror[PCE]];

			PCE = brd_pieceList[pieceIdx++]; // Kovetkezo Babu
		}

		return { scoreS : scoreS, scoreE : scoreE };
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

		if (capturesOnly === false) // Sancolas
		{
			if (currentPlayer === WHITE) // Feher oldal
			{
				if (castleRights & CASTLEBIT.WKCA) { // Kiraly oldal
					if (CHESS_BOARD[SQUARES.F1] == 0 && CHESS_BOARD[SQUARES.G1] == 0) {
						if (!isSquareUnderAttack(SQUARES.E1, WHITE) && !isSquareUnderAttack(SQUARES.F1, WHITE)) {
							AddQuietMove(SQUARES.E1, SQUARES.G1, 0, 1);
						}
					}
				}
				if (castleRights & CASTLEBIT.WQCA) { // Vezer oldal
					if (CHESS_BOARD[SQUARES.D1] == 0 && CHESS_BOARD[SQUARES.C1] == 0 && CHESS_BOARD[SQUARES.B1] == 0) {
						if (!isSquareUnderAttack(SQUARES.E1, WHITE) && !isSquareUnderAttack(SQUARES.D1, WHITE)) {
							AddQuietMove(SQUARES.E1, SQUARES.C1, 0, 1);
						}
					}
				}

			} else { // Fekete oldal

				if (castleRights & CASTLEBIT.BKCA) { // Kiraly oldal
					if (CHESS_BOARD[SQUARES.F8] == 0 && CHESS_BOARD[SQUARES.G8] == 0) {
						if (!isSquareUnderAttack(SQUARES.E8, BLACK) && !isSquareUnderAttack(SQUARES.F8, BLACK)) {
							AddQuietMove(SQUARES.E8, SQUARES.G8, 0, 1);
						}
					}
				}
				if (castleRights & CASTLEBIT.BQCA) { // Vezer oldal
					if (CHESS_BOARD[SQUARES.D8] == 0 && CHESS_BOARD[SQUARES.C8] == 0 && CHESS_BOARD[SQUARES.B8] == 0) {
						if (!isSquareUnderAttack(SQUARES.E8, BLACK) && !isSquareUnderAttack(SQUARES.D8, BLACK)) {
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
				checks.Low |= SetMask[from];
				unsafe.Low |= BetweenBBMask[BetweenBBidx(from, King, LOW)] | BehindBBMask[BetweenBBidx(from, King, LOW)];
			}
		}
		for (bb = b.High; bb != 0; bb = restBit(bb)) {
			from = firstBitHigh(bb);
			if (LineIsEmpty(from, King, xPiecesBB) == 0) {
				checks.High |= SetMask[from];
				unsafe.High |= BetweenBBMask[BetweenBBidx(from, King, HIGH)] | BehindBBMask[BetweenBBidx(from, King, HIGH)];
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		// Kiraly lepesei
		var attacks = PceAttacks(KING, King);
		for (bb = attacks.Low & ~unsafe.Low & ~friendsBB.Low; bb != 0; bb = restBit(bb)) {
			next = firstBitLow(bb);
			if (CHESS_BOARD[next] && (CHESS_BOARD[next] & 0x8) !== currentPlayer) // Ellenfel
			{
				Score = 1000006 + ((100 * MvvLvaScores[CHESS_BOARD[next]]) - MvvLvaScores[KING]); // Pontszam

				AddCaptureMove(BIT_MOVE(King, next, 1, 0, 0), Score);
			} else {
				AddQuietMove(King, next, 0, 0); // Ures mezo
			}
		}
		for (bb = attacks.High & ~unsafe.High & ~friendsBB.High; bb != 0; bb = restBit(bb)) {
			next = firstBitHigh(bb);
			if (CHESS_BOARD[next] && (CHESS_BOARD[next] & 0x8) !== currentPlayer) // Ellenfel
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

			var hashData = ProbeHash();

			if (hashData != NOMOVE) {

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
		inCheck ? GenerateEvasions() : GenerateAllMoves(true, false);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; ++index)
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
		var staticEval = -INFINITE;
		var is_pv = (beta != alpha + 1);

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var hashData = ProbeHash(); // Atultetesi tabla

		if (!is_pv && hashData != NOMOVE && hashData.depth >= depth) {

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

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (!is_pv && !inCheck
		&& (brd_pieceCount[currentPlayer | KNIGHT] != 0
		 || brd_pieceCount[currentPlayer | BISHOP] != 0
		 || brd_pieceCount[currentPlayer | ROOK]   != 0
		 || brd_pieceCount[currentPlayer | QUEEN]  != 0)) { // Metszheto csomopont
			pruneNode = true;
			if (nullMove || depth <= 4) staticEval = Evaluation(); // Futility depth
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

			if (depth <= 3 && hashData == NOMOVE) { // Razoring based on Toga II 3.0
				var threshold = beta - 240 - depth * 60;
				if (staticEval < threshold && PawnOnSeventh() == 0) {
					Score = Quiescence(threshold-1, threshold, DEPTH_ZERO, NOT_IN_CHECK);
					if (Score < threshold) return Score;
				}
			}
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (is_pv && boardPly != 0 && depth >= 4 && hashData == NOMOVE) { // Belso iterativ melyites /IID/
			Score = AlphaBeta(alpha, beta, depth-2, 0, inCheck);
			if (Score > alpha) hashData = ProbeHash();
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

		if (hashData != NOMOVE) { // Atultetesi tablabol lepes
			for (var index = brd_moveStart[boardPly]; index < brd_moveStart[boardPly + 1]; ++index)
			{
				if (brd_moveList[index] == hashData.move) { // Elore soroljuk
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

				if (Score > alpha) {

					if (boardPly == 0) {
						UpdatePv(currentMove, Score, depth, alpha, beta);
					}

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

						StoreHash(currentMove, Score, FLAG_BETA, depth);

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
			StoreHash(BestMove, BestScore, FLAG_EXACT, depth);
		} else {
			StoreHash(BestMove, BestScore, FLAG_ALPHA, depth);
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
		brd_PawnTable = null; // Hash tabla urites
		brd_PawnTable = new Array(PAWNENTRIES);
		hash_move     = new Uint32Array(HASHENTRIES);
		hash_flags    = new Uint8Array(HASHENTRIES);
		hash_depth    = new Uint8Array(HASHENTRIES);
		hash_score    = new Int16Array(HASHENTRIES);
		hash_keyLow   = new Int32Array(HASHENTRIES);
		hash_keyHigh  = new Int32Array(HASHENTRIES);
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

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		if (UI_HOST == HOST_TANKY && maxSearchDepth > 0) { // Also szint
			maxDepth = maxSearchDepth;
		} else {
			maxDepth = 64;
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		var inCheck = isCheck(currentPlayer); // Sakk..?

		inCheck ? GenerateEvasions() : GenerateAllMoves(false, false);

		for (var index = brd_moveStart[0]; index < brd_moveStart[1]; ++index)
		{
			if (!isLegal(brd_moveList[index])) { // Ervenytelen lepes
				continue;
			}

			countMove++; // Lepesek szamolasa
		}

		// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

		startTime = Date.now(); // Kezdo ido

		if (UI_HOST == HOST_TANKY) postMessage(['StartedTime', startTime]); // Kuldes!

		search :

		for (currDepth = 1; currDepth <= maxSearchDepth; currDepth++) { // Iterativ melyites

			if (countMove == 1 && currDepth > 5 && bestMove) break; // Egy ervenyes lepes

			for (var margin = (currDepth >= 4 ? 10 : INFINITE); ; margin *= 2) { // ablak

				alpha = Math.max(Score - margin, -INFINITE);
				beta  = Math.min(Score + margin,  INFINITE);

				Score = AlphaBeta(alpha, beta, currDepth, 1, inCheck);

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


	function UpdatePv(Move, Score, depth, alpha, beta) {

		var flags = FLAG_NONE;
		if (Score > alpha) flags |= FLAG_BETA;
		if (Score < beta)  flags |= FLAG_ALPHA;

		StoreHash(Move, Score, flags, depth);

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


	var HOST_WEB = 0;
	var HOST_TANKY = 1;
	var HOST_JSUCI = 2;
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

					    maxSearchTime  = getInt('movetime', 0, tokens); // Ido Parameter
					var maxSearchDepth = getInt('depth', 0, tokens); // Melyseg Parameter

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
						}

						if (maxSearchDepth > 0) { // Fix melysegnel max 1 ora
							maxSearchTime = 1000 * 3600;
						}

						if (maxSearchDepth <= 0) { // Max melyseg
							maxSearchDepth = 64;
						}

						SearchPosition(maxSearchDepth); // Kereses

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
							HASHMASK = HASHENTRIES - 1;
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


	function evalStr(n) {
		n = (n / 100).toFixed(2);
		var str = n.toString();
		for (var i = (22 - str.length) / 2; i > 0; i--) str = ' '+str+' ';
		return str.substr(0, 22);
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
				PieceKeysLow[ (pce << 6) | sq] = RAND_32();
				PieceKeysHigh[(pce << 6) | sq] = RAND_32();
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
				brd_hashKeyLow  ^= PieceKeysLow[ (CHESS_BOARD[sq] << 6) | sq];
				brd_hashKeyHigh ^= PieceKeysHigh[(CHESS_BOARD[sq] << 6) | sq];
			}
			if ((CHESS_BOARD[sq] & 0x07) === PAWN) { // Gyalog Key
				brd_pawnKeyLow  ^= PieceKeysLow[ (CHESS_BOARD[sq] << 6) | sq];
				brd_pawnKeyHigh ^= PieceKeysHigh[(CHESS_BOARD[sq] << 6) | sq];
			}
		}

		if (currentPlayer == WHITE) { // Aki lephet
			brd_hashKeyLow  ^= SideKeyLow;
			brd_hashKeyHigh ^= SideKeyHigh;
		}

		if (EN_PASSANT != 0) { // En Passant
			brd_hashKeyLow  ^= PieceKeysLow[EN_PASSANT];
			brd_hashKeyHigh ^= PieceKeysHigh[EN_PASSANT];
		}

		brd_hashKeyLow  ^= CastleKeysLow[castleRights]; // Sancolas
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

		castleRights = 0; // Sancolas nullazasa

		for (index = 0; index < Fen[2].length; index++) { // Sancolasok
			switch(Fen[2][index]) {
				case 'K': castleRights |= CASTLEBIT.WKCA; break; // White King side
				case 'Q': castleRights |= CASTLEBIT.WQCA; break; // White Queen side
				case 'k': castleRights |= CASTLEBIT.BKCA; break; // Black King side
				case 'q': castleRights |= CASTLEBIT.BQCA; break; // Black Queen side
				default: break;
			}
		}

		if (Fen[3] == '-') { // Nincs En Passant
			EN_PASSANT = 0;
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

	// Kiraly
	var KingMask = [
	-40, -30, -50, -70, -70, -50, -30, -40,
	-30, -20, -40, -60, -60, -40, -20, -30,
	-20, -10, -30, -50, -50, -30, -10, -20,
	-10,   0, -20, -40, -40, -20,   0, -10,
	  0,  10, -10, -30, -30, -10,  10,   0,
	 10,  20,   0, -20, -20,   0,  20,  10,
	 30,  40,  20,   0,   0,  20,  40,  30,
	 40,  50,  30,  10,  10,  30,  50,  40
	];

	// Kiraly vegjatek
	var KingEndMask = [
	-72, -48, -36, -24, -24, -36, -48, -72,
	-48, -24, -12,   0,   0, -12, -24, -48,
	-36, -12,   0,  12,  12,   0, -12, -36,
	-24,   0,  12,  24,  24,  12,   0, -24,
	-24,   0,  12,  24,  24,  12,   0, -24,
	-36, -12,   0,  12,  12,   0, -12, -36,
	-48, -24, -12,   0,   0, -12, -24, -48,
	-72, -48, -36, -24, -24, -36, -48, -72
	];

	// Vezer
	var QueenMask = [
	  0,   0,   0,   0,   0,   0,   0,   0,
	  0,   0,   0,   0,   0,   0,   0,   0,
	  0,   0,   0,   0,   0,   0,   0,   0,
	  0,   0,   0,   0,   0,   0,   0,   0,
	  0,   0,   0,   0,   0,   0,   0,   0,
	  0,   0,   0,   0,   0,   0,   0,   0,
	  0,   0,   0,   0,   0,   0,   0,   0,
	 -5,  -5,  -5,  -5,  -5,  -5,  -5,  -5
	];

	// Vezer vegjatek
	var QueenEndMask = [
	-24, -16, -12,  -8,  -8, -12, -16, -24,
	-16,  -8,  -4,   0,   0,  -4,  -8, -16,
	-12,  -4,   0,   4,   4,   0,  -4, -12,
	 -8,   0,   4,   8,   8,   4,   0,  -8,
	 -8,   0,   4,   8,   8,   4,   0,  -8,
	-12,  -4,   0,   4,   4,   0,  -4, -12,
	-16,  -8,  -4,   0,   0,  -4,  -8, -16,
	-24, -16, -12,  -8,  -8, -12, -16, -24
	];

	// Bastya
	var RookMask = [
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6,
	 -6,  -3,   0,   3,   3,   0,  -3,  -6
	];

	// Futo
	var BishopMask = [
	 -8,  -8,  -6,  -4,  -4,  -6,  -8,  -8,
	 -8,   0,  -2,   0,   0,  -2,   0,  -8,
	 -6,  -2,   4,   2,   2,   4,  -2,  -6,
	 -4,   0,   2,   8,   8,   2,   0,  -4,
	 -4,   0,   2,   8,   8,   2,   0,  -4,
	 -6,  -2,   4,   2,   2,   4,  -2,  -6,
	 -8,   0,  -2,   0,   0,  -2,   0,  -8,
	-18, -18, -16, -14, -14, -16, -18, -18
	];

	// Futo vegjatek
	var BishopEndMask = [
	-18, -12,  -9,  -6,  -6,  -9, -12, -18,
	-12,  -6,  -3,   0,   0,  -3,  -6, -12,
	 -9,  -3,   0,   3,   3,   0,  -3,  -9,
	 -6,   0,   3,   6,   6,   3,   0,  -6,
	 -6,   0,   3,   6,   6,   3,   0,  -6,
	 -9,  -3,   0,   3,   3,   0,  -3,  -9,
	-12,  -6,  -3,   0,   0,  -3,  -6, -12,
	-18, -12,  -9,  -6,  -6,  -9, -12, -18
	];

	// Huszar
	var KnightMask = [
   -135, -25, -15, -10, -10, -15, -25,-135,
	-20, -10,   0,   5,   5,   0, -10, -20,
	 -5,   5,  15,  20,  20,  15,   5,  -5,
	 -5,   5,  15,  20,  20,  15,   5,  -5,
	-10,   0,  10,  15,  15,  10,   0, -10,
	-20, -10,   0,   5,   5,   0, -10, -20,
	-35, -25, -15, -10, -10, -15, -25, -35,
	-50, -40, -30, -25, -25, -30, -40, -50
	];

	// Huszar vegjatek
	var KnightEndMask = [
	-40, -30, -20, -15, -15, -20, -30, -40,
	-30, -20, -10,  -5,  -5, -10, -20, -30,
	-20, -10,   0,   5,   5,   0, -10, -20,
	-15,  -5,   5,  10,  10,   5,  -5, -15,
	-15,  -5,   5,  10,  10,   5,  -5, -15,
	-20, -10,   0,   5,   5,   0, -10, -20,
	-30, -20, -10,  -5,  -5, -10, -20, -30,
	-40, -30, -20, -15, -15, -20, -30, -40
	];

	// Huszar outpost "orszem"
	var KnightOutpost = [
	  0,   0,   0,   0,   0,   0,   0,   0,
	  0,   0,   0,   0,   0,   0,   0,   0,
	  0,   0,   4,   5,   5,   4,   0,   0,
	  0,   2,   5,  10,  10,   5,   2,   0,
	  0,   2,   5,  10,  10,   5,   2,   0,
	  0,   0,   0,   0,   0,   0,   0,   0,
	  0,   0,   0,   0,   0,   0,   0,   0,
	  0,   0,   0,   0,   0,   0,   0,   0
	];

	// Gyalog
	var PawnMask = [
	-15,  -5,   0,   5,   5,   0,  -5, -15,
	-15,  -5,   0,   5,   5,   0,  -5, -15,
	-15,  -5,   0,   5,   5,   0,  -5, -15,
	-15,  -5,   0,  15,  15,   0,  -5, -15,
	-15,  -5,   0,  25,  25,   0,  -5, -15,
	-15,  -5,   0,  15,  15,   0,  -5, -15,
	-15,  -5,   0,   5,   5,   0,  -5, -15,
	-15,  -5,   0,   5,   5,   0,  -5, -15
	];
