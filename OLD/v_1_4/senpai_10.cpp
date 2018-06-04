
/*
    Senpai 1.0 Copyright (C) 2014 Fabien Letouzey.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

// macros

#ifndef DEBUG
#  define NDEBUG
#endif

// C includes

#include <cassert> // needs NDEBUG
#include <cctype>
#include <cmath>
#include <cstdlib>
#include <ctime>

// C++ includes

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

// C++11 includes

#include <chrono>
#include <condition_variable>
#include <mutex>
#include <thread>

// macros

#ifdef _MSC_VER
#  define I64(n) (n##i64)
#  define U64(u) (u##ui64)
#else
#  define I64(n) (n##LL)
#  define U64(u) (u##ULL)
#endif

// types

typedef signed   char int8;
typedef unsigned char uint8;

typedef signed   short int int16;
typedef unsigned short int uint16;

typedef signed   int int32;
typedef unsigned int uint32;

typedef signed   long long int int64;
typedef unsigned long long int uint64;

typedef uint64 bit_t;
typedef uint64 hash_t; // key_t is used by Unix :(

// modules

namespace util {

class Timer {

private:

   typedef std::chrono::time_point<std::chrono::system_clock> time_t;
   typedef std::chrono::duration<int, std::ratio<1, 1000>> millisecond_t;

   int p_elapsed;
   bool p_running;
   time_t p_start;

   static time_t now() {
      return std::chrono::system_clock::now();
   }

   int time() const {
      assert(p_running);
      return std::chrono::duration_cast<millisecond_t>(now() - p_start).count();
   }

public:

   Timer() {
      reset();
   }

   void reset() {
      p_elapsed = 0;
      p_running = false;
   }

   void start() {
      p_start = now();
      p_running = true;
   }

   void stop() {
      p_elapsed += time();
      p_running = false;
   }

   int elapsed() const {
      int time = p_elapsed;
      if (p_running) time += this->time();
      return time;
   }

};

class Lockable {

protected: // HACK for Waitable::wait()

   mutable std::mutex p_mutex;

public:

   void lock   () const { p_mutex.lock(); }
   void unlock () const { p_mutex.unlock(); }
};

class Waitable : public Lockable {

private:

   std::condition_variable_any p_cond;

public:

   void wait   () { p_cond.wait(p_mutex); } // HACK: direct access
   void signal () { p_cond.notify_one(); }
};

int round(double x) {
   return int(std::floor(x + 0.5));
}

int div(int a, int b) {

   assert(b > 0);

   int div = a / b;
   if (a < 0 && a != b * div) div--; // fix buggy C semantics

   return div;
}

int sqrt(int n) {
   return int(std::sqrt(double(n)));
}

bool is_square(int n) {
   int i = sqrt(n);
   return i * i == n;
}

double rand_float() {
   return double(std::rand()) / (double(RAND_MAX) + 1.0);
}

int rand_int(int n) {
   assert(n > 0);
   return int(rand_float() * double(n));
}

int string_find(const std::string & s, char c) {
   return int(s.find(c));
}

bool string_case_equal(const std::string & s0, const std::string & s1) {

   if (s0.size() != s1.size()) return false;

   for (int i = 0; i < int(s0.size()); i++) {
      if (std::tolower(s0[i]) != std::tolower(s1[i])) return false;
   }

   return true;
}

bool to_bool(const std::string & s) {
   if (string_case_equal(s, "true")) {
      return true;
   } else if (string_case_equal(s, "false")) {
      return false;
   } else {
      std::cerr << "not a boolean: \"" << s << "\"" << std::endl;
      std::exit(EXIT_FAILURE);
   }
}

int64 to_int(const std::string & s) {
   std::stringstream ss(s);
   int64 n;
   ss >> n;
   return n;
}

std::string to_string(int n) {
   std::stringstream ss;
   ss << n;
   return ss.str();
}

std::string to_string(double x) {
   std::stringstream ss;
   ss << x;
   return ss.str();
}

void log(const std::string & s) {
   std::ofstream log_file("log.txt", std::ios_base::app);
   log_file << s << std::endl;
}

}

namespace input {

class Input : public util::Waitable {

   bool volatile p_has_input;
   bool p_eof;
   std::string p_line;

public:

   Input() {
      p_has_input = false;
      p_eof = false;
   }

   bool has_input() const {
      return p_has_input;
   }

   bool get_line(std::string & line) {

      lock();

      while (!p_has_input) {
         wait();
      }

      bool line_ok = !p_eof;
      if (line_ok) line = p_line;

      p_has_input = false;
      signal();

      unlock();

      return line_ok;
   }

   void set_eof() {

      lock();

      while (p_has_input) {
         wait();
      }

      p_eof = true;

      p_has_input = true;
      signal();

      unlock();
   }

   void set_line(std::string & line) {

      lock();

      while (p_has_input) {
         wait();
      }

      p_line = line;

      p_has_input = true;
      signal();

      unlock();
   }

};

Input input;
std::thread thread;

void input_program(Input * input) {

   std::string line;

   while (std::getline(std::cin, line)) {
      input->set_line(line);
   }

   input->set_eof();
}

void init() {
   thread = std::thread(input_program, &input);
   thread.detach();
}

};

namespace side {

const int SIZE = 2;

enum {
   WHITE,
   BLACK,
};

int opposit(int sd) {
   return sd ^ 1;
}

}

namespace square {

const int FILE_SIZE = 8;
const int RANK_SIZE = 8;
const int SIZE = FILE_SIZE * RANK_SIZE;

enum {
   FILE_A,
   FILE_B,
   FILE_C,
   FILE_D,
   FILE_E,
   FILE_F,
   FILE_G,
   FILE_H,
};

enum {
   RANK_1,
   RANK_2,
   RANK_3,
   RANK_4,
   RANK_5,
   RANK_6,
   RANK_7,
   RANK_8,
};

enum {
   NONE = -1,
   A1, A2, A3, A4, A5, A6, A7, A8,
   B1, B2, B3, B4, B5, B6, B7, B8,
   C1, C2, C3, C4, C5, C6, C7, C8,
   D1, D2, D3, D4, D5, D6, D7, D8,
   E1, E2, E3, E4, E5, E6, E7, E8,
   F1, F2, F3, F4, F5, F6, F7, F8,
   G1, G2, G3, G4, G5, G6, G7, G8,
   H1, H2, H3, H4, H5, H6, H7, H8,
};

enum {
   INC_LEFT  = -8,
   INC_RIGHT = +8,
};

const int CASTLING_DELTA = 16;
const int DOUBLE_PAWN_DELTA = 2;

int make(int fl, int rk) {

   assert(fl < 8);
   assert(rk < 8);

   return (fl << 3) | rk;
}

int make(int fl, int rk, int sd) {

   assert(fl < 8);
   assert(rk < 8);

   return make(fl, (rk ^ -sd) & 7);
}

int file(int sq) {
   return sq >> 3;
}

int rank(int sq) {
   return sq & 7;
}

int rank(int sq, int sd) {
   return (sq ^ -sd) & 7;
}

int opposit_file(int sq) {
   return sq ^ 070;
}

int opposit_rank(int sq) {
   return sq ^ 007;
}

bool is_promotion(int sq) {
   int rk = rank(sq);
   return rk == RANK_1 || rk == RANK_8;
}

int colour(int sq) {
   return ((sq >> 3) ^ sq) & 1;
}

bool same_colour(int s0, int s1) {
   int diff = s0 ^ s1;
   return (((diff >> 3) ^ diff) & 1) == 0;
}

bool same_line(int s0, int s1) {
   return file(s0) == file(s1) || rank(s0) == rank(s1);
}

int file_distance(int s0, int s1) {
   return std::abs(file(s1) - file(s0));
}

int rank_distance(int s0, int s1) {
   return std::abs(rank(s1) - rank(s0));
}

int distance(int s0, int s1) {
   return std::max(file_distance(s0, s1), rank_distance(s0, s1));
}

int pawn_inc(int sd) {
   return (sd == side::WHITE) ? +1 : -1;
}

int stop(int sq, int sd) {
   return sq + pawn_inc(sd);
}

int promotion(int sq, int sd) {
   return make(file(sq), RANK_8, sd);
}

bool is_valid_88(int s88) {
   return (s88 & ~0x77) == 0;
}

int to_88(int sq) {
   return sq + (sq & 070);
}

int from_88(int s88) {
   assert(is_valid_88(s88));
   return (s88 + (s88 & 7)) >> 1;
}

int from_fen(int sq) {
   return make(sq & 7, (sq >> 3) ^ 7);
}

int from_string(const std::string & s) {
   assert(s.length() == 2);
   return make(s[0] - 'a', s[1] - '1');
}

std::string to_string(int sq) {

   std::string s;
   s += 'a' + file(sq);
   s += '1' + rank(sq);

   return s;
}

}

namespace wing {

const int SIZE = 2;

enum {
   KING,
   QUEEN,
};

const int shelter_file[SIZE] = { square::FILE_G, square::FILE_B }; // for pawn-shelter eval

}

namespace piece {

const int SIZE = 7;
const int SIDE_SIZE = 12;

enum Piece {
   PAWN,
   KNIGHT,
   BISHOP,
   ROOK,
   QUEEN,
   KING,
   NONE,
};

enum Side_Piece {
   WHITE_PAWN,
   BLACK_PAWN,
   WHITE_KNIGHT,
   BLACK_KNIGHT,
   WHITE_BISHOP,
   BLACK_BISHOP,
   WHITE_ROOK,
   BLACK_ROOK,
   WHITE_QUEEN,
   BLACK_QUEEN,
   WHITE_KING,
   BLACK_KING,
};

const int PAWN_VALUE   = 100;
const int KNIGHT_VALUE = 325;
const int BISHOP_VALUE = 325;
const int ROOK_VALUE   = 500;
const int QUEEN_VALUE  = 975;
const int KING_VALUE   = 10000; // for SEE

const std::string Char = "PNBRQK?";
const std::string Fen_Char = "PpNnBbRrQqKk";

bool is_minor(int pc) {
   assert(pc < SIZE);
   return pc == KNIGHT || pc == BISHOP;
}

bool is_major(int pc) {
   assert(pc < SIZE);
   return pc == ROOK || pc == QUEEN;
}

bool is_slider(int pc) {
   assert(pc < SIZE);
   return pc >= BISHOP && pc <= QUEEN;
}

int score(int pc) { // for MVV/LVA
   assert(pc < SIZE);
   assert(pc != NONE);
   return pc;
}

int value(int pc) {
   assert(pc < SIZE);
   static const int value[SIZE] = { PAWN_VALUE, KNIGHT_VALUE, BISHOP_VALUE, ROOK_VALUE, QUEEN_VALUE, KING_VALUE, 0 };
   return value[pc];
}

int make(int pc, int sd) {
   assert(pc < SIZE);
   assert(pc != NONE);
   assert(sd < side::SIZE);
   return (pc << 1) | sd;
}

int piece(int p12) {
   assert(p12 < SIDE_SIZE);
   return p12 >> 1;
}

int side(int p12) {
   assert(p12 < SIDE_SIZE);
   return p12 & 1;
}

int from_char(char c) {
   return util::string_find(Char, c);
}

char to_char(int pc) {
   assert(pc < SIZE);
   return Char[pc];
}

int from_fen(char c) {
   return util::string_find(Fen_Char, c);
}

char to_fen(int p12) {
   assert(p12 < SIDE_SIZE);
   return Fen_Char[p12];
}

}

namespace move {

const int FLAGS_BITS = 9;
const int FLAGS_SIZE = 1 << FLAGS_BITS;
const int FLAGS_MASK = FLAGS_SIZE - 1;

const int BITS = FLAGS_BITS + 12;
const int SIZE = 1 << BITS;
const int MASK = SIZE - 1;

const int SCORE_BITS = 32 - BITS;
const int SCORE_SIZE = 1 << SCORE_BITS;
const int SCORE_MASK = SCORE_SIZE - 1;

enum Move {
   NONE  = 0,
   NULL_ = 1,
};

int make_flags(int pc, int cp, int pp = piece::NONE) {

   assert(pc < piece::SIZE);
   assert(cp < piece::SIZE);
   assert(pp < piece::SIZE);

   return (pc << 6) | (cp << 3) | pp;
}

int make(int f, int t, int pc, int cp, int pp = piece::NONE) {

   assert(f < square::SIZE);
   assert(t < square::SIZE);
   assert(pc < piece::SIZE);
   assert(cp < piece::SIZE);
   assert(pp < piece::SIZE);

   assert(pc != piece::NONE);
   assert(pp == piece::NONE || pc == piece::PAWN);

   return (pc << 18) | (cp << 15) | (pp << 12) | (f << 6) | t;
}

int from(int mv) {
   assert(mv != NONE);
   assert(mv != NULL_);
   return (mv >> 6) & 077;
}

int to(int mv) {
   assert(mv != NONE);
   assert(mv != NULL_);
   return mv & 077;
}

int piece(int mv) {
   assert(mv != NONE);
   assert(mv != NULL_);
   return (mv >> 18) & 7;
}

int cap(int mv) {
   assert(mv != NONE);
   assert(mv != NULL_);
   return (mv >> 15) & 7;
}

int prom(int mv) {
   assert(mv != NONE);
   assert(mv != NULL_);
   return (mv >> 12) & 7;
}

int flags(int mv) {
   assert(mv != NONE);
   assert(mv != NULL_);
   return (mv >> 12) & 0777;
}

std::string to_can(int mv) {

   assert(mv != NONE);

   if (mv == NONE)  return "0000";
   if (mv == NULL_) return "0000";

   std::string s;

   s += square::to_string(from(mv));
   s += square::to_string(to(mv));

   if (prom(mv) != piece::NONE) {
      s += std::tolower(piece::to_char(prom(mv)));
   }

   return s;
}

}

namespace bit {

bit_t p_left[8];
bit_t p_right[8];
bit_t p_front[8];
bit_t p_rear[8];

bit_t p_side_front[side::SIZE][8];
bit_t p_side_rear[side::SIZE][8];

bit_t bit(int n) {
   assert(n < 64);
   return U64(1) << n;
}

void set(bit_t & b, int n) {
   b |= bit(n);
}

void clear(bit_t & b, int n) {
   b &= ~bit(n);
}

bool is_set(bit_t b, int n) {
   return (b & bit(n)) != 0;
}

int first(bit_t b) {

   assert(b != 0);

/*
   static const int index[64] = {
       0,  1,  2,  7,  3, 13,  8, 19,
       4, 25, 14, 28,  9, 34, 20, 40,
       5, 17, 26, 38, 15, 46, 29, 48,
      10, 31, 35, 54, 21, 50, 41, 57,
      63,  6, 12, 18, 24, 27, 33, 39,
      16, 37, 45, 47, 30, 53, 49, 56,
      62, 11, 23, 32, 36, 44, 52, 55,
      61, 22, 43, 51, 60, 42, 59, 58,
   };

   return index[((b & -b) * U64(0x218A392CD3D5DBF)) >> (64 - 6)];
*/

   return __builtin_ctzll(b); // GCC
}

bit_t rest(bit_t b) {
   assert(b != 0);
   return b & (b - 1);
}

int count(bit_t b) {

/*
   b = b - ((b >> 1) & U64(0x5555555555555555));
   b = (b & U64(0x3333333333333333)) + ((b >> 2) & U64(0x3333333333333333));
   b = (b + (b >> 4)) & U64(0x0F0F0F0F0F0F0F0F);
   return (b * U64(0x0101010101010101)) >> 56;
*/

   return __builtin_popcountll(b); // GCC
}

int count_loop(bit_t b) {

/*
   int n = 0;

   for (; b != 0; b = rest(b)) {
      n++;
   }

   return n;
*/

   return __builtin_popcountll(b); // GCC
}

bool single(bit_t b) {
   assert(b != 0);
   return rest(b) == 0;
}

bit_t file(int fl) {
   assert(fl < 8);
   return U64(0xFF) << (fl * 8);
}

bit_t rank(int rk) {
   assert(rk < 8);
   return U64(0x0101010101010101) << rk;
}

bit_t files(int fl) {
   assert(fl < 8);
   bit_t file = bit::file(fl);
   return (file << 8) | file | (file >> 8);
}

bit_t left(int fl) {
   assert(fl < 8);
   return p_left[fl];
}

bit_t right(int fl) {
   assert(fl < 8);
   return p_right[fl];
}

bit_t front(int rk) {
   assert(rk < 8);
   return p_front[rk];
}

bit_t rear(int rk) {
   assert(rk < 8);
   return p_rear[rk];
}

bit_t front(int sq, int sd) {
   int rk = square::rank(sq);
   return p_side_front[sd][rk];
}

bit_t rear(int sq, int sd) {
   int rk = square::rank(sq);
   return p_side_rear[sd][rk];
}

void init() {

   {
      bit_t bf = 0;
      bit_t br = 0;

      for (int i = 0; i < 8; i++) {
         p_left[i] = bf;
         p_rear[i] = br;
         bf |= file(i);
         br |= rank(i);
      }
   }

   {
      bit_t bf = 0;
      bit_t br = 0;

      for (int i = 7; i >= 0; i--) {
         p_right[i] = bf;
         p_front[i] = br;
         bf |= file(i);
         br |= rank(i);
      }
   }

   for (int rk = 0; rk < 8; rk++) {
      p_side_front[side::WHITE][rk] = front(rk);
      p_side_front[side::BLACK][rk] = rear(rk);
      p_side_rear [side::WHITE][rk] = rear(rk);
      p_side_rear [side::BLACK][rk] = front(rk);
   }
}

}

namespace hash {

const int TURN       = piece::SIDE_SIZE * square::SIZE;
const int CASTLE     = TURN + 1;
const int EN_PASSANT = CASTLE + 4;
const int SIZE       = EN_PASSANT + 8;

hash_t p_rand[SIZE];

hash_t rand_64() {

   hash_t rand = 0;

   for (int i = 0; i < 4; i++) {
      rand = (rand << 16) | util::rand_int(1 << 16);
   }

   return rand;
}

hash_t rand_key(int index) {
   assert(index >= 0 && index < SIZE);
   return p_rand[index];
}

hash_t piece_key(int p12, int sq) {
   return rand_key(p12 * square::SIZE + sq);
}

hash_t turn_key(int turn) {
   return (turn == side::WHITE) ? 0 : rand_key(TURN);
}

hash_t turn_flip() {
   return rand_key(TURN);
}

hash_t flag_key(int flag) {
   assert(flag < 4);
   return rand_key(CASTLE + flag);
}

hash_t en_passant_key(int sq) {
   return (sq == square::NONE) ? 0 : rand_key(EN_PASSANT + square::file(sq));
}

int64 index(hash_t key) {
   return int64(key);
}

uint32 lock(hash_t key) {
   return uint32(key >> 32);
}

void init() {
   for (int i = 0; i < SIZE; i++) {
      p_rand[i] = rand_64();
   }
}

}

namespace castling {

struct Info {
   int kf;
   int kt;
   int rf;
   int rt;
};

const Info info[4] = {
   { square::E1, square::G1, square::H1, square::F1 },
   { square::E1, square::C1, square::A1, square::D1 },
   { square::E8, square::G8, square::H8, square::F8 },
   { square::E8, square::C8, square::A8, square::D8 },
};

int flags_mask[square::SIZE];
hash_t flags_key[1 << 4];

int index(int sd, int wg) {
   return sd * 2 + wg;
}

int side(int index) {
   return index / 2;
}

bool flag(int flags, int index) {
   assert(index < 4);
   return bool((flags >> index) & 1);
}

void set_flag(int & flags, int index) {
   assert(index < 4);
   flags |= 1 << index;
}

hash_t flags_key_debug(int flags) {

   hash_t key = 0;

   for (int index = 0; index < 4; index++) {
      if (flag(flags, index)) {
         key ^= hash::flag_key(index);
      }
   }

   return key;
}

void init() {

   for (int sq = 0; sq < square::SIZE; sq++) {
      flags_mask[sq] = 0;
   }

   set_flag(flags_mask[square::E1], 0);
   set_flag(flags_mask[square::E1], 1);
   set_flag(flags_mask[square::H1], 0);
   set_flag(flags_mask[square::A1], 1);

   set_flag(flags_mask[square::E8], 2);
   set_flag(flags_mask[square::E8], 3);
   set_flag(flags_mask[square::H8], 2);
   set_flag(flags_mask[square::A8], 3);

   for (int flags = 0; flags < (1 << 4); flags++) {
      flags_key[flags] = flags_key_debug(flags);
   }
}

}

namespace stage {

const int SIZE = 2;

enum {
   MG,
   EG,
};

}

namespace material {

const int PAWN_PHASE   = 0;
const int KNIGHT_PHASE = 1;
const int BISHOP_PHASE = 1;
const int ROOK_PHASE   = 2;
const int QUEEN_PHASE  = 4;

const int TOTAL_PHASE = PAWN_PHASE * 16 + KNIGHT_PHASE * 4 + BISHOP_PHASE * 4 + ROOK_PHASE * 4 + QUEEN_PHASE * 2;

const int p_phase[piece::SIZE] = { PAWN_PHASE, KNIGHT_PHASE, BISHOP_PHASE, ROOK_PHASE, QUEEN_PHASE, 0, 0 };

int phase(int pc) {
   assert(pc < piece::SIZE);
   return p_phase[pc];
}

}

namespace board {

struct Copy {
   hash_t key;
   hash_t pawn_key;
   int flags;
   int ep_sq;
   int moves;
   int recap;
   int phase;
};

struct Undo {
   Copy copy;
   int move;
   int cap_sq;
   bool castling;
};

const std::string start_fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -";

class Board {

private:

   static const int SCORE_NONE = -10000; // HACK because "score::NONE" is defined later

   bit_t p_piece[piece::SIZE];
   bit_t p_side[side::SIZE];
   bit_t p_all;

   int p_king[side::SIZE];
   int p_count[piece::SIDE_SIZE];

   int p_square[square::SIZE];
   int p_turn;
   Copy p_copy;

   int p_root;
   int p_sp;
   Undo p_stack[1024];

public:

   void operator=(const Board & bd) {

      for (int pc = 0; pc < piece::SIZE; pc++) {
         p_piece[pc] = bd.p_piece[pc];
      }

      for (int sd = 0; sd < side::SIZE; sd++) {
         p_side[sd] = bd.p_side[sd];
         p_king[sd] = bd.p_king[sd];
      }

      p_all = bd.p_all;

      for (int p12 = 0; p12 < piece::SIDE_SIZE; p12++) {
         p_count[p12] = bd.p_count[p12];
      }

      for (int sq = 0; sq < square::SIZE; sq++) {
         p_square[sq] = bd.p_square[sq];
      }

      p_turn = bd.p_turn;
      p_copy = bd.p_copy;

      p_root = bd.p_root;
      p_sp = bd.p_sp;

      for (int sp = 0; sp < bd.p_sp; sp++) {
         p_stack[sp] = bd.p_stack[sp];
      }

      assert(moves() == bd.moves());
   }

   bit_t piece(int pc) const {
      assert(pc < piece::SIZE);
      assert(pc != piece::NONE);
      return p_piece[pc];
   }

   bit_t piece(int pc, int sd) const {
      assert(pc < piece::SIZE);
      assert(pc != piece::NONE);
      return p_piece[pc] & p_side[sd];
   }

   int count(int pc, int sd) const {
      assert(pc < piece::SIZE);
      assert(pc != piece::NONE);
      // return bit::count(piece(pc, sd));
      return p_count[piece::make(pc, sd)];
   }

   bit_t side(int sd) const {
      return p_side[sd];
   }

   bit_t pieces(int sd) const {
      return p_side[sd] & ~piece(piece::PAWN, sd);
   }

   bit_t all() const {
      return p_all;
   }

   bit_t empty() const {
      return ~p_all;
   }

   int square(int sq) const {
      return p_square[sq];
   }

   int square_side(int sq) const {
      assert(p_square[sq] != piece::NONE);
      return (p_side[side::BLACK] >> sq) & 1; // HACK: uses Side internals
   }

   bool square_is(int sq, int pc, int sd) const {
      assert(pc < piece::SIZE);
      assert(pc != piece::NONE);
      return square(sq) == pc && square_side(sq) == sd;
   }

   int king(int sd) const {
      int sq = p_king[sd];
      assert(sq == bit::first(piece(piece::KING, sd)));
      return sq;
   }

   int turn() const {
      return p_turn;
   }

   hash_t key() const {
      hash_t key = p_copy.key;
      key ^= castling::flags_key[p_copy.flags];
      key ^= hash::en_passant_key(p_copy.ep_sq);
      return key;
   }

   hash_t pawn_key() const {
      return p_copy.pawn_key;
   }

   hash_t eval_key() const {
      hash_t key = p_copy.key;
      key ^= hash::turn_key(p_turn); // remove incremental STM
      key ^= castling::flags_key[p_copy.flags];
      return key;
   }

   int flags() const {
      return p_copy.flags;
   }

   int ep_sq() const {
      return p_copy.ep_sq;
   }

   int moves() const {
      return p_copy.moves;
   }

   int recap() const {
      return p_copy.recap;
   }

   int phase() const {
      return p_copy.phase;
   }

   int ply() const {
      assert(p_sp >= p_root);
      return p_sp - p_root;
   }

   int last_move() const {
      return (p_sp == 0) ? move::NONE : p_stack[p_sp - 1].move;
   }

   bool is_draw() const {

      if (p_copy.moves > 100) { // TODO: check for mate
         return true;
      }

      hash_t key = p_copy.key; // HACK: ignores castling flags and e.p. square

      assert(p_copy.moves <= p_sp);

      for (int i = 4; i < p_copy.moves; i += 2) {
         if (p_stack[p_sp - i].copy.key == key) {
            return true;
         }
      }

      return false;
   }

   void set_root() {
      p_root = p_sp;
   }

   void clear() {

      for (int pc = 0; pc < piece::SIZE; pc++) {
         p_piece[pc] = 0;
      }

      for (int sd = 0; sd < side::SIZE; sd++) {
         p_side[sd] = 0;
      }

      for (int sq = 0; sq < square::SIZE; sq++) {
         p_square[sq] = piece::NONE;
      }

      for (int sd = 0; sd < side::SIZE; sd++) {
         p_king[sd] = square::NONE;
      }

      for (int p12 = 0; p12 < piece::SIDE_SIZE; p12++) {
         p_count[p12] = 0;
      }

      p_turn = side::WHITE;

      p_copy.key = 0;
      p_copy.pawn_key = 0;
      p_copy.flags = 0;
      p_copy.ep_sq = square::NONE;
      p_copy.moves = 0;
      p_copy.recap = square::NONE;
      p_copy.phase = 0;

      p_root = 0;
      p_sp = 0;
   }

   void clear_square(int pc, int sd, int sq, bool update_copy) {

      assert(pc < piece::SIZE);
      assert(pc != piece::NONE);
      assert(sq >= 0 && sq < square::SIZE);

      assert(pc == p_square[sq]);

      assert(bit::is_set(p_piece[pc], sq));
      bit::clear(p_piece[pc], sq);

      assert(bit::is_set(p_side[sd], sq));
      bit::clear(p_side[sd], sq);

      assert(p_square[sq] != piece::NONE);
      p_square[sq] = piece::NONE;

      int p12 = piece::make(pc, sd);

      assert(p_count[p12] != 0);
      p_count[p12]--;

      if (update_copy) {

         hash_t key = hash::piece_key(p12, sq);
         p_copy.key ^= key;
         if (pc == piece::PAWN) p_copy.pawn_key ^= key;

         p_copy.phase -= material::phase(pc);
      }
   }

   void set_square(int pc, int sd, int sq, bool update_copy) {

      assert(pc < piece::SIZE);
      assert(pc != piece::NONE);
      assert(sq >= 0 && sq < square::SIZE);

      assert(!bit::is_set(p_piece[pc], sq));
      bit::set(p_piece[pc], sq);

      assert(!bit::is_set(p_side[sd], sq));
      bit::set(p_side[sd], sq);

      assert(p_square[sq] == piece::NONE);
      p_square[sq] = pc;

      if (pc == piece::KING) {
         p_king[sd] = sq;
      }

      int p12 = piece::make(pc, sd);

      p_count[p12]++;

      if (update_copy) {

         hash_t key = hash::piece_key(p12, sq);
         p_copy.key ^= key;
         if (pc == piece::PAWN) p_copy.pawn_key ^= key;

         p_copy.phase += material::phase(pc);
      }
   }

   void move_square(int pc, int sd, int f, int t, bool update_copy) { // TODO
      clear_square(pc, sd, f, update_copy);
      set_square(pc, sd, t, update_copy);
   }

   void flip_turn() {
      p_turn = side::opposit(p_turn);
      p_copy.key ^= hash::turn_flip();
   }

   void update() {

      p_all = p_side[side::WHITE] | p_side[side::BLACK];

#ifdef DEBUG

      for (int p12 = 0; p12 < piece::SIDE_SIZE; p12++) {
         assert(p_count[p12] == bit::count(piece(piece::piece(p12), piece::side(p12))));
      }

      assert(p_count[piece::WHITE_KING] == 1);
      assert(p_count[piece::BLACK_KING] == 1);

      assert((p_piece[piece::PAWN] & bit::rank(square::RANK_1)) == 0);
      assert((p_piece[piece::PAWN] & bit::rank(square::RANK_8)) == 0);

      for (int sd = 0; sd < side::SIZE; sd++) {
         for (int wg = 0; wg < side::SIZE; wg++) {
            int index = castling::index(sd, wg);
            if (castling::flag(p_copy.flags, index)) {
               assert(square_is(castling::info[index].kf, piece::KING, sd));
               assert(square_is(castling::info[index].rf, piece::ROOK, sd));
            }
         }
      }

#endif

   }

   bool can_castle(int index) const {

      int sd = castling::side(index);

      return square_is(castling::info[index].kf, piece::KING, sd)
          && square_is(castling::info[index].rf, piece::ROOK, sd);
   }

   bool pawn_is_attacked(int sq, int sd) const {

      int fl = square::file(sq);
      sq -= square::pawn_inc(sd);

      return (fl != square::FILE_A && square_is(sq + square::INC_LEFT,  piece::PAWN, sd))
          || (fl != square::FILE_H && square_is(sq + square::INC_RIGHT, piece::PAWN, sd));
   }

   void init_fen(const std::string & s) {

      clear();

      int pos = 0;

      // piece placement

      int sq = 0;

      while (pos < int(s.size())) {

         assert(sq <= square::SIZE);

         char c = s[pos++];

         if (false) {

         } else if (c == ' ') {

            break;

         } else if (c == '/') {

            continue;

         } else if (std::isdigit(c)) {

            sq += c - '0';

         } else { // assume piece

            int p12 = piece::from_fen(c);
            int pc = piece::piece(p12);
            int sd = piece::side(p12);
            set_square(pc, sd, square::from_fen(sq), true);
            sq++;
         }
      }

      assert(sq == square::SIZE);

      // turn

      p_turn = side::WHITE;

      if (pos < int(s.size())) {

         p_turn = util::string_find("wb", s[pos++]);

         if (pos < int(s.size())) {
            assert(s[pos] == ' ');
            pos++;
         }
      }

      p_copy.key ^= hash::turn_key(p_turn);

      // castling flags

      p_copy.flags = 0;

      if (pos < int(s.size())) { // read from FEN

         while (pos < int(s.size())) {

            char c = s[pos++];
            if (c == ' ') break;
            if (c == '-') continue;

            int index = util::string_find("KQkq", c);

            if (can_castle(index)) {
               castling::set_flag(p_copy.flags, index);
            }
         }

      } else { // guess from position

         for (int index = 0; index < 4; index++) {
            if (can_castle(index)) {
               castling::set_flag(p_copy.flags, index);
            }
         }
      }

      // en-passant square

      p_copy.ep_sq = square::NONE;

      if (pos < int(s.size())) { // read from FEN

         std::string ep_string;

         while (pos < int(s.size())) {

            char c = s[pos++];
            if (c == ' ') break;

            ep_string += c;
         }

         if (ep_string != "-") {

            int sq = square::from_string(ep_string);

            if (pawn_is_attacked(sq, p_turn)) {
               p_copy.ep_sq = sq;
            }
         }
      }

      update();
   }

   void move(int mv) {

      assert(mv != move::NONE);
      assert(mv != move::NULL_);

      int sd = p_turn;
      int xd = side::opposit(sd);

      int f = move::from(mv);
      int t = move::to(mv);

      int pc = move::piece(mv);
      int cp = move::cap(mv);
      int pp = move::prom(mv);

      assert(p_square[f] == pc);
      assert(square_side(f) == sd);

      assert(p_sp < 1024);
      Undo & undo = p_stack[p_sp++];

      undo.copy = p_copy;
      undo.move = mv;
      undo.castling = false;

      p_copy.moves++;
      p_copy.recap = square::NONE;

      // capture

      assert(cp != piece::KING);

      if (pc == piece::PAWN && t == p_copy.ep_sq) {

         int cap_sq = t - square::pawn_inc(sd);
         assert(p_square[cap_sq] == cp);
         assert(cp == piece::PAWN);

         undo.cap_sq = cap_sq;

         clear_square(cp, xd, cap_sq, true);

      } else if (cp != piece::NONE) {

         assert(p_square[t] == cp);
         assert(square_side(t) == xd);

         undo.cap_sq = t;

         clear_square(cp, xd, t, true);

      } else {

         assert(p_square[t] == cp);
      }

      // promotion

      if (pp != piece::NONE) {
         assert(pc == piece::PAWN);
         clear_square(piece::PAWN, sd, f, true);
         set_square(pp, sd, t, true);
      } else {
         move_square(pc, sd, f, t, true);
      }

      // castling rook

      if (pc == piece::KING && std::abs(t - f) == square::CASTLING_DELTA) {

         undo.castling = true;

         int wg = (t > f) ? wing::KING : wing::QUEEN;
         int index = castling::index(sd, wg);

         assert(castling::flag(p_copy.flags, index));

         assert(f == castling::info[index].kf);
         assert(t == castling::info[index].kt);

         move_square(piece::ROOK, sd, castling::info[index].rf, castling::info[index].rt, true);
      }

      // turn

      flip_turn();

      // castling flags

      p_copy.flags &= ~castling::flags_mask[f];
      p_copy.flags &= ~castling::flags_mask[t];

      // en-passant square

      p_copy.ep_sq = square::NONE;

      if (pc == piece::PAWN && std::abs(t - f) == square::DOUBLE_PAWN_DELTA) {
         int sq = (f + t) / 2;
         if (pawn_is_attacked(sq, xd)) {
            p_copy.ep_sq = sq;
         }
      }

      // move counter

      if (cp != piece::NONE || pc == piece::PAWN) {
         p_copy.moves = 0; // conversion;
      }

      // recapture

      if (cp != piece::NONE || pp != piece::NONE) {
         p_copy.recap = t;
      }

      update();
   }

   void undo() {

      assert(p_sp > 0);
      const Undo & undo = p_stack[--p_sp];

      int mv = undo.move;

      int f = move::from(mv);
      int t = move::to(mv);

      int pc = move::piece(mv);
      int cp = move::cap(mv);
      int pp = move::prom(mv);

      int xd = p_turn;
      int sd = side::opposit(xd);

      assert(p_square[t] == pc || p_square[t] == pp);
      assert(square_side(t) == sd);

      // castling rook

      if (undo.castling) {

         int wg = (t > f) ? wing::KING : wing::QUEEN;
         int index = castling::index(sd, wg);

         assert(f == castling::info[index].kf);
         assert(t == castling::info[index].kt);

         move_square(piece::ROOK, sd, castling::info[index].rt, castling::info[index].rf, false);
      }

      // promotion

      if (pp != piece::NONE) {
         assert(pc == piece::PAWN);
         clear_square(pp, sd, t, false);
         set_square(piece::PAWN, sd, f, false);
      } else {
         move_square(pc, sd, t, f, false);
      }

      // capture

      if (cp != piece::NONE) {
         set_square(cp, xd, undo.cap_sq, false);
      }

      flip_turn();
      p_copy = undo.copy;

      update();
   }

   void move_null() {

      assert(p_sp < 1024);
      Undo & undo = p_stack[p_sp++];

      undo.move = move::NULL_;

      undo.copy = p_copy;

      flip_turn();
      p_copy.ep_sq = square::NONE;
      p_copy.moves = 0; // HACK: conversion
      p_copy.recap = square::NONE;

      update();
   }

   void undo_null() {

      assert(p_sp > 0);
      const Undo & undo = p_stack[--p_sp];

      assert(undo.move == move::NULL_);

      flip_turn();
      p_copy = undo.copy;

      update();
   }

};

}

namespace attack {

struct Attacks {
   int size;
   int square[2];
   bit_t avoid;
   bit_t pinned;
};

const int Pawn_Move[side::SIZE] = { +1, -1 };
const int Pawn_Attack[side::SIZE][2] = { { -15, +17 }, { -17, +15 } };

const int Knight_Inc[] = { -33, -31, -18, -14, +14, +18, +31, +33, 0 };
const int Bishop_Inc[] = { -17, -15, +15, +17, 0 };
const int Rook_Inc[]   = { -16, -1, +1, +16, 0 };
const int Queen_Inc[]  = { -17, -16, -15, -1, +1, +15, +16, +17, 0 };

const int * Piece_Inc[piece::SIZE] = { NULL, Knight_Inc, Bishop_Inc, Rook_Inc, Queen_Inc, Queen_Inc, NULL };

bit_t Pawn_Moves[side::SIZE][square::SIZE];
bit_t Pawn_Attacks[side::SIZE][square::SIZE];
bit_t Piece_Attacks[piece::SIZE][square::SIZE];
bit_t Blockers[piece::SIZE][square::SIZE];

bit_t Between[square::SIZE][square::SIZE];
bit_t Behind[square::SIZE][square::SIZE];

bool line_is_empty(int f, int t, const board::Board & bd) {
   return (bd.all() & Between[f][t]) == 0;
}

bit_t ray(int f, int t) {
   return Between[f][t] | Behind[f][t]; // HACK: t should be included
}

bool pawn_move(int sd, int f, int t, const board::Board & bd) {
   assert(sd < side::SIZE);
   return bit::is_set(Pawn_Moves[sd][f], t) && line_is_empty(f, t, bd);
}

bool pawn_attack(int sd, int f, int t) {
   assert(sd < side::SIZE);
   return bit::is_set(Pawn_Attacks[sd][f], t);
}

bool piece_attack(int pc, int f, int t, const board::Board & bd) {
   assert(pc != piece::PAWN);
   return bit::is_set(Piece_Attacks[pc][f], t) && line_is_empty(f, t, bd);
}

bool attack(int pc, int sd, int f, int t, const board::Board & bd) {
   assert(sd < side::SIZE);
   if (pc == piece::PAWN) {
      return pawn_attack(sd, f, t);
   } else {
      return piece_attack(pc, f, t, bd);
   }
}

bit_t pawn_moves_from(int sd, const board::Board & bd) { // for pawn mobility

   assert(sd < side::SIZE);

   bit_t fs = bd.piece(piece::PAWN, sd);

   if (sd == side::WHITE) {
      return fs << 1;
   } else {
      return fs >> 1;
   }
}

bit_t pawn_moves_to(int sd, bit_t ts, const board::Board & bd) {

   assert(sd < side::SIZE);
   assert((bd.all() & ts) == 0);

   bit_t pawns = bd.piece(piece::PAWN, sd);
   bit_t empty = bd.empty();

   bit_t fs = 0;

   if (sd == side::WHITE) {
      fs |= (ts >> 1);
      fs |= (ts >> 2) & (empty >> 1) & bit::rank(square::RANK_2);
   } else {
      fs |= (ts << 1);
      fs |= (ts << 2) & (empty << 1) & bit::rank(square::RANK_7);
   }

   return pawns & fs;
}

bit_t pawn_attacks_from(int sd, const board::Board & bd) {

   assert(sd < side::SIZE);

   bit_t fs = bd.piece(piece::PAWN, sd);

   if (sd == side::WHITE) {
      return (fs >> 7) | (fs << 9);
   } else {
      return (fs >> 9) | (fs << 7);
   }
}

bit_t pawn_attacks_tos(int sd, bit_t ts) {

   assert(sd < side::SIZE);

   if (sd == side::WHITE) {
      return (ts >> 9) | (ts << 7);
   } else {
      return (ts >> 7) | (ts << 9);
   }
}

bit_t pawn_attacks_from(int sd, int f) {
   assert(sd < side::SIZE);
   return Pawn_Attacks[sd][f];
}

bit_t pawn_attacks_to(int sd, int t) {
   assert(sd < side::SIZE);
   return pawn_attacks_from(side::opposit(sd), t);
}

bit_t piece_attacks_from(int pc, int f, const board::Board & bd) {

   assert(pc != piece::PAWN);

   bit_t ts = Piece_Attacks[pc][f];

   for (bit_t b = bd.all() & Blockers[pc][f]; b != 0; b = bit::rest(b)) {
      int sq = bit::first(b);
      ts &= ~Behind[f][sq];
   }

   return ts;
}

bit_t piece_attacks_to(int pc, int t, const board::Board & bd) {
   assert(pc != piece::PAWN);
   return piece_attacks_from(pc, t, bd);
}

bit_t piece_moves_from(int pc, int sd, int f, const board::Board & bd) {
   if (pc == piece::PAWN) {
      assert(false); // TODO: blockers
      return Pawn_Moves[sd][f];
   } else {
      return piece_attacks_from(pc, f, bd);
   }
}

bit_t attacks_from(int pc, int sd, int f, const board::Board & bd) {
   if (pc == piece::PAWN) {
      return Pawn_Attacks[sd][f];
   } else {
      return piece_attacks_from(pc, f, bd);
   }
}

bit_t attacks_to(int pc, int sd, int t, const board::Board & bd) {
   return attacks_from(pc, side::opposit(sd), t, bd); // HACK for pawns
}

bit_t pseudo_attacks_from(int pc, int sd, int f) {
   if (pc == piece::PAWN) {
      return Pawn_Attacks[sd][f];
   } else {
      return Piece_Attacks[pc][f];
   }
}

bit_t pseudo_attacks_to(int pc, int sd, int t) {
   return pseudo_attacks_from(pc, side::opposit(sd), t); // HACK for pawns
}

bit_t slider_pseudo_attacks_to(int sd, int t, const board::Board & bd) {

   assert(sd < side::SIZE);

   bit_t b = 0;
   b |= bd.piece(piece::BISHOP, sd) & Piece_Attacks[piece::BISHOP][t];
   b |= bd.piece(piece::ROOK,   sd) & Piece_Attacks[piece::ROOK][t];
   b |= bd.piece(piece::QUEEN,  sd) & Piece_Attacks[piece::QUEEN][t];

   return b;
}

bool attack_behind(int f, int t, int sd, const board::Board & bd) {

   assert(bd.square(t) != piece::NONE);

   bit_t behind = Behind[f][t];
   if (behind == 0) return false;

   for (bit_t b = slider_pseudo_attacks_to(sd, t, bd) & behind; b != 0; b = bit::rest(b)) {

      int sq = bit::first(b);

      if (bit::single(bd.all() & Between[sq][f])) {
         return true;
      }
   }

   return false;
}

bool is_attacked(int t, int sd, const board::Board & bd) {

   // non-sliders

   if ((bd.piece(piece::PAWN, sd) & Pawn_Attacks[side::opposit(sd)][t]) != 0) { // HACK
      return true;
   }

   if ((bd.piece(piece::KNIGHT, sd) & Piece_Attacks[piece::KNIGHT][t]) != 0) {
      return true;
   }

   if ((bd.piece(piece::KING, sd) & Piece_Attacks[piece::KING][t]) != 0) {
      return true;
   }

   // sliders

   for (bit_t b = slider_pseudo_attacks_to(sd, t, bd); b != 0; b = bit::rest(b)) {

      int f = bit::first(b);

      if ((bd.all() & Between[f][t]) == 0) {
         return true;
      }
   }

   return false;
}

bit_t pinned_by(int t, int sd, const board::Board & bd) {

   bit_t pinned = 0;

   for (bit_t b = slider_pseudo_attacks_to(sd, t, bd); b != 0; b = bit::rest(b)) {

      int f = bit::first(b);

      bit_t bb = bd.all() & Between[f][t];

      if (bb != 0 && bit::single(bb)) {
         pinned |= bb;
      }
   }

   return pinned;
}

void init_attacks(Attacks & attacks, int sd, const board::Board & bd) { // for strictly-legal moves

   int atk = side::opposit(sd);
   int def = sd;

   int t = bd.king(def);

   attacks.size   = 0;
   attacks.avoid  = 0;
   attacks.pinned = 0;

   // non-sliders

   {
      bit_t b = 0;
      b |= bd.piece(piece::PAWN,   atk) & Pawn_Attacks[def][t]; // HACK
      b |= bd.piece(piece::KNIGHT, atk) & Piece_Attacks[piece::KNIGHT][t];

      if (b != 0) {
         assert(bit::single(b));
         assert(attacks.size < 2);
         attacks.square[attacks.size++] = bit::first(b);
      }
   }

   // sliders

   for (bit_t b = slider_pseudo_attacks_to(atk, t, bd); b != 0; b = bit::rest(b)) {

      int f = bit::first(b);

      bit_t bb = bd.all() & Between[f][t];

      if (bb == 0) {
         assert(attacks.size < 2);
         attacks.square[attacks.size++] = f;
         attacks.avoid |= ray(f, t);
      } else if (bit::single(bb)) {
         attacks.pinned |= bb;
      }
   }
}

void init_attacks(Attacks & attacks, const board::Board & bd) {
   init_attacks(attacks, bd.turn(), bd);
}

bool is_legal(const board::Board & bd) {

   int atk = bd.turn();
   int def = side::opposit(atk);

   return !is_attacked(bd.king(def), atk, bd);
}

bool is_in_check(const board::Board & bd) {

   int atk = bd.turn();
   int def = side::opposit(atk);

   return is_attacked(bd.king(atk), def, bd);
}

bit_t pawn_moves_debug(int sd, int sq) {

   assert(sd < side::SIZE);

   bit_t b = 0;

   int f = square::to_88(sq);
   int inc = Pawn_Move[sd];

   int t = f + inc;

   if (square::is_valid_88(t)) {
      bit::set(b, square::from_88(t));
   }

   if (square::rank(sq, sd) == square::RANK_2) {
      t += inc;
      assert(square::is_valid_88(t));
      bit::set(b, square::from_88(t));
   }

   return b;
}

bit_t pawn_attacks_debug(int sd, int sq) {

   assert(sd < side::SIZE);

   bit_t b = 0;

   int f = square::to_88(sq);

   for (int dir = 0; dir < 2; dir++) {
      int t = f + Pawn_Attack[sd][dir];
      if (square::is_valid_88(t)) {
         bit::set(b, square::from_88(t));
      }
   }

   return b;
}

bit_t piece_attacks_debug(int pc, int sq) {

   assert(pc != piece::PAWN);

   bit_t b = 0;

   int f = square::to_88(sq);

   for (int dir = 0; true; dir++) {

      int inc = Piece_Inc[pc][dir];
      if (inc == 0) break;

      if (piece::is_slider(pc)) {

         for (int t = f + inc; square::is_valid_88(t); t += inc) {
            bit::set(b, square::from_88(t));
         }

      } else {

         int t = f + inc;

         if (square::is_valid_88(t)) {
            bit::set(b, square::from_88(t));
         }
      }
   }

   return b;
}

int delta_inc(int f, int t) {

   for (int dir = 0; dir < 8; dir++) {

      int inc = Queen_Inc[dir];

      for (int sq = f + inc; square::is_valid_88(sq); sq += inc) {
         if (sq == t) {
            return inc;
         }
      }
   }

   return 0;
}

bit_t between_debug(int f, int t) {

   f = square::to_88(f);
   t = square::to_88(t);

   bit_t b = 0;

   int inc = delta_inc(f, t);

   if (inc != 0) {
      for (int sq = f + inc; sq != t; sq += inc) {
         bit::set(b, square::from_88(sq));
      }
   }

   return b;
}

bit_t behind_debug(int f, int t) {

   f = square::to_88(f);
   t = square::to_88(t);

   bit_t b = 0;

   int inc = delta_inc(f, t);

   if (inc != 0) {
      for (int sq = t + inc; square::is_valid_88(sq); sq += inc) {
         bit::set(b, square::from_88(sq));
      }
   }

   return b;
}

bit_t blockers_debug(int pc, int f) {

   assert(pc != piece::PAWN);

   bit_t b = 0;

   bit_t attacks = piece_attacks_debug(pc, f);

   for (bit_t bb = attacks; bb != 0; bb = bit::rest(bb)) {
      int sq = bit::first(bb);
      if ((attacks & behind_debug(f, sq)) != 0) {
         bit::set(b, sq);
      }
   }

   return b;
}

void init() {

   for (int sd = 0; sd < side::SIZE; sd++) {
      for (int sq = 0; sq < square::SIZE; sq++) {
         Pawn_Moves[sd][sq] = pawn_moves_debug(sd, sq);
         Pawn_Attacks[sd][sq] = pawn_attacks_debug(sd, sq);
      }
   }

   for (int pc = piece::KNIGHT; pc <= piece::KING; pc++) {
      for (int sq = 0; sq < square::SIZE; sq++) {
         Piece_Attacks[pc][sq] = piece_attacks_debug(pc, sq);
         Blockers[pc][sq] = blockers_debug(pc, sq);
      }
   }

   for (int f = 0; f < square::SIZE; f++) {
      for (int t = 0; t < square::SIZE; t++) {
         Between[f][t] = between_debug(f, t);
         Behind[f][t]  = behind_debug(f, t);
      }
   }
}

}

namespace gen {

class List {

private:

   static const int SIZE = 256;

   int p_size;
   uint32 p_pair[SIZE];

   void move_to(int pf, int pt) {

      assert(pt <= pf && pf < p_size);

      uint32 p = p_pair[pf];

      for (int i = pf; i > pt; i--) {
         p_pair[i] = p_pair[i - 1];
      }

      p_pair[pt] = p;
   }

   void add_pair(uint32 p) {
      assert(p_size < SIZE);
      p_pair[p_size++] = p;
   }

   uint32 pair(int pos) const {
      assert(pos < p_size);
      return p_pair[pos];
   }

public:

   List() {
      clear();
   }

   void operator=(const List & ml) {

      clear();

      for (int pos = 0; pos < ml.size(); pos++) {
         uint32 p = ml.pair(pos);
         add_pair(p);
      }
   }

   void clear() {
      p_size = 0;
   }

   void add(int mv, int sc = 0) {
      assert(mv >= 0 && mv < move::SIZE);
      assert(sc >= 0 && sc < move::SCORE_SIZE);
      assert(!contain(mv));
      add_pair((sc << move::BITS) | mv);
   }

   void set_score(int pos, int sc) {
      assert(pos < p_size);
      assert(sc >= 0 && sc < move::SCORE_SIZE);
      p_pair[pos] = (sc << move::BITS) | move(pos);
      assert(score(pos) == sc);
   }

   void move_to_front(int pos) {
      move_to(pos, 0);
   }

   void sort() { // insertion sort

      for (int i = 1; i < p_size; i++) {

         uint32 p = p_pair[i];

         int j;

         for (j = i; j > 0 && p_pair[j - 1] < p; j--) {
            p_pair[j] = p_pair[j - 1];
         }

         p_pair[j] = p;
      }

      for (int i = 0; i < p_size - 1; i++) {
         assert(p_pair[i] >= p_pair[i + 1]);
      }
   }

   int size() const {
      return p_size;
   }

   int move(int pos) const {
      return pair(pos) & move::MASK;
   }

   int score(int pos) const {
      return pair(pos) >> move::BITS;
   }

   bool contain(int mv) const {

      for (int pos = 0; pos < size(); pos++) {
         if (move(pos) == mv) {
            return true;
         }
      }

      return false;
   }

};

void add_pawn_move(List & ml, int f, int t, const board::Board & bd) {

   assert(bd.square(f) == piece::PAWN);

   int pc = bd.square(f);
   int cp = bd.square(t);

   if (square::is_promotion(t)) {
      ml.add(move::make(f, t, pc, cp, piece::QUEEN));
      ml.add(move::make(f, t, pc, cp, piece::KNIGHT));
      ml.add(move::make(f, t, pc, cp, piece::ROOK));
      ml.add(move::make(f, t, pc, cp, piece::BISHOP));
   } else {
      ml.add(move::make(f, t, pc, cp));
   }
}

void add_piece_move(List & ml, int f, int t, const board::Board & bd) {
   assert(bd.square(f) != piece::PAWN);
   ml.add(move::make(f, t, bd.square(f), bd.square(t)));
}

void add_move(List & ml, int f, int t, const board::Board & bd) {
   if (bd.square(f) == piece::PAWN) {
      add_pawn_move(ml, f, t, bd);
   } else {
      add_piece_move(ml, f, t, bd);
   }
}

void add_piece_moves_from(List & ml, int f, bit_t ts, const board::Board & bd) {

   int pc = bd.square(f);

   for (bit_t b = attack::piece_attacks_from(pc, f, bd) & ts; b != 0; b = bit::rest(b)) {
      int t = bit::first(b);
      add_piece_move(ml, f, t, bd);
   }
}

void add_captures_to(List & ml, int sd, int t, const board::Board & bd) {

   for (int pc = piece::PAWN; pc <= piece::KING; pc++) {
      for (bit_t b = bd.piece(pc, sd) & attack::attacks_to(pc, sd, t, bd); b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         add_move(ml, f, t, bd);
      }
   }
}

void add_captures_to_no_king(List & ml, int sd, int t, const board::Board & bd) { // for evasions

   for (int pc = piece::PAWN; pc <= piece::QUEEN; pc++) { // skip king
      for (bit_t b = bd.piece(pc, sd) & attack::attacks_to(pc, sd, t, bd); b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         add_move(ml, f, t, bd);
      }
   }
}

void add_pawn_captures(List & ml, int sd, bit_t ts, const board::Board & bd) {

   bit_t pawns = bd.piece(piece::PAWN, sd);
   ts &= bd.side(side::opposit(sd)); // not needed

   if (sd == side::WHITE) {

      for (bit_t b = (ts << 7) & pawns; b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         int t = f - 7;
         add_pawn_move(ml, f, t, bd);
      }

      for (bit_t b = (ts >> 9) & pawns; b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         int t = f + 9;
         add_pawn_move(ml, f, t, bd);
      }

   } else {

      for (bit_t b = (ts << 9) & pawns; b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         int t = f - 9;
         add_pawn_move(ml, f, t, bd);
      }

      for (bit_t b = (ts >> 7) & pawns; b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         int t = f + 7;
         add_pawn_move(ml, f, t, bd);
      }
   }
}

void add_promotions(List & ml, int sd, bit_t ts, const board::Board & bd) {

   bit_t pawns = bd.piece(piece::PAWN, sd);

   if (sd == side::WHITE) {

      for (bit_t b = pawns & (ts >> 1) & bit::rank(square::RANK_7); b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         int t = f + 1;
         assert(bd.square(t) == piece::NONE);
         assert(square::is_promotion(t));
         add_pawn_move(ml, f, t, bd);
      }

   } else {

      for (bit_t b = pawns & (ts << 1) & bit::rank(square::RANK_2); b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         int t = f - 1;
         assert(bd.square(t) == piece::NONE);
         assert(square::is_promotion(t));
         add_pawn_move(ml, f, t, bd);
      }
   }
}

void add_promotions(List & ml, int sd, const board::Board & bd) {
   add_promotions(ml, sd, bd.empty(), bd);
}

void add_pawn_quiets(List & ml, int sd, bit_t ts, const board::Board & bd) {

   bit_t pawns = bd.piece(piece::PAWN, sd);
   bit_t empty = bd.empty();

   if (sd == side::WHITE) {

      for (bit_t b = pawns & (ts >> 1) & ~bit::rank(square::RANK_7); b != 0; b = bit::rest(b)) { // don't generate promotions
         int f = bit::first(b);
         int t = f + 1;
         assert(bd.square(t) == piece::NONE);
         assert(!square::is_promotion(t));
         add_pawn_move(ml, f, t, bd);
      }

      for (bit_t b = pawns & (ts >> 2) & (empty >> 1) & bit::rank(square::RANK_2); b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         int t = f + 2;
         assert(bd.square(t) == piece::NONE);
         assert(!square::is_promotion(t));
         add_pawn_move(ml, f, t, bd);
      }

   } else {

      for (bit_t b = pawns & (ts << 1) & ~bit::rank(square::RANK_2); b != 0; b = bit::rest(b)) { // don't generate promotions
         int f = bit::first(b);
         int t = f - 1;
         assert(bd.square(t) == piece::NONE);
         assert(!square::is_promotion(t));
         add_pawn_move(ml, f, t, bd);
      }

      for (bit_t b = pawns & (ts << 2) & (empty << 1) & bit::rank(square::RANK_7); b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         int t = f - 2;
         assert(bd.square(t) == piece::NONE);
         assert(!square::is_promotion(t));
         add_pawn_move(ml, f, t, bd);
      }
   }
}

void add_pawn_pushes(List & ml, int sd, const board::Board & bd) {

   bit_t ts = 0;

   if (sd == side::WHITE) {

      ts |= bit::rank(square::RANK_7);
      ts |= bit::rank(square::RANK_6) & ~attack::pawn_attacks_from(side::BLACK, bd) & (~bd.piece(piece::PAWN) >> 1); // HACK: direct access

   } else {

      ts |= bit::rank(square::RANK_2);
      ts |= bit::rank(square::RANK_3) & ~attack::pawn_attacks_from(side::WHITE, bd) & (~bd.piece(piece::PAWN) << 1); // HACK: direct access
   }

   add_pawn_quiets(ml, sd, ts & bd.empty(), bd);
}

void add_en_passant(List & ml, int sd, const board::Board & bd) {

   int t = bd.ep_sq();

   if (t != square::NONE) {

      bit_t fs = bd.piece(piece::PAWN, sd) & attack::Pawn_Attacks[side::opposit(sd)][t];

      for (bit_t b = fs; b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         ml.add(move::make(f, t, piece::PAWN, piece::PAWN));
      }
   }
}

bool can_castle(int sd, int wg, const board::Board & bd) {

   int index = castling::index(sd, wg);

   if (castling::flag(bd.flags(), index)) {

      int kf = castling::info[index].kf;
      // int kt = castling::info[index].kt;
      int rf = castling::info[index].rf;
      int rt = castling::info[index].rt;

      assert(bd.square_is(kf, piece::KING, sd));
      assert(bd.square_is(rf, piece::ROOK, sd));

      return attack::line_is_empty(kf, rf, bd) && !attack::is_attacked(rt, side::opposit(sd), bd);
   }

   return false;
}

void add_castling(List & ml, int sd, const board::Board & bd) {

   for (int wg = 0; wg < wing::SIZE; wg++) {
      if (can_castle(sd, wg, bd)) {
         int index = castling::index(sd, wg);
         add_piece_move(ml, castling::info[index].kf, castling::info[index].kt, bd);
      }
   }
}

void add_piece_moves(List & ml, int sd, bit_t ts, const board::Board & bd) {

   assert(ts != 0);

   for (int pc = piece::KNIGHT; pc <= piece::KING; pc++) {
      for (bit_t b = bd.piece(pc, sd); b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         add_piece_moves_from(ml, f, ts, bd);
      }
   }
}

void add_piece_moves_no_king(List & ml, int sd, bit_t ts, const board::Board & bd) { // for evasions

   assert(ts != 0);

   for (int pc = piece::KNIGHT; pc <= piece::QUEEN; pc++) { // skip king
      for (bit_t b = bd.piece(pc, sd); b != 0; b = bit::rest(b)) {
         int f = bit::first(b);
         add_piece_moves_from(ml, f, ts, bd);
      }
   }
}

void add_piece_moves_rare(List & ml, int sd, bit_t ts, const board::Board & bd) { // for captures

   assert(ts != 0);

   for (int pc = piece::KNIGHT; pc <= piece::KING; pc++) {

      for (bit_t b = bd.piece(pc, sd); b != 0; b = bit::rest(b)) {

         int f = bit::first(b);

         for (bit_t bb = attack::pseudo_attacks_from(pc, sd, f) & ts; bb != 0; bb = bit::rest(bb)) {

            int t = bit::first(bb);

            if (attack::line_is_empty(f, t, bd)) {
               add_piece_move(ml, f, t, bd);
            }
         }
      }
   }
}

void add_captures(List & ml, int sd, const board::Board & bd) {

   bit_t ts = bd.side(side::opposit(sd));

   add_pawn_captures(ml, sd, ts, bd);
   add_piece_moves_rare(ml, sd, ts, bd);
   add_en_passant(ml, sd, bd);
}

void add_captures_mvv_lva(List & ml, int sd, const board::Board & bd) { // unused

   for (int pc = piece::QUEEN; pc >= piece::PAWN; pc--) {
      for (bit_t b = bd.piece(pc, side::opposit(sd)); b != 0; b = bit::rest(b)) {
         int t = bit::first(b);
         add_captures_to(ml, sd, t, bd);
      }
   }

   add_en_passant(ml, sd, bd);
}

bool is_move(int mv, const board::Board & bd) { // for TT-move legality

   int sd = bd.turn();

   int f = move::from(mv);
   int t = move::to(mv);

   int pc = move::piece(mv);
   int cp = move::cap(mv);

   if (!(bd.square(f) == pc && bd.square_side(f) == sd)) {
      return false;
   }

   if (bd.square(t) != piece::NONE && bd.square_side(t) == sd) {
      return false;
   }

   if (pc == piece::PAWN && t == bd.ep_sq()) {
      if (cp != piece::PAWN) {
         return false;
      }
   } else if (bd.square(t) != cp) {
      return false;
   }

   if (cp == piece::KING) {
      return false;
   }

   if (pc == piece::PAWN) {

      // TODO

      return true;

   } else {

      // TODO: castling

      // return attack::piece_attack(pc, f, t, bd);

      return true;
   }

   assert(false);
}

bool is_quiet_move(int mv, const board::Board & bd) { // for killer legality

   int sd = bd.turn();

   int f = move::from(mv);
   int t = move::to(mv);

   int pc = move::piece(mv);
   assert(move::cap(mv) == piece::NONE);
   assert(move::prom(mv) == piece::NONE);

   if (!(bd.square(f) == pc && bd.square_side(f) == sd)) {
      return false;
   }

   if (bd.square(t) != piece::NONE) {
      return false;
   }

   if (pc == piece::PAWN) {

      int inc = square::pawn_inc(sd);

      if (false) {
      } else if (t - f == inc && !square::is_promotion(t)) {
         return true;
      } else if (t - f == inc * 2 && square::rank(f, sd) == square::RANK_2) {
         return bd.square(f + inc) == piece::NONE;
      } else {
         return false;
      }

   } else {

      // TODO: castling

      return attack::piece_attack(pc, f, t, bd);
   }

   assert(false);
}

void add_quiets(List & ml, int sd, const board::Board & bd) {
   add_castling(ml, sd, bd);
   add_piece_moves(ml, sd, bd.empty(), bd);
   add_pawn_quiets(ml, sd, bd.empty(), bd);
}

void add_evasions(List & ml, int sd, const board::Board & bd, const attack::Attacks & attacks) {

   assert(attacks.size > 0);

   int king = bd.king(sd);

   add_piece_moves_from(ml, king, ~bd.side(sd) & ~attacks.avoid, bd);

   if (attacks.size == 1) {

      int t = attacks.square[0];

      add_captures_to_no_king(ml, sd, t, bd);
      add_en_passant(ml, sd, bd);

      bit_t ts = attack::Between[king][t];
      assert(attack::line_is_empty(king, t, bd));

      if (ts != 0) {
         add_pawn_quiets(ml, sd, ts, bd);
         add_promotions(ml, sd, ts, bd);
         add_piece_moves_no_king(ml, sd, ts, bd);
      }
   }
}

void add_evasions(List & ml, int sd, const board::Board & bd) {
   attack::Attacks attacks;
   attack::init_attacks(attacks, sd, bd);
   add_evasions(ml, sd, bd, attacks);
}

void add_checks(List & ml, int sd, const board::Board & bd) {

   int atk = sd;
   int def = side::opposit(sd);

   int king = bd.king(def);
   bit_t pinned = attack::pinned_by(king, atk, bd);
   bit_t empty = bd.empty();
   empty &= ~attack::pawn_attacks_from(side::opposit(sd), bd); // pawn-safe

   // discovered checks

   for (bit_t fs = bd.pieces(atk) & pinned; fs != 0; fs = bit::rest(fs)) { // TODO: pawns
      int f = bit::first(fs);
      bit_t ts = empty & ~attack::ray(king, f); // needed only for pawns
      add_piece_moves_from(ml, f, ts, bd);
   }

   // direct checks, pawns

   {
      bit_t ts = attack::pseudo_attacks_to(piece::PAWN, sd, king) & empty;

      add_pawn_quiets(ml, sd, ts, bd);
   }

   // direct checks, knights

   {
      int pc = piece::KNIGHT;

      bit_t attacks = attack::pseudo_attacks_to(pc, sd, king) & empty;

      for (bit_t b = bd.piece(pc, sd) & ~pinned; b != 0; b = bit::rest(b)) {

         int f = bit::first(b);

         bit_t moves = attack::pseudo_attacks_from(pc, sd, f);

         for (bit_t bb = moves & attacks; bb != 0; bb = bit::rest(bb)) {
            int t = bit::first(bb);
            add_piece_move(ml, f, t, bd);
         }
      }
   }

   // direct checks, sliders

   for (int pc = piece::BISHOP; pc <= piece::QUEEN; pc++) {

      bit_t attacks = attack::pseudo_attacks_to(pc, sd, king) & empty;

      for (bit_t b = bd.piece(pc, sd) & ~pinned; b != 0; b = bit::rest(b)) {

         int f = bit::first(b);

         bit_t moves = attack::pseudo_attacks_from(pc, sd, f);

         for (bit_t bb = moves & attacks; bb != 0; bb = bit::rest(bb)) {

            int t = bit::first(bb);

            if (attack::line_is_empty(f, t, bd) && attack::line_is_empty(t, king, bd)) {
               add_piece_move(ml, f, t, bd);
            }
         }
      }
   }
}

bool is_legal_debug(int mv, board::Board & bd) { // HACK: duplicate from Move_Type

   bd.move(mv);
   bool b = attack::is_legal(bd);
   bd.undo();

   return b;
}

void gen_moves_debug(List & ml, const board::Board & bd) {

   ml.clear();

   int sd = bd.turn();

   if (attack::is_in_check(bd)) {
      add_evasions(ml, sd, bd);
   } else {
      add_captures(ml, sd, bd);
      add_promotions(ml, sd, bd);
      add_quiets(ml, sd, bd);
   }
}

void filter_legals(List & dst, const List & src, board::Board & bd) {

   dst.clear();

   for (int pos = 0; pos < src.size(); pos++) {

      int mv = src.move(pos);

      if (is_legal_debug(mv, bd)) {
         dst.add(mv);
      }
   }
}

void gen_legals(List & ml, board::Board & bd) {

   List pseudos;
   gen_moves_debug(pseudos, bd);

   filter_legals(ml, pseudos, bd);
}

void gen_legal_evasions(List & ml, board::Board & bd) {

   int sd = bd.turn();

   attack::Attacks attacks;
   attack::init_attacks(attacks, sd, bd);

   if (attacks.size == 0) {
      ml.clear();
      return;
   }

   List pseudos;
   add_evasions(pseudos, sd, bd, attacks);

   filter_legals(ml, pseudos, bd);
}

}

namespace score {

enum {
   NONE     = -10000,
   MIN      =  -9999,
   EVAL_MIN =  -8999,
   EVAL_MAX =  +8999,
   MAX      =  +9999,
   MATE     = +10000,
};

enum {
   FLAGS_NONE  = 0,
   FLAGS_LOWER = 1 << 0,
   FLAGS_UPPER = 1 << 1,
   FLAGS_EXACT = FLAGS_LOWER | FLAGS_UPPER,
};

bool is_mate(int sc) {
   return sc < EVAL_MIN || sc > EVAL_MAX;
}

int signed_mate(int sc) {
   if (sc < EVAL_MIN) { // -MATE
      return -(MATE + sc) / 2;
   } else if (sc > EVAL_MAX) { // +MATE
      return (MATE - sc + 1) / 2;
   } else {
      assert(false);
      return 0;
   }
}

int side_score(int sc, int sd) {
   return (sd == side::WHITE) ? +sc : -sc;
}

int from_trans(int sc, int ply) {
   if (sc < EVAL_MIN) {
      return sc + ply;
   } else if (sc > EVAL_MAX) {
      return sc - ply;
   } else {
      return sc;
   }
}

int to_trans(int sc, int ply) {
   if (sc < EVAL_MIN) {
      return sc - ply;
   } else if (sc > EVAL_MAX) {
      return sc + ply;
   } else {
      return sc;
   }
}

int flags(int sc, int alpha, int beta) {

   int flags = FLAGS_NONE;
   if (sc > alpha) flags |= FLAGS_LOWER;
   if (sc < beta)  flags |= FLAGS_UPPER;

   return flags;
}

}

namespace trans {

struct Entry { // 16 bytes
   uint32 lock;
   uint32 move; // TODO: uint16 #
   uint16 pad_1;
   int16 score;
   uint8 date;
   int8 depth;
   uint8 flags;
   uint8 pad_2;
};

void clear_entry(Entry & entry) {

   assert(sizeof(Entry) == 16);

   entry.lock = 0;
   entry.move = move::NONE;
   entry.pad_1 = 0;
   entry.score = 0;
   entry.date = 0;
   entry.depth = -1;
   entry.flags = score::FLAGS_NONE;
   entry.pad_2 = 0;
}

class Table {

private:

   Entry * p_table;
   int p_bits;
   uint64 p_size;
   uint64 p_mask;

   int p_date;
   uint64 p_used;

   int size_to_bits(int size) {

      int bits = 0;

      for (uint64 entries = (uint64(size) << 20) / sizeof(Entry); entries > 1; entries /= 2) {
         bits++;
      }

      return bits;
   }

public:

   Table() {

      p_table = NULL;
      p_bits = 0;
      p_size = 1;
      p_mask = 0;

      p_date = 0;
      p_used = 0;
   }

   void set_size(int size) {

      int bits = size_to_bits(size);
      if (bits == p_bits) return;

      p_bits = bits;
      p_size = U64(1) << bits;
      p_mask = p_size - 1;

      if (p_table != NULL) {
         free();
         alloc();
      }
   }

   void alloc() {
      assert(p_table == NULL);
      p_table = new Entry[p_size];
      clear();
   }

   void free() {
      assert(p_table != NULL);
      delete [] p_table;
      p_table = NULL;
   }

   void clear() {

      Entry e;
      clear_entry(e);

      for (uint64 i = 0; i < p_size; i++) {
         p_table[i] = e;
      }

      p_date = 1;
      p_used = 0;
   }

   void inc_date() {
      p_date = (p_date + 1) % 256;
      p_used = 0;
   }

   void store(hash_t key, int depth, int ply, int move, int score, int flags) {

      assert(depth >= 0 && depth < 100);
      assert(move != move::NULL_);
      assert(score >= score::MIN && score <= score::MAX);

      score = score::to_trans(score, ply);

      uint64 index = hash::index(key) & p_mask;
      uint32 lock  = hash::lock(key);

      Entry * be = NULL;
      int bs = -1;

      for (uint64 i = 0; i < 4; i++) {

         uint64 idx = (index + i) & p_mask;
         assert(idx < p_size);
         Entry & entry = p_table[idx];

         if (entry.lock == lock) {

            if (entry.date != p_date) {
               entry.date = p_date;
               p_used++;
            }

            if (depth >= entry.depth) {
               if (move != move::NONE) entry.move = move;
               entry.depth = depth;
               entry.score = score;
               entry.flags = flags;
            } else if (entry.move == move::NONE) {
               entry.move = move;
            }

            return;
         }

         int sc = 99 - entry.depth; // NOTE: entry.depth can be -1
         if (entry.date != p_date) sc += 101;
         assert(sc >= 0 && sc < 202);

         if (sc > bs) {
            be = &entry;
            bs = sc;
         }
      }

      assert(be != NULL);

      if (be->date != p_date) p_used++;

      be->lock = lock;
      be->date = p_date;
      be->move = move;
      be->depth = depth;
      be->score = score;
      be->flags = flags;
   }

   bool retrieve(hash_t key, int depth, int ply, int & move, int & score, int & flags) {

      assert(depth >= 0 && depth < 100);

      uint64 index = hash::index(key) & p_mask;
      uint32 lock  = hash::lock(key);

      for (uint64 i = 0; i < 4; i++) {

         uint64 idx = (index + i) & p_mask;
         assert(idx < p_size);
         Entry & entry = p_table[idx];

         if (entry.lock == lock) {

            if (entry.date != p_date) {
               entry.date = p_date; // touch entry
               p_used++;
            }

            move = entry.move;
            score = score::from_trans(entry.score, ply);
            flags = entry.flags;

            if (entry.depth >= depth) {
               return true;
            } else if (score::is_mate(score)) {
               flags &= ~(score < 0 ? score::FLAGS_LOWER : score::FLAGS_UPPER);
               return true;
            }

            return false;
         }
      }

      return false;
   }

   int used() const {
      return int((p_used * 1000 + p_size / 2) / p_size);
   }

};

}

namespace engine {

struct Engine {
   int hash;
   bool ponder;
   int threads;
   bool log;
};

Engine engine;

void init() {
   engine.hash = 64;
   engine.ponder = false;
   engine.threads = 1;
   engine.log = false;
}

}

namespace pawn { // HACK: early declaration for pawn-pushes move type

bit_t passed_me[square::SIZE][side::SIZE];
bit_t passed_opp[square::SIZE][side::SIZE];

bool is_passed(int sq, int sd, const board::Board & bd) {
   return (bd.piece(piece::PAWN, side::opposit(sd)) & passed_opp[sq][sd]) == 0
       && (bd.piece(piece::PAWN, sd) & passed_me[sq][sd]) == 0;
}

int square_distance(int ks, int ps, int sd) {
   int prom = square::promotion(ps, sd);
   return square::distance(ks, prom) - square::distance(ps, prom);
}

}

namespace move {

bool is_win (int mv, const board::Board & bd);

class SEE {

private:

   const board::Board * p_board;
   int p_to;
   bit_t p_all;

   int p_val;
   int p_side;

   void init(int t, int sd) {

      p_to = t;
      p_all = p_board->all();

      int pc = p_board->square(t);

      p_val = piece::value(pc);
      p_side = sd;
   }

   int move(int f) {

      assert(bit::is_set(p_all, f));
      bit::clear(p_all, f);

      int pc = p_board->square(f);
      assert(pc != piece::NONE && p_board->square_side(f) == p_side);

      int val = p_val;
      p_val = piece::value(pc);

      if (pc == piece::PAWN && square::is_promotion(p_to)) {
         int delta = piece::QUEEN_VALUE - piece::PAWN_VALUE;
         val   += delta;
         p_val += delta;
      }

      if (val == piece::KING_VALUE) { // stop at king capture
         p_all = 0; // HACK: erase all attackers
      }

      p_side = side::opposit(p_side);

      return val;
   }

   int see_rec(int alpha, int beta) {

      assert(alpha < beta);

      int s0 = 0;

      if (s0 > alpha) {
         alpha = s0;
         if (s0 >= beta) return s0;
      }

      if (p_val <= alpha) { // FP, NOTE: fails for promotions
         return p_val;
      }

      int f = pick_lva();

      if (f == square::NONE) {
         return s0;
      }

      int cap = move(f); // NOTE: has side effect
      int s1 = cap - see_rec(cap - beta, cap - alpha);

      return std::max(s0, s1);
   }

   int pick_lva() const {

      int sd = p_side;

      for (int pc = piece::PAWN; pc <= piece::KING; pc++) {

         bit_t fs = p_board->piece(pc, sd) & attack::pseudo_attacks_to(pc, sd, p_to) & p_all;

         for (bit_t b = fs; b != 0; b = bit::rest(b)) {

            int f = bit::first(b);

            if ((p_all & attack::Between[f][p_to]) == 0) {
               return f;
            }
         }
      }

      return square::NONE;
   }

public:

   int see(int mv, int alpha, int beta, const board::Board & bd) {

      assert(alpha < beta);

      p_board = &bd;

      int f = from(mv);
      int t = to(mv);

      int pc = p_board->square(f);
      int sd = p_board->square_side(f);

      init(t, sd);
      int cap = move(f); // NOTE: assumes queen promotion

      if (pc == piece::PAWN && square::is_promotion(t)) { // adjust for under-promotion
         int delta = piece::QUEEN_VALUE - piece::value(prom(mv));
         cap   -= delta;
         p_val -= delta;
      }

      return cap - see_rec(cap - beta, cap - alpha);
   }

};

bool is_capture(int mv) {
   return cap(mv) != piece::NONE;
}

bool is_en_passant(int mv, const board::Board & bd) {
   return piece(mv) == piece::PAWN && to(mv) == bd.ep_sq();
}

bool is_recapture(int mv, const board::Board & bd) {
   return to(mv) == bd.recap() && is_win(mv, bd);
}

bool is_promotion(int mv) {
   return prom(mv) != piece::NONE;
}

bool is_queen_promotion(int mv) {
   return prom(mv) == piece::QUEEN;
}

bool is_under_promotion(int mv) {
   int pp = prom(mv);
   return pp != piece::NONE && pp != piece::QUEEN;
}

bool is_tactical(int mv) {
   return is_capture(mv) || is_promotion(mv);
}

bool is_pawn_push(int mv, const board::Board & bd) {

   if (is_tactical(mv)) {
      return false;
   }

   int f = from(mv);
   int t = to(mv);

   int pc = bd.square(f);
   int sd = bd.square_side(f);

   return pc == piece::PAWN && square::rank(t, sd) >= square::RANK_6 && pawn::is_passed(t, sd, bd) && !is_capture(mv);
}

bool is_castling(int mv) {
   return piece(mv) == piece::KING && std::abs(to(mv) - from(mv)) == square::CASTLING_DELTA;
}

bool is_conversion(int mv) {
   return is_capture(mv) || piece(mv) == piece::PAWN || is_castling(mv);
}

int make(int f, int t, int pp, const board::Board & bd) {

   int pc = bd.square(f);
   int cp = bd.square(t);

   if (pc == piece::PAWN && t == bd.ep_sq()) {
      cp = piece::PAWN;
   }

   if (pc == piece::PAWN && square::is_promotion(t) && pp == piece::NONE) { // not needed
      pp = piece::QUEEN;
   }

   return make(f, t, pc, cp, pp);
}

int from_string(const std::string & s, const board::Board & bd) {

   assert(s.length() >= 4);

   int f = square::from_string(s.substr(0, 2));
   int t = square::from_string(s.substr(2, 2));
   int pp = (s.length() > 4) ? piece::from_char(std::toupper(s[4])) : piece::NONE;

   return make(f, t, pp, bd);
}

int see(int mv, int alpha, int beta, const board::Board & bd) {
   SEE see;
   return see.see(mv, alpha, beta, bd);
}

int see_max(int mv) {

   assert(is_tactical(mv));

   int sc = piece::value(cap(mv));

   int pp = prom(mv);
   if (pp != piece::NONE) sc += piece::value(pp) - piece::PAWN_VALUE;

   return sc;
}

bool is_safe(int mv, const board::Board & bd) {

   int pc = piece(mv);
   int cp = cap(mv);
   int pp = prom(mv);

   if (false) {
   } else if (pc == piece::KING) {
      return true;
   } else if (piece::value(cp) >= piece::value(pc)) {
      return true;
   } else if (pp != piece::NONE && pp != piece::QUEEN) { // under-promotion
      return false;
   } else {
      return see(mv, -1, 0, bd) >= 0;
   }
}

bool is_win(int mv, const board::Board & bd) {

   assert(is_tactical(mv));

   int pc = piece(mv);
   int cp = cap(mv);
   int pp = prom(mv);

   if (false) {
   } else if (pc == piece::KING) {
      return true;
   } else if (piece::value(cp) > piece::value(pc)) {
      return true;
   } else if (pp != piece::NONE && pp != piece::QUEEN) { // under-promotion
      return false;
   } else {
      return see(mv, 0, +1, bd) > 0;
   }
}

bool is_legal_debug(int mv, board::Board & bd) {

   bd.move(mv);
   bool b = attack::is_legal(bd);
   bd.undo();

   return b;
}

bool is_legal(int mv, board::Board & bd, const attack::Attacks & attacks) {

   int sd = bd.turn();

   int f = from(mv);
   int t = to(mv);

   if (is_en_passant(mv, bd)) {
      return is_legal_debug(mv, bd);
   }

   if (piece(mv) == piece::KING) {
      return !attack::is_attacked(t, side::opposit(sd), bd);
   }

   if (!bit::is_set(attacks.pinned, f)) {
      return true;
   }

   if (bit::is_set(attack::ray(bd.king(sd), f), t)) {
      return true;
   }

   return false;
}

bool is_check_debug(int mv, board::Board & bd) {

   bd.move(mv);
   bool b = attack::is_in_check(bd);
   bd.undo();

   return b;
}

bool is_check(int mv, board::Board & bd) {

   if (is_promotion(mv) || is_en_passant(mv, bd) || is_castling(mv)) {
      return is_check_debug(mv, bd);
   }

   int f = from(mv);
   int t = to(mv);

   int pc = (prom(mv) != piece::NONE) ? prom(mv) : piece(mv);
   int sd = bd.square_side(f);

   int king = bd.king(side::opposit(sd));

   if (attack::attack(pc, sd, t, king, bd)) {
      return true;
   }

   if (attack::attack_behind(king, f, sd, bd) && !bit::is_set(attack::ray(king, f), t)) {
      return true;
   }

   return false;
}

}

namespace sort {

class Killer {

private:

   static const int PLY = 100;

   struct List {
      int k0;
      int k1;
   };

   List p_killer[PLY];

public:

   void clear() {
      for (int ply = 0; ply < PLY; ply++) {
         p_killer[ply].k0 = move::NONE;
         p_killer[ply].k1 = move::NONE;
      }
   }

   void add(int mv, int ply) {
      if (p_killer[ply].k0 != mv) {
         p_killer[ply].k1 = p_killer[ply].k0;
         p_killer[ply].k0 = mv;
      }
   }

   int killer_0(int ply) const {
      return p_killer[ply].k0;
   }

   int killer_1(int ply) const {
      return p_killer[ply].k1;
   }

};

class History {

private:

   static const int PROB_BIT   = 11;
   static const int PROB_ONE   = 1 << PROB_BIT;
   static const int PROB_HALF  = 1 << (PROB_BIT - 1);
   static const int PROB_SHIFT = 5;

   int p_prob[piece::SIDE_SIZE * square::SIZE];

   static int index(int mv, const board::Board & bd) {

      assert(!move::is_tactical(mv));

      int sd = bd.square_side(move::from(mv));
      int p12 = piece::make(move::piece(mv), sd);

      int idx = p12 * square::SIZE + move::to(mv);
      assert(idx < piece::SIDE_SIZE * square::SIZE);

      return idx;
   }

   void update_good(int mv, const board::Board & bd) {
      if (!move::is_tactical(mv)) {
         int idx = index(mv, bd);
         p_prob[idx] += (PROB_ONE - p_prob[idx]) >> PROB_SHIFT;
      }
   }

   void update_bad(int mv, const board::Board & bd) {
      if (!move::is_tactical(mv)) {
         int idx = index(mv, bd);
         p_prob[idx] -= p_prob[idx] >> PROB_SHIFT;
      }
   }

public:

   void clear() {
      for (int idx = 0; idx < piece::SIDE_SIZE * square::SIZE; idx++) {
         p_prob[idx] = PROB_HALF;
      }
   }

   void add(int bm, const gen::List & searched, const board::Board & bd) {

      assert(bm != move::NONE);

      update_good(bm, bd);

      for (int pos = 0; pos < searched.size(); pos++) {
         int mv = searched.move(pos);
         if (mv != bm) update_bad(mv, bd);
      }
   }

   int score(int mv, const board::Board & bd) const {
      int idx = index(mv, bd);
      return p_prob[idx];
   }

};

int capture_score_debug(int pc, int cp) {
   int sc = piece::score(cp) * 6 + (5 - piece::score(pc));
   assert(sc >= 0 && sc < 36);
   return sc;
}

int promotion_score_debug(int pp) {
   switch (pp) {
   case piece::QUEEN:
      return 3;
   case piece::KNIGHT:
      return 2;
   case piece::ROOK:
      return 1;
   case piece::BISHOP:
      return 0;
   default:
      assert(false);
      return 0;
   }
}

int tactical_score_debug(int pc, int cp, int pp) {

   int sc;

   if (cp != piece::NONE) {
      sc = capture_score_debug(pc, cp) + 4;
   } else {
      sc = promotion_score_debug(pp);
   }

   assert(sc >= 0 && sc < 40);
   return sc;
}

int capture_score(int mv) {
   assert(move::is_capture(mv));
   return capture_score_debug(move::piece(mv), move::cap(mv));
}

int promotion_score(int mv) {
   assert(move::is_promotion(mv) && !move::is_capture(mv));
   return promotion_score_debug(move::prom(mv));
}

int tactical_score(int mv) {
   assert(move::is_tactical(mv));
   return tactical_score_debug(move::piece(mv), move::cap(mv), move::prom(mv));
}

int evasion_score(int mv, int trans_move) {

   int sc;

   if (false) {
   } else if (mv == trans_move) {
      sc = move::SCORE_MASK;
   } else if (move::is_tactical(mv)) {
      sc = tactical_score(mv) + 1;
      assert (sc >= 1 && sc < 41);
   } else {
      sc = 0;
   }

   return sc;
}

void sort_tacticals(gen::List & ml) {

   for (int pos = 0; pos < ml.size(); pos++) {
      int mv = ml.move(pos);
      int sc = tactical_score(mv);
      ml.set_score(pos, sc);
   }

   ml.sort();
}

void sort_history(gen::List & ml, const board::Board & bd, const History & history) {

   for (int pos = 0; pos < ml.size(); pos++) {
      int mv = ml.move(pos);
      int sc = history.score(mv, bd);
      ml.set_score(pos, sc);
   }

   ml.sort();
}

void sort_evasions(gen::List & ml, int trans_move) {

   for (int pos = 0; pos < ml.size(); pos++) {
      int mv = ml.move(pos);
      int sc = evasion_score(mv, trans_move);
      ml.set_score(pos, sc);
   }

   ml.sort();
}

}

namespace gen_sort {

// HACK: outside of List class because of C++ "static const" limitations :(

enum Inst {
   GEN_EVASION,
   GEN_TRANS,
   GEN_TACTICAL,
   GEN_KILLER,
   GEN_CHECK,
   GEN_PAWN,
   GEN_QUIET,
   GEN_BAD,
   GEN_END,
   POST_MOVE,
   POST_MOVE_SEE,
   POST_KILLER,
   POST_KILLER_SEE,
   POST_BAD,
};

const Inst Prog_Main[]    = { GEN_TRANS, POST_KILLER, GEN_TACTICAL, POST_MOVE_SEE, GEN_KILLER, POST_KILLER_SEE, GEN_QUIET, POST_MOVE_SEE, GEN_BAD, POST_BAD, GEN_END };
const Inst Prog_QS_Root[] = { GEN_TRANS, POST_KILLER, GEN_TACTICAL, POST_MOVE, GEN_CHECK, POST_KILLER, GEN_PAWN, POST_MOVE, GEN_END };
const Inst Prog_QS[]      = { GEN_TRANS, POST_KILLER, GEN_TACTICAL, POST_MOVE, GEN_END };
const Inst Prog_Evasion[] = { GEN_EVASION, POST_MOVE_SEE, GEN_BAD, POST_BAD, GEN_END };

class List {

private:

   board::Board * p_board;
   const attack::Attacks * p_attacks;
   const sort::Killer * p_killer;
   const sort::History * p_hist;
   int p_trans_move;

   const Inst * p_ip;
   Inst p_gen;
   Inst p_post;

   gen::List p_todo;
   gen::List p_done;
   gen::List p_bad;

   int p_pos;
   bool p_candidate;

   bool gen() {

      p_todo.clear();
      p_pos = 0;

      switch (p_gen) { {

      } case GEN_EVASION: {

         gen::add_evasions(p_todo, p_board->turn(), *p_board, *p_attacks);
         sort::sort_evasions(p_todo, p_trans_move);
         break;

      } case GEN_TRANS: {

         int mv = p_trans_move;

         if (mv != move::NONE && gen::is_move(mv, *p_board)) {
            p_todo.add(mv);
         }

         p_candidate = true;

         break;

      } case GEN_TACTICAL: {

         gen::add_captures(p_todo, p_board->turn(), *p_board);
         gen::add_promotions(p_todo, p_board->turn(), *p_board);
         sort::sort_tacticals(p_todo);

         p_candidate = true;

         break;

      } case GEN_KILLER: {

         int k0 = p_killer->killer_0(p_board->ply());

         if (k0 != move::NONE && gen::is_quiet_move(k0, *p_board)) {
            p_todo.add(k0);
         }

         int k1 = p_killer->killer_1(p_board->ply());

         if (k1 != move::NONE && gen::is_quiet_move(k1, *p_board)) {
            p_todo.add(k1);
         }

         p_candidate = true;

         break;

      } case GEN_CHECK: {

         gen::add_checks(p_todo, p_board->turn(), *p_board);

         p_candidate = true; // not needed yet

         break;

      } case GEN_PAWN: {

         gen::add_castling(p_todo, p_board->turn(), *p_board);
         gen::add_pawn_pushes(p_todo, p_board->turn(), *p_board);

         p_candidate = true; // not needed yet

         break;

      } case GEN_QUIET: {

         gen::add_quiets(p_todo, p_board->turn(), *p_board);
         sort::sort_history(p_todo, *p_board, *p_hist);

         p_candidate = false;

         break;

      } case GEN_BAD: {

         p_todo = p_bad;

         p_candidate = false;

         break;

      } case GEN_END: {

         return false;

      } default: {

         assert(false);

      } }

      return true;
   }

   bool post(int mv) {

      assert(mv != move::NONE);

      switch (p_post) { {

      } case POST_MOVE: {

         if (p_done.contain(mv)) {
            return false;
         }

         if (!move::is_legal(mv, *p_board, *p_attacks)) {
            return false;
         }

         break;

      } case POST_MOVE_SEE: {

         if (p_done.contain(mv)) {
            return false;
         }

         if (!move::is_legal(mv, *p_board, *p_attacks)) {
            return false;
         }

         if (!move::is_safe(mv, *p_board)) {
            p_bad.add(mv);
            return false;
         }

         break;

      } case POST_KILLER: {

         if (p_done.contain(mv)) {
            return false;
         }

         if (!move::is_legal(mv, *p_board, *p_attacks)) {
            return false;
         }

         p_done.add(mv);

         break;

      } case POST_KILLER_SEE: {

         if (p_done.contain(mv)) {
            return false;
         }

         if (!move::is_legal(mv, *p_board, *p_attacks)) {
            return false;
         }

         p_done.add(mv);

         if (!move::is_safe(mv, *p_board)) {
            p_bad.add(mv);
            return false;
         }

         break;

      } case POST_BAD: {

         assert(move::is_legal(mv, *p_board, *p_attacks));

         break;

      } default: {

         assert(false);

      } }

      return true;
   }

public:

   void init(int depth, board::Board & bd, const attack::Attacks & attacks, int trans_move, const sort::Killer & killer, const sort::History & history, bool use_fp = false) {

      p_board = &bd;
      p_attacks = &attacks;
      p_killer = &killer;
      p_hist = &history;
      p_trans_move = trans_move;

      if (false) {
      } else if (attacks.size != 0) { // in check
         p_ip = Prog_Evasion;
      } else if (depth < 0) {
         p_ip = Prog_QS;
      } else if (depth == 0) {
         p_ip = Prog_QS_Root;
      } else if (use_fp) {
         p_ip = Prog_QS_Root;
      } else {
         p_ip = Prog_Main;
      }

      p_todo.clear();
      p_done.clear();
      p_bad.clear();

      p_pos = 0;
      p_candidate = false;
   }

   int next() {

      while (true) {

         while (p_pos >= p_todo.size()) {

            p_gen  = *p_ip++;
            p_post = *p_ip++;

            if (!gen()) return move::NONE;
         }

         int mv = p_todo.move(p_pos++);
         if (post(mv)) return mv;
      }
   }

   bool is_candidate() const {
      return p_candidate;
   }

};

}

namespace material {

const int p_power[piece::SIZE] = { 0, 1, 1, 2, 4, 0, 0 };
const int p_score[piece::SIZE][stage::SIZE] = { { 85, 95 }, { 325, 325 }, { 325, 325 }, { 460, 540 }, { 975, 975 }, { 0, 0 }, { 0, 0 } };

int phase_weight[TOTAL_PHASE + 1];

int power(int pc) {
   assert(pc < piece::SIZE);
   return p_power[pc];
}

int score(int pc, int stage) {
   assert(pc < piece::SIZE);
   assert(stage < stage::SIZE);
   return p_score[pc][stage];
}

int force(int sd, const board::Board & bd) { // for draw eval

   int force = 0;

   for (int pc = piece::KNIGHT; pc <= piece::QUEEN; pc++) {
      force += bd.count(pc, sd) * power(pc);
   }

   return force;
}

bool lone_king(int sd, const board::Board & bd) {

   return bd.count(piece::KNIGHT, sd) == 0
       && bd.count(piece::BISHOP, sd) == 0
       && bd.count(piece::ROOK,   sd) == 0
       && bd.count(piece::QUEEN,  sd) == 0;
}

bool lone_bishop(int sd, const board::Board & bd) {

   return bd.count(piece::KNIGHT, sd) == 0
       && bd.count(piece::BISHOP, sd) == 1
       && bd.count(piece::ROOK,   sd) == 0
       && bd.count(piece::QUEEN,  sd) == 0;
}

bool lone_king_or_bishop(int sd, const board::Board & bd) {

   return bd.count(piece::KNIGHT, sd) == 0
       && bd.count(piece::BISHOP, sd) <= 1
       && bd.count(piece::ROOK,   sd) == 0
       && bd.count(piece::QUEEN,  sd) == 0;
}

bool lone_king_or_minor(int sd, const board::Board & bd) {

   return bd.count(piece::KNIGHT, sd) + bd.count(piece::BISHOP, sd) <= 1
       && bd.count(piece::ROOK,   sd) == 0
       && bd.count(piece::QUEEN,  sd) == 0;
}

bool two_knights(int sd, const board::Board & bd) {

   return bd.count(piece::KNIGHT, sd) == 2
       && bd.count(piece::BISHOP, sd) == 0
       && bd.count(piece::ROOK,   sd) == 0
       && bd.count(piece::QUEEN,  sd) == 0;
}

int interpolation(int mg, int eg, const board::Board & bd) {

   int phase = std::min(bd.phase(), TOTAL_PHASE);
   assert(phase >= 0 && phase <= TOTAL_PHASE);

   int weight = phase_weight[phase];
   return (mg * weight + eg * (256 - weight) + 128) >> 8;
}

void init() {

   for (int i = 0; i <= TOTAL_PHASE; i++) {
      double x = double(i) / double(TOTAL_PHASE / 2) - 1.0;
      double y = 1.0 / (1.0 + std::exp(-x * 5.0));
      phase_weight[i] = util::round(y * 256.0);
   }
}

}

namespace pst {

const int Knight_Line[8]  = { -4, -2,  0, +1, +1,  0, -2, -4 };
const int King_Line[8]    = { -3, -1,  0, +1, +1,  0, -1, -3 };
const int King_File[8]    = { +1, +2,  0, -2, -2,  0, +2, +1 };
const int King_Rank[8]    = { +1,  0, -2, -4, -6, -8,-10,-12 };

const int Advance_Rank[8] = { -3, -2, -1,  0, +1, +2, +1,  0 };

int p_score[piece::SIDE_SIZE][square::SIZE][stage::SIZE];

int score(int p12, int sq, int stage) {
   return p_score[p12][sq][stage];
}

void init() {

   for (int p12 = 0; p12 < piece::SIDE_SIZE; p12++) {
      for (int sq = 0; sq < square::SIZE; sq++) {
         p_score[p12][sq][stage::MG] = 0;
         p_score[p12][sq][stage::EG] = 0;
      }
   }

   for (int sq = 0; sq < square::SIZE; sq++) {

      int fl = square::file(sq);
      int rk = square::rank(sq);

      p_score[piece::WHITE_PAWN][sq][stage::MG] = 0;
      p_score[piece::WHITE_PAWN][sq][stage::EG] = 0;

      p_score[piece::WHITE_KNIGHT][sq][stage::MG] = (Knight_Line[fl] + Knight_Line[rk] + Advance_Rank[rk]) * 4;
      p_score[piece::WHITE_KNIGHT][sq][stage::EG] = (Knight_Line[fl] + Knight_Line[rk] + Advance_Rank[rk]) * 4;

      p_score[piece::WHITE_BISHOP][sq][stage::MG] = (King_Line[fl] + King_Line[rk]) * 2;
      p_score[piece::WHITE_BISHOP][sq][stage::EG] = (King_Line[fl] + King_Line[rk]) * 2;

      p_score[piece::WHITE_ROOK][sq][stage::MG] = King_Line[fl] * 5;
      p_score[piece::WHITE_ROOK][sq][stage::EG] = 0;

      p_score[piece::WHITE_QUEEN][sq][stage::MG] = (King_Line[fl] + King_Line[rk]) * 1;
      p_score[piece::WHITE_QUEEN][sq][stage::EG] = (King_Line[fl] + King_Line[rk]) * 1;

      p_score[piece::WHITE_KING][sq][stage::MG] = (King_File[fl] + King_Rank[rk]) * 8;
      p_score[piece::WHITE_KING][sq][stage::EG] = (King_Line[fl] + King_Line[rk] + Advance_Rank[rk]) * 8;
   }

   for (int pc = piece::PAWN; pc <= piece::KING; pc++) {

      int wp = piece::make(pc, side::WHITE);
      int bp = piece::make(pc, side::BLACK);

      for (int bs = 0; bs < square::SIZE; bs++) {

         int ws = square::opposit_rank(bs);

         p_score[bp][bs][stage::MG] = p_score[wp][ws][stage::MG];
         p_score[bp][bs][stage::EG] = p_score[wp][ws][stage::EG];
      }
   }
}

}

namespace pawn {

struct Info { // 80 bytes; TODO: merge some bitboards and/or file info?
   int8 open[square::FILE_SIZE][side::SIZE];
   uint8 shelter[square::FILE_SIZE][side::SIZE];
   bit_t passed;
   bit_t target[side::SIZE];
   bit_t safe;
   uint32 lock;
   int16 mg;
   int16 eg;
   int8 left_file;
   int8 right_file;
};

void clear_info (Info & info);
void comp_info  (Info & info, const board::Board & bd);

class Table {

private:

   static const int BITS = 12;
   static const int SIZE = 1 << BITS;
   static const int MASK = SIZE - 1;

   Info p_table[SIZE];

public:

   void clear() {

      Info info;
      clear_info(info);

      for (int index = 0; index < SIZE; index++) {
         p_table[index] = info;
      }
   }

   void clear_fast() {
      for (int index = 0; index < SIZE; index++) {
         p_table[index].lock = 1; // board w/o pawns has key 0!
      }
   }

   const Info & info(const board::Board & bd) {

      hash_t key = bd.pawn_key();

      int    index = hash::index(key) & MASK;
      uint32 lock  = hash::lock(key);

      Info & entry = p_table[index];

      if (entry.lock != lock) {
         entry.lock = lock;
         comp_info(entry, bd);
      }

      return entry;
   }

};

bit_t duo[square::SIZE];

void clear_info(Info & info) {

   info.passed = 0;
   info.safe = 0;
   info.lock = 1; // board w/o pawns has key 0!
   info.mg = 0;
   info.eg = 0;
   info.left_file  = square::FILE_A;
   info.right_file = square::FILE_H;

   for (int sd = 0; sd < side::SIZE; sd++) {
      info.target[sd] = 0;
   }

   for (int fl = 0; fl < square::FILE_SIZE; fl++) {
      for (int sd = 0; sd < side::SIZE; sd++) {
         info.open[fl][sd] = 0;
         info.shelter[fl][sd] = 0;
      }
   }
}

bool is_empty(int sq, const board::Board & bd) {
   return bd.square(sq) != piece::PAWN;
}

bool is_attacked(int sq, int sd, const board::Board & bd) {
   return (bd.piece(piece::PAWN, sd) & attack::pawn_attacks_to(sd, sq)) != 0;
}

bool is_controlled(int sq, int sd, const board::Board & bd) {

   bit_t attackers = bd.piece(piece::PAWN, sd) & attack::pawn_attacks_to(sd, sq);
   bit_t defenders = bd.piece(piece::PAWN, side::opposit(sd)) & attack::pawn_attacks_to(side::opposit(sd), sq);

   return bit::count_loop(attackers) > bit::count_loop(defenders);
}

bool is_safe(int sq, int sd, const board::Board & bd) {
   return is_empty(sq, bd) && !is_controlled(sq, side::opposit(sd), bd);
}

bit_t potential_attacks(int sq, int sd, const board::Board & bd) {

   int inc = square::pawn_inc(sd);

   bit_t attacks = attack::pawn_attacks_from(sd, sq);

   for (sq += inc; !square::is_promotion(sq) && is_safe(sq, sd, bd); sq += inc) {
      attacks |= attack::pawn_attacks_from(sd, sq);
   }

   return attacks;
}

bool is_duo(int sq, int sd, const board::Board & bd) {
   return (bd.piece(piece::PAWN, sd) & duo[sq]) != 0;
}

bool is_isolated(int sq, int sd, const board::Board & bd) {

   int fl = square::file(sq);
   bit_t files = bit::files(fl) & ~bit::file(fl);

   return (bd.piece(piece::PAWN, sd) & files) == 0;
}

bool is_weak(int sq, int sd, const board::Board & bd) {

   int fl = square::file(sq);
   int rk = square::rank(sq, sd);

   uint64 pawns = bd.piece(piece::PAWN, sd);
   int inc = square::pawn_inc(sd);

   // already fine?

   if ((pawns & duo[sq]) != 0) {
      return false;
   }

   if (is_attacked(sq, sd, bd)) {
      return false;
   }

   // can advance next to other pawn in one move?

   int s1 = sq + inc;
   int s2 = s1 + inc;

   if ((pawns & duo[s1]) != 0 && is_safe(s1, sd, bd)) {
      return false;
   }

   if (rk == square::RANK_2 && (pawns & duo[s2]) != 0 && is_safe(s1, sd, bd) && is_safe(s2, sd, bd)) {
      return false;
   }

   // can be defended in one move?

   if (fl != square::FILE_A) {

      int s0 = sq + square::INC_LEFT;
      int s1 = s0 - inc;
      int s2 = s1 - inc;
      int s3 = s2 - inc;

      if (bd.square_is(s2, piece::PAWN, sd) && is_safe(s1, sd, bd)) {
         return false;
      }

      if (rk == square::RANK_5 && bd.square_is(s3, piece::PAWN, sd) && is_safe(s2, sd, bd) && is_safe(s1, sd, bd)) {
         return false;
      }
   }

   if (fl != square::FILE_H) {

      int s0 = sq + square::INC_RIGHT;
      int s1 = s0 - inc;
      int s2 = s1 - inc;
      int s3 = s2 - inc;

      if (bd.square_is(s2, piece::PAWN, sd) && is_safe(s1, sd, bd)) {
         return false;
      }

      if (rk == square::RANK_5 && bd.square_is(s3, piece::PAWN, sd) && is_safe(s2, sd, bd) && is_safe(s1, sd, bd)) {
         return false;
      }
   }

   return true;
}

bool is_doubled(int sq, int sd, const board::Board & bd) {
   int fl = square::file(sq);
   return (bd.piece(piece::PAWN, sd) & bit::file(fl) & bit::rear(sq, sd)) != 0;
}

bool is_blocked(int sq, int sd, const board::Board & bd) {
   return !is_safe(square::stop(sq, sd), sd, bd) && !is_attacked(sq, side::opposit(sd), bd);
}

int shelter_file(int fl, int sd, const board::Board & bd) {

   assert(fl >= 0 && fl < 8);

   if (false) {
   } else if (bd.square_is(square::make(fl, square::RANK_2, sd), piece::PAWN, sd)) {
      return 2;
   } else if (bd.square_is(square::make(fl, square::RANK_3, sd), piece::PAWN, sd)) {
      return 1;
   } else {
      return 0;
   }
}

int shelter_files(int fl, int sd, const board::Board & bd) {

   int fl_left  = (fl == square::FILE_A) ? fl + 1 : fl - 1;
   int fl_right = (fl == square::FILE_H) ? fl - 1 : fl + 1;

   int sc = shelter_file(fl, sd, bd) * 2 + shelter_file(fl_left, sd, bd) + shelter_file(fl_right, sd, bd);
   assert(sc >= 0 && sc <= 8);

   return sc;
}

void comp_info(Info & info, const board::Board & bd) {

   info.passed = 0;
   info.safe = 0;

   info.mg = 0;
   info.eg = 0;

   info.left_file  = square::FILE_H + 1;
   info.right_file = square::FILE_A - 1;

   for (int sd = 0; sd < side::SIZE; sd++) {
      info.target[sd] = 0;
   }

   bit_t weak = 0;
   bit_t strong = 0;
   bit_t safe[side::SIZE] = { bit_t(~0), bit_t(~0) };

   for (int sd = 0; sd < side::SIZE; sd++) {

      int p12 = piece::make(piece::PAWN, sd);

      strong |= bd.piece(piece::PAWN, sd) & attack::pawn_attacks_from(sd, bd); // defended pawns

      {
         int n = bd.count(piece::PAWN, sd);
         info.mg += n * material::score(piece::PAWN, stage::MG);
         info.eg += n * material::score(piece::PAWN, stage::EG);
      }

      for (bit_t b = bd.piece(piece::PAWN, sd); b != 0; b = bit::rest(b)) {

         int sq = bit::first(b);

         int fl = square::file(sq);
         int rk = square::rank(sq, sd);

         if (fl < info.left_file)  info.left_file  = fl;
         if (fl > info.right_file) info.right_file = fl;

         info.mg += pst::score(p12, sq, stage::MG);
         info.eg += pst::score(p12, sq, stage::EG);

         if (is_isolated(sq, sd, bd)) {

            bit::set(weak, sq);

            info.mg -= 10;
            info.eg -= 20;

         } else if (is_weak(sq, sd, bd)) {

            bit::set(weak, sq);

            info.mg -= 5;
            info.eg -= 10;
         }

         if (is_doubled(sq, sd, bd)) {
            info.mg -= 5;
            info.eg -= 10;
         }

         if (is_passed(sq, sd, bd)) {

            bit::set(info.passed, sq);

            info.mg += 10;
            info.eg += 20;

            if (rk >= square::RANK_5) {
               int stop = square::stop(sq, sd);
               if (is_duo(sq, sd, bd) && rk <= square::RANK_6) stop += square::pawn_inc(sd); // stop one line "later" for duos
               bit::set(info.target[side::opposit(sd)], stop);
            }
         }

         safe[side::opposit(sd)] &= ~potential_attacks(sq, sd, bd);
      }

      for (int fl = 0; fl < square::FILE_SIZE; fl++) {
         info.shelter[fl][sd] = shelter_files(fl, sd, bd) * 4;
      }

      info.mg = -info.mg;
      info.eg = -info.eg;
   }

   weak &= ~strong; // defended doubled pawns are not weak
   assert((weak & strong) == 0);

   info.target[side::WHITE] |= bd.piece(piece::PAWN, side::BLACK) & weak;
   info.target[side::BLACK] |= bd.piece(piece::PAWN, side::WHITE) & weak;

   info.safe = (safe[side::WHITE] & bit::front(square::RANK_4))
             | (safe[side::BLACK] & bit::rear (square::RANK_5));

   if (info.left_file > info.right_file) { // no pawns
      info.left_file  = square::FILE_A;
      info.right_file = square::FILE_H;
   }

   assert(info.left_file <= info.right_file);

   // file "openness"

   for (int sd = 0; sd < side::SIZE; sd++) {

      for (int fl = 0; fl < square::FILE_SIZE; fl++) {

         bit_t file = bit::file(fl);

         int open;

         if (false) {
         } else if ((bd.piece(piece::PAWN, sd) & file) != 0) {
            open = 0;
         } else if ((bd.piece(piece::PAWN, side::opposit(sd)) & file) == 0) {
            open = 4;
         } else if ((strong & file) != 0) {
            open = 1;
         } else if ((weak & file) != 0) {
            open = 3;
         } else {
            open = 2;
         }

         info.open[fl][sd] = open * 5;
      }
   }
}

void init() {

   for (int sq = 0; sq < square::SIZE; sq++) {

      int fl = square::file(sq);
      int rk = square::rank(sq);

      passed_me[sq][side::WHITE] = bit::file(fl) & bit::front(rk);
      passed_me[sq][side::BLACK] = bit::file(fl) & bit::rear(rk);

      passed_opp[sq][side::WHITE] = bit::files(fl) & bit::front(rk);
      passed_opp[sq][side::BLACK] = bit::files(fl) & bit::rear(rk);

      bit_t b = 0;
      if (fl != square::FILE_A) bit::set(b, sq + square::INC_LEFT);
      if (fl != square::FILE_H) bit::set(b, sq + square::INC_RIGHT);
      duo[sq] = b;
   }
}

}

namespace eval {

int comp_eval (const board::Board & bd, pawn::Table & pawn_table);

struct Entry {
   uint32 lock;
   int eval;
};

class Table {

private:

   static const int BITS = 16;
   static const int SIZE = 1 << BITS;
   static const int MASK = SIZE - 1;

   Entry p_table[SIZE];

public:

   void clear() {
      for (int index = 0; index < SIZE; index++) {
         p_table[index].lock = 0;
         p_table[index].eval = 0;
      }
   }

   int eval(const board::Board & bd, pawn::Table & pawn_table) { // NOTE: score for white

      hash_t key = bd.eval_key();

      int    index = hash::index(key) & MASK;
      uint32 lock  = hash::lock(key);

      Entry & entry = p_table[index];

      if (entry.lock == lock) {
         return entry.eval;
      }

      int eval = comp_eval(bd, pawn_table);

      entry.lock = lock;
      entry.eval = eval;

      return eval;
   }

};

struct Attack_Info {

   bit_t piece_attacks[square::SIZE];
   bit_t all_attacks[side::SIZE];
   bit_t multiple_attacks[side::SIZE];

   bit_t ge_pieces[side::SIZE][piece::SIZE];

   bit_t lt_attacks[side::SIZE][piece::SIZE];
   bit_t le_attacks[side::SIZE][piece::SIZE];

   bit_t king_evasions[side::SIZE];

   bit_t pinned;
};

const int attack_weight[piece::SIZE]   = { 0, 4, 4, 2, 1, 4, 0 };
const int attacked_weight[piece::SIZE] = { 0, 1, 1, 2, 4, 8, 0 };

int mob_weight[32];
int dist_weight[8]; // for king-passer distance

bit_t small_centre, medium_centre, large_centre;
bit_t centre_0, centre_1;

bit_t side_area[side::SIZE];
bit_t king_area[side::SIZE][square::SIZE];

void comp_attacks(Attack_Info & ai, const board::Board & bd) {

   // prepare for adding defended opponent pieces

   for (int sd = 0; sd < side::SIZE; sd++) {

      bit_t b = 0;

      for (int pc = piece::KING; pc >= piece::KNIGHT; pc--) {
         b |= bd.piece(pc, sd);
         ai.ge_pieces[sd][pc] = b;
      }

      ai.ge_pieces[sd][piece::BISHOP] = ai.ge_pieces[sd][piece::KNIGHT]; // minors are equal
   }

   // pawn attacks

   {
      int pc = piece::PAWN;

      for (int sd = 0; sd < side::SIZE; sd++) {

         bit_t b = attack::pawn_attacks_from(sd, bd);

         ai.lt_attacks[sd][pc] = 0; // not needed
         ai.le_attacks[sd][pc] = b;
         ai.all_attacks[sd] = b;
      }
   }

   // piece attacks

   ai.multiple_attacks[side::WHITE] = 0;
   ai.multiple_attacks[side::BLACK] = 0;

   for (int pc = piece::KNIGHT; pc <= piece::KING; pc++) {

      int lower_piece = (pc == piece::BISHOP) ? piece::PAWN : pc - 1; // HACK: direct access
      assert(lower_piece >= piece::PAWN && lower_piece < pc);

      for (int sd = 0; sd < side::SIZE; sd++) {
         ai.lt_attacks[sd][pc] = ai.le_attacks[sd][lower_piece];
      }

      for (int sd = 0; sd < side::SIZE; sd++) {

         for (bit_t fs = bd.piece(pc, sd); fs != 0; fs = bit::rest(fs)) {

            int sq = bit::first(fs);

            bit_t ts = attack::piece_attacks_from(pc, sq, bd);
            ai.piece_attacks[sq] = ts;

            ai.multiple_attacks[sd] |= ts & ai.all_attacks[sd];
            ai.all_attacks[sd] |= ts;
         }

         ai.le_attacks[sd][pc] = ai.all_attacks[sd];
         assert((ai.le_attacks[sd][pc] & ai.lt_attacks[sd][pc]) == ai.lt_attacks[sd][pc]);

         if (pc == piece::BISHOP) { // minors are equal
            ai.le_attacks[sd][piece::KNIGHT] = ai.le_attacks[sd][piece::BISHOP];
         }
      }
   }

   for (int sd = 0; sd < side::SIZE; sd++) {
      int king = bd.king(sd);
      bit_t ts = attack::pseudo_attacks_from(piece::KING, sd, king);
      ai.king_evasions[sd] = ts & ~bd.side(sd) & ~ai.all_attacks[side::opposit(sd)];
   }

   // pinned pieces

   ai.pinned = 0;

   for (int sd = 0; sd < side::SIZE; sd++) {
      int sq = bd.king(sd);
      ai.pinned |= bd.side(sd) & attack::pinned_by(sq, side::opposit(sd), bd);
   }
}

int mul_shift(int a, int b, int c) {
   int bias = 1 << (c - 1);
   return (a * b + bias) >> c;
}

int passed_score(int sc, int rk) {
   static const int passed_weight[8] = { 0, 0, 0, 2, 6, 12, 20, 0 };
   return mul_shift(sc, passed_weight[rk], 4);
}

int mobility_score(int /* pc */, bit_t ts) {
   // assert(pc < piece::SIZE);
   int mob = bit::count(ts);
   return mul_shift(20, mob_weight[mob], 8);
}

int attack_mg_score(int pc, int sd, bit_t ts) {

   assert(pc < piece::SIZE);

   int c0 = bit::count(ts & centre_0);
   int c1 = bit::count(ts & centre_1);
   int sc = c1 * 2 + c0;

   sc += bit::count(ts & side_area[side::opposit(sd)]);

   return (sc - 4) * attack_weight[pc] / 2;
}

int attack_eg_score(int pc, int sd, bit_t ts, const pawn::Info & pi) {
   assert(pc < piece::SIZE);
   return bit::count(ts & pi.target[sd]) * attack_weight[pc] * 4;
}

int capture_score(int pc, int sd, bit_t ts, const board::Board & bd, const Attack_Info & ai) {

   assert(pc < piece::SIZE);

   int sc = 0;

   for (bit_t b = ts & bd.pieces(side::opposit(sd)); b != 0; b = bit::rest(b)) {

      int t = bit::first(b);

      int cp = bd.square(t);
      sc += attacked_weight[cp];
      if (bit::is_set(ai.pinned, t)) sc += attacked_weight[cp] * 2;
   }

   return attack_weight[pc] * sc * 4;
}

int shelter_score(int sq, int sd, const board::Board & bd, const pawn::Info & pi) {

   if (square::rank(sq, sd) > square::RANK_2) {
      return 0;
   }

   int s0 = pi.shelter[square::file(sq)][sd];

   int s1 = 0;

   for (int wg = 0; wg < wing::SIZE; wg++) {

      int index = castling::index(sd, wg);

      if (castling::flag(bd.flags(), index)) {
         int fl = wing::shelter_file[wg];
         s1 = std::max(s1, int(pi.shelter[fl][sd]));
      }
   }

   if (s1 > s0) {
      return (s0 + s1) / 2;
   } else {
      return s0;
   }
}

int king_score(int sc, int n) {
   int weight = 256 - (256 >> n);
   return mul_shift(sc, weight, 8);
}

int eval_outpost(int sq, int sd, const board::Board & bd, const pawn::Info & pi) {

   assert(square::rank(sq, sd) >= square::RANK_5);

   int xd = side::opposit(sd);

   int weight = 0;

   if (bit::is_set(pi.safe, sq)) { // safe square
      weight += 2;
   }

   if (bd.square_is(square::stop(sq, sd), piece::PAWN, xd)) { // shielded
      weight++;
   }

   if (pawn::is_attacked(sq, sd, bd)) { // defended
      weight++;
   }

   return weight - 2;
}

bool passer_is_unstoppable(int sq, int sd, const board::Board & bd) {

   if (!material::lone_king(side::opposit(sd), bd)) return false;

   int fl = square::file(sq);
   bit_t front = bit::file(fl) & bit::front(sq, sd);

   if ((bd.all() & front) != 0) { // path not free
      return false;
   }

   if (pawn::square_distance(bd.king(side::opposit(sd)), sq, sd) >= 2) { // opponent king outside square
      return true;
   }

   if ((front & ~attack::pseudo_attacks_from(piece::KING, sd, bd.king(sd))) == 0) { // king controls promotion path
      return true;
   }

   return false;
}

int eval_passed(int sq, int sd, const board::Board & bd, const Attack_Info & ai) {

   int fl = square::file(sq);
   int xd = side::opposit(sd);

   int weight = 4;

   // blocker

   if (bd.square(square::stop(sq, sd)) != piece::NONE) {
      weight--;
   }

   // free path

   bit_t front = bit::file(fl) & bit::front(sq, sd);
   bit_t rear  = bit::file(fl) & bit::rear (sq, sd);

   if ((bd.all() & front) == 0) {

      bool major_behind = false;
      bit_t majors = bd.piece(piece::ROOK, xd) | bd.piece(piece::QUEEN, xd);

      for (bit_t b = majors & rear; b != 0; b = bit::rest(b)) {

         int f = bit::first(b);

         if (attack::line_is_empty(f, sq, bd)) {
            major_behind = true;
         }
      }

      if (!major_behind && (ai.all_attacks[xd] & front) == 0) {
         weight += 2;
      }
   }

   return weight;
}

int eval_pawn_cap(int sd, const board::Board & bd, const Attack_Info & ai) {

   bit_t ts = attack::pawn_attacks_from(sd, bd);

   int sc = 0;

   for (bit_t b = ts & bd.pieces(side::opposit(sd)); b != 0; b = bit::rest(b)) {

      int t = bit::first(b);

      int cp = bd.square(t);
      if (cp == piece::KING) continue;

      sc += piece::value(cp) - 50;
      if (bit::is_set(ai.pinned, t)) sc += (piece::value(cp) - 50) * 2;
   }

   return sc / 10;
}

int eval_pattern(const board::Board & bd) {

   int eval = 0;

   // fianchetto

   if (bd.square_is(square::B2, piece::BISHOP, side::WHITE)
    && bd.square_is(square::B3, piece::PAWN,   side::WHITE)
    && bd.square_is(square::C2, piece::PAWN,   side::WHITE)) {
      eval += 20;
   }

   if (bd.square_is(square::G2, piece::BISHOP, side::WHITE)
    && bd.square_is(square::G3, piece::PAWN,   side::WHITE)
    && bd.square_is(square::F2, piece::PAWN,   side::WHITE)) {
      eval += 20;
   }

   if (bd.square_is(square::B7, piece::BISHOP, side::BLACK)
    && bd.square_is(square::B6, piece::PAWN,   side::BLACK)
    && bd.square_is(square::C7, piece::PAWN,   side::BLACK)) {
      eval -= 20;
   }

   if (bd.square_is(square::G7, piece::BISHOP, side::BLACK)
    && bd.square_is(square::G6, piece::PAWN,   side::BLACK)
    && bd.square_is(square::F7, piece::PAWN,   side::BLACK)) {
      eval -= 20;
   }

   return eval;
}

bool has_minor(int sd, const board::Board & bd) {
   return bd.count(piece::KNIGHT, sd) + bd.count(piece::BISHOP, sd) != 0;
}

int draw_mul(int sd, const board::Board & bd, const pawn::Info & pi) {

   int xd = side::opposit(sd);

   int pawn[side::SIZE];
   pawn[side::WHITE] = bd.count(piece::PAWN, side::WHITE);
   pawn[side::BLACK] = bd.count(piece::PAWN, side::BLACK);

   int force = material::force(sd, bd) - material::force(xd, bd);

   // rook-file pawns

   if (material::lone_king_or_bishop(sd, bd) && pawn[sd] != 0) {

      bit_t b = bd.piece(piece::BISHOP, sd);

      if ((bd.piece(piece::PAWN, sd) & ~bit::file(square::FILE_A)) == 0
       && (bd.piece(piece::PAWN, xd) &  bit::file(square::FILE_B)) == 0) {

         int prom = (sd == side::WHITE) ? square::A8 : square::A1;

         if (square::distance(bd.king(xd), prom) <= 1) {
            if (b == 0 || !square::same_colour(bit::first(b), prom)) {
               return 1;
            }
         }
      }

      if ((bd.piece(piece::PAWN, sd) & ~bit::file(square::FILE_H)) == 0
       && (bd.piece(piece::PAWN, xd) &  bit::file(square::FILE_G)) == 0) {

         int prom = (sd == side::WHITE) ? square::H8 : square::H1;

         if (square::distance(bd.king(xd), prom) <= 1) {
            if (b == 0 || !square::same_colour(bit::first(b), prom)) {
               return 1;
            }
         }
      }
   }

   if (pawn[sd] == 0 && material::lone_king_or_minor(sd, bd)) {
      return 1;
   }

   if (pawn[sd] == 0 && material::two_knights(sd, bd)) {
      return 2;
   }

   if (pawn[sd] == 0 && force <= 1) {
      return 2;
   }

   if (pawn[sd] == 1 && force == 0 && has_minor(xd, bd)) {
      return 4;
   }

   if (pawn[sd] == 1 && force == 0) {

      int king = bd.king(xd);
      int pawn = bit::first(bd.piece(piece::PAWN, sd));
      int stop = square::stop(pawn, sd);

      if (king == stop || (square::rank(pawn, sd) <= square::RANK_6 && king == square::stop(stop, sd))) {
         return 4;
      }
   }

   if (pawn[sd] == 2 && pawn[xd] >= 1 && force == 0 && has_minor(xd, bd) && (bd.piece(piece::PAWN, sd) & pi.passed) == 0) {
      return 8;
   }

   if (material::lone_bishop(side::WHITE, bd) && material::lone_bishop(side::BLACK, bd) && std::abs(pawn[side::WHITE] - pawn[side::BLACK]) <= 2) { // opposit-colour bishops

      int wb = bit::first(bd.piece(piece::BISHOP, side::WHITE));
      int bb = bit::first(bd.piece(piece::BISHOP, side::BLACK));

      if (!square::same_colour(wb, bb)) {
         return 8;
      }
   }

   return 16;
}

int my_distance(int f, int t, int weight) {
   int dist = square::distance(f, t);
   return mul_shift(dist_weight[dist], weight, 8);
}

int check_number(int pc, int sd, bit_t ts, int king, const board::Board & bd) {

   assert(pc != piece::KING);

   int xd = side::opposit(sd);
   bit_t checks = ts & ~bd.side(sd) & attack::pseudo_attacks_to(pc, sd, king);

   if (!piece::is_slider(pc)) {
      return bit::count_loop(checks);
   }

   int n = 0;

   bit_t b = checks & attack::pseudo_attacks_to(piece::KING, xd, king); // contact checks
   n += bit::count_loop(b) * 2;
   checks &= ~b;

   for (bit_t b = checks; b != 0; b = bit::rest(b)) {

      int t = bit::first(b);

      if (attack::line_is_empty(t, king, bd)) {
         n++;
      }
   }

   return n;
}

int comp_eval(const board::Board & bd, pawn::Table & pawn_table) { // NOTE: score for white

   Attack_Info ai;
   comp_attacks(ai, bd);

   const pawn::Info & pi = pawn_table.info(bd);

   int eval = 0;
   int mg = 0;
   int eg = 0;

   int shelter[side::SIZE];

   for (int sd = 0; sd < side::SIZE; sd++) {
      shelter[sd] = shelter_score(bd.king(sd), sd, bd, pi);
   }

   for (int sd = 0; sd < side::SIZE; sd++) {

      int xd = side::opposit(sd);

      int my_king = bd.king(sd);
      int op_king = bd.king(xd);

      bit_t target = ~(bd.piece(piece::PAWN, sd) | attack::pawn_attacks_from(xd, bd));

      int king_n = 0;
      int king_power = 0;

      // pawns

      {
         bit_t fs = bd.piece(piece::PAWN, sd);

         bit_t front = (sd == side::WHITE) ? bit::front(square::RANK_3) : bit::rear(square::RANK_6);

         for (bit_t b = fs & pi.passed & front; b != 0; b = bit::rest(b)) {

            int sq = bit::first(b);

            int rk = square::rank(sq, sd);

            if (passer_is_unstoppable(sq, sd, bd)) {

               int weight = std::max(rk - square::RANK_3, 0);
               assert(weight >= 0 and weight < 5);

               eg += (piece::QUEEN_VALUE - piece::PAWN_VALUE) * weight / 5;

            } else {

               int sc = eval_passed(sq, sd, bd, ai);

               int sc_mg = sc * 20;
               int sc_eg = sc * 25;

               int stop = square::stop(sq, sd);
               sc_eg -= my_distance(my_king, stop, 10);
               sc_eg += my_distance(op_king, stop, 20);

               mg += passed_score(sc_mg, rk);
               eg += passed_score(sc_eg, rk);
            }
         }

         eval += bit::count(attack::pawn_moves_from(sd, bd) & bd.empty()) * 4 - bd.count(piece::PAWN, sd) * 2;

         eval += eval_pawn_cap(sd, bd, ai);
      }

      // pieces

      for (int pc = piece::KNIGHT; pc <= piece::KING; pc++) {

         int p12 = piece::make(pc, sd); // for PST

         {
            int n = bd.count(pc, sd);
            mg += n * material::score(pc, stage::MG);
            eg += n * material::score(pc, stage::EG);
         }

         for (bit_t b = bd.piece(pc, sd); b != 0; b = bit::rest(b)) {

            int sq = bit::first(b);

            int fl = square::file(sq);
            int rk = square::rank(sq, sd);

            // compute safe attacks

            bit_t ts_all = ai.piece_attacks[sq];
            bit_t ts_pawn_safe = ts_all & target;

            bit_t safe = ~ai.all_attacks[xd] | ai.multiple_attacks[sd];

            if (true && piece::is_slider(pc)) { // battery support

               bit_t bishops = bd.piece(piece::BISHOP, sd) | bd.piece(piece::QUEEN, sd);
               bit_t rooks   = bd.piece(piece::ROOK,   sd) | bd.piece(piece::QUEEN, sd);

               bit_t support = 0;
               support |= bishops & attack::pseudo_attacks_to(piece::BISHOP, sd, sq);
               support |= rooks   & attack::pseudo_attacks_to(piece::ROOK,   sd, sq);

               for (bit_t b = ts_all & support; b != 0; b = bit::rest(b)) {
                  int f = bit::first(b);
                  assert(attack::line_is_empty(f, sq, bd));
                  safe |= attack::Behind[f][sq];
               }
            }

            bit_t ts_safe = ts_pawn_safe & ~ai.lt_attacks[xd][pc] & safe;

            mg += pst::score(p12, sq, stage::MG);
            eg += pst::score(p12, sq, stage::EG);

            if (pc == piece::KING) {
               eg += mobility_score(pc, ts_safe);
            } else {
               eval += mobility_score(pc, ts_safe);
            }

            if (pc != piece::KING) {
               mg += attack_mg_score(pc, sd, ts_pawn_safe);
            }

            eg += attack_eg_score(pc, sd, ts_pawn_safe, pi);

            eval += capture_score(pc, sd, ts_all & (ai.ge_pieces[xd][pc] | target), bd, ai);

            if (pc != piece::KING) {
               eval += check_number(pc, sd, ts_safe, op_king, bd) * material::power(pc) * 6;
            }

            if (pc != piece::KING && (ts_safe & king_area[xd][op_king]) != 0) { // king attack
               king_n++;
               king_power += material::power(pc);
            }

            if (piece::is_minor(pc) && rk >= square::RANK_5 && rk <= square::RANK_6 && fl >= square::FILE_C && fl <= square::FILE_F) { // outpost
               eval += eval_outpost(sq, sd, bd, pi) * 5;
            }

            if (piece::is_minor(pc) && rk >= square::RANK_5 && !bit::is_set(ai.all_attacks[sd], sq)) { // loose minor
               mg -= 10;
            }

            if (piece::is_minor(pc) && rk >= square::RANK_3 && rk <= square::RANK_4 && bd.square_is(square::stop(sq, sd), piece::PAWN, sd)) { // shielded minor
               mg += 10;
            }

            if (pc == piece::ROOK) { // open file

               int sc = pi.open[fl][sd];

               bit_t minors = bd.piece(piece::KNIGHT, xd) | bd.piece(piece::BISHOP, xd);
               if (true && sc >= 10 && (minors & bit::file(fl) & ~target) != 0) { // blocked by minor
                  sc = 5;
               }

               eval += sc - 10;

               if (sc >= 10 && std::abs(square::file(op_king) - fl) <= 1) { // open file on king
                  int weight = (square::file(op_king) == fl) ? 2 : 1;
                  mg += sc * weight / 2;
               }
            }

            if (pc == piece::ROOK && rk == square::RANK_7) { // 7th rank

               bit_t pawns = bd.piece(piece::PAWN, xd) & bit::rank(square::rank(sq));

               if (square::rank(op_king, sd) >= square::RANK_7 || pawns != 0) {
                  mg += 10;
                  eg += 20;
               }
            }

            if (pc == piece::KING) { // king out

               int dl = (pi.left_file - 1) - fl;
               if (dl > 0) eg -= dl * 20;

               int dr = fl - (pi.right_file + 1);
               if (dr > 0) eg -= dr * 20;
            }
         }
      }

      if (bd.count(piece::BISHOP, sd) >= 2) {
         mg += 30;
         eg += 50;
      }

      mg += shelter[sd];
      mg += mul_shift(king_score(king_power * 30, king_n), 32 - shelter[xd], 5);

      eval = -eval;
      mg = -mg;
      eg = -eg;
   }

   mg += pi.mg;
   eg += pi.eg;

   eval += eval_pattern(bd);

   eval += material::interpolation(mg, eg, bd);

   if (eval != 0) { // draw multiplier
      int winner = (eval > 0) ? side::WHITE : side::BLACK;
      eval = mul_shift(eval, draw_mul(winner, bd, pi), 4);
   }

   assert(eval >= score::EVAL_MIN && eval <= score::EVAL_MAX);
   return eval;
}

int eval(board::Board & bd, Table & table, pawn::Table & pawn_table) {
   return score::side_score(table.eval(bd, pawn_table), bd.turn());
}

void init() {

   small_centre  = 0;
   medium_centre = 0;
   large_centre  = 0;

   for (int sq = 0; sq < square::SIZE; sq++) {

      int fl = square::file(sq);
      int rk = square::rank(sq);

      if (fl >= square::FILE_D && fl <= square::FILE_E && rk >= square::RANK_4 && rk <= square::RANK_5) {
         bit::set(small_centre, sq);
      }

      if (fl >= square::FILE_C && fl <= square::FILE_F && rk >= square::RANK_3 && rk <= square::RANK_6) {
         bit::set(medium_centre, sq);
      }

      if (fl >= square::FILE_B && fl <= square::FILE_G && rk >= square::RANK_2 && rk <= square::RANK_7) {
         bit::set(large_centre, sq);
      }
   }

   large_centre  &= ~medium_centre;
   medium_centre &= ~small_centre;

   centre_0 = small_centre | large_centre;
   centre_1 = small_centre | medium_centre;

   side_area[side::WHITE] = 0;
   side_area[side::BLACK] = 0;

   for (int sq = 0; sq < square::SIZE; sq++) {
      if (square::rank(sq) <= square::RANK_4) {
         bit::set(side_area[side::WHITE], sq);
      } else {
         bit::set(side_area[side::BLACK], sq);
      }
   }

   for (int ks = 0; ks < square::SIZE; ks++) {

      king_area[side::WHITE][ks] = 0;
      king_area[side::BLACK][ks] = 0;

      for (int as = 0; as < square::SIZE; as++) {

         int df = square::file(as) - square::file(ks);
         int dr = square::rank(as) - square::rank(ks);

         if (std::abs(df) <= 1 && dr >= -1 && dr <= +2) {
            bit::set(king_area[side::WHITE][ks], as);
         }

         if (std::abs(df) <= 1 && dr >= -2 && dr <= +1) {
            bit::set(king_area[side::BLACK][ks], as);
         }
      }
   }

   for (int i = 0; i < 32; i++) {
      double x = double(i) * 0.5;
      double y = 1.0 - std::exp(-x);
      mob_weight[i] = util::round(y * 512.0) - 256;
   }

   for (int i = 0; i < 8; i++) {
      double x = double(i) - 3.0;
      double y = 1.0 / (1.0 + std::exp(-x));
      dist_weight[i] = util::round(y * 7.0 * 256.0);
   }
}

}

namespace uci {

bool infinite; // for UCI-design mistake :(

}

namespace search {

const int MAX_DEPTH = 100;
const int MAX_PLY = 100;
const int NODE_PERIOD = 1024;

const int MAX_THREADS = 16;

class Abort : public std::exception { // SP fail-high exception

};

void update_current ();

class PV {

private:

   static const int SIZE = MAX_PLY;

   int p_size;
   int p_move[SIZE];

public:

   PV() {
      clear();
   }

   void operator=(const PV & pv) {
      clear();
      add(pv);
   }

   void clear() {
      p_size = 0;
   }

   void add(int mv) {
      if (p_size < SIZE) {
         p_move[p_size++] = mv;
      }
   }

   void add(const PV & pv) {
      for (int pos = 0; pos < pv.size(); pos++) {
         int mv = pv.move(pos);
         add(mv);
      }
   }

   void cat(int mv, const PV & pv) {
      clear();
      add(mv);
      add(pv);
   }

   int size() const {
      return p_size;
   }

   int move(int pos) const {
      return p_move[pos];
   }

   std::string to_can() const {

      std::string s;

      for (int pos = 0; pos < size(); pos++) {
         int mv = move(pos);
         if (pos != 0) s += " ";
         s += move::to_can(mv);
      }

      return s;
   }

};

struct Time {
   bool depth_limited;
   bool node_limited;
   bool time_limited;
   int depth_limit;
   int64 node_limit;
   int64 time_limit;
   bool smart;
   bool ponder;
   bool flag;
   int64 limit_0;
   int64 limit_1;
   int64 limit_2;
   int last_score;
   bool drop;
   util::Timer timer;
};

struct Current {

   int depth;
   int max_ply;
   int64 node;
   int time;
   int speed;

   int move;
   int pos;
   int size;
   bool fail_high;

   int last_time;
};

struct Best {
   int depth;
   int move;
   int score;
   int flags;
   PV pv;
};

Time p_time;
Current current;
Best best;

class Search_Global : public util::Lockable {

public:

   trans::Table trans;
   sort::History history;

};

Search_Global sg;

class SMP : public util::Lockable {

};

SMP smp;

class Search_Local;
class Split_Point;

void clear_iteration(Search_Local & sl);
void search_root(Search_Local & sl, gen::List & ml, int depth, int alpha, int beta);
int search(Search_Local & sl, int depth, int alpha, int beta, PV & pv);
int split(Search_Local & sl, int depth, int old_alpha, int alpha, int beta, PV & pv, gen_sort::List & todo, const gen::List & done, int bs, int bm);
void master_split_point(Search_Local & sl, Split_Point & sp);
void search_split_point(Search_Local & sl, Split_Point & sp);
int qs_static(Search_Local & sl, int beta, int gain);
void inc_node(Search_Local & sl);
bool poll();
void move(Search_Local & sl, int mv);
void undo(Search_Local & sl);
int eval(Search_Local & sl);
int extension(Search_Local & sl, int mv, int depth, bool pv_node);
static int reduction(Search_Local & sl, int mv, int depth, bool pv_node, bool in_check, int searched_size, bool dangerous);
void gen_sort(Search_Local & sl, gen::List & ml);

void sg_abort ();

void          sl_init_early (Search_Local & sl, int id);
void          sl_init_late  (Search_Local & sl);
void          sl_set_root   (Search_Local & sl, const board::Board & bd);
void          sl_signal     (Search_Local & sl);
bool          sl_stop       (const Search_Local & sl);
bool          sl_idle       (const Search_Local & sl, Split_Point * sp);
void          sl_push       (Search_Local & sl, Split_Point & sp);
void          sl_pop        (Search_Local & sl);
Split_Point & sl_top        (const Search_Local & sl);

class Split_Point : public util::Lockable {

private:

   Search_Local * p_master;
   Split_Point * p_parent;

   board::Board p_board;
   int p_depth;
   int p_old_alpha;
   int volatile p_alpha;
   int p_beta;

   gen::List p_todo;
   gen::List p_done;

   int volatile p_workers;
   int volatile p_sent;
   int volatile p_received;

   int volatile p_bs;
   int volatile p_bm;
   PV p_pv;

public:

   void init_root(Search_Local & master) {

      p_master = &master;
      p_parent = NULL;

      p_bs = score::NONE;
      p_beta = score::MAX;
      p_todo.clear();

      p_workers = 1;
      p_received = -1; // HACK
   }

   void init(Search_Local & master, Split_Point & parent, const board::Board & bd, int depth, int old_alpha, int alpha, int beta, gen_sort::List & todo, const gen::List & done, int bs, int bm, const PV & pv) {

      assert(depth > 4);
      assert(old_alpha <= alpha);
      assert(alpha < beta);
      assert(done.size() != 0);
      assert(bs != score::NONE);

      p_master = &master;
      p_parent = &parent;

      p_board = bd;
      p_depth = depth;
      p_old_alpha = old_alpha;
      p_alpha = alpha;
      p_beta = beta;

      p_todo.clear();

      for (int mv = todo.next(); mv != move::NONE; mv = todo.next()) {
         p_todo.add(mv);
      }

      p_done = done;

      p_workers = 0;
      p_sent = 0;
      p_received = 0;

      p_bs = bs;
      p_bm = bm;
      p_pv = pv;
   }

   void enter() {
      lock();
      p_workers++;
      unlock();
   }

   void leave() {

      lock();

      assert(p_workers > 0);
      p_workers--;

      if (p_workers == 0) sl_signal(*p_master);

      unlock();
   }

   int next_move() {

      // lock();

      int mv = move::NONE;

      if (p_bs < p_beta && p_sent < p_todo.size()) {
         mv = p_todo.move(p_sent++);
      }

      // unlock();

      return mv;
   }

   void update_root() {
      lock();
      p_received = 0;
      p_workers = 0;
      unlock();
   }

   void update(int mv, int sc, const PV & pv) {

      lock();

      p_done.add(mv);

      assert(p_received < p_todo.size());
      p_received++;

      if (sc > p_bs) {

         p_bs = sc;
         p_pv.cat(mv, pv);

         if (sc > p_alpha) {
            p_bm = mv;
            p_alpha = sc;
         }
      }

      unlock();
   }

   const board::Board & board() const { return p_board; }

   Split_Point * parent() const { return p_parent; }

   int  depth()     const { return p_depth; }
   int  alpha()     const { return p_alpha; }
   int  beta()      const { return p_beta; }
   int  old_alpha() const { return p_old_alpha; }
   int  bs()        const { return p_bs; }
   int  bm()        const { return p_bm; }
   bool solved()    const { return p_bs >= p_beta || p_received == p_todo.size(); }
   bool free()      const { return p_workers == 0; }

   const gen::List & searched() const { return p_done; }
   int searched_size() const { return p_done.size(); }

   int result(PV & pv) const {
      pv = p_pv;
      return p_bs;
   }

};

Split_Point root_sp;

class Search_Local : public util::Waitable {

public:

   int id;
   std::thread thread;

   bool volatile todo;
   Split_Point * volatile todo_sp;

   board::Board board;
   sort::Killer killer;
   pawn::Table pawn_table;
   eval::Table eval_table;

   int64 volatile node;
   int volatile max_ply;

   Split_Point msp_stack[16];
   int msp_stack_size;

   Split_Point * ssp_stack[64];
   int ssp_stack_size;
};

Search_Local p_sl[MAX_THREADS];

void new_search() {

   p_time.depth_limited = true;
   p_time.node_limited = false;
   p_time.time_limited = false;

   p_time.depth_limit = MAX_DEPTH - 1;

   p_time.smart = false;
   p_time.ponder = false;
}

void set_depth_limit(int depth) {
   p_time.depth_limited = true;
   p_time.depth_limit = depth;
}

void set_node_limit(int64 node) {
   p_time.node_limited = true;
   p_time.node_limit = node;
}

void set_time_limit(int64 time) {
   p_time.time_limited = true;
   p_time.time_limit = time;
}

void set_ponder() {
   p_time.ponder = true;
}

void clear() {

   p_time.flag = false;
   p_time.timer.reset();
   p_time.timer.start();

   current.depth = 0;
   current.max_ply = 0;
   current.node = 0;
   current.time = 0;
   current.speed = 0;

   current.move = move::NONE;
   current.pos = 0;
   current.size = 0;
   current.fail_high = false;

   current.last_time = 0;

   best.depth = 0;
   best.move = move::NONE;
   best.score = score::NONE;
   best.flags = score::FLAGS_NONE;
   best.pv.clear();
}

void update_current() {

   int64 node = 0;
   int max_ply = 0;

   for (int id = 0; id < engine::engine.threads; id++) {

      Search_Local & sl = p_sl[id];

      node += sl.node;
      if (sl.max_ply > max_ply) max_ply = sl.max_ply;
   }

   current.node = node;
   current.max_ply = max_ply;

   current.time = p_time.timer.elapsed();
   current.speed = (current.time < 10) ? 0 : int(current.node * 1000 / current.time);
}

void write_pv(Best & best) {

   sg.lock();

   std::cout << "info";
   std::cout << " depth " << best.depth;
   std::cout << " seldepth " << current.max_ply;
   std::cout << " nodes " << current.node;
   std::cout << " time " << current.time;

   if (score::is_mate(best.score)) {
      std::cout << " score mate " << score::signed_mate(best.score);
   } else {
      std::cout << " score cp " << best.score;
   }
   if (best.flags == score::FLAGS_LOWER) std::cout << " lowerbound";
   if (best.flags == score::FLAGS_UPPER) std::cout << " upperbound";

   std::cout << " pv " << best.pv.to_can();
   std::cout << std::endl;

   sg.unlock();
}

void write_info() {

   sg.lock();

   std::cout << "info";
   std::cout << " depth " << current.depth;
   std::cout << " seldepth " << current.max_ply;
   std::cout << " currmove " << move::to_can(current.move);
   std::cout << " currmovenumber " << current.pos + 1;
   std::cout << " nodes " << current.node;
   std::cout << " time " << current.time;
   if (current.speed != 0) std::cout << " nps " << current.speed;
   std::cout << " hashfull " << sg.trans.used();
   std::cout << std::endl;

   sg.unlock();
}

void write_info_opt() {

   int time = current.time;

   if (time >= current.last_time + 1000) {
      write_info();
      current.last_time = time - time % 1000;
   }
}

void depth_start(int depth) {
   current.depth = depth;
}

void depth_end() {
}

void move_start(int mv, int pos, int size) {

   assert(size > 0);
   assert(pos < size);

   current.move = mv;
   current.pos = pos;
   current.size = size;

   current.fail_high = false;
}

void move_fail_high() {
   current.fail_high = true;
   p_time.flag = false;
}

void move_end() {
   current.fail_high = false;
}

void update_best(Best & best, int sc, int flags, const PV & pv) {

   assert(sc != score::NONE);
   assert(pv.size() != 0);

   p_time.drop = flags == score::FLAGS_UPPER || (sc <= p_time.last_score - 30 && current.size > 1);

   if (pv.move(0) != best.move || p_time.drop) {
      p_time.flag = false;
   }

   best.depth = current.depth;
   best.move = pv.move(0);
   best.score = sc;
   best.flags = flags;
   best.pv = pv;
}

void search_end() {
   p_time.timer.stop();
   update_current();
   write_info();
}

void idle_loop(Search_Local & sl, Split_Point & wait_sp) {

   sl_push(sl, wait_sp);

   while (true) {

      sl.lock();

      assert(sl.todo);
      assert(sl.todo_sp == NULL);

      sl.todo = false;
      sl.todo_sp = NULL;

      while (!wait_sp.free() && sl.todo_sp == NULL) {
         sl.wait();
      }

      Split_Point & sp = *sl.todo_sp;
      sl.todo = true;
      sl.todo_sp = NULL;

      sl.unlock();

      if (&sp == NULL) {
         break;
      }

      // sp.enter();

      sl_push(sl, sp);

      try {
         search_split_point(sl, sp);
      } catch (const Abort & /* abort */) {
         // no-op
      }

      sl_pop(sl);

      sp.leave();
   }

   sl_pop(sl);
}

void helper_program(Search_Local * sl) {
   sl_init_late(*sl);
   idle_loop(*sl, root_sp);
}

bool can_split(Search_Local & master, Split_Point & parent) {

   if (engine::engine.threads == 1) return false;
   if (master.msp_stack_size >= 16) return false;
   if (sl_stop(master)) return false;

   for (int id = 0; id < engine::engine.threads; id++) {
      Search_Local & worker = p_sl[id];
      if (&worker != &master && sl_idle(worker, &parent)) return true;
   }

   return false;
}

void send_work(Search_Local & worker, Split_Point & sp) {

   worker.lock();

   if (sl_idle(worker, sp.parent())) {

      sp.enter();

      worker.todo = true;
      worker.todo_sp = &sp;
      worker.signal();
   }

   worker.unlock();
}

void init_sg() {
   sg.history.clear();
}

void search_root(Search_Local & sl, gen::List & ml, int depth, int alpha, int beta) {

   assert(depth > 0 && depth < MAX_DEPTH);
   assert(alpha < beta);

   board::Board & bd = sl.board;
   assert(attack::is_legal(bd));

   bool pv_node = true;

   int bs = score::NONE;
   int bm = move::NONE;
   int old_alpha = alpha;

   // transposition table

   hash_t key = 0;

   if (depth >= 0) {
      key = bd.key();
   }

   // move loop

   bool in_check = attack::is_in_check(bd);

   int searched_size = 0;

   for (int pos = 0; pos < ml.size(); pos++) {

      int mv = ml.move(pos);

      bool dangerous = in_check || move::is_tactical(mv) || move::is_check(mv, bd) || move::is_castling(mv) || move::is_pawn_push(mv, bd);

      int ext = extension(sl, mv, depth, pv_node);
      int red = reduction(sl, mv, depth, pv_node, in_check, searched_size, dangerous); // LMR

      if (ext != 0) red = 0;
      assert(ext == 0 || red == 0);

      int sc;
      PV npv;

      move_start(mv, pos, ml.size());

      move(sl, mv);

      if ((pv_node && searched_size != 0) || red != 0) {

         sc = -search(sl, depth + ext - red - 1, -alpha - 1, -alpha, npv);

         if (sc > alpha) { // PVS/LMR re-search
            move_fail_high();
            sc = -search(sl, depth + ext - 1, -beta, -alpha, npv);
         }

      } else {

         sc = -search(sl, depth + ext - 1, -beta, -alpha, npv);
      }

      undo(sl);

      move_end();

      searched_size++;

      if (sc > bs) {

         bs = sc;

         PV pv;
         pv.cat(mv, npv);

         update_best(best, sc, score::flags(sc, alpha, beta), pv);

         update_current();
         write_pv(best);

         if (sc > alpha) {

            bm = mv;
            alpha = sc;

            // ml.set_score(pos, sc); // not needed
            ml.move_to_front(pos);

            if (depth >= 0) {
               sg.trans.store(key, depth, bd.ply(), mv, sc, score::FLAGS_LOWER);
            }

            if (sc >= beta) return;
         }
      }
   }

   assert(bs != score::NONE);
   assert(bs < beta);

   if (depth >= 0) {
      int flags = score::flags(bs, old_alpha, beta);
      sg.trans.store(key, depth, bd.ply(), bm, bs, flags);
   }
}

int search(Search_Local & sl, int depth, int alpha, int beta, PV & pv) {

   assert(depth < MAX_DEPTH);
   assert(alpha < beta);

   board::Board & bd = sl.board;
   assert(attack::is_legal(bd));

   pv.clear();

   bool pv_node = depth > 0 && beta != alpha + 1;

   // mate-distance pruning

   {
      int sc = score::from_trans(score::MATE - 1, bd.ply());

      if (sc < beta) {

         beta = sc;

         if (sc <= alpha) {
            return sc;
         }
      }
   }

   // transposition table

   if (bd.is_draw()) return 0;

   attack::Attacks attacks;
   attack::init_attacks(attacks, bd);
   bool in_check = attacks.size != 0;

   bool use_trans = depth >= 0;
   int trans_depth = depth;

   if (depth < 0 && in_check) {
      use_trans = true;
      trans_depth = 0;
   }

   hash_t key = 0;
   int trans_move = move::NONE;

   if (use_trans) {

      key = bd.key();

      int score;
      int flags;

      if (sg.trans.retrieve(key, trans_depth, bd.ply(), trans_move, score, flags) && !pv_node) { // assigns trans_move #
         if (flags == score::FLAGS_LOWER && score >= beta)  return score;
         if (flags == score::FLAGS_UPPER && score <= alpha) return score;
         if (flags == score::FLAGS_EXACT) return score;
      }
   }

   // ply limit

   if (bd.ply() >= MAX_PLY) return eval(sl);

   // beta pruning

   if (!pv_node && depth > 0 && depth <= 3 && !score::is_mate(beta) && !in_check) {

      int sc = eval(sl) - depth * 50;

      if (sc >= beta) {
         return sc;
      }
   }

   // null-move pruning

   if (!pv_node && depth > 0 && !score::is_mate(beta) && !in_check && !material::lone_king(bd.turn(), bd) && eval(sl) >= beta) {

      bd.move_null(); // TODO: use sl?

       int sc = score::MIN;

      if (depth <= 3) { // static
         sc = -qs_static(sl, -beta + 1, 100);
      } else { // dynamic
         PV npv;
         sc = -search(sl, depth - 3 - 1, -beta, -beta + 1, npv);
      }

      bd.undo_null(); // TODO: use sl?

      if (sc >= beta) {

         if (use_trans) {
            sg.trans.store(key, trans_depth, bd.ply(), move::NONE, sc, score::FLAGS_LOWER);
         }

         return sc;
      }
   }

   // stand pat

   int bs = score::NONE;
   int bm = move::NONE;
   int old_alpha = alpha;
   int val = score::NONE; // for delta pruning

   if (depth <= 0 && !in_check) {

      bs = eval(sl);
      val = bs + 100; // QS-DP margin

      if (bs > alpha) {

         alpha = bs;

         if (bs >= beta) {
            return bs;
         }
      }
   }

   // futility-pruning condition

   bool use_fp = false;

   if (depth > 0 && depth <= 8 && !score::is_mate(alpha) && !in_check) {

      int sc = eval(sl) + depth * 40;
      val = sc + 50; // FP-DP margin, extra 50 for captures

      if (sc <= alpha) {
         bs = sc;
         use_fp = true;
      }
   }

   if (depth <= 0 && !in_check) { // unify FP and QS
      use_fp = true;
   }

   // IID

   if (pv_node && depth >= 3 && trans_move == move::NONE) {

      PV npv;
      int sc = search(sl, depth - 2, alpha, beta, npv); // to keep PV-node property

      if (sc > alpha && npv.size() != 0) {
         trans_move = npv.move(0);
      }
   }

   // move loop

   gen_sort::List ml;
   ml.init(depth, bd, attacks, trans_move, sl.killer, sg.history, use_fp);

   gen::List searched;

   for (int mv = ml.next(); mv != move::NONE; mv = ml.next()) {

      bool dangerous = in_check || move::is_tactical(mv) || move::is_check(mv, bd) || move::is_castling(mv) || move::is_pawn_push(mv, bd) || ml.is_candidate();

      if (use_fp && move::is_tactical(mv) && !move::is_check(mv, bd) && val + move::see_max(mv) <= alpha) { // delta pruning
         continue;
      }

      if (use_fp && !move::is_safe(mv, bd)) { // SEE pruning
         continue;
      }

      if (!pv_node && depth > 0 && depth <= 3 && !score::is_mate(bs) && searched.size() >= depth * 4 && !dangerous) { // late-move pruning
         continue;
      }

      int ext = extension(sl, mv, depth, pv_node);
      int red = reduction(sl, mv, depth, pv_node, in_check, searched.size(), dangerous); // LMR

      if (ext != 0) red = 0;
      assert(ext == 0 || red == 0);

      int sc;
      PV npv;

      move(sl, mv);

      if ((pv_node && searched.size() != 0) || red != 0) {

         sc = -search(sl, depth + ext - red - 1, -alpha - 1, -alpha, npv);

         if (sc > alpha) { // PVS/LMR re-search
            sc = -search(sl, depth + ext - 1, -beta, -alpha, npv);
         }

      } else {

         sc = -search(sl, depth + ext - 1, -beta, -alpha, npv);
      }

      undo(sl);

      searched.add(mv);

      if (sc > bs) {

         bs = sc;
         pv.cat(mv, npv);

         if (sc > alpha) {

            bm = mv;
            alpha = sc;

            if (use_trans) {
               sg.trans.store(key, trans_depth, bd.ply(), mv, sc, score::FLAGS_LOWER);
            }

            if (sc >= beta) {

               if (depth > 0 && !in_check && !move::is_tactical(mv)) {
                  sl.killer.add(mv, bd.ply());
                  sg.history.add(mv, searched, bd);
               }

               return sc;
            }
         }
      }

      if (depth >= 6 && !in_check && !use_fp && can_split(sl, sl_top(sl))) {
         return split(sl, depth, old_alpha, alpha, beta, pv, ml, searched, bs, bm);
      }
   }

   if (bs == score::NONE) {
      assert(depth > 0 || in_check);
      return in_check ? -score::MATE + bd.ply() : 0;
   }

   assert(bs < beta);

   if (use_trans) {
      int flags = score::flags(bs, old_alpha, beta);
      sg.trans.store(key, trans_depth, bd.ply(), bm, bs, flags);
   }

   return bs;
}

int split(Search_Local & master, int depth, int old_alpha, int alpha, int beta, PV & pv, gen_sort::List & todo, const gen::List & done, int bs, int bm) {

   smp.lock();

   assert(master.msp_stack_size < 16);
   Split_Point & sp = master.msp_stack[master.msp_stack_size++];

   Split_Point & parent = sl_top(master);

   sp.init(master, parent, master.board, depth, old_alpha, alpha, beta, todo, done, bs, bm, pv);

   for (int id = 0; id < engine::engine.threads; id++) {

      Search_Local & worker = p_sl[id];

      if (&worker != &master && sl_idle(worker, &parent)) {
         send_work(worker, sp);
      }
   }

   smp.unlock();

   try {
      master_split_point(master, sp);
   } catch (const Abort & /* abort */) {
      // no-op
   }

   assert(master.msp_stack_size > 0);
   assert(&master.msp_stack[master.msp_stack_size - 1] == &sp);
   master.msp_stack_size--;

   return sp.result(pv);
}

void master_split_point(Search_Local & sl, Split_Point & sp) {

   sp.enter();

   sl_push(sl, sp);

   try {
      search_split_point(sl, sp);
   } catch (const Abort & /* abort */) {
      // no-op
   }

   sl_pop(sl);

   sp.leave();

   idle_loop(sl, sp);
   sl.board = sp.board();

   assert(sp.free());

   // update move-ordering tables

   board::Board & bd = sl.board;

   int depth = sp.depth();
   int ply = bd.ply();

   int bs = sp.bs();
   int bm = sp.bm();

   assert(bs != score::NONE);

   if (bs >= sp.beta() && depth > 0 && !attack::is_in_check(bd) && !move::is_tactical(bm)) {
      sl.killer.add(bm, ply);
      sg.history.add(bm, sp.searched(), bd);
   }

   if (depth >= 0) {
      int flags = score::flags(bs, sp.old_alpha(), sp.beta());
      sg.trans.store(bd.key(), depth, ply, bm, bs, flags);
   }
}

void search_split_point(Search_Local & sl, Split_Point & sp) {

   board::Board & bd = sl.board;
   bd = sp.board();

   int depth = sp.depth();
   int old_alpha = sp.old_alpha();
   int beta = sp.beta();

   bool pv_node = depth > 0 && beta != old_alpha + 1;

   bool in_check = attack::is_in_check(bd);

   while (true) {

      sp.lock();
      int mv = sp.next_move();
      int alpha = sp.alpha();
      int searched_size = sp.searched_size();
      sp.unlock();

      if (mv == move::NONE) {
         break;
      }

      assert(alpha < beta);

      bool dangerous = in_check || move::is_tactical(mv) || move::is_check(mv, bd) || move::is_castling(mv) || move::is_pawn_push(mv, bd);

      int ext = extension(sl, mv, depth, pv_node);
      int red = reduction(sl, mv, depth, pv_node, in_check, searched_size, dangerous); // LMR

      if (ext != 0) red = 0;
      assert(ext == 0 || red == 0);

      int sc;
      PV npv;

      move(sl, mv);

      if ((pv_node && searched_size != 0) || red != 0) {

         sc = -search(sl, depth + ext - red - 1, -alpha - 1, -alpha, npv);

         if (sc > alpha) { // PVS/LMR re-search
            sc = -search(sl, depth + ext - 1, -beta, -alpha, npv);
         }

      } else {

         sc = -search(sl, depth + ext - 1, -beta, -alpha, npv);
      }

      undo(sl);

      sp.update(mv, sc, npv);
   }
}

int qs_static(Search_Local & sl, int beta, int gain) { // for static NMP

   board::Board & bd = sl.board;

   assert(attack::is_legal(bd));
   // assert(!attack::is_in_check()); // triggers for root move ordering

   // stand pat

   int bs = eval(sl);
   int val = bs + gain;

   if (bs >= beta) {
      return bs;
   }

   // move loop

   attack::Attacks attacks;
   attack::init_attacks(attacks, bd);

   gen_sort::List ml;
   ml.init(-1, bd, attacks, move::NONE, sl.killer, sg.history, false); // QS move generator

   bit_t done = 0;

   for (int mv = ml.next(); mv != move::NONE; mv = ml.next()) {

      if (bit::is_set(done, move::to(mv))) { // process only LVA capture for each opponent piece
         continue;
      }

      bit::set(done, move::to(mv));

      int see = move::see(mv, 0, score::EVAL_MAX, bd); // TODO: beta - val?
      if (see <= 0) continue; // don't consider equal captures as "threats"

      int sc = val + see;

      if (sc > bs) {

         bs = sc;

        if (sc >= beta) {
            return sc;
         }
      }
   }

   assert(bs < beta);

   return bs;
}

void inc_node(Search_Local & sl) {

   sl.node++;

   if (sl.node % NODE_PERIOD == 0) {

      bool abort = false;

      update_current();

      if (poll()) abort = true;

      if (p_time.node_limited && current.node >= p_time.node_limit) {
         abort = true;
      }

      if (p_time.time_limited && current.time >= p_time.time_limit) {
         abort = true;
      }

      if (p_time.smart && current.depth > 1 && current.time >= p_time.limit_0) {
         if (current.pos == 0 || current.time >= p_time.limit_1) {
            if (!(p_time.drop || current.fail_high) || current.time >= p_time.limit_2) {
               if (p_time.ponder) {
                  p_time.flag = true;
               } else {
                  abort = true;
               }
            }
         }
      }

      if (p_time.smart && current.depth > 1 && current.size == 1 && current.time >= p_time.limit_0 / 8) {
         if (p_time.ponder) {
            p_time.flag = true;
         } else {
            abort = true;
         }
      }

      if (abort) sg_abort();
   }

   if (sl_stop(sl)) throw Abort();
}

bool poll() {

   write_info_opt();

   sg.lock();

   if (!input::input.has_input()) {
      sg.unlock();
      return false;
   }

   std::string line;
   bool eof = !input::input.get_line(line);
   if (engine::engine.log) util::log(line);

   sg.unlock();

   if (false) {
   } else if (eof) {
      std::exit(EXIT_SUCCESS);
   } else if (line == "isready") {
      std::cout << "readyok" << std::endl;
      return false;
   } else if (line == "stop") {
      uci::infinite = false;
      return true;
   } else if (line == "ponderhit") {
      uci::infinite = false;
      p_time.ponder = false;
      return p_time.flag;
   } else if (line == "quit") {
      std::exit(EXIT_SUCCESS);
   }

   return false;
}

void move(Search_Local & sl, int mv) {

   board::Board & bd = sl.board;

   inc_node(sl);
   bd.move(mv);

   int ply = bd.ply();

   if (ply > sl.max_ply) {
      assert(ply <= MAX_PLY);
      sl.max_ply = ply;
   }
}

void undo(Search_Local & sl) {
   board::Board & bd = sl.board;
   bd.undo();
}

int eval(Search_Local & sl) {
   board::Board & bd = sl.board;
   return eval::eval(bd, sl.eval_table, sl.pawn_table);
}

int extension(Search_Local & sl, int mv, int depth, bool pv_node) {

   board::Board & bd = sl.board;

   if ((depth <= 4 && move::is_check(mv, bd))
    || (depth <= 4 && move::is_recapture(mv, bd))
    || (pv_node && move::is_check(mv, bd))
    || (pv_node && move::is_tactical(mv) && move::is_win(mv, bd))
    || (pv_node && move::is_pawn_push(mv, bd))) {
      return 1;
   } else {
      return 0;
   }
}

int reduction(Search_Local & /* sl */, int /* mv */, int depth, bool /* pv_node */, bool /* in_check */, int searched_size, bool dangerous) {

   int red = 0;

   if (depth >= 3 && searched_size >= 3 && !dangerous) {
      red = (searched_size >= 6) ? depth / 3 : 1;
   }

   return red;
}

void gen_sort(Search_Local & sl, gen::List & ml) {

   board::Board & bd = sl.board;

   gen::gen_legals(ml, bd);

   int v = eval(sl);

   for (int pos = 0; pos < ml.size(); pos++) {

      int mv = ml.move(pos);

      move(sl, mv);
      int sc = -qs_static(sl, score::MAX, 0);
      undo(sl);

      sc = ((sc - v) / 4) + 1024; // HACK for unsigned 11-bit move-list scores
      assert(sc >= 0 && sc < move::SCORE_SIZE);

      ml.set_score(pos, sc);
   }

   ml.sort();
}

void sl_init_early(Search_Local & sl, int id) {

   sl.id = id;

   sl.todo = true;
   sl.todo_sp = NULL;

   sl.node = 0;
   sl.max_ply = 0;

   sl.msp_stack_size = 0;
   sl.ssp_stack_size = 0;
}

void sl_init_late(Search_Local & sl) {
   sl.killer.clear();
   sl.pawn_table.clear(); // pawn-eval cache
   sl.eval_table.clear(); // eval cache
}

void sl_set_root(Search_Local & sl, const board::Board & bd) {
   sl.board = bd;
   sl.board.set_root();
}

void sl_signal(Search_Local & sl) {
   sl.lock();
   sl.signal();
   sl.unlock();
}

bool sl_stop(const Search_Local & sl) {

   for (Split_Point * sp = &sl_top(sl); sp != NULL; sp = sp->parent()) {
      if (sp->solved()) return true;
   }

   return false;
}

bool sl_idle(const Search_Local & worker, Split_Point * sp) {

   assert(sp != NULL);

   if (worker.todo) return false;
   if (worker.todo_sp != NULL) return false;

   Split_Point & wait_sp = sl_top(worker);

   for (; sp != NULL; sp = sp->parent()) {
      if (sp == &wait_sp) return true;
   }

   return false;
}

void sl_push(Search_Local & sl, Split_Point & sp) {
   assert(sl.ssp_stack_size < 16);
   sl.ssp_stack[sl.ssp_stack_size++] = &sp;
}

void sl_pop(Search_Local & sl) {
   assert(sl.ssp_stack_size > 0);
   sl.ssp_stack_size--;
}

Split_Point & sl_top(const Search_Local & sl) {
   assert(sl.ssp_stack_size > 0);
   return *sl.ssp_stack[sl.ssp_stack_size - 1];
}

void sg_abort() {

   root_sp.update_root();

   for (int id = 0; id < engine::engine.threads; id++) {
      sl_signal(p_sl[id]);
   }
}

void search_asp(gen::List & ml, int depth) {

   Search_Local & sl = p_sl[0];

   assert(depth <= 1 || p_time.last_score == best.score);

   if (depth >= 6 && !score::is_mate(p_time.last_score)) {

      for (int margin = 10; margin < 500; margin *= 2) {

         int a = p_time.last_score - margin;
         int b = p_time.last_score + margin;
         assert(score::EVAL_MIN <= a && a < b && b <= score::EVAL_MAX);

         search_root(sl, ml, depth, a, b);

         if (best.score > a && best.score < b) {
            return;
         } else if (score::is_mate(best.score)) {
            break;
         }
      }
   }

   search_root(sl, ml, depth, score::MIN, score::MAX);
}

void search_id(const board::Board & bd) {

   Search_Local & sl = p_sl[0];

   sl_set_root(sl, bd);

   sl_push(sl, root_sp);

   // move generation

   gen::List ml;
   gen_sort(sl, ml);
   assert(ml.size() != 0);

   best.move = ml.move(0);
   best.score = 0;

   bool easy = (ml.size() == 1 || (ml.size() > 1 && ml.score(0) - ml.score(1) >= 50 / 4)); // HACK: uses gen_sort() internals
   int easy_move = ml.move(0);

   p_time.last_score = score::NONE;

   // iterative deepening

   assert(p_time.depth_limited);

   for (int depth = 1; depth <= p_time.depth_limit; depth++) {

      depth_start(depth);
      search_asp(ml, depth);
      depth_end();

      // p_time.drop = (best.score <= p_time.last_score - 50); // moved to update_best()
      p_time.last_score = best.score;

      if (best.move != easy_move || p_time.drop) {
         easy = false;
      }

      if (p_time.smart && !p_time.drop) {

         bool abort = false;

         update_current();
 
         if (ml.size() == 1 && current.time >= p_time.limit_0 / 16) {
            abort = true;
         }

         if (easy && current.time >= p_time.limit_0 / 4) {
            abort = true;
         }

         if (current.time >= p_time.limit_0 / 2) {
            abort = true;
         }

         if (abort) {
            if (p_time.ponder) {
               p_time.flag = true;
            } else {
               break;
            }
         }
      }
   }

   sl_pop(sl);
}

void search_go(const board::Board & bd) {

   clear();

   init_sg();
   sg.trans.inc_date();

   for (int id = 0; id < engine::engine.threads; id++) {
      sl_init_early(p_sl[id], id);
   }

   root_sp.init_root(p_sl[0]);

   for (int id = 1; id < engine::engine.threads; id++) { // skip 0
      p_sl[id].thread = std::thread(helper_program, &p_sl[id]);
   }

   sl_init_late(p_sl[0]);

   try {
      search_id(bd);
   } catch (const Abort & /* abort */) {
      // no-op
   }

   sg_abort();

   for (int id = 1; id < engine::engine.threads; id++) { // skip 0
      p_sl[id].thread.join();
   }

   search_end();
}

void search_dumb(const board::Board & bd) {

   p_time.smart = false;
   p_time.last_score = score::NONE;
   p_time.drop = false;

   search_go(bd);
}

void search_smart(const board::Board & bd, int moves, int64 time, int64 inc) {

   if (moves == 0) moves = 40;
   moves = std::min(moves, material::interpolation(35, 15, bd));
   assert(moves > 0);

   int64 total = time + inc * (moves - 1);
   int factor = engine::engine.ponder ? 140 : 120;
   int64 alloc = total / moves * factor / 100;
   int64 reserve = total * (moves - 1) / 40;
   int64 max = std::min(time, total - reserve);
   max = std::min(max - 60, max * 95 / 100); // 60ms for lag

   alloc = std::max(alloc, I64(0));
   max = std::max(max, I64(0));

   p_time.smart = true;
   p_time.limit_0 = std::min(alloc, max);
   p_time.limit_1 = std::min(alloc * 4, max);
   p_time.limit_2 = max;
   p_time.last_score = score::NONE;
   p_time.drop = false;

   assert(0 <= p_time.limit_0 && p_time.limit_0 <= p_time.limit_1 && p_time.limit_1 <= p_time.limit_2);

   search_go(bd);
}

void init() {
   sg.trans.set_size(engine::engine.hash);
   sg.trans.alloc();
}

}

namespace uci {

board::Board bd;
bool delay;

class Scanner {

private:

  std::stringstream * p_ss;
  std::vector<std::string> p_keywords;

  bool p_undo;
  std::string p_word;

   bool is_keyword(const std::string & word) const {

      for (int i = 0; i < int(p_keywords.size()); i++) {
         if (p_keywords[i] == word) return true;
      }

      return false;
   }

public:

   Scanner(std::stringstream & ss) {
      p_ss = &ss;
      p_undo = false;
      add_keyword("");
   }

   void add_keyword(const std::string & keyword) {
      p_keywords.push_back(keyword);
   }

   std::string get_keyword() {

      std::string word = get_word();
      assert(is_keyword(word));

      return word;
   }

   std::string get_args() {

      std::string args;
      std::string word;

      while (true) {

         std::string word = get_word();

         if (is_keyword(word)) {
            unget_word();
            break;
         }

         if (args != "") args += " ";
         args += word;
      }

      return args;
   }

   std::string get_word() {

      if (p_undo) {
         p_undo = false;
      } else if (!(*p_ss >> p_word)) { // NOTE: reads as a side effect
         p_word = "";
      }

      return p_word;
   }

   void unget_word() {
      assert(!p_undo);
      p_undo = true;
   }

};

void fen(const std::string & fen) {
   bd.init_fen(fen);
}

void move(const std::string & move) {
   int mv = move::from_string(move, bd);
   bd.move(mv);
}

void send_bestmove() {

   std::cout << "bestmove " << move::to_can(search::best.move);
   if (search::best.pv.size() > 1) std::cout << " ponder " << move::to_can(search::best.pv.move(1));
   std::cout << std::endl;

   delay = false;
}

void command(Scanner & scan) {

   std::string command = scan.get_word();

   if (false) {

   } else if (command == "uci") {

      std::cout << "id name Senpai 1.0" << std::endl;
      std::cout << "id author Fabien Letouzey" << std::endl;

      std::cout << "option name Hash type spin default " << engine::engine.hash << " min 16 max 16384" << std::endl;
      std::cout << "option name Ponder type check default " << engine::engine.ponder << std::endl;
      std::cout << "option name Threads type spin default " << engine::engine.threads << " min 1 max 16" << std::endl;
      std::cout << "option name Log File type check default " << engine::engine.log << std::endl;

      std::cout << "uciok" << std::endl;

   } else if (command == "isready") {

      std::cout << "readyok" << std::endl;

   } else if (command == "setoption") {

      scan.add_keyword("name");
      scan.add_keyword("value");

      std::string name;
      std::string value;

      std::string part;

      while ((part = scan.get_keyword()) != "") {

         if (false) {
         } else if (part == "name") {
            name = scan.get_args();
         } else if (part == "value") {
            value = scan.get_args();
         }	
      }

      if (false) {
      } else if (util::string_case_equal(name, "Hash")) {
         engine::engine.hash = int(util::to_int(value));
         search::sg.trans.set_size(engine::engine.hash);
      } else if (util::string_case_equal(name, "Ponder")) {
         engine::engine.ponder = util::to_bool(value);
      } else if (util::string_case_equal(name, "Threads") || util::string_case_equal(name, "Cores")) {
         engine::engine.threads = int(util::to_int(value));
      } else if (util::string_case_equal(name, "Log File")) {
         engine::engine.log = util::to_bool(value);
      }

   } else if (command == "ucinewgame") {

      search::sg.trans.clear();

   } else if (command == "position") {

      scan.add_keyword("fen");
      scan.add_keyword("startpos");
      scan.add_keyword("moves");

      std::string part;

      while ((part = scan.get_keyword()) != "") {

         if (false) {

         } else if (part == "fen") {

            fen(scan.get_args());

         } else if (part == "startpos") {

            fen(board::start_fen);

         } else if (part == "moves") {

            std::string arg;

            while ((arg = scan.get_word()) != "") {
               uci::move(arg);
            }
         }
      }

   } else if (command == "go") {

      scan.add_keyword("searchmoves");
      scan.add_keyword("ponder");
      scan.add_keyword("wtime");
      scan.add_keyword("btime");
      scan.add_keyword("winc");
      scan.add_keyword("binc");
      scan.add_keyword("movestogo");
      scan.add_keyword("depth");
      scan.add_keyword("nodes");
      scan.add_keyword("mate");
      scan.add_keyword("movetime");
      scan.add_keyword("infinite");

      search::new_search();

      infinite = false;
      delay = false;

      bool smart = false;
      int time = 60000;
      int inc = 0;
      int movestogo = 0;

      std::string part;

      while ((part = scan.get_keyword()) != "") {

         std::string args = scan.get_args();

         if (false) {

         } else if (part == "ponder") {

            infinite = true;
            search::set_ponder();

         } else if (part == "wtime") {

            if (bd.turn() == side::WHITE) {
               smart = true;
               time = int(util::to_int(args));
            }

         } else if (part == "btime") {

            if (bd.turn() == side::BLACK) {
               smart = true;
               time = int(util::to_int(args));
            }

         } else if (part == "winc") {

            if (bd.turn() == side::WHITE) {
               smart = true;
               inc = int(util::to_int(args));
            }

         } else if (part == "binc") {

            if (bd.turn() == side::BLACK) {
               smart = true;
               inc = int(util::to_int(args));
            }

         } else if (part == "movestogo") {

            smart = true;
            movestogo = int(util::to_int(args));

         } else if (part == "depth") {

            search::set_depth_limit(int(util::to_int(args)));

         } else if (part == "nodes") {

            search::set_node_limit(util::to_int(args));

         } else if (part == "movetime") {

            search::set_time_limit(int(util::to_int(args)));

         } else if (part == "infinite") {

            infinite = true;
         }
      }

      if (smart) {
         search::search_smart(bd, movestogo, time, inc);
      } else {
         search::search_dumb(bd);
      }

      if (infinite) { // let's implement the UCI-design mistake :(
         delay = true;
      } else {
         send_bestmove();
      }

   } else if (command == "stop") {

      if (delay) send_bestmove();

   } else if (command == "ponderhit") {

      if (delay) send_bestmove();

   } else if (command == "quit") {

      std::exit(EXIT_SUCCESS);
   }
}

void line(const std::string & line) {

   if (engine::engine.log) util::log(line);

   std::stringstream args(line);
   Scanner scan(args);
   command(scan);
}

void loop() {

   std::cout << std::boolalpha;

   infinite = false;
   delay = false;

   fen(board::start_fen);

   std::string line;

   while (input::input.get_line(line)) {
      uci::line(line);
   }
}

}

int main(int /* argc */, char * /* argv */ []) {

   assert(sizeof(uint8)  == 1);
   assert(sizeof(uint16) == 2);
   assert(sizeof(uint32) == 4);
   assert(sizeof(uint64) == 8);

   input::init();
   bit::init();
   hash::init();
   castling::init();
   attack::init();
   engine::init();
   material::init();
   pst::init();
   pawn::init();
   eval::init();
   search::init();

   uci::loop();

   return EXIT_SUCCESS;
}

