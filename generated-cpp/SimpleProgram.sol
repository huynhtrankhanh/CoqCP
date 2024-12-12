#include <iostream>
#include <tuple>
#include <cstdlib>
#include <cstdint>
using std::get;
/**
 * Author: chilli
 * License: CC0
 * Source: Own work
 * Description: Read an integer from stdin. Usage requires your program to pipe in
 * input from file.
 * Usage: ./a.out < input.txt
 * Time: About 5x as fast as cin/scanf.
 * Status: tested on SPOJ INTEST, unit tested
 */

inline uint64_t readChar() { // like getchar()
  static char buf[1 << 16];
  static size_t bc, be;
  if (bc >= be) {
    buf[0] = 0, bc = 0;
    be = fread(buf, 1, sizeof(buf), stdin);
  }
  if (bc >= be) return -1;
  return buf[bc++]; // returns -1 on EOF
}

void writeChar(uint8_t x) {
  std::cout << (char)x;
}

void flushSTDOUT() {
  std::cout << std::flush;
}
int8_t toSigned(uint8_t x) { return x; }
int16_t toSigned(uint16_t x) { return x; }
int32_t toSigned(uint32_t x) { return x; }
int64_t toSigned(uint64_t x) { return x; }
auto binaryOp(auto a, auto b, auto f)
{
  auto c = a();
  auto d = b();
  return f(c, d);
}
std::tuple<uint8_t> environment_0[20];
int main() {
  std::cin.tie(0)->sync_with_stdio(0);
  auto procedure_0 = [&](std::tuple<uint8_t> *environment_0, uint64_t local_0, uint64_t local_1, uint8_t local_2) {
    if ((local_0 == uint64_t(0))) {
      writeChar(uint8_t(uint64_t(48)));
    } else {
      local_1 = uint64_t(0);
      for (uint64_t binder_0 = 0, loop_end = uint64_t(20); binder_0 < loop_end; binder_0++) {
        if ((local_0 == uint64_t(0))) {
          break;
        } else {
        }
        local_2 = uint8_t(((local_0 % uint64_t(10)) + uint64_t(48)));
        environment_0[local_1] = { local_2 };
        local_0 = (local_0 / uint64_t(10));
        local_1 = (local_1 + uint64_t(1));
      }
      for (uint64_t binder_0 = 0, loop_end = local_1; binder_0 < loop_end; binder_0++) {
        writeChar(get<0>(environment_0[((local_1 - binder_0) - uint64_t(1))]));
      }
    }
  };
  auto procedure_1 = [&](std::tuple<uint8_t> *environment_0, uint64_t local_0) {
    if ((toSigned(local_0) < toSigned(uint64_t(0)))) {
      local_0 = (-local_0);
      writeChar(uint8_t(uint64_t(45)));
    } else {
    }
    procedure_0(environment_0, local_0, 0, 0);
  };
  auto procedure_2 = [&](std::tuple<uint8_t> *environment_0) {
    for (uint8_t binder_0 : { 84, 104, 101, 32, 110, 117, 109, 98, 101, 114, 32, 105, 115, 32 }) {
      writeChar(binder_0);
    }
    procedure_1(environment_0, (uint64_t(1) + uint64_t(1)));
  };
  procedure_2(environment_0);
}
