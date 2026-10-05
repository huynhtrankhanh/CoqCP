#include <iostream>
#include <tuple>
#include <cstdlib>
#include <cstdint>
#include <unistd.h>
#include <cerrno>
using std::get;
/**
 * Author: chilli
 * License: CC0
 * Source: Own work
 * Description: Buffered character input for batch and interactive programs.
 * Refill uses a short POSIX read, retrying interruptions.
 * Usage: ./a.out < input.txt
 * Time: About 5x as fast as cin/scanf.
 * Status: tested on SPOJ INTEST, unit tested
 */

inline uint64_t readChar() { // buffered for both files and interactive pipes
  static unsigned char buf[1 << 16];
  static size_t bc, be;
  if (bc >= be) {
    ssize_t count;
    do {
      count = ::read(STDIN_FILENO, buf, sizeof(buf));
    } while (count < 0 && errno == EINTR);
    if (count <= 0) return uint64_t(-1);
    bc = 0;
    be = static_cast<size_t>(count);
  }
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
std::tuple<uint64_t> environment_0[1];
std::tuple<uint64_t> environment_1[1];
std::tuple<uint8_t> environment_2[20];
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
  auto procedure_2 = [&](std::tuple<uint64_t> *environment_0, uint64_t local_0, uint64_t local_1) {
    local_1 = uint64_t(0);
    for (uint64_t binder_0 = 0, loop_end = uint64_t(20); binder_0 < loop_end; binder_0++) {
      local_0 = readChar();
      if ((local_0 < uint64_t(48)) || (!(local_0 < uint64_t(58)))) {
        continue;
      } else {
      }
      local_1 = ((local_1 * uint64_t(10)) + (local_0 - uint64_t(48)));
      break;
    }
    for (uint64_t binder_0 = 0, loop_end = uint64_t(20); binder_0 < loop_end; binder_0++) {
      local_0 = readChar();
      if ((local_0 < uint64_t(48)) || (!(local_0 < uint64_t(58)))) {
        break;
      } else {
      }
      local_1 = ((local_1 * uint64_t(10)) + (local_0 - uint64_t(48)));
    }
    environment_0[uint64_t(0)] = { local_1 };
  };
  auto procedure_3 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t> *environment_1, std::tuple<uint8_t> *environment_2, uint8_t local_0, uint64_t local_1, uint64_t local_2) {
    if ((local_1 == uint64_t(0))) {
      environment_1[uint64_t(0)] = { uint64_t(1000000001) };
    } else {
      if ((local_1 == (local_2 + uint64_t(1)))) {
        environment_1[uint64_t(0)] = { uint64_t(0) };
      } else {
        writeChar(local_0);
        writeChar(uint8_t(uint64_t(32)));
        procedure_0(environment_2, local_1, 0, 0);
        writeChar(uint8_t(uint64_t(10)));
        flushSTDOUT();
        procedure_2(environment_0, 0, 0);
        environment_1[uint64_t(0)] = { get<0>(environment_0[uint64_t(0)]) };
      }
    }
  };
  auto procedure_4 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t> *environment_1, std::tuple<uint8_t> *environment_2, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6, uint64_t local_7, uint64_t local_8) {
    procedure_2(environment_0, 0, 0);
    local_0 = get<0>(environment_0[uint64_t(0)]);
    procedure_2(environment_0, 0, 0);
    local_1 = get<0>(environment_0[uint64_t(0)]);
    if ((local_0 < local_1)) {
      local_2 = (local_1 - local_0);
    } else {
    }
    local_3 = local_1;
    if ((local_0 < local_3)) {
      local_3 = local_0;
    } else {
    }
    for (uint64_t binder_0 = 0, loop_end = uint64_t(17); binder_0 < loop_end; binder_0++) {
      if ((local_2 == local_3)) {
        break;
      } else {
      }
      local_4 = ((local_2 + local_3) / uint64_t(2));
      local_5 = (local_1 - local_4);
      procedure_3(environment_0, environment_1, environment_2, uint8_t(uint64_t(70)), (local_4 + uint64_t(1)), local_0);
      local_6 = get<0>(environment_1[uint64_t(0)]);
      procedure_3(environment_0, environment_1, environment_2, uint8_t(uint64_t(83)), local_5, local_0);
      local_7 = get<0>(environment_1[uint64_t(0)]);
      if ((local_6 < local_7)) {
        local_3 = local_4;
      } else {
        local_2 = (local_4 + uint64_t(1));
      }
    }
    procedure_3(environment_0, environment_1, environment_2, uint8_t(uint64_t(70)), local_2, local_0);
    local_6 = get<0>(environment_1[uint64_t(0)]);
    procedure_3(environment_0, environment_1, environment_2, uint8_t(uint64_t(83)), (local_1 - local_2), local_0);
    local_7 = get<0>(environment_1[uint64_t(0)]);
    local_8 = local_6;
    if ((local_7 < local_8)) {
      local_8 = local_7;
    } else {
    }
    for (uint8_t binder_0 : { 33, 32 }) {
      writeChar(binder_0);
    }
    procedure_0(environment_2, local_8, 0, 0);
    writeChar(uint8_t(uint64_t(10)));
    flushSTDOUT();
  };
  procedure_4(environment_0, environment_1, environment_2, 0, 0, 0, 0, 0, 0, 0, 0, 0);
}
