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
std::tuple<uint64_t> environment_0[200001];
std::tuple<uint64_t> environment_1[1];
std::tuple<uint64_t> environment_2[1];
std::tuple<uint64_t> environment_3[1];
std::tuple<uint64_t> environment_4[1];
std::tuple<uint64_t> environment_5[1];
std::tuple<uint8_t> environment_6[20];
std::tuple<uint64_t> environment_7[1];
std::tuple<uint64_t> environment_8[1];
int main() {
  std::cin.tie(0)->sync_with_stdio(0);
  auto procedure_0 = [&](std::tuple<uint64_t> *environment_0, uint64_t local_0, uint64_t local_1) {
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
  auto procedure_1 = [&](std::tuple<uint8_t> *environment_0, uint64_t local_0, uint64_t local_1, uint8_t local_2) {
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
  auto procedure_2 = [&](std::tuple<uint8_t> *environment_0, uint64_t local_0) {
    if ((toSigned(local_0) < toSigned(uint64_t(0)))) {
      local_0 = (-local_0);
      writeChar(uint8_t(uint64_t(45)));
    } else {
    }
    procedure_1(environment_0, local_0, 0, 0);
  };
  auto procedure_3 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t> *environment_1, std::tuple<uint64_t> *environment_2, std::tuple<uint64_t> *environment_3, std::tuple<uint64_t> *environment_4, std::tuple<uint64_t> *environment_5, std::tuple<uint8_t> *environment_6, std::tuple<uint64_t> *environment_7, std::tuple<uint64_t> *environment_8, uint64_t local_0, uint64_t local_1) {
    environment_3[uint64_t(0)] = { (local_0 + uint64_t(1)) };
    environment_4[uint64_t(0)] = { local_1 };
    for (uint64_t binder_0 = 0, loop_end = uint64_t(30); binder_0 < loop_end; binder_0++) {
      if ((get<0>(environment_7[uint64_t(0)]) < get<0>(environment_3[uint64_t(0)]))) {
        break;
      } else {
      }
      environment_0[get<0>(environment_3[uint64_t(0)])] = { (get<0>(environment_0[get<0>(environment_3[uint64_t(0)])]) + get<0>(environment_4[uint64_t(0)])) };
      environment_3[uint64_t(0)] = { (get<0>(environment_3[uint64_t(0)]) + (get<0>(environment_3[uint64_t(0)]) & (-get<0>(environment_3[uint64_t(0)])))) };
    }
  };
  auto procedure_4 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t> *environment_1, std::tuple<uint64_t> *environment_2, std::tuple<uint64_t> *environment_3, std::tuple<uint64_t> *environment_4, std::tuple<uint64_t> *environment_5, std::tuple<uint8_t> *environment_6, std::tuple<uint64_t> *environment_7, std::tuple<uint64_t> *environment_8, uint64_t local_0) {
    environment_5[uint64_t(0)] = { uint64_t(0) };
    environment_3[uint64_t(0)] = { (local_0 + uint64_t(1)) };
    for (uint64_t binder_0 = 0, loop_end = uint64_t(30); binder_0 < loop_end; binder_0++) {
      if ((get<0>(environment_3[uint64_t(0)]) < uint64_t(1))) {
        break;
      } else {
      }
      environment_5[uint64_t(0)] = { (get<0>(environment_5[uint64_t(0)]) + get<0>(environment_0[get<0>(environment_3[uint64_t(0)])])) };
      environment_3[uint64_t(0)] = { (get<0>(environment_3[uint64_t(0)]) - (get<0>(environment_3[uint64_t(0)]) & (-get<0>(environment_3[uint64_t(0)])))) };
    }
    environment_1[uint64_t(0)] = { get<0>(environment_5[uint64_t(0)]) };
  };
  auto procedure_5 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t> *environment_1, std::tuple<uint64_t> *environment_2, std::tuple<uint64_t> *environment_3, std::tuple<uint64_t> *environment_4, std::tuple<uint64_t> *environment_5, std::tuple<uint8_t> *environment_6, std::tuple<uint64_t> *environment_7, std::tuple<uint64_t> *environment_8, uint64_t local_0, uint64_t local_1) {
    procedure_4(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, local_1);
    environment_2[uint64_t(0)] = { get<0>(environment_1[uint64_t(0)]) };
    procedure_4(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, (local_0 - uint64_t(1)));
    environment_2[uint64_t(0)] = { (get<0>(environment_2[uint64_t(0)]) - get<0>(environment_1[uint64_t(0)])) };
    environment_1[uint64_t(0)] = { get<0>(environment_2[uint64_t(0)]) };
  };
  auto procedure_6 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t> *environment_1, std::tuple<uint64_t> *environment_2, std::tuple<uint64_t> *environment_3, std::tuple<uint64_t> *environment_4, std::tuple<uint64_t> *environment_5, std::tuple<uint8_t> *environment_6, std::tuple<uint64_t> *environment_7, std::tuple<uint64_t> *environment_8, uint64_t local_0, uint64_t local_1) {
    procedure_5(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, local_0, local_0);
    environment_2[uint64_t(0)] = { get<0>(environment_1[uint64_t(0)]) };
    environment_2[uint64_t(0)] = { (local_1 - get<0>(environment_2[uint64_t(0)])) };
    procedure_3(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, local_0, get<0>(environment_2[uint64_t(0)]));
  };
  auto procedure_7 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t> *environment_1, std::tuple<uint64_t> *environment_2, std::tuple<uint64_t> *environment_3, std::tuple<uint64_t> *environment_4, std::tuple<uint64_t> *environment_5, std::tuple<uint8_t> *environment_6, std::tuple<uint64_t> *environment_7, std::tuple<uint64_t> *environment_8) {
    procedure_0(environment_1, 0, 0);
    environment_7[uint64_t(0)] = { get<0>(environment_1[uint64_t(0)]) };
    procedure_0(environment_1, 0, 0);
    environment_8[uint64_t(0)] = { get<0>(environment_1[uint64_t(0)]) };
    for (uint64_t binder_0 = 0, loop_end = get<0>(environment_7[uint64_t(0)]); binder_0 < loop_end; binder_0++) {
      procedure_0(environment_1, 0, 0);
      procedure_3(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, binder_0, get<0>(environment_1[uint64_t(0)]));
    }
    for (uint64_t binder_0 = 0, loop_end = get<0>(environment_8[uint64_t(0)]); binder_0 < loop_end; binder_0++) {
      procedure_0(environment_1, 0, 0);
      environment_2[uint64_t(0)] = { get<0>(environment_1[uint64_t(0)]) };
      procedure_0(environment_1, 0, 0);
      environment_3[uint64_t(0)] = { get<0>(environment_1[uint64_t(0)]) };
      if ((get<0>(environment_2[uint64_t(0)]) == uint64_t(1))) {
        procedure_0(environment_1, 0, 0);
        environment_4[uint64_t(0)] = { get<0>(environment_1[uint64_t(0)]) };
        procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, (get<0>(environment_3[uint64_t(0)]) - uint64_t(1)), get<0>(environment_4[uint64_t(0)]));
      } else {
        procedure_0(environment_1, 0, 0);
        environment_2[uint64_t(0)] = { get<0>(environment_1[uint64_t(0)]) };
        procedure_5(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, (get<0>(environment_3[uint64_t(0)]) - uint64_t(1)), (get<0>(environment_2[uint64_t(0)]) - uint64_t(1)));
        procedure_1(environment_6, get<0>(environment_1[uint64_t(0)]), 0, 0);
        writeChar(uint8_t(uint64_t(10)));
      }
    }
  };
  procedure_7(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8);
}
