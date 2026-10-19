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
#include <vector>

template<class T>
void growArray(std::vector<T>& array, uint64_t minimumLength) {
  if (minimumLength > array.max_size()) std::abort();
  if (minimumLength > array.size()) array.resize(minimumLength);
}
std::tuple<uint64_t> environment_0[32];
std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> environment_1[1];
std::vector<std::tuple<uint64_t>> environment_2(1024);
std::vector<std::tuple<uint64_t>> environment_3(0);
std::vector<std::tuple<uint64_t, uint64_t, uint64_t>> environment_4(0);
std::vector<std::tuple<uint64_t, uint64_t>> environment_5(0);
std::vector<std::tuple<uint64_t>> environment_6(0);
std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>> environment_7(0);
std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>> environment_8(0);
std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>> environment_9(0);
std::vector<std::tuple<uint64_t>> environment_10(0);
std::vector<std::tuple<uint8_t>> environment_11(0);
std::vector<std::tuple<uint64_t>> environment_12(0);
std::vector<std::tuple<uint8_t>> environment_13(0);
std::tuple<uint8_t> environment_14[1024];
std::tuple<uint8_t> environment_15[20];
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
  auto procedure_2 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3) {
    local_0 = get<0>(environment_1[uint64_t(0)]);
    local_1 = get<1>(environment_1[uint64_t(0)]);
    local_2 = get<2>(environment_1[uint64_t(0)]);
    local_3 = get<3>(environment_1[uint64_t(0)]);
    local_0 = (local_0 + local_1);
    local_1 = (((local_1 << uint64_t(13)) | (local_1 >> uint64_t(51))) ^ local_0);
    local_0 = ((local_0 << uint64_t(32)) | (local_0 >> uint64_t(32)));
    local_2 = (local_2 + local_3);
    local_3 = (((local_3 << uint64_t(16)) | (local_3 >> uint64_t(48))) ^ local_2);
    local_0 = (local_0 + local_3);
    local_3 = (((local_3 << uint64_t(21)) | (local_3 >> uint64_t(43))) ^ local_0);
    local_2 = (local_2 + local_1);
    local_1 = (((local_1 << uint64_t(17)) | (local_1 >> uint64_t(47))) ^ local_2);
    local_2 = ((local_2 << uint64_t(32)) | (local_2 >> uint64_t(32)));
    environment_1[uint64_t(0)] = { local_0, local_1, local_2, local_3 };
  };
  auto procedure_3 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0) {
    environment_1[uint64_t(0)] = { get<0>(environment_1[uint64_t(0)]), get<1>(environment_1[uint64_t(0)]), get<2>(environment_1[uint64_t(0)]), (get<3>(environment_1[uint64_t(0)]) ^ local_0) };
    procedure_2(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0, 0, 0);
    procedure_2(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0, 0, 0);
    environment_1[uint64_t(0)] = { (get<0>(environment_1[uint64_t(0)]) ^ local_0), get<1>(environment_1[uint64_t(0)]), get<2>(environment_1[uint64_t(0)]), get<3>(environment_1[uint64_t(0)]) };
  };
  auto procedure_4 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3) {
    environment_1[uint64_t(0)] = { (uint64_t(8317987319222330741) ^ get<0>(environment_0[uint64_t(26)])), (uint64_t(7237128888997146477) ^ get<0>(environment_0[uint64_t(27)])), (uint64_t(7816392313619706465) ^ get<0>(environment_0[uint64_t(26)])), (uint64_t(8387220255154660723) ^ get<0>(environment_0[uint64_t(27)])) };
    procedure_3(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_0);
    procedure_3(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1);
    procedure_3(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_2);
    procedure_3(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1729382256910270464));
    environment_1[uint64_t(0)] = { get<0>(environment_1[uint64_t(0)]), get<1>(environment_1[uint64_t(0)]), (get<2>(environment_1[uint64_t(0)]) ^ uint64_t(255)), get<3>(environment_1[uint64_t(0)]) };
    for (uint64_t binder_0 = 0, loop_end = uint64_t(4); binder_0 < loop_end; binder_0++) {
      procedure_2(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0, 0, 0);
    }
    local_3 = (((get<0>(environment_1[uint64_t(0)]) ^ get<1>(environment_1[uint64_t(0)])) ^ get<2>(environment_1[uint64_t(0)])) ^ get<3>(environment_1[uint64_t(0)]));
    environment_0[uint64_t(28)] = { local_3 };
    environment_0[uint64_t(21)] = { (local_3 % get<0>(environment_0[uint64_t(20)])) };
  };
  auto procedure_5 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1) {
    local_0 = get<0>(environment_0[uint64_t(20)]);
    if ((uint64_t(9223372036854775807) < local_0)) {
      environment_0[uint64_t(8)] = { uint64_t(1) };
    } else {
      local_0 = (local_0 * uint64_t(2));
      growArray(environment_2, local_0);
      for (uint64_t binder_0 = 0, loop_end = local_0; binder_0 < loop_end; binder_0++) {
        environment_2[binder_0] = { uint64_t(0) };
      }
      environment_0[uint64_t(20)] = { local_0 };
      for (uint64_t binder_0 = 0, loop_end = get<0>(environment_0[uint64_t(1)]); binder_0 < loop_end; binder_0++) {
        procedure_4(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_4[binder_0]), get<1>(environment_4[binder_0]), get<2>(environment_4[binder_0]), 0);
        local_1 = get<0>(environment_0[uint64_t(21)]);
        environment_3[binder_0] = { get<0>(environment_2[local_1]) };
        environment_2[local_1] = { (binder_0 + uint64_t(1)) };
      }
    }
  };
  auto procedure_6 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5) {
    local_3 = uint64_t(0);
    if ((get<0>(environment_0[uint64_t(1)]) == get<0>(environment_0[uint64_t(20)]))) {
      procedure_5(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
    } else {
    }
    if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
      procedure_4(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_0, local_1, local_2, 0);
      local_5 = get<0>(environment_0[uint64_t(21)]);
      local_4 = get<0>(environment_2[local_5]);
      for (uint64_t binder_0 = 0, loop_end = get<0>(environment_0[uint64_t(1)]); binder_0 < loop_end; binder_0++) {
        if ((local_4 == uint64_t(0))) {
          break;
        } else {
        }
        local_4 = (local_4 - uint64_t(1));
        if ((get<0>(environment_4[local_4]) == local_0) && (get<1>(environment_4[local_4]) == local_1) && (get<2>(environment_4[local_4]) == local_2)) {
          environment_0[uint64_t(0)] = { local_4 };
          local_3 = uint64_t(1);
          break;
        } else {
        }
        local_4 = get<0>(environment_3[local_4]);
      }
      if ((local_3 == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(1)]) == uint64_t(18446744073709551615))) {
          environment_0[uint64_t(8)] = { uint64_t(1) };
        } else {
          environment_0[uint64_t(0)] = { get<0>(environment_0[uint64_t(1)]) };
          growArray(environment_4, (get<0>(environment_0[uint64_t(1)]) + uint64_t(1)));
          growArray(environment_3, (get<0>(environment_0[uint64_t(1)]) + uint64_t(1)));
          environment_4[get<0>(environment_0[uint64_t(1)])] = { local_0, local_1, local_2 };
          environment_3[get<0>(environment_0[uint64_t(1)])] = { get<0>(environment_2[local_5]) };
          environment_2[local_5] = { (get<0>(environment_0[uint64_t(1)]) + uint64_t(1)) };
          environment_0[uint64_t(1)] = { (get<0>(environment_0[uint64_t(1)]) + uint64_t(1)) };
        }
      } else {
      }
    } else {
    }
  };
  auto procedure_7 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1) {
    if ((get<0>(environment_0[uint64_t(10)]) == uint64_t(18446744073709551615))) {
      environment_0[uint64_t(8)] = { uint64_t(1) };
    } else {
      growArray(environment_7, (get<0>(environment_0[uint64_t(10)]) + uint64_t(1)));
      environment_7[get<0>(environment_0[uint64_t(10)])] = { local_0, local_1, uint64_t(0), uint64_t(0) };
      environment_0[uint64_t(10)] = { (get<0>(environment_0[uint64_t(10)]) + uint64_t(1)) };
    }
  };
  auto procedure_8 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0) {
    if ((local_0 == uint64_t(32)) || (local_0 == uint64_t(9)) || (local_0 == uint64_t(10)) || (local_0 == uint64_t(13))) {
      if ((get<0>(environment_0[uint64_t(6)]) != uint64_t(0))) {
        environment_0[uint64_t(17)] = { uint64_t(1) };
      } else {
      }
    } else {
      if ((get<0>(environment_0[uint64_t(6)]) == uint64_t(1024))) {
        environment_0[uint64_t(8)] = { uint64_t(1) };
      } else {
        environment_14[get<0>(environment_0[uint64_t(6)])] = { uint8_t(local_0) };
        environment_0[uint64_t(6)] = { (get<0>(environment_0[uint64_t(6)]) + uint64_t(1)) };
      }
    }
  };
  auto procedure_9 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15) {
    environment_0[uint64_t(6)] = { uint64_t(0) };
    environment_0[uint64_t(14)] = { uint64_t(0) };
    environment_0[uint64_t(17)] = { uint64_t(0) };
    if ((get<0>(environment_0[uint64_t(15)]) != uint64_t(0))) {
      procedure_8(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, (get<0>(environment_0[uint64_t(15)]) - uint64_t(1)));
      environment_0[uint64_t(15)] = { uint64_t(0) };
    } else {
    }
    if ((get<0>(environment_0[uint64_t(17)]) == uint64_t(0)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
      for (uint64_t tape_byte_0; (tape_byte_0 = readChar()) != UINT64_MAX;) {
        const uint8_t binder_0 = static_cast<uint8_t>(tape_byte_0);
        procedure_8(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(binder_0));
        if ((get<0>(environment_0[uint64_t(17)]) != uint64_t(0)) || (get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
          break;
        } else {
        }
      }
      if ((get<0>(environment_0[uint64_t(17)]) == uint64_t(0)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        environment_0[uint64_t(7)] = { uint64_t(1) };
      } else {
      }
    } else {
    }
    if ((get<0>(environment_0[uint64_t(6)]) != uint64_t(0)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
      environment_0[uint64_t(14)] = { uint64_t(1) };
    } else {
    }
  };
  auto procedure_10 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1) {
    procedure_9(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
    local_1 = uint64_t(0);
    if ((get<0>(environment_0[uint64_t(14)]) != uint64_t(0))) {
      for (uint64_t binder_0 = 0, loop_end = get<0>(environment_0[uint64_t(6)]); binder_0 < loop_end; binder_0++) {
        local_0 = uint64_t(get<0>(environment_14[binder_0]));
        if ((local_0 < uint64_t(48)) || (uint64_t(57) < local_0)) {
          environment_0[uint64_t(14)] = { uint64_t(0) };
          break;
        } else {
        }
        local_0 = (local_0 - uint64_t(48));
        if ((((uint64_t(18446744073709551615) - local_0) / uint64_t(10)) < local_1)) {
          environment_0[uint64_t(14)] = { uint64_t(0) };
          break;
        } else {
        }
        local_1 = ((local_1 * uint64_t(10)) + local_0);
      }
    } else {
    }
    environment_0[uint64_t(11)] = { local_1 };
  };
  auto procedure_11 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0) {
    environment_0[uint64_t(0)] = { uint64_t(18446744073709551615) };
    for (uint64_t binder_0 = 0, loop_end = get<0>(environment_0[uint64_t(4)]); binder_0 < loop_end; binder_0++) {
      if ((get<1>(environment_8[binder_0]) == get<0>(environment_0[uint64_t(6)]))) {
        local_0 = uint64_t(1);
        for (uint64_t binder_1 = 0, loop_end = get<0>(environment_0[uint64_t(6)]); binder_1 < loop_end; binder_1++) {
          if ((get<0>(environment_13[(get<0>(environment_8[binder_0]) + binder_1)]) != get<0>(environment_14[binder_1]))) {
            local_0 = uint64_t(0);
            break;
          } else {
          }
        }
        if ((local_0 != uint64_t(0))) {
          environment_0[uint64_t(0)] = { binder_0 };
          break;
        } else {
        }
      } else {
      }
    }
  };
  auto procedure_12 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0) {
    for (uint8_t binder_0 : { 79, 75, 32 }) {
      writeChar(binder_0);
    }
    procedure_0(environment_15, local_0, 0, 0);
    writeChar(uint8_t(uint64_t(10)));
    flushSTDOUT();
  };
  auto procedure_13 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15) {
    for (uint8_t binder_0 : { 78, 79, 10 }) {
      writeChar(binder_0);
    }
    flushSTDOUT();
  };
  auto procedure_14 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1) {
    procedure_11(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0);
    if ((get<0>(environment_0[uint64_t(0)]) != uint64_t(18446744073709551615))) {
      procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
    } else {
      if ((get<0>(environment_0[uint64_t(4)]) == uint64_t(18446744073709551615)) || ((uint64_t(18446744073709551615) - get<0>(environment_0[uint64_t(5)])) < get<0>(environment_0[uint64_t(6)]))) {
        environment_0[uint64_t(8)] = { uint64_t(1) };
      } else {
        growArray(environment_13, (get<0>(environment_0[uint64_t(5)]) + get<0>(environment_0[uint64_t(6)])));
        for (uint64_t binder_0 = 0, loop_end = get<0>(environment_0[uint64_t(6)]); binder_0 < loop_end; binder_0++) {
          environment_13[(get<0>(environment_0[uint64_t(5)]) + binder_0)] = { get<0>(environment_14[binder_0]) };
        }
        growArray(environment_8, (get<0>(environment_0[uint64_t(4)]) + uint64_t(1)));
        environment_8[get<0>(environment_0[uint64_t(4)])] = { get<0>(environment_0[uint64_t(5)]), get<0>(environment_0[uint64_t(6)]), local_0, uint64_t(0), local_1 };
        environment_0[uint64_t(5)] = { (get<0>(environment_0[uint64_t(5)]) + get<0>(environment_0[uint64_t(6)])) };
        procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_0);
        environment_0[uint64_t(4)] = { (get<0>(environment_0[uint64_t(4)]) + uint64_t(1)) };
      }
    }
  };
  auto procedure_15 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0) {
    if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
      if ((get<0>(environment_0[uint64_t(3)]) == uint64_t(18446744073709551615))) {
        environment_0[uint64_t(8)] = { uint64_t(1) };
      } else {
        growArray(environment_6, (get<0>(environment_0[uint64_t(3)]) + uint64_t(1)));
        environment_6[get<0>(environment_0[uint64_t(3)])] = { local_0 };
        procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(3)]));
        environment_0[uint64_t(3)] = { (get<0>(environment_0[uint64_t(3)]) + uint64_t(1)) };
      }
    } else {
    }
  };
  auto procedure_16 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2) {
    local_2 = get<0>(environment_6[local_0]);
    if ((get<0>(environment_4[local_2]) == uint64_t(3)) && (get<1>(environment_4[local_2]) == get<0>(environment_6[local_1]))) {
      procedure_15(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<2>(environment_4[local_2]));
    } else {
      procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
    }
  };
  auto procedure_17 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0) {
    procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), get<0>(environment_6[local_0]), uint64_t(0), 0, 0, 0);
    procedure_15(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(0)]));
  };
  auto procedure_18 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6) {
    environment_0[uint64_t(0)] = { local_0 };
    if ((!(local_0 < local_1))) {
      local_5 = (local_0 - local_1);
      local_6 = local_5;
      if ((local_2 == uint64_t(0))) {
        if (((uint64_t(18446744073709551615) - local_5) < local_3)) {
          environment_0[uint64_t(8)] = { uint64_t(1) };
        } else {
        }
        local_6 = (local_5 + local_3);
      } else {
      }
      if ((local_2 == uint64_t(1))) {
        if ((local_5 == uint64_t(0))) {
          local_6 = local_4;
        } else {
          local_6 = (local_5 - uint64_t(1));
        }
      } else {
      }
      if ((local_2 == uint64_t(2)) && (local_5 != uint64_t(0))) {
        if ((local_5 == uint64_t(18446744073709551615))) {
          environment_0[uint64_t(8)] = { uint64_t(1) };
        } else {
        }
        local_6 = (local_5 + uint64_t(1));
      } else {
      }
      if ((local_2 == uint64_t(3)) || (local_2 == uint64_t(4)) || (local_2 == uint64_t(5))) {
        if ((local_5 == uint64_t(0)) && (local_2 != uint64_t(5))) {
          local_6 = uint64_t(2);
        } else {
        }
        if ((local_5 == uint64_t(1)) && (local_2 == uint64_t(4))) {
          local_6 = uint64_t(0);
        } else {
        }
        if ((!(local_5 < uint64_t(2)))) {
          if ((local_5 == uint64_t(18446744073709551615))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
          local_6 = (local_5 + uint64_t(1));
        } else {
        }
      } else {
      }
      if ((local_2 == uint64_t(6))) {
        if ((local_5 == uint64_t(0))) {
          local_6 = local_4;
        } else {
          if (((uint64_t(18446744073709551615) - (local_5 - uint64_t(1))) < local_3)) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
          local_6 = ((local_5 - uint64_t(1)) + local_3);
        }
      } else {
      }
      if (((uint64_t(18446744073709551615) - local_6) < local_1)) {
        environment_0[uint64_t(8)] = { uint64_t(1) };
      } else {
      }
      environment_0[uint64_t(0)] = { (local_6 + local_1) };
    } else {
    }
  };
  auto procedure_19 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6, uint64_t local_7, uint64_t local_8, uint64_t local_9, uint64_t local_10, uint64_t local_11, uint64_t local_12, uint64_t local_13) {
    environment_0[uint64_t(10)] = { uint64_t(0) };
    procedure_7(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_0, local_4);
    for (uint64_t binder_0 = 0, loop_end = uint64_t(4294967296); binder_0 < loop_end; binder_0++) {
      if ((get<0>(environment_0[uint64_t(10)]) == uint64_t(0)) || (get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
        break;
      } else {
      }
      for (uint64_t binder_1 = 0, loop_end = uint64_t(4294967296); binder_1 < loop_end; binder_1++) {
        if ((get<0>(environment_0[uint64_t(10)]) == uint64_t(0)) || (get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
          break;
        } else {
        }
        for (uint64_t binder_2 = 0, loop_end = uint64_t(4294967296); binder_2 < loop_end; binder_2++) {
          if ((get<0>(environment_0[uint64_t(10)]) == uint64_t(0)) || (get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
            break;
          } else {
          }
          for (uint64_t binder_3 = 0, loop_end = uint64_t(4294967296); binder_3 < loop_end; binder_3++) {
            if ((get<0>(environment_0[uint64_t(10)]) == uint64_t(0)) || (get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
              break;
            } else {
            }
            for (uint64_t binder_4 = 0, loop_end = uint64_t(4294967296); binder_4 < loop_end; binder_4++) {
              if ((get<0>(environment_0[uint64_t(10)]) == uint64_t(0)) || (get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
                break;
              } else {
              }
              for (uint64_t binder_5 = 0, loop_end = uint64_t(4294967296); binder_5 < loop_end; binder_5++) {
                if ((get<0>(environment_0[uint64_t(10)]) == uint64_t(0)) || (get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
                  break;
                } else {
                }
                for (uint64_t binder_6 = 0, loop_end = uint64_t(4294967296); binder_6 < loop_end; binder_6++) {
                  if ((get<0>(environment_0[uint64_t(10)]) == uint64_t(0)) || (get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
                    break;
                  } else {
                  }
                  for (uint64_t binder_7 = 0, loop_end = uint64_t(4294967296); binder_7 < loop_end; binder_7++) {
                    if ((get<0>(environment_0[uint64_t(10)]) == uint64_t(0)) || (get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
                      break;
                    } else {
                    }
                    local_5 = (get<0>(environment_0[uint64_t(10)]) - uint64_t(1));
                    local_6 = get<0>(environment_7[local_5]);
                    local_7 = get<1>(environment_7[local_5]);
                    local_8 = get<2>(environment_7[local_5]);
                    local_12 = get<3>(environment_7[local_5]);
                    local_9 = get<0>(environment_4[local_6]);
                    local_10 = get<1>(environment_4[local_6]);
                    local_11 = get<2>(environment_4[local_6]);
                    if ((local_8 == uint64_t(0))) {
                      if ((local_9 == uint64_t(0))) {
                        environment_0[uint64_t(0)] = { uint64_t(0) };
                        environment_0[uint64_t(10)] = { local_5 };
                      } else {
                      }
                      if ((local_9 == uint64_t(1)) || (local_9 == uint64_t(2))) {
                        procedure_18(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_10, local_7, local_1, local_2, local_3, 0, 0);
                        local_10 = get<0>(environment_0[uint64_t(0)]);
                        procedure_18(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_11, local_7, local_1, local_2, local_3, 0, 0);
                        local_11 = get<0>(environment_0[uint64_t(0)]);
                        procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_9, local_10, local_11, 0, 0, 0);
                        environment_0[uint64_t(10)] = { local_5 };
                      } else {
                      }
                      if ((local_9 == uint64_t(3))) {
                        environment_7[local_5] = { local_6, local_7, uint64_t(1), uint64_t(0) };
                        procedure_7(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_10, local_7);
                      } else {
                      }
                      if ((local_9 == uint64_t(4))) {
                        if ((local_7 == uint64_t(18446744073709551615))) {
                          environment_0[uint64_t(8)] = { uint64_t(1) };
                        } else {
                          environment_7[local_5] = { local_6, local_7, uint64_t(3), uint64_t(0) };
                          procedure_7(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_10, (local_7 + uint64_t(1)));
                        }
                      } else {
                      }
                    } else {
                    }
                    if ((local_8 == uint64_t(1))) {
                      environment_7[local_5] = { local_6, local_7, uint64_t(2), get<0>(environment_0[uint64_t(0)]) };
                      procedure_7(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_11, local_7);
                    } else {
                    }
                    if ((local_8 == uint64_t(2))) {
                      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_12, get<0>(environment_0[uint64_t(0)]), 0, 0, 0);
                      environment_0[uint64_t(10)] = { local_5 };
                    } else {
                    }
                    if ((local_8 == uint64_t(3))) {
                      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), get<0>(environment_0[uint64_t(0)]), uint64_t(0), 0, 0, 0);
                      environment_0[uint64_t(10)] = { local_5 };
                    } else {
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    if ((get<0>(environment_0[uint64_t(10)]) != uint64_t(0))) {
      environment_0[uint64_t(8)] = { uint64_t(1) };
    } else {
    }
  };
  auto procedure_20 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3) {
    if ((get<0>(environment_5[local_0]) == uint64_t(0))) {
      local_3 = get<1>(environment_5[local_0]);
      if (((uint64_t(18446744073709551615) - local_3) < local_1)) {
        environment_0[uint64_t(8)] = { uint64_t(1) };
      } else {
      }
      if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), local_2, (local_3 + local_1), 0, 0, 0);
      } else {
      }
    } else {
      procedure_19(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<1>(environment_5[local_0]), uint64_t(6), local_1, local_2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    }
  };
  auto procedure_21 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6, uint64_t local_7, uint64_t local_8, uint64_t local_9) {
    if ((get<0>(environment_5[local_0]) == uint64_t(0)) && (get<0>(environment_5[local_1]) == uint64_t(0))) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), get<1>(environment_5[local_0]), get<1>(environment_5[local_1]), 0, 0, 0);
    } else {
      procedure_20(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_0, uint64_t(1), uint64_t(0), 0);
      local_2 = get<0>(environment_0[uint64_t(0)]);
      procedure_20(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(1), uint64_t(0), 0);
      local_3 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_2, local_3, 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_3, local_2, 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, uint64_t(0), 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_6, 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_7, uint64_t(0), 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_8, uint64_t(0), 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_9 };
    }
  };
  auto procedure_22 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6, uint64_t local_7, uint64_t local_8, uint64_t local_9, uint64_t local_10, uint64_t local_11, uint64_t local_12, uint64_t local_13, uint64_t local_14, uint64_t local_15, uint64_t local_16) {
    if ((get<0>(environment_5[local_0]) == uint64_t(0))) {
      procedure_20(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(0), get<1>(environment_5[local_0]), 0);
    } else {
      procedure_20(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_0, uint64_t(2), uint64_t(0), 0);
      local_2 = get<0>(environment_0[uint64_t(0)]);
      procedure_20(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(1), uint64_t(0), 0);
      local_3 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(1), 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_2, 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_2, local_4, 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_6, uint64_t(0), 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, local_7, 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_8, uint64_t(0), 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_9, uint64_t(0), 0, 0, 0);
      local_10 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_3, uint64_t(0), 0, 0, 0);
      local_11 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_10, local_11, 0, 0, 0);
      local_12 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_12, uint64_t(0), 0, 0, 0);
      local_13 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_13, uint64_t(0), 0, 0, 0);
      local_14 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_14, uint64_t(0), 0, 0, 0);
      local_15 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_15, uint64_t(0), 0, 0, 0);
      local_16 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_16 };
    }
  };
  auto procedure_23 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6, uint64_t local_7, uint64_t local_8, uint64_t local_9, uint64_t local_10, uint64_t local_11, uint64_t local_12) {
    if ((get<0>(environment_5[local_0]) == uint64_t(0))) {
      local_1 = get<1>(environment_5[local_0]);
      if ((local_1 == uint64_t(18446744073709551615))) {
        environment_0[uint64_t(8)] = { uint64_t(1) };
      } else {
      }
      if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), uint64_t(0), (local_1 + uint64_t(1)), 0, 0, 0);
        local_3 = get<0>(environment_0[uint64_t(0)]);
        procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_3, uint64_t(0), 0, 0, 0);
        local_4 = get<0>(environment_0[uint64_t(0)]);
        procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_4, uint64_t(0), 0, 0, 0);
        local_5 = get<0>(environment_0[uint64_t(0)]);
        procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, uint64_t(0), 0, 0, 0);
        local_6 = get<0>(environment_0[uint64_t(0)]);
        environment_0[uint64_t(0)] = { local_6 };
      } else {
      }
    } else {
      procedure_20(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_0, uint64_t(2), uint64_t(0), 0);
      local_2 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(1), 0, 0, 0);
      local_3 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_3, local_2, 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_2, local_3, 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, uint64_t(0), 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_6, 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_7, uint64_t(0), 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_8, uint64_t(0), 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_9, uint64_t(0), 0, 0, 0);
      local_10 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_10, uint64_t(0), 0, 0, 0);
      local_11 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_11, uint64_t(0), 0, 0, 0);
      local_12 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_12 };
    }
  };
  auto procedure_24 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6, uint64_t local_7, uint64_t local_8, uint64_t local_9, uint64_t local_10, uint64_t local_11, uint64_t local_12, uint64_t local_13, uint64_t local_14, uint64_t local_15, uint64_t local_16, uint64_t local_17, uint64_t local_18, uint64_t local_19, uint64_t local_20, uint64_t local_21, uint64_t local_22, uint64_t local_23, uint64_t local_24, uint64_t local_25, uint64_t local_26, uint64_t local_27, uint64_t local_28, uint64_t local_29, uint64_t local_30, uint64_t local_31, uint64_t local_32, uint64_t local_33, uint64_t local_34, uint64_t local_35, uint64_t local_36, uint64_t local_37, uint64_t local_38, uint64_t local_39, uint64_t local_40, uint64_t local_41, uint64_t local_42, uint64_t local_43, uint64_t local_44, uint64_t local_45) {
    environment_0[uint64_t(13)] = { uint64_t(0) };
    if ((local_0 == uint64_t(0)) && (local_1 < get<0>(environment_0[uint64_t(1)])) && (local_2 < get<0>(environment_0[uint64_t(1)]))) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_2, local_1, 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_1, local_4, 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_5 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(1)) && (local_1 < get<0>(environment_0[uint64_t(1)])) && (local_2 < get<0>(environment_0[uint64_t(1)])) && (local_3 < get<0>(environment_0[uint64_t(1)]))) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_2, local_3, 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_1, local_4, 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_1, local_2, 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_1, local_3, 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_6, local_7, 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, local_8, 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_9 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(2)) && (local_1 < get<0>(environment_0[uint64_t(1)]))) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_1, uint64_t(0), 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, uint64_t(0), 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, local_1, 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_6 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(3)) && (local_1 < get<0>(environment_0[uint64_t(1)]))) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_1, uint64_t(0), 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_19(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(1), uint64_t(0), local_2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_5, 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_6 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(4)) && (local_1 < get<0>(environment_0[uint64_t(1)])) && (local_2 < get<0>(environment_0[uint64_t(1)]))) {
      procedure_19(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(0), uint64_t(1), uint64_t(0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_2, 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_5, uint64_t(0), 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_2, uint64_t(0), 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_1, local_7, 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_6, local_8, 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_9 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(5)) && true) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), local_1, local_1, 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_4 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(6)) && true) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), local_1, local_2, 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), local_1, local_3, 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), local_2, local_3, 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, local_6, 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_7, 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_8 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(7)) && true) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), local_1, local_2, 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), local_3, local_1, 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), local_3, local_2, 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, local_6, 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_7, 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_8 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(8)) && true) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), local_1, local_2, 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), local_1, local_3, 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), local_2, local_3, 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, local_6, 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_7, 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_8 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(9)) && true) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(1), 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(2), 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_5, 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, local_4, 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_7, uint64_t(0), 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_6, local_8, 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_9, uint64_t(0), 0, 0, 0);
      local_10 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_10, uint64_t(0), 0, 0, 0);
      local_11 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), uint64_t(0), uint64_t(1), 0, 0, 0);
      local_12 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_11, local_12, 0, 0, 0);
      local_13 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_13 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(10)) && true) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(1), 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, uint64_t(0), 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_5, uint64_t(0), 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_6, uint64_t(0), 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(2), 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_8, uint64_t(0), 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_9, 0, 0, 0);
      local_10 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_10, uint64_t(0), 0, 0, 0);
      local_11 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_11, uint64_t(0), 0, 0, 0);
      local_12 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_12, 0, 0, 0);
      local_13 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_13, uint64_t(0), 0, 0, 0);
      local_14 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_14, uint64_t(0), 0, 0, 0);
      local_15 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_15, uint64_t(0), 0, 0, 0);
      local_16 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_16, uint64_t(0), 0, 0, 0);
      local_17 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_7, local_17, 0, 0, 0);
      local_18 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_18 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(11)) && true) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(1), uint64_t(0), 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(2), uint64_t(0), 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, uint64_t(0), 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_6, 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_7, uint64_t(0), 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_8, uint64_t(0), 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_9, uint64_t(0), 0, 0, 0);
      local_10 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_10, uint64_t(0), 0, 0, 0);
      local_11 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_11 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(12)) && true) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(1), 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(1), uint64_t(3), 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(2), 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, local_6, 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_7, 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_8, uint64_t(0), 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_9, uint64_t(0), 0, 0, 0);
      local_10 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_10, uint64_t(0), 0, 0, 0);
      local_11 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_11, uint64_t(0), 0, 0, 0);
      local_12 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_12, uint64_t(0), 0, 0, 0);
      local_13 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_13 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(13)) && true) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(1), 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(3), 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_5, 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_6, uint64_t(0), 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_7, local_4, 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_8, uint64_t(0), 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_9, uint64_t(0), 0, 0, 0);
      local_10 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_10, uint64_t(0), 0, 0, 0);
      local_11 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_11, uint64_t(0), 0, 0, 0);
      local_12 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_12 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(14)) && true) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(1), 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, uint64_t(0), 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_5, uint64_t(0), 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_6, uint64_t(0), 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_7, 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_8, uint64_t(0), 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_9, uint64_t(0), 0, 0, 0);
      local_10 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_10, uint64_t(0), 0, 0, 0);
      local_11 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_11, uint64_t(0), 0, 0, 0);
      local_12 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(2), 0, 0, 0);
      local_13 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_13, uint64_t(0), 0, 0, 0);
      local_14 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), uint64_t(0), uint64_t(2), 0, 0, 0);
      local_15 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_14, local_15, 0, 0, 0);
      local_16 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_16, 0, 0, 0);
      local_17 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_16, local_4, 0, 0, 0);
      local_18 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_18, uint64_t(0), 0, 0, 0);
      local_19 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_17, local_19, 0, 0, 0);
      local_20 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_20, uint64_t(0), 0, 0, 0);
      local_21 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_21, uint64_t(0), 0, 0, 0);
      local_22 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_22, uint64_t(0), 0, 0, 0);
      local_23 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_13, local_23, 0, 0, 0);
      local_24 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_24, uint64_t(0), 0, 0, 0);
      local_25 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_25, uint64_t(0), 0, 0, 0);
      local_26 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_26, uint64_t(0), 0, 0, 0);
      local_27 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_27, uint64_t(0), 0, 0, 0);
      local_28 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_28, 0, 0, 0);
      local_29 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_29, uint64_t(0), 0, 0, 0);
      local_30 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_30, uint64_t(0), 0, 0, 0);
      local_31 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_12, local_31, 0, 0, 0);
      local_32 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_32, uint64_t(0), 0, 0, 0);
      local_33 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_33, uint64_t(0), 0, 0, 0);
      local_34 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_34, uint64_t(0), 0, 0, 0);
      local_35 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_35, uint64_t(0), 0, 0, 0);
      local_36 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_36 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(15)) && (local_1 < get<0>(environment_0[uint64_t(1)]))) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(1), 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(2), 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_19(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(2), uint64_t(0), uint64_t(0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_6, uint64_t(0), 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, local_7, 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_8, uint64_t(0), 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_9, 0, 0, 0);
      local_10 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_9, local_4, 0, 0, 0);
      local_11 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_11, uint64_t(0), 0, 0, 0);
      local_12 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_10, local_12, 0, 0, 0);
      local_13 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_13, uint64_t(0), 0, 0, 0);
      local_14 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_14, uint64_t(0), 0, 0, 0);
      local_15 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_15, uint64_t(0), 0, 0, 0);
      local_16 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_16, uint64_t(0), 0, 0, 0);
      local_17 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_17, uint64_t(0), 0, 0, 0);
      local_18 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_18 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(16)) && (local_1 < get<0>(environment_0[uint64_t(1)]))) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(1), 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_19(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(3), uint64_t(0), uint64_t(0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_19(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(4), uint64_t(0), uint64_t(0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), uint64_t(1), uint64_t(0), 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_6, local_7, 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_5, local_8, 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_9, uint64_t(0), 0, 0, 0);
      local_10 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_10, uint64_t(0), 0, 0, 0);
      local_11 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_11, 0, 0, 0);
      local_12 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_12, uint64_t(0), 0, 0, 0);
      local_13 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(3), 0, 0, 0);
      local_14 = get<0>(environment_0[uint64_t(0)]);
      procedure_19(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(5), uint64_t(0), uint64_t(0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
      local_15 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_15, uint64_t(0), 0, 0, 0);
      local_16 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_14, local_16, 0, 0, 0);
      local_17 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_17, uint64_t(0), 0, 0, 0);
      local_18 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_18, uint64_t(0), 0, 0, 0);
      local_19 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_19, uint64_t(0), 0, 0, 0);
      local_20 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_20, uint64_t(0), 0, 0, 0);
      local_21 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_21, local_4, 0, 0, 0);
      local_22 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_22, uint64_t(0), 0, 0, 0);
      local_23 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_23, uint64_t(0), 0, 0, 0);
      local_24 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_24, uint64_t(0), 0, 0, 0);
      local_25 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_25, uint64_t(0), 0, 0, 0);
      local_26 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_13, local_26, 0, 0, 0);
      local_27 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_27 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
    if ((local_0 == uint64_t(17)) && true) {
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(1), 0, 0, 0);
      local_4 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, uint64_t(0), 0, 0, 0);
      local_5 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_5, uint64_t(0), 0, 0, 0);
      local_6 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_6, uint64_t(0), 0, 0, 0);
      local_7 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_7, 0, 0, 0);
      local_8 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_8, uint64_t(0), 0, 0, 0);
      local_9 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(1), uint64_t(2), 0, 0, 0);
      local_10 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(2), 0, 0, 0);
      local_11 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_11, local_5, 0, 0, 0);
      local_12 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_12, uint64_t(0), 0, 0, 0);
      local_13 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_13, uint64_t(0), 0, 0, 0);
      local_14 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_14, uint64_t(0), 0, 0, 0);
      local_15 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_15, uint64_t(0), 0, 0, 0);
      local_16 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), uint64_t(1), uint64_t(0), 0, 0, 0);
      local_17 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_16, local_17, 0, 0, 0);
      local_18 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_11, local_18, 0, 0, 0);
      local_19 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_10, local_19, 0, 0, 0);
      local_20 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_20, uint64_t(0), 0, 0, 0);
      local_21 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_21, uint64_t(0), 0, 0, 0);
      local_22 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_22, uint64_t(0), 0, 0, 0);
      local_23 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_9, local_23, 0, 0, 0);
      local_24 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_24, uint64_t(0), 0, 0, 0);
      local_25 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), uint64_t(0), uint64_t(3), 0, 0, 0);
      local_26 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), uint64_t(0), uint64_t(1), 0, 0, 0);
      local_27 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_26, local_27, 0, 0, 0);
      local_28 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_11, local_28, 0, 0, 0);
      local_29 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_29, uint64_t(0), 0, 0, 0);
      local_30 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_30, uint64_t(0), 0, 0, 0);
      local_31 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_11, local_31, 0, 0, 0);
      local_32 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_32, uint64_t(0), 0, 0, 0);
      local_33 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_33, uint64_t(0), 0, 0, 0);
      local_34 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_4, local_34, 0, 0, 0);
      local_35 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_35, uint64_t(0), 0, 0, 0);
      local_36 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_36, uint64_t(0), 0, 0, 0);
      local_37 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_37, uint64_t(0), 0, 0, 0);
      local_38 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_38, uint64_t(0), 0, 0, 0);
      local_39 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_11, local_39, 0, 0, 0);
      local_40 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_40, uint64_t(0), 0, 0, 0);
      local_41 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_41, uint64_t(0), 0, 0, 0);
      local_42 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_42, uint64_t(0), 0, 0, 0);
      local_43 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_43, uint64_t(0), 0, 0, 0);
      local_44 = get<0>(environment_0[uint64_t(0)]);
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_25, local_44, 0, 0, 0);
      local_45 = get<0>(environment_0[uint64_t(0)]);
      environment_0[uint64_t(0)] = { local_45 };
      environment_0[uint64_t(13)] = { uint64_t(1) };
    } else {
    }
  };
  auto procedure_25 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1) {
    if ((!(local_0 < get<0>(environment_0[uint64_t(16)])))) {
      environment_0[uint64_t(18)] = { uint64_t(0) };
    } else {
      if ((get<5>(environment_9[local_0]) != local_1)) {
        environment_0[uint64_t(18)] = { uint64_t(0) };
      } else {
      }
      if ((get<0>(environment_0[uint64_t(19)]) < get<6>(environment_9[local_0]))) {
        environment_0[uint64_t(19)] = { get<6>(environment_9[local_0]) };
      } else {
      }
    }
  };
  auto procedure_26 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5) {
    environment_0[uint64_t(18)] = { uint64_t(1) };
    environment_0[uint64_t(19)] = { uint64_t(0) };
    local_5 = uint64_t(0);
    if ((uint64_t(11) < local_0)) {
      environment_0[uint64_t(18)] = { uint64_t(0) };
    } else {
    }
    if ((local_0 == uint64_t(0))) {
      if ((local_1 == uint64_t(18446744073709551615))) {
        environment_0[uint64_t(18)] = { uint64_t(0) };
      } else {
        environment_0[uint64_t(19)] = { (local_1 + uint64_t(1)) };
      }
    } else {
    }
    if ((local_0 == uint64_t(1)) && (!(local_1 < get<0>(environment_0[uint64_t(2)])))) {
      environment_0[uint64_t(18)] = { uint64_t(0) };
    } else {
    }
    if ((local_0 == uint64_t(2))) {
      local_5 = uint64_t(1);
      if ((!(local_1 < get<0>(environment_0[uint64_t(1)])))) {
        environment_0[uint64_t(18)] = { uint64_t(0) };
      } else {
      }
    } else {
    }
    if ((local_0 == uint64_t(3))) {
      procedure_25(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(1));
    } else {
    }
    if ((local_0 == uint64_t(4)) || (local_0 == uint64_t(5))) {
      local_5 = uint64_t(1);
      procedure_25(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(0));
      procedure_25(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_2, uint64_t(0));
    } else {
    }
    if ((local_0 == uint64_t(6)) || (local_0 == uint64_t(7))) {
      local_5 = uint64_t(1);
      procedure_25(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(1));
      if ((local_0 == uint64_t(6))) {
        procedure_25(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_2, uint64_t(1));
      } else {
      }
    } else {
    }
    if ((local_0 == uint64_t(8))) {
      local_5 = uint64_t(2);
      if ((uint64_t(17) < local_1)) {
        environment_0[uint64_t(18)] = { uint64_t(0) };
      } else {
      }
      if ((local_1 == uint64_t(0)) || (local_1 == uint64_t(1)) || (local_1 == uint64_t(2)) || (local_1 == uint64_t(3)) || (local_1 == uint64_t(4)) || (local_1 == uint64_t(15)) || (local_1 == uint64_t(16))) {
        procedure_25(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_2, uint64_t(1));
      } else {
      }
      if ((local_1 == uint64_t(0)) || (local_1 == uint64_t(1)) || (local_1 == uint64_t(4))) {
        procedure_25(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_3, uint64_t(1));
      } else {
      }
      if ((local_1 == uint64_t(1))) {
        procedure_25(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_4, uint64_t(1));
      } else {
      }
    } else {
    }
    if ((local_0 == uint64_t(9)) || (local_0 == uint64_t(10))) {
      local_5 = uint64_t(2);
      procedure_25(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(2));
      if ((local_0 == uint64_t(9))) {
        procedure_25(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_2, uint64_t(2));
      } else {
      }
    } else {
    }
    if ((local_0 == uint64_t(11))) {
      local_5 = uint64_t(2);
      if ((!(local_1 < get<0>(environment_0[uint64_t(3)])))) {
        environment_0[uint64_t(18)] = { uint64_t(0) };
      } else {
        local_1 = get<0>(environment_6[local_1]);
      }
    } else {
    }
    if ((get<0>(environment_0[uint64_t(18)]) == uint64_t(0))) {
      procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
    } else {
      if ((get<0>(environment_0[uint64_t(16)]) == uint64_t(18446744073709551615))) {
        environment_0[uint64_t(8)] = { uint64_t(1) };
      } else {
        growArray(environment_9, (get<0>(environment_0[uint64_t(16)]) + uint64_t(1)));
        environment_9[get<0>(environment_0[uint64_t(16)])] = { local_0, local_1, local_2, local_3, local_4, local_5, get<0>(environment_0[uint64_t(19)]) };
        procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(16)]));
        environment_0[uint64_t(16)] = { (get<0>(environment_0[uint64_t(16)]) + uint64_t(1)) };
      }
    }
  };
  auto procedure_27 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1) {
    if ((get<0>(environment_0[uint64_t(2)]) == uint64_t(18446744073709551615))) {
      environment_0[uint64_t(8)] = { uint64_t(1) };
    } else {
      growArray(environment_5, (get<0>(environment_0[uint64_t(2)]) + uint64_t(1)));
      environment_5[get<0>(environment_0[uint64_t(2)])] = { local_0, local_1 };
      environment_0[uint64_t(0)] = { get<0>(environment_0[uint64_t(2)]) };
      environment_0[uint64_t(2)] = { (get<0>(environment_0[uint64_t(2)]) + uint64_t(1)) };
    }
  };
  auto procedure_28 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2) {
    environment_0[uint64_t(0)] = { local_0 };
    if ((local_1 != uint64_t(0))) {
      local_2 = get<1>(environment_5[local_0]);
      if ((get<0>(environment_5[local_0]) == uint64_t(0))) {
        if (((uint64_t(18446744073709551615) - local_2) < local_1)) {
          environment_0[uint64_t(8)] = { uint64_t(1) };
        } else {
          procedure_27(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(0), (local_2 + local_1));
        }
      } else {
        procedure_19(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_2, uint64_t(0), local_1, 0, uint64_t(1), 0, 0, 0, 0, 0, 0, 0, 0, 0);
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_27(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), get<0>(environment_0[uint64_t(0)]));
        } else {
        }
      }
    } else {
    }
  };
  auto procedure_29 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2) {
    environment_11[((local_0 * local_2) + local_1)] = { uint8_t(uint64_t(1)) };
  };
  auto procedure_30 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6, uint64_t local_7, uint64_t local_8, uint64_t local_9, uint64_t local_10, uint64_t local_11, uint64_t local_12, uint64_t local_13) {
    local_1 = (local_0 + uint64_t(1));
    if (((uint64_t(18446744073709551615) / local_1) < local_1)) {
      environment_0[uint64_t(8)] = { uint64_t(1) };
    } else {
      local_2 = (local_1 * local_1);
      growArray(environment_11, local_2);
      growArray(environment_10, local_2);
      for (uint64_t binder_0 = 0, loop_end = local_2; binder_0 < loop_end; binder_0++) {
        environment_11[binder_0] = { uint8_t(uint64_t(0)) };
      }
      procedure_29(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_0, uint64_t(0), local_1);
      for (uint64_t binder_0 = 0, loop_end = local_1; binder_0 < loop_end; binder_0++) {
        local_3 = (local_0 - binder_0);
        for (uint64_t binder_1 = 0, loop_end = local_1; binder_1 < loop_end; binder_1++) {
          local_5 = ((local_3 * local_1) + binder_1);
          if ((get<0>(environment_11[local_5]) != uint8_t(uint64_t(0)))) {
            local_6 = get<0>(environment_9[local_3]);
            local_7 = get<1>(environment_9[local_3]);
            local_8 = get<2>(environment_9[local_3]);
            local_9 = get<3>(environment_9[local_3]);
            local_10 = get<4>(environment_9[local_3]);
            if ((local_6 == uint64_t(3)) || (local_6 == uint64_t(7)) || (local_6 == uint64_t(10))) {
              procedure_29(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_7, (binder_1 + uint64_t(1)), local_1);
            } else {
            }
            if ((local_6 == uint64_t(4)) || (local_6 == uint64_t(5)) || (local_6 == uint64_t(6)) || (local_6 == uint64_t(9))) {
              procedure_29(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_7, binder_1, local_1);
              procedure_29(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_8, binder_1, local_1);
            } else {
            }
            if ((local_6 == uint64_t(8))) {
              if ((local_7 == uint64_t(0)) || (local_7 == uint64_t(1)) || (local_7 == uint64_t(2)) || (local_7 == uint64_t(3)) || (local_7 == uint64_t(4)) || (local_7 == uint64_t(15)) || (local_7 == uint64_t(16))) {
                procedure_29(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_8, binder_1, local_1);
              } else {
              }
              if ((local_7 == uint64_t(0)) || (local_7 == uint64_t(1)) || (local_7 == uint64_t(4))) {
                procedure_29(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_9, binder_1, local_1);
              } else {
              }
              if ((local_7 == uint64_t(1))) {
                procedure_29(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_10, binder_1, local_1);
              } else {
              }
            } else {
            }
          } else {
          }
        }
      }
      for (uint64_t binder_0 = 0, loop_end = local_1; binder_0 < loop_end; binder_0++) {
        if ((get<0>(environment_0[uint64_t(18)]) == uint64_t(0)) || (get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
          break;
        } else {
        }
        for (uint64_t binder_1 = 0, loop_end = local_1; binder_1 < loop_end; binder_1++) {
          if ((get<0>(environment_0[uint64_t(18)]) == uint64_t(0)) || (get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
            break;
          } else {
          }
          local_5 = ((binder_0 * local_1) + binder_1);
          if ((get<0>(environment_11[local_5]) != uint8_t(uint64_t(0)))) {
            local_6 = get<0>(environment_9[binder_0]);
            local_7 = get<1>(environment_9[binder_0]);
            local_8 = get<2>(environment_9[binder_0]);
            local_9 = get<3>(environment_9[binder_0]);
            local_10 = get<4>(environment_9[binder_0]);
            if ((local_6 == uint64_t(0))) {
              procedure_28(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_12[local_7]), binder_1, 0);
            } else {
            }
            if ((local_6 == uint64_t(1)) || (local_6 == uint64_t(2)) || (local_6 == uint64_t(11))) {
              environment_0[uint64_t(0)] = { local_7 };
            } else {
            }
            if ((local_6 == uint64_t(3))) {
              procedure_27(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), get<0>(environment_10[(((local_7 * local_1) + binder_1) + uint64_t(1))]));
            } else {
            }
            if ((local_6 == uint64_t(4)) || (local_6 == uint64_t(5)) || (local_6 == uint64_t(6)) || (local_6 == uint64_t(9))) {
              local_11 = get<0>(environment_10[((local_7 * local_1) + binder_1)]);
              local_12 = get<0>(environment_10[((local_8 * local_1) + binder_1)]);
              if ((local_6 == uint64_t(4))) {
                procedure_21(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_11, local_12, 0, 0, 0, 0, 0, 0, 0, 0);
              } else {
              }
              if ((local_6 == uint64_t(5))) {
                procedure_22(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_11, local_12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
              } else {
              }
              if ((local_6 == uint64_t(6))) {
                procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_11, local_12, 0, 0, 0);
              } else {
              }
              if ((local_6 == uint64_t(9))) {
                if ((get<0>(environment_4[local_11]) == uint64_t(3)) && (get<1>(environment_4[local_11]) == local_12)) {
                  environment_0[uint64_t(0)] = { get<2>(environment_4[local_11]) };
                } else {
                  environment_0[uint64_t(18)] = { uint64_t(0) };
                }
              } else {
              }
            } else {
            }
            if ((local_6 == uint64_t(7)) || (local_6 == uint64_t(10))) {
              procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), get<0>(environment_10[(((local_7 * local_1) + binder_1) + uint64_t(1))]), uint64_t(0), 0, 0, 0);
            } else {
            }
            if ((local_6 == uint64_t(8))) {
              local_11 = local_8;
              local_12 = local_9;
              local_13 = local_10;
              if ((local_7 == uint64_t(0)) || (local_7 == uint64_t(1)) || (local_7 == uint64_t(2)) || (local_7 == uint64_t(3)) || (local_7 == uint64_t(4)) || (local_7 == uint64_t(15)) || (local_7 == uint64_t(16))) {
                local_11 = get<0>(environment_10[((local_8 * local_1) + binder_1)]);
              } else {
              }
              if ((local_7 == uint64_t(0)) || (local_7 == uint64_t(1)) || (local_7 == uint64_t(4))) {
                local_12 = get<0>(environment_10[((local_9 * local_1) + binder_1)]);
              } else {
              }
              if ((local_7 == uint64_t(1))) {
                local_13 = get<0>(environment_10[((local_10 * local_1) + binder_1)]);
              } else {
              }
              procedure_24(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_7, local_11, local_12, local_13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
              if ((get<0>(environment_0[uint64_t(13)]) == uint64_t(0))) {
                environment_0[uint64_t(18)] = { uint64_t(0) };
              } else {
              }
            } else {
            }
            environment_10[local_5] = { get<0>(environment_0[uint64_t(0)]) };
          } else {
          }
        }
      }
      if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0)) && (get<0>(environment_0[uint64_t(18)]) != uint64_t(0))) {
        environment_0[uint64_t(0)] = { get<0>(environment_10[(local_0 * local_1)]) };
      } else {
      }
    }
  };
  auto procedure_31 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6) {
    procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
    local_0 = get<0>(environment_0[uint64_t(11)]);
    if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
      if ((get<0>(environment_0[uint64_t(7)]) != uint64_t(0)) && (get<0>(environment_0[uint64_t(6)]) == uint64_t(0)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        environment_0[uint64_t(9)] = { uint64_t(1) };
      } else {
        environment_0[uint64_t(8)] = { uint64_t(1) };
      }
    } else {
      if ((uint64_t(26) < local_0)) {
        environment_0[uint64_t(8)] = { uint64_t(1) };
      } else {
      }
      if ((local_0 == uint64_t(0)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            environment_0[uint64_t(9)] = { uint64_t(1) };
            for (uint8_t binder_0 : { 66, 89, 69, 10 }) {
              writeChar(binder_0);
            }
            flushSTDOUT();
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(1)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_2 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(1), local_1, local_2, 0, 0, 0);
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(0)]));
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(2)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_2 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(2), local_1, local_2, 0, 0, 0);
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(0)]));
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(3)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_2 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if ((local_1 < get<0>(environment_0[uint64_t(1)])) && (local_2 < get<0>(environment_0[uint64_t(1)]))) {
            procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(3), local_1, local_2, 0, 0, 0);
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(0)]));
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(4)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if ((local_1 < get<0>(environment_0[uint64_t(1)]))) {
            procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(4), local_1, uint64_t(0), 0, 0, 0);
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(0)]));
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(5)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            if ((get<0>(environment_0[uint64_t(2)]) == uint64_t(18446744073709551615))) {
              environment_0[uint64_t(8)] = { uint64_t(1) };
            } else {
              growArray(environment_5, (get<0>(environment_0[uint64_t(2)]) + uint64_t(1)));
              environment_5[get<0>(environment_0[uint64_t(2)])] = { uint64_t(0), local_1 };
              procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(2)]));
              environment_0[uint64_t(2)] = { (get<0>(environment_0[uint64_t(2)]) + uint64_t(1)) };
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(6)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if ((local_1 < get<0>(environment_0[uint64_t(1)]))) {
            if ((get<0>(environment_0[uint64_t(2)]) == uint64_t(18446744073709551615))) {
              environment_0[uint64_t(8)] = { uint64_t(1) };
            } else {
              growArray(environment_5, (get<0>(environment_0[uint64_t(2)]) + uint64_t(1)));
              environment_5[get<0>(environment_0[uint64_t(2)])] = { uint64_t(1), local_1 };
              procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(2)]));
              environment_0[uint64_t(2)] = { (get<0>(environment_0[uint64_t(2)]) + uint64_t(1)) };
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(7)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_2 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if ((local_1 < get<0>(environment_0[uint64_t(2)])) && (local_2 < get<0>(environment_0[uint64_t(2)]))) {
            procedure_21(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, local_2, 0, 0, 0, 0, 0, 0, 0, 0);
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(0)]));
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(8)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_2 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if ((local_1 < get<0>(environment_0[uint64_t(2)])) && (local_2 < get<0>(environment_0[uint64_t(2)]))) {
            procedure_22(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, local_2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(0)]));
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(9)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_9(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
              environment_0[uint64_t(8)] = { uint64_t(1) };
            } else {
            }
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              if ((!(local_1 < get<0>(environment_0[uint64_t(2)])))) {
                procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
              } else {
                procedure_14(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(0));
              }
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(10)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_9(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
              environment_0[uint64_t(8)] = { uint64_t(1) };
            } else {
            }
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_11(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0);
              if ((get<0>(environment_0[uint64_t(0)]) == uint64_t(18446744073709551615)) || (get<4>(environment_8[get<0>(environment_0[uint64_t(0)])]) != uint64_t(0))) {
                procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
              } else {
                procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<2>(environment_8[get<0>(environment_0[uint64_t(0)])]));
              }
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(11)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_4 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_2 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_3 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_24(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_4, local_1, local_2, local_3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
            if ((get<0>(environment_0[uint64_t(13)]) == uint64_t(0))) {
              procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            } else {
              procedure_15(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(0)]));
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(12)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_2 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if ((local_1 < get<0>(environment_0[uint64_t(3)])) && (local_2 < get<0>(environment_0[uint64_t(3)]))) {
            procedure_16(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, local_2, 0);
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(13)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if ((local_1 < get<0>(environment_0[uint64_t(3)]))) {
            procedure_17(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1);
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(14)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_9(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
              environment_0[uint64_t(8)] = { uint64_t(1) };
            } else {
            }
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_11(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0);
              local_6 = get<0>(environment_0[uint64_t(0)]);
              if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
                procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
                local_1 = get<0>(environment_0[uint64_t(11)]);
                if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
                  environment_0[uint64_t(8)] = { uint64_t(1) };
                } else {
                }
              } else {
              }
              if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
                if ((local_6 != uint64_t(18446744073709551615)) && (get<4>(environment_8[local_6]) == uint64_t(0)) && (local_1 < get<0>(environment_0[uint64_t(3)]))) {
                  procedure_23(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<2>(environment_8[local_6]), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
                  if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
                    if ((get<0>(environment_0[uint64_t(0)]) == get<0>(environment_6[local_1]))) {
                      environment_8[local_6] = { get<0>(environment_8[local_6]), get<1>(environment_8[local_6]), get<2>(environment_8[local_6]), uint64_t(1), uint64_t(0) };
                      procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<2>(environment_8[local_6]));
                    } else {
                      procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
                    }
                  } else {
                  }
                } else {
                  procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
                }
              } else {
              }
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(15)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_9(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
              environment_0[uint64_t(8)] = { uint64_t(1) };
            } else {
            }
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_11(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0);
              if ((get<0>(environment_0[uint64_t(0)]) == uint64_t(18446744073709551615)) || (get<4>(environment_8[get<0>(environment_0[uint64_t(0)])]) != uint64_t(0))) {
                procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
              } else {
                if ((get<3>(environment_8[get<0>(environment_0[uint64_t(0)])]) == uint64_t(1))) {
                  for (uint8_t binder_0 : { 83, 69, 84, 10 }) {
                    writeChar(binder_0);
                  }
                } else {
                  for (uint8_t binder_0 : { 67, 76, 65, 83, 83, 10 }) {
                    writeChar(binder_0);
                  }
                }
                flushSTDOUT();
              }
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(16)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            if ((get<0>(environment_0[uint64_t(3)]) == uint64_t(0))) {
              procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            } else {
              environment_0[uint64_t(3)] = { (get<0>(environment_0[uint64_t(3)]) - uint64_t(1)) };
              procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(3)]));
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(17)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            environment_0[uint64_t(3)] = { uint64_t(0) };
            procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(0));
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(18)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_2 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if ((local_1 < get<0>(environment_0[uint64_t(3)])) && (local_2 < get<0>(environment_0[uint64_t(1)]))) {
            if ((get<0>(environment_6[local_1]) == local_2)) {
              procedure_15(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_2);
            } else {
              procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(19)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if ((local_1 < get<0>(environment_0[uint64_t(3)]))) {
            procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_6[local_1]));
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(20)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_9(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
              environment_0[uint64_t(8)] = { uint64_t(1) };
            } else {
            }
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              if ((local_1 < get<0>(environment_0[uint64_t(3)]))) {
                procedure_14(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_6[local_1]), uint64_t(1));
              } else {
                procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
              }
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(21)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_9(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
              environment_0[uint64_t(8)] = { uint64_t(1) };
            } else {
            }
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_11(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0);
              if ((get<0>(environment_0[uint64_t(0)]) == uint64_t(18446744073709551615)) || (get<4>(environment_8[get<0>(environment_0[uint64_t(0)])]) != uint64_t(1))) {
                procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
              } else {
                procedure_15(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<2>(environment_8[get<0>(environment_0[uint64_t(0)])]));
              }
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(22)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_4 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_2 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_3 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_5 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_26(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_4, local_1, local_2, local_3, local_5, 0);
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(23)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
          local_1 = get<0>(environment_0[uint64_t(11)]);
          if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
            environment_0[uint64_t(8)] = { uint64_t(1) };
          } else {
          }
        } else {
        }
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_9(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
              environment_0[uint64_t(8)] = { uint64_t(1) };
            } else {
            }
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              if ((local_1 < get<0>(environment_0[uint64_t(16)])) && (get<5>(environment_9[local_1]) == uint64_t(2))) {
                procedure_14(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_1, uint64_t(2));
              } else {
                procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
              }
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(24)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_9(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
              environment_0[uint64_t(8)] = { uint64_t(1) };
            } else {
            }
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_11(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0);
              local_6 = get<0>(environment_0[uint64_t(0)]);
              if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
                procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
                local_1 = get<0>(environment_0[uint64_t(11)]);
                if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
                  environment_0[uint64_t(8)] = { uint64_t(1) };
                } else {
                }
              } else {
              }
              environment_0[uint64_t(18)] = { uint64_t(1) };
              for (uint64_t binder_0 = 0, loop_end = local_1; binder_0 < loop_end; binder_0++) {
                if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
                  procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
                  local_2 = get<0>(environment_0[uint64_t(11)]);
                  if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
                    environment_0[uint64_t(8)] = { uint64_t(1) };
                  } else {
                  }
                } else {
                }
                if ((get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
                  break;
                } else {
                }
                if ((!(local_2 < get<0>(environment_0[uint64_t(2)])))) {
                  environment_0[uint64_t(18)] = { uint64_t(0) };
                } else {
                }
                growArray(environment_12, (binder_0 + uint64_t(1)));
                environment_12[binder_0] = { local_2 };
              }
              if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
                if ((local_6 == uint64_t(18446744073709551615)) || (get<4>(environment_8[local_6]) != uint64_t(2))) {
                  procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
                } else {
                  local_5 = get<2>(environment_8[local_6]);
                  if ((local_1 != get<6>(environment_9[local_5])) || (get<0>(environment_0[uint64_t(18)]) == uint64_t(0))) {
                    procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
                  } else {
                    procedure_30(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, local_5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
                    if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
                      if ((get<0>(environment_0[uint64_t(18)]) == uint64_t(0))) {
                        procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
                      } else {
                        procedure_15(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<0>(environment_0[uint64_t(0)]));
                      }
                    } else {
                    }
                  }
                }
              } else {
              }
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(25)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_9(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
              environment_0[uint64_t(8)] = { uint64_t(1) };
            } else {
            }
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_11(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0);
              if ((get<0>(environment_0[uint64_t(0)]) == uint64_t(18446744073709551615))) {
                procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
              } else {
                if ((get<4>(environment_8[get<0>(environment_0[uint64_t(0)])]) == uint64_t(0))) {
                  for (uint8_t binder_0 : { 67, 76, 65, 83, 83, 10 }) {
                    writeChar(binder_0);
                  }
                } else {
                }
                if ((get<4>(environment_8[get<0>(environment_0[uint64_t(0)])]) == uint64_t(1))) {
                  for (uint8_t binder_0 : { 84, 72, 69, 79, 82, 69, 77, 10 }) {
                    writeChar(binder_0);
                  }
                } else {
                }
                if ((get<4>(environment_8[get<0>(environment_0[uint64_t(0)])]) == uint64_t(2))) {
                  for (uint8_t binder_0 : { 83, 67, 72, 69, 77, 65, 10 }) {
                    writeChar(binder_0);
                  }
                } else {
                }
                flushSTDOUT();
              }
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
      if ((local_0 == uint64_t(26)) && (get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
        if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
          if (true) {
            procedure_9(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
            if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
              environment_0[uint64_t(8)] = { uint64_t(1) };
            } else {
            }
            if ((get<0>(environment_0[uint64_t(8)]) == uint64_t(0))) {
              procedure_11(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0);
              if ((get<0>(environment_0[uint64_t(0)]) == uint64_t(18446744073709551615))) {
                procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
              } else {
                if ((get<4>(environment_8[get<0>(environment_0[uint64_t(0)])]) != uint64_t(2))) {
                  procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
                } else {
                  procedure_12(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, get<6>(environment_9[get<2>(environment_8[get<0>(environment_0[uint64_t(0)])])]));
                }
              }
            } else {
            }
          } else {
            procedure_13(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
          }
        } else {
        }
      } else {
      }
    }
    if ((get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
      for (uint8_t binder_0 : { 69, 82, 82, 10 }) {
        writeChar(binder_0);
      }
      flushSTDOUT();
      environment_0[uint64_t(9)] = { uint64_t(1) };
    } else {
    }
  };
  auto procedure_32 = [&](std::tuple<uint64_t> *environment_0, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t> *environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>& environment_4, std::vector<std::tuple<uint64_t, uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t>>& environment_7, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_8, std::vector<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t>>& environment_9, std::vector<std::tuple<uint64_t>>& environment_10, std::vector<std::tuple<uint8_t>>& environment_11, std::vector<std::tuple<uint64_t>>& environment_12, std::vector<std::tuple<uint8_t>>& environment_13, std::tuple<uint8_t> *environment_14, std::tuple<uint8_t> *environment_15) {
    for (uint8_t binder_0 : { 83, 69, 69, 68, 10 }) {
      writeChar(binder_0);
    }
    flushSTDOUT();
    procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
    if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
      environment_0[uint64_t(8)] = { uint64_t(1) };
    } else {
      environment_0[uint64_t(26)] = { get<0>(environment_0[uint64_t(11)]) };
      procedure_10(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0);
      if ((get<0>(environment_0[uint64_t(14)]) == uint64_t(0))) {
        environment_0[uint64_t(8)] = { uint64_t(1) };
      } else {
        environment_0[uint64_t(27)] = { get<0>(environment_0[uint64_t(11)]) };
      }
    }
    if ((get<0>(environment_0[uint64_t(8)]) != uint64_t(0))) {
      for (uint8_t binder_0 : { 69, 82, 82, 10 }) {
        writeChar(binder_0);
      }
      flushSTDOUT();
    } else {
      environment_0[uint64_t(20)] = { uint64_t(1024) };
      procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, uint64_t(0), uint64_t(0), uint64_t(0), 0, 0, 0);
      for (uint8_t binder_0 : { 82, 69, 65, 68, 89, 10 }) {
        writeChar(binder_0);
      }
      flushSTDOUT();
      for (uint64_t tape_byte_0; (tape_byte_0 = readChar()) != UINT64_MAX;) {
        const uint8_t binder_0 = static_cast<uint8_t>(tape_byte_0);
        environment_0[uint64_t(15)] = { (uint64_t(binder_0) + uint64_t(1)) };
        procedure_31(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15, 0, 0, 0, 0, 0, 0, 0);
        if ((get<0>(environment_0[uint64_t(9)]) != uint64_t(0))) {
          break;
        } else {
        }
      }
    }
  };
  procedure_32(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, environment_12, environment_13, environment_14, environment_15);
}
