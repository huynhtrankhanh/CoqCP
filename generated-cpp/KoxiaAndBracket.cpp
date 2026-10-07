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
std::vector<std::tuple<uint8_t>> environment_0(0);
std::vector<std::tuple<uint64_t>> environment_1(0);
std::vector<std::tuple<uint64_t>> environment_2(0);
std::vector<std::tuple<uint64_t>> environment_3(0);
std::vector<std::tuple<uint64_t>> environment_4(0);
std::vector<std::tuple<uint64_t>> environment_5(0);
std::vector<std::tuple<uint64_t>> environment_6(0);
std::vector<std::tuple<uint64_t>> environment_7(0);
std::vector<std::tuple<uint64_t>> environment_8(0);
std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t> environment_9[32];
std::tuple<uint64_t> environment_10[3];
std::tuple<uint8_t> environment_11[20];
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
  auto procedure_2 = [&](std::vector<std::tuple<uint8_t>>& environment_0, std::vector<std::tuple<uint64_t>>& environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t>>& environment_4, std::vector<std::tuple<uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t>>& environment_7, std::vector<std::tuple<uint64_t>>& environment_8, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t> *environment_9, std::tuple<uint64_t> *environment_10, std::tuple<uint8_t> *environment_11, uint64_t local_0, uint64_t local_1, uint64_t local_2) {
    local_2 = uint64_t(1);
    for (uint64_t binder_0 = 0, loop_end = uint64_t(64); binder_0 < loop_end; binder_0++) {
      if ((local_1 == uint64_t(0))) {
        break;
      } else {
      }
      if (((local_1 % uint64_t(2)) == uint64_t(1))) {
        local_2 = ((local_2 * local_0) % uint64_t(998244353));
      } else {
      }
      local_0 = ((local_0 * local_0) % uint64_t(998244353));
      local_1 = (local_1 / uint64_t(2));
    }
    environment_10[uint64_t(2)] = { local_2 };
  };
  auto procedure_3 = [&](std::vector<std::tuple<uint8_t>>& environment_0, std::vector<std::tuple<uint64_t>>& environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t>>& environment_4, std::vector<std::tuple<uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t>>& environment_7, std::vector<std::tuple<uint64_t>>& environment_8, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t> *environment_9, std::tuple<uint64_t> *environment_10, std::tuple<uint8_t> *environment_11, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6, uint64_t local_7) {
    for (uint64_t binder_0 = 0, loop_end = local_0; binder_0 < loop_end; binder_0++) {
      if ((binder_0 < local_1)) {
        local_3 = get<0>(environment_5[binder_0]);
        environment_5[binder_0] = { get<0>(environment_5[local_1]) };
        environment_5[local_1] = { local_3 };
      } else {
      }
      local_2 = (local_0 / uint64_t(2));
      for (uint64_t binder_1 = 0, loop_end = uint64_t(21); binder_1 < loop_end; binder_1++) {
        if ((local_2 == uint64_t(0)) || (local_1 < local_2)) {
          break;
        } else {
        }
        local_1 = (local_1 - local_2);
        local_2 = (local_2 / uint64_t(2));
      }
      local_1 = (local_1 + local_2);
    }
    local_4 = uint64_t(1);
    for (uint64_t binder_0 = 0, loop_end = uint64_t(20); binder_0 < loop_end; binder_0++) {
      if ((!(local_4 < local_0))) {
        break;
      } else {
      }
      for (uint64_t binder_1 = 0, loop_end = (local_0 / (uint64_t(2) * local_4)); binder_1 < loop_end; binder_1++) {
        local_7 = ((binder_1 * uint64_t(2)) * local_4);
        for (uint64_t binder_2 = 0, loop_end = local_4; binder_2 < loop_end; binder_2++) {
          local_5 = get<0>(environment_5[(local_7 + binder_2)]);
          local_6 = ((get<0>(environment_4[(local_4 + binder_2)]) * get<0>(environment_5[((local_7 + binder_2) + local_4)])) % uint64_t(998244353));
          environment_5[(local_7 + binder_2)] = { ((local_5 + local_6) % uint64_t(998244353)) };
          environment_5[((local_7 + binder_2) + local_4)] = { (((local_5 + uint64_t(998244353)) - local_6) % uint64_t(998244353)) };
        }
      }
      local_4 = (local_4 * uint64_t(2));
    }
  };
  auto procedure_4 = [&](std::vector<std::tuple<uint8_t>>& environment_0, std::vector<std::tuple<uint64_t>>& environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t>>& environment_4, std::vector<std::tuple<uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t>>& environment_7, std::vector<std::tuple<uint64_t>>& environment_8, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t> *environment_9, std::tuple<uint64_t> *environment_10, std::tuple<uint8_t> *environment_11, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6, uint64_t local_7) {
    local_4 = ((local_1 - local_0) + local_2);
    local_5 = uint64_t(1);
    for (uint64_t binder_0 = 0, loop_end = uint64_t(20); binder_0 < loop_end; binder_0++) {
      if ((!(local_5 < local_4))) {
        break;
      } else {
      }
      local_5 = (local_5 * uint64_t(2));
    }
    for (uint64_t binder_0 = 0, loop_end = local_5; binder_0 < loop_end; binder_0++) {
      environment_5[binder_0] = { uint64_t(0) };
      if ((binder_0 < (local_1 - local_0))) {
        environment_5[binder_0] = { get<0>(environment_7[(local_0 + binder_0)]) };
      } else {
      }
    }
    procedure_3(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, local_5, 0, 0, 0, 0, 0, 0, 0);
    for (uint64_t binder_0 = 0, loop_end = local_5; binder_0 < loop_end; binder_0++) {
      environment_6[binder_0] = { get<0>(environment_5[binder_0]) };
      environment_5[binder_0] = { uint64_t(0) };
      if ((binder_0 < (local_2 + uint64_t(1)))) {
        environment_5[binder_0] = { ((((get<0>(environment_2[local_2]) * get<0>(environment_3[binder_0])) % uint64_t(998244353)) * get<0>(environment_3[(local_2 - binder_0)])) % uint64_t(998244353)) };
      } else {
      }
    }
    procedure_3(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, local_5, 0, 0, 0, 0, 0, 0, 0);
    procedure_2(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, local_5, uint64_t(998244351), 0);
    local_6 = get<0>(environment_10[uint64_t(2)]);
    for (uint64_t binder_0 = 0, loop_end = local_5; binder_0 < loop_end; binder_0++) {
      environment_5[binder_0] = { ((((get<0>(environment_5[binder_0]) * get<0>(environment_6[binder_0])) % uint64_t(998244353)) * local_6) % uint64_t(998244353)) };
    }
    for (uint64_t binder_0 = 0, loop_end = ((local_5 - uint64_t(1)) / uint64_t(2)); binder_0 < loop_end; binder_0++) {
      local_7 = get<0>(environment_5[(binder_0 + uint64_t(1))]);
      environment_5[(binder_0 + uint64_t(1))] = { get<0>(environment_5[((local_5 - binder_0) - uint64_t(1))]) };
      environment_5[((local_5 - binder_0) - uint64_t(1))] = { local_7 };
    }
    procedure_3(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, local_5, 0, 0, 0, 0, 0, 0, 0);
    for (uint64_t binder_0 = 0, loop_end = local_4; binder_0 < loop_end; binder_0++) {
      environment_8[(local_3 + binder_0)] = { get<0>(environment_5[binder_0]) };
    }
  };
  auto procedure_5 = [&](std::vector<std::tuple<uint8_t>>& environment_0, std::vector<std::tuple<uint64_t>>& environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t>>& environment_4, std::vector<std::tuple<uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t>>& environment_7, std::vector<std::tuple<uint64_t>>& environment_8, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t> *environment_9, std::tuple<uint64_t> *environment_10, std::tuple<uint8_t> *environment_11, uint64_t local_0, uint64_t local_1, bool local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6, uint64_t local_7, uint64_t local_8, uint64_t local_9, uint64_t local_10, uint64_t local_11, uint64_t local_12, uint64_t local_13, uint64_t local_14, uint64_t local_15, uint64_t local_16, uint64_t local_17, uint64_t local_18, uint64_t local_19, uint64_t local_20, uint64_t local_21, uint64_t local_22) {
    environment_1[uint64_t(0)] = { uint64_t(0) };
    for (uint64_t binder_0 = 0, loop_end = (local_1 - local_0); binder_0 < loop_end; binder_0++) {
      if (local_2) {
        local_22 = (uint64_t(get<0>(environment_0[((local_1 - binder_0) - uint64_t(1))])) ^ uint64_t(1));
      } else {
        local_22 = uint64_t(get<0>(environment_0[(local_0 + binder_0)]));
      }
      if ((local_22 == uint64_t(40))) {
        local_3 = (local_3 + uint64_t(1));
      } else {
        local_3 = (local_3 - uint64_t(1));
        local_18 = uint64_t(0);
        if ((toSigned(local_3) < toSigned(local_4))) {
          local_4 = local_3;
          local_18 = uint64_t(1);
        } else {
        }
        environment_1[(local_5 + uint64_t(1))] = { (get<0>(environment_1[local_5]) + local_18) };
        local_5 = (local_5 + uint64_t(1));
      }
    }
    environment_7[uint64_t(0)] = { uint64_t(1) };
    local_8 = uint64_t(1);
    environment_9[uint64_t(0)] = { uint64_t(0), local_5, uint64_t(0), uint64_t(0), uint64_t(0) };
    for (uint64_t binder_0 = 0, loop_end = ((uint64_t(4) * local_5) + uint64_t(1)); binder_0 < loop_end; binder_0++) {
      local_9 = get<0>(environment_9[local_6]);
      local_10 = get<1>(environment_9[local_6]);
      local_11 = get<2>(environment_9[local_6]);
      local_12 = get<3>(environment_9[local_6]);
      local_13 = get<4>(environment_9[local_6]);
      local_14 = ((local_9 + local_10) / uint64_t(2));
      if ((local_11 == uint64_t(0))) {
        if (((local_10 - local_9) < uint64_t(33))) {
          for (uint64_t binder_1 = 0, loop_end = (local_10 - local_9); binder_1 < loop_end; binder_1++) {
            local_18 = (get<0>(environment_1[((local_9 + binder_1) + uint64_t(1))]) - get<0>(environment_1[(local_9 + binder_1)]));
            local_20 = uint64_t(0);
            if ((local_18 == uint64_t(0))) {
              for (uint64_t binder_2 = 0, loop_end = local_8; binder_2 < loop_end; binder_2++) {
                local_19 = get<0>(environment_7[binder_2]);
                environment_7[binder_2] = { ((local_19 + local_20) % uint64_t(998244353)) };
                local_20 = local_19;
              }
              environment_7[local_8] = { local_20 };
              local_8 = (local_8 + uint64_t(1));
            } else {
              for (uint64_t binder_2 = 0, loop_end = local_8; binder_2 < loop_end; binder_2++) {
                local_19 = uint64_t(0);
                if (((binder_2 + uint64_t(1)) < local_8)) {
                  local_19 = get<0>(environment_7[(binder_2 + uint64_t(1))]);
                } else {
                }
                environment_7[binder_2] = { ((get<0>(environment_7[binder_2]) + local_19) % uint64_t(998244353)) };
              }
            }
          }
          if ((local_6 == uint64_t(0))) {
            break;
          } else {
          }
          local_6 = (local_6 - uint64_t(1));
        } else {
          local_15 = (get<0>(environment_1[local_10]) - get<0>(environment_1[local_9]));
          local_16 = local_15;
          if ((local_8 < local_16)) {
            local_16 = local_8;
          } else {
          }
          local_17 = uint64_t(0);
          if ((local_15 < local_8)) {
            local_17 = (((local_8 - local_15) + local_10) - local_9);
            procedure_4(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, local_15, local_8, (local_10 - local_9), local_7, 0, 0, 0, 0);
          } else {
          }
          environment_9[local_6] = { local_9, local_10, uint64_t(1), local_7, local_17 };
          local_7 = (local_7 + local_17);
          local_8 = local_16;
          local_6 = (local_6 + uint64_t(1));
          environment_9[local_6] = { local_9, local_14, uint64_t(0), uint64_t(0), uint64_t(0) };
        }
      } else {
        if ((local_11 == uint64_t(1))) {
          environment_9[local_6] = { local_9, local_10, uint64_t(2), local_12, local_13 };
          local_6 = (local_6 + uint64_t(1));
          environment_9[local_6] = { local_14, local_10, uint64_t(0), uint64_t(0), uint64_t(0) };
        } else {
          local_21 = local_8;
          if ((local_21 < local_13)) {
            local_21 = local_13;
          } else {
          }
          for (uint64_t binder_1 = 0, loop_end = local_21; binder_1 < loop_end; binder_1++) {
            local_19 = uint64_t(0);
            if ((binder_1 < local_8)) {
              local_19 = get<0>(environment_7[binder_1]);
            } else {
            }
            if ((binder_1 < local_13)) {
              local_19 = ((local_19 + get<0>(environment_8[(local_12 + binder_1)])) % uint64_t(998244353));
            } else {
            }
            environment_7[binder_1] = { local_19 };
          }
          local_8 = local_21;
          local_7 = local_12;
          if ((local_6 == uint64_t(0))) {
            break;
          } else {
          }
          local_6 = (local_6 - uint64_t(1));
        }
      }
    }
    environment_10[uint64_t(0)] = { get<0>(environment_7[uint64_t(0)]) };
  };
  auto procedure_6 = [&](std::vector<std::tuple<uint8_t>>& environment_0, std::vector<std::tuple<uint64_t>>& environment_1, std::vector<std::tuple<uint64_t>>& environment_2, std::vector<std::tuple<uint64_t>>& environment_3, std::vector<std::tuple<uint64_t>>& environment_4, std::vector<std::tuple<uint64_t>>& environment_5, std::vector<std::tuple<uint64_t>>& environment_6, std::vector<std::tuple<uint64_t>>& environment_7, std::vector<std::tuple<uint64_t>>& environment_8, std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, uint64_t> *environment_9, std::tuple<uint64_t> *environment_10, std::tuple<uint8_t> *environment_11, uint64_t local_0, uint64_t local_1, uint64_t local_2, uint64_t local_3, uint64_t local_4, uint64_t local_5, uint64_t local_6, uint64_t local_7, uint64_t local_8) {
    growArray(environment_0, uint64_t(500000));
    for (uint64_t binder_0 = 0, loop_end = uint64_t(500001); binder_0 < loop_end; binder_0++) {
      local_1 = readChar();
      if ((local_1 != uint64_t(40)) && (local_1 != uint64_t(41))) {
        break;
      } else {
      }
      environment_0[local_0] = { uint8_t(local_1) };
      local_0 = (local_0 + uint64_t(1));
      if ((local_1 == uint64_t(40))) {
        local_2 = (local_2 + uint64_t(1));
      } else {
        local_2 = (local_2 - uint64_t(1));
      }
      if ((toSigned(local_2) < toSigned(local_3))) {
        local_3 = local_2;
        local_4 = local_0;
      } else {
      }
    }
    growArray(environment_1, (local_0 + uint64_t(1)));
    growArray(environment_2, (local_0 + uint64_t(1)));
    growArray(environment_3, (local_0 + uint64_t(1)));
    growArray(environment_7, ((uint64_t(2) * local_0) + uint64_t(64)));
    growArray(environment_8, ((uint64_t(4) * local_0) + uint64_t(128)));
    local_5 = uint64_t(1);
    for (uint64_t binder_0 = 0, loop_end = uint64_t(20); binder_0 < loop_end; binder_0++) {
      if ((!(local_5 < ((uint64_t(2) * local_0) + uint64_t(1))))) {
        break;
      } else {
      }
      local_5 = (local_5 * uint64_t(2));
    }
    growArray(environment_5, local_5);
    growArray(environment_6, local_5);
    growArray(environment_4, local_5);
    local_6 = uint64_t(1);
    for (uint64_t binder_0 = 0, loop_end = uint64_t(20); binder_0 < loop_end; binder_0++) {
      if ((!(local_6 < local_5))) {
        break;
      } else {
      }
      procedure_2(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, uint64_t(3), (uint64_t(998244352) / (uint64_t(2) * local_6)), 0);
      local_7 = get<0>(environment_10[uint64_t(2)]);
      environment_4[local_6] = { uint64_t(1) };
      for (uint64_t binder_1 = 0, loop_end = (local_6 - uint64_t(1)); binder_1 < loop_end; binder_1++) {
        environment_4[((local_6 + binder_1) + uint64_t(1))] = { ((get<0>(environment_4[(local_6 + binder_1)]) * local_7) % uint64_t(998244353)) };
      }
      local_6 = (local_6 * uint64_t(2));
    }
    environment_2[uint64_t(0)] = { uint64_t(1) };
    for (uint64_t binder_0 = 0, loop_end = local_0; binder_0 < loop_end; binder_0++) {
      environment_2[(binder_0 + uint64_t(1))] = { ((get<0>(environment_2[binder_0]) * (binder_0 + uint64_t(1))) % uint64_t(998244353)) };
    }
    procedure_2(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, get<0>(environment_2[local_0]), uint64_t(998244351), 0);
    environment_3[local_0] = { get<0>(environment_10[uint64_t(2)]) };
    for (uint64_t binder_0 = 0, loop_end = local_0; binder_0 < loop_end; binder_0++) {
      environment_3[((local_0 - binder_0) - uint64_t(1))] = { ((get<0>(environment_3[(local_0 - binder_0)]) * (local_0 - binder_0)) % uint64_t(998244353)) };
    }
    procedure_5(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, uint64_t(0), local_4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    local_8 = get<0>(environment_10[uint64_t(0)]);
    procedure_5(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, local_4, local_0, true, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    local_8 = ((local_8 * get<0>(environment_10[uint64_t(0)])) % uint64_t(998244353));
    procedure_0(environment_11, local_8, 0, 0);
    writeChar(uint8_t(uint64_t(10)));
  };
  procedure_6(environment_0, environment_1, environment_2, environment_3, environment_4, environment_5, environment_6, environment_7, environment_8, environment_9, environment_10, environment_11, 0, 0, 0, 0, 0, 0, 0, 0, 0);
}
