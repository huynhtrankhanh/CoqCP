import { transformer } from './exampleCode'
import { cppCodegen } from './cppCodegen'

describe('cppCodegen function', () => {
  it('should produce correct C++ code', () => {
    const ast = transformer.transform()
    const cppCode = cppCodegen([ast])
    console.log(cppCode)
    expect(cppCode).toEqual(`#include <iostream>
#include <tuple>
#include <cstdlib>
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
std::tuple<uint32_t> environment_0[100];
std::tuple<uint8_t, uint64_t> environment_1[3];
std::tuple<bool> environment_2[0];

int main() {
  std::cin.tie(0)->sync_with_stdio(0);
  auto procedure_0 = [&](uint32_t local_0) {
    writeChar(uint8_t(local_0));
  };
  auto procedure_1 = [&](uint8_t local_0, uint8_t local_1, uint8_t local_2) {
  };
  auto procedure_2 = [&](uint32_t local_0, uint32_t local_1, uint32_t local_2, uint32_t local_3) {
    local_0 = readChar();
    local_1 = uint64_t(0);
    local_2 = uint64_t(1);
    environment_0[uint64_t(0)] = { local_1 };
    environment_0[uint64_t(1)] = { local_2 };
    for (uint64_t binder_0 = 0; binder_0 < (uint64_t(local_0) - uint64_t(2)); binder_0++) {
      local_3 = (get<0>(environment_0[binder_0]) + get<0>(environment_0[(binder_0 + uint64_t(1))]));
      environment_0[(binder_0 + uint64_t(2))] = { local_3 };
      break;
      continue;
      flushSTDOUT();
    }
    for (uint8_t binder_0 : { 104, 101, 108, 108, 111, 32, 108, 105, 102, 101 }) {
      writeChar(binder_0);
    }
    (uint64_t(2) / uint64_t(3));
    (toSigned(uint64_t(1)) / toSigned(uint64_t(2)));
    binaryOp([&]() { return readChar(); }, [&]() { return uint8_t(uint64_t(3)); }, [&](auto a, auto b) { return a / b; });
    binaryOp([&]() { return toSigned(readChar()); }, [&]() { return toSigned(readChar()); }, [&](auto a, auto b) { return a / b; });
    procedure_0(uint64_t(100));
    procedure_0(0);
    ([&]() {auto workaround_0 = readChar(); auto workaround_1 = 0; auto workaround_2 = readChar(); procedure_1(workaround_0, workaround_1, workaround_2);})();
    procedure_1(uint8_t(uint64_t(0)), 0, uint8_t(uint64_t(0)));
    if ((local_0 == uint64_t(100))) {
      writeChar(uint64_t(32));
    }
    if ((local_0 < uint64_t(200)) || true && (!false)) {
      writeChar(uint64_t(100));
    }
    if (binaryOp([&]() { return binaryOp([&]() { return readChar(); }, [&]() { return readChar(); }, [&](auto a, auto b) { return a + b; }); }, [&]() { return uint8_t(uint64_t(3)); }, [&](auto a, auto b) { return a < b; }) && binaryOp([&]() { return toSigned(readChar()); }, [&]() { return toSigned(readChar()); }, [&](auto a, auto b) { return a < b; })) {
    }
  };
  procedure_2(0, 0, 0, 0);
}`)
  })
})
