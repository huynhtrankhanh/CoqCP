import { CoqCPASTTransformer } from './parse'
import { cppCodegen } from './cppCodegen' // replace with actual path to module

const code = `environment({
    fibSeq: array([int32], 100),  // Memory to hold Fibonacci sequence up to the 100th term
    anotherArray: array([int8, int64], 3), // Example of an array where each element can hold multiple values
    visited: array([bool], 0)
});

procedure("pointless", { preset: int32 }, () => {
    writeChar(coerceInt8(get("preset")))
})

procedure("more", { a: int8, b: int8, c: int8 }, () => {})

procedure("fibonacci", { n: int32, a: int32, b: int32, i: int32 }, () => {
    set("n", readChar());  // Reading the term 'n' to which Fibonacci sequence is to be calculated
    set("a", 0);
    set("b", 1);
    
    // Initialize first two numbers in fibonacci series
    store("fibSeq", 0, [get("a")]);
    store("fibSeq", 1, [get("b")]);

    range(get("n") - 2, x => {  
        set("i", retrieve("fibSeq", x)[0] + retrieve("fibSeq", x + 1)[0]);  // Getting sum of last two fibonacci numbers
        store("fibSeq", x + 2, [get("i")]);  // Storing the newly calculated fibonacci term
        "break"
        "continue"
        "flush"
    })

    divide(2, 3)
    sDivide(1, 2)

    divide(readChar(), coerceInt8(3))
    sDivide(readChar(), readChar())

    call("pointless", { preset: 100 })
    call("pointless", {})

    call("more", { a: readChar(), c: readChar() })
    call("more", { a: coerceInt8(0), c: coerceInt8(0) })

    if (get("n") == 100) {
      writeChar(32);
    } else {writeChar(64);}

    if (less(get("n"), 200) || true && !false) {
      writeChar(100);
    }

    if (less(readChar() + readChar(), coerceInt8(3)) && sLess(readChar(), readChar())) {}
});`

const transformer = new CoqCPASTTransformer(code)

describe('cppCodegen function', () => {
  it('should produce correct C++ code', () => {
    const ast = transformer.transform()
    const cppCode = cppCodegen(ast)
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

inline uint8_t readChar() { // like getchar()
  static char buf[1 << 16];
  static size_t bc, be;
  if (bc >= be) {
    buf[0] = 0, bc = 0;
    be = fread(buf, 1, sizeof(buf), stdin);
  }
  return buf[bc++]; // returns 0 on EOF
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
    for (uint64_t binder_0 = 0; binder_0 < (local_0 - uint64_t(2)); binder_0++) {
      local_3 = (get<0>(environment_0[binder_0]) + get<0>(environment_0[(binder_0 + uint64_t(1))]));
      environment_0[(binder_0 + uint64_t(2))] = { local_3 };
      break;
      continue;
      flushSTDOUT();
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
}`)
  })
})
