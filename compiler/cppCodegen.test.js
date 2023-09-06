import { CoqCPASTTransformer } from './parse'
import { cppCodegen } from './cppCodegen' // replace with actual path to module

const code = `environment({
    fibSeq: array([int32], 100),  // Memory to hold Fibonacci sequence up to the 100th term
    anotherArray: array([int8, int64], 3) // Example of an array where each element can hold multiple values
});

procedure("pointless", { preset: int32 }, () => {
    writeInt8(coerceInt8(get("preset")))
})

procedure("fibonacci", { n: int32, a: int32, b: int32, i: int32 }, () => {
    set("n", readInt8());  // Reading the term 'n' to which Fibonacci sequence is to be calculated
    set("a", 0);
    set("b", 1);
    
    // Initialize first two numbers in fibonacci series
    store("fibSeq", 0, [get("a")]);
    store("fibSeq", 1, [get("b")]);

    range(get("n") - 2, x => {  
        set("i", retrieve("fibSeq", x)[0] + retrieve("fibSeq", x + 1)[0]);  // Getting sum of last two fibonacci numbers
        store("fibSeq", x + 2, [get("i")]);  // Storing the newly calculated fibonacci term
    })

    call("pointless", { preset: 100 })
    call("pointless", {})

    if (get("n") == 100) {
      writeInt8(32);
    } else {writeInt8(64);}

    if (less(get("n"), 200)) {
      writeInt8(100);
    }
});`

const transformer = new CoqCPASTTransformer(code)

describe('cppCodegen function', () => {
  it('should produce correct C++ code', () => {
    const ast = transformer.transform()
    const cppCode = cppCodegen(ast)
    console.log(cppCode)
    expect(cppCode).toEqual(`#include <iostream>
#include <tuple>
int8_t toSigned(uint8_t x) { return x; }
int16_t toSigned(uint16_t x) { return x; }
int32_t toSigned(uint32_t x) { return x; }
int64_t toSigned(uint64_t x) { return x; }
std::tuple<uint32_t> environment_0[100];
std::tuple<uint8_t, uint64_t> environment_1[3];

int main() {
  auto procedure_0 = [&](uint32_t local_0) {
    writeInt8(uint8_t(local_0));
  };
  auto procedure_1 = [&](uint32_t local_0, uint32_t local_1, uint32_t local_2, uint32_t local_3) {
    local_0 = readInt8();
    local_1 = uint64_t(0);
    local_2 = uint64_t(1);
    environment_0[uint64_t(0)] = { local_1 };
    environment_0[uint64_t(1)] = { local_2 };
    for (uint64_t binder_0 = 0; binder_0 < (local_0 - uint64_t(2)); binder_0++) {
      local_3 = (get<0>(environment_0[binder_0]) + get<0>(environment_0[(binder_0 + uint64_t(1))]));

      environment_0[(binder_0 + uint64_t(2))] = { local_3 };

    }
    procedure_0(uint64_t(100));
    procedure_0(0);
    if ((local_0 == uint64_t(100))) {
      writeInt8(uint64_t(32));
    }
    if ((local_0 < uint64_t(200))) {
      writeInt8(uint64_t(100));
    }
  };
}`)
  })
})
