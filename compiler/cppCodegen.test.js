import { CoqCPASTTransformer } from './parse'
import { cppCodegen } from './cppCodegen' // replace with actual path to module

const code = `environment({
    fibSeq: array([int32], 100),  // Memory to hold Fibonacci sequence up to the 100th term
    anotherArray: array([int8, int64], 3) // Example of an array where each element can hold multiple values
});

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

    if (get("n") == 100) {
      writeInt8(32);
    } else {writeInt8(64);}

    if (less(get("n"), 200)) {
      writeInt8(100);
    }
});`

const transformer = new CoqCPASTTransformer(code)

describe('cppCodegen function', () => {
  it('should produce correct C++ include statement', () => {
    const ast = transformer.transform()
    const cppCode = cppCodegen(ast)
    expect(cppCode).toEqual(
      `#include <iostream>
namespace environment {
  std::tuple<uint32_t> fibSeq[100];
  std::tuple<uint8_t, uint64_t> anotherArray[3];
};
int main() {
  auto procedure_fibonacci = [&](uint32_t local_n, uint32_t local_a, uint32_t local_b, uint32_t local_i) {
    local_n = readInt8();
    local_a = 0;
    local_b = 1;
    environment::fibSeq[0] = { local_a };
    environment::fibSeq[1] = { local_b };
    for (uint32 counter_x = 0; counter_x < local_n - 2; counter_x++) {
      local_i = std::get<0>(environment::fibSeq[counter_x])
      environment::fibSeq[counter_x + 2] = { local_i };
    }
    if (local_n == 100) {
      writeInt8(32);
    } else {
      writeInt8(64);
    }
    if (local_n < 200) {
      writeInt8(100);
    }
  };
}`
    )
  })
})
