import { CoqCPASTTransformer } from './parse'

const code = `environment({
    fibSeq: array([int32], 100),  // Memory to hold Fibonacci sequence up to the 100th term
    anotherArray: array([int8, int64], 3) // Example of an array where each element can hold multiple values
});

procedure("fibonacci", { n: int32, a: int32, b: int32, i: int32 }, () => {
    set("n", readChar());  // Reading the term 'n' to which Fibonacci sequence is to be calculated
    set("a", coerceInt32(0));
    set("b", coerceInt32(1));
    
    // Initialize first two numbers in fibonacci series
    store("fibSeq", 0, [get("a")]);
    store("fibSeq", 1, [get("b")]);

    range(coerceInt64(get("n")) - 2, x => {  
        set("i", retrieve("fibSeq", x)[0] + retrieve("fibSeq", x + 1)[0]);  // Getting sum of last two fibonacci numbers
        store("fibSeq", x + 2, [get("i")]);  // Storing the newly calculated fibonacci term
    })

    if (get("n") == coerceInt32(100)) {
      writeChar(32);
    } else {writeChar(64);}

    if (less(get("n"), coerceInt32(200))) {
      writeChar(100);
    }
});`
const transformer = new CoqCPASTTransformer(code)
console.log(
  JSON.stringify(
    transformer.transform(),
    function replacer(key, value) {
      if (value instanceof Map) {
        // Handle Map types
        return {
          dataType: 'Map',
          value: Array.from(value.entries()), // converting Map to a nested Array
        }
      } else {
        return value
      }
    },
    4
  )
)
