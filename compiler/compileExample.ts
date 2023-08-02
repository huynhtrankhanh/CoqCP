import { CoqCPASTTransformer } from './compile'

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
console.log(JSON.stringify(transformer.transform(), null, 4))
