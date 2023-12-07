import { CoqCPASTTransformer } from './parse'

export const code = `environment({
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

    range(coerceInt64(get("n")) - 2, x => {  
        set("i", retrieve("fibSeq", x)[0] + retrieve("fibSeq", x + 1)[0]);  // Getting sum of last two fibonacci numbers
        store("fibSeq", x + 2, [get("i")]);  // Storing the newly calculated fibonacci term
        "break"
        "continue"
        "flush"
    })

    range("hello life", x => { writeChar(x) })

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

export const transformer = new CoqCPASTTransformer(code)
