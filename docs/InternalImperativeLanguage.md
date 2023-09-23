# Internal imperative language

The CoqCP project now includes a compiler. The compiler compiles an internal imperative language to both Coq and C++.

To work on the compiler, you will need to have Node.js installed. After that, switch to the `compiler` directory, and run `npm` to install the dependencies.

Then, you will need to run the `tsc` compiler in watch mode. To do this, run `npx tsc -w -p .`. The `tsc` compiler now monitors all changes to the TypeScript files and produces the corresponding files in the `dist` subdirectory.

The internal imperative language steals JavaScript syntax and interprets the parsed AST differently. As JavaScript syntax is stolen, the internal language is subject to every single JavaScript syntactic rule, including automatic semicolon insertion.

A source file consists of 0 or 1 `environment` block and any number of `procedure` blocks.

The `environment` block can be placed at the top, at the bottom or between procedures.

Here is an example of an `environment` block.

```js
environment({
    fibSeq: array([int32], 100),
    anotherArray: array([int8, int64], 3)
})
```

In the above example, we declare two arrays `fibSeq` and `anotherArray`. `fibSeq` is an array of 100 elements, each element has a type of `[int32]`. `anotherArray` is an array of 3 elements, each element has a type of `[int8, int64]`.

The permitted primitive types are `int8`, `int16`, `int32`, `int64` and `bool`.
