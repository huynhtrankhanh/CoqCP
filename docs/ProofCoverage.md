# Proof coverage

`theories/KnapsackCode2.v` proves `extractAnswerEq` for the generated competitive Knapsack program. The proof covers decimal input, array growth and initialization, loading items, every dynamic-programming cell, and decimal output with a final newline. It assumes the allocated table size and total item value fit unsigned 64-bit arithmetic, and each weight and value fits unsigned 32-bit arithmetic. The theorem ends in `Qed`; there are no admitted lemmas in its dependency chain. `Print Assumptions extractAnswerEq` reports functional extensionality.

`theories/ArrayGrowth.v` proves length, preservation of existing elements, zero initialization, no shrinking, and execution of translated growth for the Coq runtime. The compiler performs a fixed-point analysis over growth calls and cross-module array mappings to select vector storage consistently for aliases.

`theories/DisjointSetUnionCode.v` and `DisjointSetUnionCode2.v` preserve the ancestor, path-compression, and union proofs. `competitiveMergeRefinesModel` proves that the generated library's merge operation refines the mathematical DSU state. `DisjointSetUnionCode3.v` proves the cumulative merge-score bound. The competitive DSU input/output frontend has executable checks, but no end-to-end theorem.

The other generated examples have compile-and-run checks. The TypeScript parser, validation, growth analysis, and C++ emitter are tested; they are not themselves formally verified compiler passes. The proofs establish properties of generated Coq actions. They do not prove equivalence of arbitrary emitted C++ programs to those actions or model C++ allocation failure.

To check the compiler and regenerate examples:

```sh
npm --prefix compiler ci
npm --prefix compiler run build
npm --prefix compiler run typecheck
npm --prefix compiler test
node compiler/dist/cli '?json' programs/Knapsack.module.json
```

With Coq 8.20.1 and stdpp 1.11.0 installed:

```sh
coq_makefile -f _CoqProject -o Makefile
make -j2
coqchk -silent -R theories CoqCP -R generated-coq Generated CoqCP.KnapsackCode2 CoqCP.ArrayGrowth CoqCP.DisjointSetUnionCode3
```

The project maps `theories/` to `CoqCP`, `generated-coq/` to `Generated`, and `programs/llmGeneratedCode/` to `GeneratedExamples`.

The checked-in HTML pages for the migrated imperative runtime and generated-program proofs were refreshed with `coqdoc` from the current sources.
