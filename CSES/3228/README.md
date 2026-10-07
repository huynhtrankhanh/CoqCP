# CSES 3228 — Permuted Binary Strings

[Problem statement](https://cses.fi/problemset/task/3228).
The grader permutes each queried binary string by a hidden permutation of
`1..n`. Recover the permutation using at most ten queries, with `n <= 1000`.

## Algorithm

For each `k = 0..9`, query the `k`-th binary digit of each zero-based index:

```text
query[i] = ((i-1) / 2^k) % 2       (1 <= i <= n)
```

The returned character at position `j` is therefore the `k`-th digit of
`a[j]-1`. Start every answer at zero and add `2^k` when the response digit is
one. After all ten queries, add one to each answer and print the permutation.
Every query and the final answer ends with a newline and an explicit flush.
The bit reader handles response separators without parsing a whole binary
string as an integer.

This uses exactly **10 queries**, `O(10n)` time, and a fixed array of 1000
unsigned integers. It also handles `n = 1`.

## Correctness and formal coverage

After `k` rounds, an answer for zero-based hidden value `x` equals
`x mod 2^k`. The next response contributes
`((x / 2^k) mod 2) * 2^k`, making the answer `x mod 2^(k+1)`.
Since every hidden value satisfies `0 <= x < 1000 < 1024`, ten rounds recover
`x` exactly. Adding one restores the statement's one-based values.

- `PermutedBinaryStrings.js`: CoqCP source and interactive protocol.
- `PermutedBinaryStrings.module.json`: compiler configuration.
- `../../generated-cpp/PermutedBinaryStrings.cpp`: standalone C++20 submission.
- `../../generated-coq/PermutedBinaryStrings.v`: generated Coq actions.
- `../../verification/permuted-binary-strings/candidate/PermutedBinaryStrings.v`: response-based executable solver
  and correctness proofs. `interaction_correct` feeds the solver replies formed
  by indexing the actual query lists as specified by the grader and proves that
  the output equals the hidden permutation. `solve_correct` additionally proves
  query length, binary digits, and the ten-query bound.
- `../../verification/permuted-binary-strings/candidate/PermutedBinaryStringsCode.v`: proofs of the complete generated
  `queryBit` and `recordBit` procedure bodies. `generated_query_bit` proves the
  exact ASCII byte emitted for each query position. `generated_decode_step`
  proves that the generated array update implements the reconstruction invariant,
  including array bounds and unsigned arithmetic without wraparound.
- `test_interactive.py`: pipe-based grader checking the complete executable's
  query trace, flushes, responses, answer, and termination.

`../../verification/permuted-binary-strings/candidate/PermutedBinaryStringsEndToEnd.v` proves
`generated_end_to_end` for the actual generated `main`, initialized with the
actual generated arrays. For every valid permutation it proves successful
execution, the exact ten query lines and final answer line, complete input
consumption, and exactly eleven flushes. Every query flush occurs before its
reply is read; the final flush contains the full permutation and no unread
input. This includes the numeric reader, bit reader, loop composition,
initialization, memory bounds, unsigned arithmetic, and repeated decimal printing.

The single input/output specification is
`../../verification/permuted-binary-strings/spec/Spec.v`. It binds the certificate
to the generated entry point and requires this full execution contract.
`candidate/PermutedBinaryStringsProtocol.v` proves the truthful-reply lemma.
The reusable
framework change and the gap it closes are documented in
[End-to-end verification](../../docs/EndToEndVerification.md).

The mathematical and generated bit-procedure proofs have no axioms. The full
execution proof uses functional extensionality and has no admitted obligations.
The formal protocol uses decimal `n` followed by LF and truthful binary reply
lines followed by LF. The local grader additionally tests CRLF and fragmented
responses, every permutation through size 6, randomized cases, power-of-two
boundaries, and maximum-size cases. The proof is about generated Coq actions;
the TypeScript compiler and native C++ runtime remain outside the formal proof.

## Build and check

With the repository's pinned Rocq toolchain on `PATH`:

```sh
npm --prefix compiler run build
node compiler/dist/cli '?json' CSES/3228/PermutedBinaryStrings.module.json
g++ -std=c++20 -O2 generated-cpp/PermutedBinaryStrings.cpp -o /tmp/cses3228
python3 CSES/3228/test_interactive.py --binary /tmp/cses3228
rocq makefile -f _CoqProject -o Makefile
make -j2
make validate
python3 tools/adversarial/examples.py --only permuted-binary-strings \
  --output .verification/permuted-binary-strings-review
```
