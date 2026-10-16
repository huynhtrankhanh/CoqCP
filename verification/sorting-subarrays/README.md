# Sorting Subarrays

The solution binary searches the answer in `[-10^9, 10^9]`. For a threshold
`m`, replace each value `x` with the bit `m < x`. Sorting any subarray then
places all its false bits before all its true bits. A lazy segment tree counts
the true bits in the query interval and assigns its false prefix and true
suffix. After all queries, the bit at `K` tells the binary search whether the
answer exceeds `m`. Exactly 31 iterations suffice, including negative values
and duplicates.

Each threshold pass takes `O((N + Q) log(N + 1))` time, including tree
construction, and `O(N + Q)` live storage. The full solver takes
`O((N + Q) log(N + 1) log(2 * 10^9 + 1))` time. This is an analysis of the
algorithm with constant-time machine arithmetic; the theorem establishes
functional correctness rather than instruction costs.

## Formal contract

[`spec/Spec.v`](spec/Spec.v) independently defines each query by splitting the
array and merge sorting the selected interval. It specifies the original
one-based, inclusive indices and all problem bounds. `SOLUTION.correct`
requires the submitted program's answer to equal the element at `K` after
all these reference operations, for every valid input.

All algorithm definitions and proofs are submitted as source under
[`candidate/`](candidate/):

| File | Proof responsibility |
| --- | --- |
| `Bits.v` | Interval assignment and bit-count list laws |
| `Tree.v` | Lazy assignments, cached counts, prefix queries, and construction |
| `Threshold.v` | Thresholding commutes with a reference subarray sort |
| `Simulation.v` | Every query, padding, and final lookup refine the reference |
| `Search.v` | Binary search, including floor division for negative midpoints |
| `Algorithm.v` | The complete mathematical solver |
| `ByteIO.v` | Signed decimal input and byte output |
| `MainIO.v` | Complete byte-stream entry point and successful execution |
| `Candidate.v` | The actual entry point satisfies the frozen end-to-end contract |

The submitted program is the complete `Action BasicEffect` entry point, not
just a function on decoded values. Its frozen contract requires:

```coq
forall a k qs, valid_input a k qs ->
  runIO program (input_bytes a k qs) [] =
    Some (tt, [], output_bytes a k qs).
```

This equality proves successful termination, exact entire stdout, and full
consumption of the canonical decimal input. The input contains the `N K Q`
header, the signed array values, and all one-based inclusive queries, with
spaces within lines and LF line endings. The output is the signed decimal
answer followed by LF. A theorem conditional on execution succeeding cannot
satisfy this contract.

`Algorithm.v` retains the mathematical solver proof. `ByteIO.v` proves the
actual signed decimal reader, checked digit accumulation, delimiters, and byte
writer. `MainIO.v` proves the header checks, loading every value and query,
list construction, query validation, EOF handling, solver call, complete signed
output, and termination. The readers construct lists using tail-recursive
reverse accumulation. `Candidate.v` composes these proofs for the exact entry
point exported by extraction.

The program is written directly in the existing CoqCP `Action` language and
uses its existing `runIO` semantics. It is extracted as a whole, including the
parser and printer. The native [`main.ml`](main.ml) only implements the four
raw byte effects; it has no decimal parser, formatter, or solver. Signed values,
decimal arithmetic, and the 64-bit EOF sentinel use Zarith arbitrary-precision
integers. Counts and indices use machine naturals within the validated bounds.
As with the repository's other execution proofs, extraction, native compilation,
and the raw I/O backend are the trusted deployment chain, not a verified native
compiler theorem.

The standard CI runner accepted this end-to-end contract under the existing
`ci` axiom policy on October 16, 2026. The independent audit reports functional
extensionality from the imported general `Imperative` runtime and no admissions.
The specification ID is
`be01b60424f5cc9555996134cfbc52bcb469312c1e39de0232d190b0d80793b8`.
The report is in
`.verification/sorting-subarrays-e2e-v2-20261016/sorting-subarrays/result/report.json`.

## Build and run

From the repository root, with the existing Rocq project libraries built. The
native build also needs a 64-bit OCaml compiler, `ocamlfind`, and Zarith:

```sh
python3 verification/sorting-subarrays/build.py \
  --output .verification/sorting-native
printf '5 3 2\n4 2 1 3 5\n1 3\n2 4\n' | \
  .verification/sorting-native/sorting-subarrays
```

The executable prints `3` followed by a newline. The build copies the sources
into a fresh output directory, compiles the proofs, extracts the verified
program, and compiles it with `ocamlfind ocamlopt` and Zarith. It leaves the
candidate source only.

## Adversarial validation

Use the same manifest-driven runner as CI, with working Docker/gVisor access:

```sh
export PATH=/opt/rocq/9.3.0/bin:$PATH
python3 tools/adversarial/examples.py --only sorting-subarrays \
  --output .verification/sorting-adversarial
```

The entry in [`adversarial-examples.json`](../adversarial-examples.json) selects
the existing `ci` axiom policy and `full-proof-chain` resource profile.
The runner freezes the specification and independently checks every candidate
library and the final module contract. Each invocation requires a fresh output
directory. CI runs this runner without `--only`, so Sorting Subarrays is included
with all other registered problems.

The existing CI acceptance and containment suite exercises rejection of invalid
certificates. The checker, workflow, policies, project build, and `theories/`
files are unchanged.

The stronger frozen contract also rejected the former algorithm-only
certificate and an always-trapping program with a correctness theorem
conditional on successful execution. Both sources compiled and failed the
independent module-signature check, rather than failing to compile. The reports
are in `.verification/sorting-e2e-rejections-20261016/`.

## Executable validation

```sh
python3 verification/sorting-subarrays/test.py \
  .verification/sorting-native/sorting-subarrays --stress \
  --report .verification/sorting-native/tests.json
```

Recorded validation passed 5,215 comparisons with an independent Python
list-sorting oracle, including exhaustive binary arrays of length up to five,
all selected positions and single query ranges, and 2,000 seeded cases with
overlapping queries, signed endpoints of the value range, duplicates, CRLF,
lengths around powers of two, and an EOF-terminated final token without a
newline. Eleven malformed inputs were rejected, including truncated input,
oversized integers, bad signs, and extra non-whitespace data.

All five stress cases passed: 200,000 queries on one element, a full sort of
200,000 descending values, and `N = Q = 200000` with singleton, random
overlapping, and nested intervals. The retained report
`.verification/sorting-e2e-native-v2-20261016/tests.json` records the timings for
this executable.
