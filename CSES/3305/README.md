# CSES 3305 — K-th Highest Score

[Problem statement](https://cses.fi/problemset/task/3305).
This is an interactive problem: each country has `n` distinct scores in decreasing
order, and the grader answers requests for a country's score at a chosen rank.
All `2n` scores are different. The task allows at most 100 requests.

## Algorithm

Write the country scores as `F[1..n]` and `S[1..n]`. Define local sentinels
`F[0] = S[0] = 1000000001` and `F[n+1] = S[n+1] = 0`.
Sentinel lookups never produce a request to the grader.

If the top `k` scores contain `i` Finnish scores, they contain `j = k-i`
Swedish scores. Feasible values of `i` are

```
lo = max(0, k-n)
hi = min(k, n)
```

Find the smallest feasible `i` for which

```
F[i+1] < S[k-i]
```

using binary search. For each midpoint `m`, request `F[m+1]` and `S[k-m]`.
If the inequality holds, set `hi = m`; otherwise set `lo = m+1`.
After convergence, request `F[lo]` and `S[k-lo]` and report their minimum.
Every request and the final answer ends with a newline and an explicit flush.

The initial interval width is at most `100000 < 2^17`. Each iteration halves
its width, so 17 iterations suffice. Two requests per iteration and two final
requests give a maximum of **36 requests**. Local sentinels can reduce this
number. The program uses `O(log n)` operations and `O(1)` storage.

## Correctness proof

The predicate `F[i+1] < S[k-i]` is monotone: as `i` increases, its left side
falls and its right side rises. The predicate holds at `hi`: either `hi = k`
and the right side is the upper sentinel, or `hi = n` and the left side is zero.

The search invariant says that the predicate holds at the upper bound, and
that it fails at every feasible index below the lower bound. The midpoint
updates preserve this invariant. When the bounds coincide, their value `i`
is the smallest feasible index satisfying the predicate.

Let `j = k-i`. We therefore have

```
F[i+1] < S[j]
S[j+1] < F[i]
```

The first inequality is the predicate itself. For the second, if `i` is above
the initial lower bound, the predicate fails at `i-1`, so
`F[i] >= S[j+1]`. Distinctness makes this inequality strict. If `i` equals the
initial lower bound, either `i = 0` and `F[i]` is the upper sentinel, or `j = n`
and `S[j+1] = 0`; the same strict inequality follows.

Both countries' selected prefixes are consequently above both unselected
suffixes. Their total size is `i+j = k`. The smaller of `F[i]` and `S[j]`
is their smallest real score; the upper sentinel handles an empty prefix.
Exactly `k-1` real scores are greater than this answer. Thus it is the
`k`-th highest score.

## Files and formal coverage

- `KthHighestScore.js`: CoqCP source.
- `KthHighestScore.module.json`: compiler configuration.
- `../../generated-cpp/KthHighestScore.cpp`: standalone C++20 submission.
- `../../generated-coq/KthHighestScore.v`: compiler-generated Coq actions.
- `../../verification/kth-highest-score/candidate/KthHighestScore.v`: executable mathematical model and proofs.
- `../../verification/kth-highest-score/candidate/KthHighestScoreCode.v`: generated search loop refinement.
- `test_interactive.py`: pipe-based grader with exhaustive small cases, randomized
  contests, maximum-size cases, and exact comparison of source/model query traces.

`solve_correct` proves that the modeled answer is a real score with exactly
`k-1` scores above it, that every emitted query has an index in `1..n`, and that
at most 36 queries are emitted. `extend_valid` derives the sentinel-based input
contract from decreasing country scores in `1..1000000000`.

`generated_search_correct` extracts the search loop from the actual generated
Coq main body and proves that its local-variable execution returns the partition
used by the mathematical model. It abstracts the query procedure by an oracle
that stores the correct score in the reply array. The proof includes unsigned
64-bit arithmetic, midpoint division, local-variable updates, and loop exit.
It does not prove the decimal I/O procedures or the C++ compiler correct.
The complete emitted C++ program's I/O and query trace are checked by the local
grader. The mathematical proof uses no axioms; the generated-loop refinement
uses functional extensionality, as permitted by the repository's proof policy.
There are no admitted obligations.

## Build and check

With the repository's pinned Rocq toolchain on `PATH`:

```sh
npm --prefix compiler run build
node compiler/dist/cli '?json' CSES/3305/KthHighestScore.module.json
g++ -std=c++20 -O2 generated-cpp/KthHighestScore.cpp -o /tmp/cses3305
python3 CSES/3305/test_interactive.py --binary /tmp/cses3305
rocq makefile -f _CoqProject -o Makefile
make -j2
make validate
python3 tools/adversarial/examples.py --only kth-highest-score \
  --output .verification/kth-highest-score-review
```

The shared FastIO template uses a 64 KiB buffer for both batch and interactive
programs. A single POSIX `read` refills that buffer with whatever bytes are
available; interrupted reads are retried, and EOF returns the same unsigned
`-1` sentinel as before. There is no interactive mode or flag. The generated
Coq input actions are unchanged. Queries are flushed explicitly in the source.
The C++ runtime targets POSIX systems, including the Linux contest environment.
