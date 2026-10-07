# Codeforces 1770G: Koxia and Bracket

The generated solver has a complete Rocq execution proof against a small,
self-contained specification. The adversarial kernel and frozen-contract gate
accepts its `SOLUTION` certificate and rejects eight insufficient or invalid
certificates. The algorithm runs in **O(n log²(n+2))** time, meeting the requested
O(n log² n) bound.

[Problem](https://codeforces.com/contest/1770/problem/G),
[editorial](https://codeforces.com/blog/entry/110754).

## Solution and proof

- [Compiler-language source](KoxiaAndBracket.js)
- [Build configuration](KoxiaAndBracket.module.json)
- [Generated C++](../../../../generated-cpp/KoxiaAndBracket.cpp)
- [Generated Rocq](../../../../generated-coq/KoxiaAndBracket.v)
- [Correctness and complexity explanation](Proof.md)
- [End-to-end certificate](../../../../verification/examples/koxia-and-bracket/Candidate.v)
- [Recorded adversarial validation](verification-report.json)

Split the string at its first global minimum balance. Every optimal deletion
mask factors uniquely into a prefix mask deleting only closing brackets and a
suffix mask deleting only opening brackets. Reverse and flip the suffix, count
the two halves, then multiply their counts modulo 998244353.

For each half, a closing bracket is special when it establishes a new minimum.
The DP tracks extra deleted closing brackets above the running deficit. An
ordinary closing event gives `next[j]=dp[j]+dp[j-1]`; a special event gives
`next[j]=dp[j]+dp[j+1]`. Divide and conquer processes the low states recursively.
High states cannot hit the lower boundary and are processed together using a
binomial convolution and radix-two NTT. Each recursion depth costs O(n log n),
and the balanced recursion has O(log n) depths. Solver storage is O(n), plus
the fixed 500000-element input buffer and 32 frames. See [the proof](Proof.md)
for the split bijection, DP interpretation, convolution identity, and recurrence.

## Formal contract and coverage

[KoxiaAndBracketIO.v](../../../../verification/specs/KoxiaAndBracketIO.v)
enumerates Boolean **position masks**, retains their selected characters,
checks the Dyck prefix condition and zero total balance, chooses the greatest
retained length, and counts masks attaining it. Different masks count
separately even if they produce identical strings. The answer definition uses
no DP, split algorithm, NTT routine, or existing problem specification.

Its `required program` contract binds the program to the actual generated main.
For every bracket string of length 1 through 500000, it requires successful
execution from the generated initial arrays and zero locals, exact decimal
output followed by LF, and full consumption of the string followed by LF.
The certificate proves this universal statement, including allocation,
input parsing, selection of the split, table initialization, preprocessing,
both complete solves, modular multiplication, and decimal printing.

The proof chain includes:

- `SpecProperties.v`, `OptimalSplit.v`, `HalfCounting.v`, `FullCounting.v`, and
  `MinimumScan.v`: mask semantics, optimal split, half counts, product, and scan.
- `KoxiaPolynomial.v` and `KoxiaPaths.v`: DP decomposition, convolution identity,
  path multiplicities, and moving balance origin.
- `KoxiaNTTCorrect.v`, `KoxiaTableLoops.v`, and `KoxiaConvolutionCorrect.v`:
  successful generated transforms, table setup, and convolution coefficients.
- `KoxiaVisitInvariant.v` and `KoxiaSolveExecution.v`: complete generated frame
  traversal and solve execution, including address and capacity bounds.
- `KoxiaMainInitialization.v`, `KoxiaMainSegments.v`, `KoxiaMainResult.v`, and
  `Candidate.v`: the generated main and exact input/output contract.

All supplied proofs end in `Qed`; no admissions or additional axioms are used.
The approved assumption is functional extensionality. The independent kernel
check reports no unsafe definitions. The time bound is an algorithmic analysis;
the framework's functional semantics do not formalize instruction costs.
The proofs cover the generated Rocq actions. The TypeScript compiler, emitted
C++ correspondence, POSIX runtime, and allocation success remain outside those
semantics, as in the framework. Compiler and native tests cover those parts.

The specification source SHA-256 is
`b9f4de67aad9b3ec0d00d20e487e80ebf588b1a5155effc585c1454a252fe37d`.
The recorded validation includes the frozen bundle ID and proof-source hashes.

## Reproduce checks

Use the pinned toolchain and compile the registered project libraries first:

```sh
export PATH=/opt/rocq/9.3.0/bin:$PATH
npm --prefix compiler run build
node compiler/dist/cli '?json' Codeforces/contests/1770/G/KoxiaAndBracket.module.json
rocq makefile -f _CoqProject -o Makefile
make -j2
make validate
g++ -std=c++20 -O2 generated-cpp/KoxiaAndBracket.cpp -o /tmp/koxia
python3 Codeforces/contests/1770/G/test_solution.py --executable /tmp/koxia --large
python3 Codeforces/contests/1770/G/check_adversarial.py \
  --output .verification/koxia-review-new --network-isolation seccomp
```

Use a fresh output directory. The default network isolation uses a network
namespace; the explicit seccomp mode blocks network syscalls before the worker
starts and is supported when namespace creation is unavailable. Both modes
retain the compilation sandbox, resource limits, independent kernel checking,
frozen module contract, and CI axiom policy. The solution review defaults to
180 CPU seconds, 300 wall seconds, and 4096 MiB per sandboxed process so the
complete proof dependency chain can be checked; these budgets are configurable.

The native suite passed 2496 independent oracle comparisons, including all
bracket strings of length 1 through 10 checked by literal deletion-mask
enumeration. Larger inputs use a quadratic DP that tracks longest retained
length and multiplicity at each retained balance, independently of the split
and NTT algorithm. LF, CRLF, and EOF endings are tested. Seven maximum-size
cases cover uniform brackets, balanced input, random data, sparse and dense
record minima, and a large valley. Bounds assertions and address/undefined
behavior sanitizer runs also passed.

The adversarial script records the spec ID before source submission, independently
checks the review and implementation libraries, then requires acceptance of the
complete generated-main certificate. It also requires kernel/contract rejection
of missing proofs, `True` proofs, extra premises, admissions, notation shadowing,
conditional claims about failing executions, and abstract-only algorithm or
problem proofs. Its summary records `solver_certified: true` only after the
positive certificate and all eight rejection checks pass.
