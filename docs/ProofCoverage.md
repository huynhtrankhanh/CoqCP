# Proof coverage

`theories/KnapsackCode2.v` proves `extractAnswerEq` for the generated competitive Knapsack program. The proof covers decimal input, array growth and initialization, loading items, every dynamic-programming cell, and decimal output with a final newline. It assumes the allocated table size and total item value fit unsigned 64-bit arithmetic, and each weight and value fits unsigned 32-bit arithmetic. The theorem ends in `Qed`; there are no admitted lemmas in its dependency chain. `Print Assumptions extractAnswerEq` reports functional extensionality.

`theories/ArrayGrowth.v` proves length, preservation of existing elements, zero initialization, no shrinking, and execution of translated growth for the Coq runtime. The compiler performs a fixed-point analysis over growth calls and cross-module array mappings to select vector storage consistently for aliases.

`theories/DisjointSetUnionCode.v` and `DisjointSetUnionCode2.v` preserve the ancestor, path-compression, and union proofs. `competitiveMergeRefinesModel` proves that the generated library's merge operation refines the mathematical DSU state. `DisjointSetUnionCode3.v` proves the cumulative merge-score bound. The competitive DSU input/output frontend has executable checks, but no end-to-end theorem.

`theories/KthHighestScore.v` proves the CSES 3305 algorithm's answer rank,
valid query indices, and a maximum of 36 queries. Its `solve_correct` theorem
has no axioms. `theories/KthHighestScoreCode.v` proves that the search loop
extracted from the generated Coq main body refines that algorithm when its
query procedure is replaced by a truthful score oracle; this includes
64-bit arithmetic and loop control. That refinement uses functional
extensionality. Decimal I/O and the emitted C++ are tested with a pipe-based
interactive grader, rather than covered by an end-to-end proof. See the
[solution and verification commands](../CSES/3305/README.md).

The shared FastIO template buffers POSIX `read` calls for batch and interactive
inputs. This C++ runtime change does not change generated Coq actions. Compiler
regressions exercise short responses with open stdin, multiple buffer refills,
all byte values, and the EOF sentinel on files and pipes.

`theories/PermutedBinaryStringsEndToEnd.v` proves `generated_end_to_end`
for the actual generated CSES 3228 entry point, starting with its generated
initial arrays. It covers decimal input, binary response input, all ten rounds,
array bounds and unsigned arithmetic, decimal answer formatting, successful
termination, exact output, full consumption of the specified input, and all
11 flush boundaries. At each query flush, the query's reply is still unread.
The formal input contract uses truthful replies with LF separators. The proof
uses functional extensionality; there are no admitted obligations.
`PermutedBinaryStrings.v` and `PermutedBinaryStringsCode.v` supply the mathematical
reconstruction and generated bit-procedure proofs, which have no axioms.
The emitted C++ is also checked by a pipe-based interactive grader, including
CRLF and fragmented replies. See the [solution](../CSES/3228/README.md).

The Codeforces 1770G solver has a complete generated-main execution proof.
Its self-contained `verification/specs/KoxiaAndBracketIO.v` enumerates positional
masks, selects longest balanced retained subsequences, and counts the optima
modulo 998244353. For every input length from 1 through 500000, the contract
requires successful execution of the actual generated main from the generated
initial arrays, exact decimal output followed by LF, and full consumption of
the LF-terminated input. `verification/examples/koxia-and-bracket/Candidate.v`
proves this contract and is accepted by the adversarial kernel and frozen module
gate under the CI axiom policy. It uses functional extensionality and no admissions.

The proof covers the input scan and optimal split, the half-count bijection,
modular DP decomposition, certified prime and roots, generated NTT and binomial
convolution, table initialization, leaf transitions, every frame transition,
complete traversal, preprocessing, both solve calls, and decimal printing.
`KoxiaVisitInvariant.v`, `KoxiaSolveExecution.v`, and the `KoxiaMain*` modules
compose the generated operations with their memory and capacity invariants.
The algorithmic analysis establishes O(n log²(n+2)) time and O(n) solver storage,
plus the fixed input buffer and frame stack. This is an analysis of the
algorithm; the functional semantics do not formalize instruction costs.

Independent native oracles, maximum-size stress cases, compiler regressions,
and all eight adversarial certificate rejection checks have passed. The rejection
checks complement the accepted universal theorem. See the
[solution and recorded validation](../Codeforces/contests/1770/G/README.md) and
[correctness and complexity explanation](../Codeforces/contests/1770/G/Proof.md).

`theories/InteractiveExecution.v` provides the reusable observed interpreter and
`endToEnd` contract. It preserves ordinary execution while recording output and
unread input at every flush. The evaluator-owned
`verification/specs/PermutedBinaryStringsIO.v` requires this complete contract
and binds it to the generated entry point. See the
[framework fix and proof requirements](EndToEndVerification.md).

The other generated examples have compile-and-run checks. The TypeScript parser, validation, growth analysis, and C++ emitter are tested; they are not themselves formally verified compiler passes. The proofs establish properties of generated Coq actions. They do not prove equivalence of arbitrary emitted C++ programs to those actions or model C++ allocation failure.

To check the compiler and regenerate examples:

```sh
npm --prefix compiler ci
npm --prefix compiler run build
npm --prefix compiler run typecheck
npm --prefix compiler test
node compiler/dist/cli '?json' programs/Knapsack.module.json
```

The project uses the latest stable releases checked on October 4, 2026: Rocq
9.3.0, its separately released Stdlib 9.2.0, and stdpp 1.13.0. Versions are pinned
in [coqcp-toolchain.opam](../coqcp-toolchain.opam).

On Ubuntu 26.04, install the toolchain outside the repository:

```sh
sudo apt-get update
sudo apt-get install ca-certificates curl git python3 build-essential ocaml opam libgmp-dev pkg-config m4 rsync unzip libseccomp-dev bubblewrap
sudo install -d -o "$(id -un)" -g "$(id -gn)" /opt/rocq
bash tools/install-toolchain.sh
export PATH=/opt/rocq/9.3.0/bin:$PATH
rocq --version
```

Compile the project and independently check every registered proof:

```sh
rocq makefile -f _CoqProject -o Makefile
make clean
make -j2
make validate
```

The project maps `theories/` to `CoqCP`, `generated-coq/` to `Generated`, and `programs/llmGeneratedCode/` to `GeneratedExamples`.
`make validate` runs `rocq check` on every module listed in `_CoqProject` with those load paths and prints the assumption summary. CI uses the same target and allows only the axioms in [trusted_axioms.json](../verification/trusted_axioms.json), currently functional extensionality, with no unsafe definitions. The adversarial checker uses this same policy. Standard library imports use the `Stdlib` namespace; the code generator emits it too.

Rocq 9.3 reports six declarations from the trusted libraries that rely on its
default inductive index semantics, including equality. The same policy file
records their exact names, and both checks reject additional declarations with
that property.

After upgrading from Coq 8.20, regenerate the Makefile and recompile all `.vo`
files. Frozen specification bundles from that toolchain must also be prepared
again; the checker rejects bundles with a different toolchain fingerprint.

For untrusted AI-generated submissions, use the separate [adversarial checking infrastructure](AdversarialChecking.md). It freezes an evaluator-owned `Spec.v`, compiles source-only submissions in a Bubblewrap/seccomp sandbox, independently checks every submitted library, and checks the submitted module against the frozen signature. It includes mathematical knapsack and complete input/output contracts for the existing proofs.

The checked-in HTML pages for the migrated imperative runtime and generated-program proofs were refreshed with `coqdoc` from the current sources.
