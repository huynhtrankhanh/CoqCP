# Program verification

Each verified program has one adversarial specification and a source-only
candidate containing its implementation and proof helpers:

```text
verification/<problem>/
  spec/Spec.v
  candidate/Candidate.v
  candidate/<proof helpers>.v
```

`spec/Spec.v` defines the inputs, mathematical answer or refinement relation,
and `SOLUTION` signature. Keep it small and free of proof developments. It may
import general theories and generated program definitions, but never candidate
modules. Supporting lemmas, algorithm analysis, and execution proofs belong in
`candidate/`, even when they establish properties of specification definitions.

Candidates import the frozen specification as `Trusted.Spec`, other candidate
helpers as `Submission.<name>`, and general libraries as `CoqCP.<name>`.
Reusable mathematics and language/runtime semantics belong in `theories/`.
Concrete program proofs do not belong in the trusted `_CoqProject` build.

Build the general libraries and generated definitions, then check all candidates:

```sh
rocq makefile -f _CoqProject -o Makefile
make -j2
python3 tools/adversarial/examples.py --output .verification/program-checks
```

Use `--only knapsack` (repeatable) to select problems. Every run needs a fresh
output directory. The runner freezes each spec, compiles all of its candidate
sources in the sandbox, and independently checks every helper and the final
`Implementation` module. Reports and compiled artifacts stay under
`.verification/`; candidate directories contain only `.v` sources.

The shipped program checks, except the tiny increment example, use 180 seconds of CPU per process,
4 GiB of memory, and 600 seconds per sandbox command; Koxia allows 1800 seconds
for compilation of its 74-source chain. The checker CLI's smaller default
budgets remain available for small submissions.

Knapsack, Permuted Binary Strings, and Koxia and Bracket certify generated-main
execution. K-th Highest Score certifies the generated search loop with truthful
oracle queries; DSU certifies generated union operations and score bounds.
Watermelon and Restore Three Numbers certify Gallina solvers. These scopes do
not claim additional byte-stream or emitted-C++ verification.

`trusted_axioms.json` and `compiler_plugins.json` are evaluator policies, not
problem specifications. See [adversarial checking](../docs/AdversarialChecking.md)
for the sandbox, frozen bundle IDs, and direct prepare/check commands.
