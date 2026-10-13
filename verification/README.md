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

Example paths, axiom-policy selections, and resource profiles are configuration
in [adversarial-examples.json](adversarial-examples.json), validated against the
independent [JSON Schema](adversarial-examples.schema.json). Python orchestrates
the checks; it does not define the example configuration. Most complete proof
chains allow 600 seconds CPU and 4 GiB memory per invocation, with a 1,200-second
wall deadline per compilation batch or independent checking operation. Freezing
the spec and checking the candidate are separate operations, so this is not a
total example duration. Koxia has a longer wall budget, and K-th Highest Score
has a larger CPU budget. The tiny increment example uses the checker CLI's
default profile.
The sandbox runs native Rocq inside gVisor, preserving the frozen specification
and independent kernel audit. Docker remains available during checking. See the
[gVisor runtime guide](../docs/GvisorRuntime.md) for installation, resource
bounds, and the trust boundary.

Successful compilation artifacts and independent kernel reports are cached by
default in evaluator-owned `.verification/cache`. Keys bind the full validation
runtime identity, input bytes, frozen bundle, flags, policies, and limits. Changes
to the runtime invalidate both caches. `examples.py --cache PATH` selects another
private cache; `--no-cache` forces fresh compilation and checking. Each run still
writes complete bundles, source snapshots, artifacts, and reports, including
cache hit/miss counts. See [sound caching](../docs/AdversarialChecking.md#sound-caching).

Knapsack, Permuted Binary Strings, and Koxia and Bracket certify generated-main
execution. K-th Highest Score certifies the generated search loop with truthful
oracle queries; DSU certifies generated union operations and score bounds.
Watermelon and Restore Three Numbers certify Gallina solvers. These scopes do
not claim additional byte-stream or emitted-C++ verification.

`trusted_axioms.json` and `compiler_plugins.json` are evaluator policies, not
problem specifications. See [adversarial checking](../docs/AdversarialChecking.md)
for the sandbox, frozen bundle IDs, and direct prepare/check commands.
