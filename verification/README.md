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
`operation_attempts` permits a bounded retry after a compilation or kernel
resource failure only when completed modules or library checkpoints were saved.
Failed attempt reports and artifacts remain under `attempt-N`; logical failures
and operations without completed progress are not retried. Each attempt retains
its declared resource limits and full audit.

The default backend compiles Rocq's original C runtime and VM to WASI. Docker
builds and exports the standalone host, then proof checking runs directly.
See the [WASI runtime guide](../docs/WasiRuntime.md) and
[technical decisions](../docs/WasiDecisions.md) for provisioning, cache taint,
the trust boundary, and performance limits.

Knapsack, Permuted Binary Strings, and Koxia and Bracket certify generated-main
execution. K-th Highest Score certifies the generated search loop with truthful
oracle queries; DSU certifies generated union operations and score bounds.
Watermelon and Restore Three Numbers certify Gallina solvers. These scopes do
not claim additional byte-stream or emitted-C++ verification.

`trusted_axioms.json` and `compiler_plugins.json` are evaluator policies, not
problem specifications. See [adversarial checking](../docs/AdversarialChecking.md)
for the sandbox, frozen bundle IDs, and direct prepare/check commands.
