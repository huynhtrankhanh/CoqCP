# Native ZFC proofchecker: adversarial submission

This directory is an ordinary source-only adversarial example. The evaluator
freezes `spec/Spec.v` and its adjacent dependencies; it does not run a generator
or a submission-supplied preparation script. `spec/ProofChecker.v` is the
checked-in Rocq program fixed by the specification. The candidate contains the
proof sources under the standard `Submission` namespace and proves the
contract for that program and the evaluator-owned `Capacity.within_capacity`.
The capacity domain is the union of the general and set-schema resource plans.

The specified streams use canonical encodings and satisfy the explicit shape
and capacity premises in `Spec.v`. The theorem asserts successful Rocq-model
execution, the logical dialogue and safety guarantees, exact flush snapshots,
output and remaining input. It does not cover every possible input byte stream.

`spec/ProofChecker.v` was generated from `programs/ZFCProofChecker.js` and
`programs/IO/PrintInt64.js`; the adversarial gate checks the frozen Rocq source,
not the correctness of that translation or of the generated C++ executable.
The separate compiler CI compares its generated Rocq output with this snapshot;
it does not run as part of adversarial evaluation. When the program or its
specification changes, review and update the snapshot and proof submission
together.
