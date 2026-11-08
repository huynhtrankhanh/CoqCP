# Uniform schema certification (work in progress)

This document describes the proposed replacement for schema instantiation.
It is not yet the wire protocol implemented by the checker. The current
protocol is specified in [README.md](README.md).

The current opcode 23 saves a proof-shaped expression without checking that
modus ponens will work for all class arguments. Opcode 24 therefore has to
check the proof again after substitution. For example, a proof can use a
formula `X = Y` as an antecedent and a proof of `0 = 0` as its argument. That
modus-ponens step matches when both `X` and `Y` are the class of set variable
0, but it need not match when they are different. Caching its conclusion after
checking a single instance would be unsound.

The proposed opcode 23 checks the proof symbolically and caches its symbolic
conclusion. A modus-ponens step is accepted only when the symbolic antecedent
and the symbolic argument are structurally equal. Thus acceptance is
independent of the eventual class arguments. Symbolic structural matching is
conservative: some schemas whose instances all happen to be valid may still be
rejected. All accepted schemas permit arbitrary class arguments of the right
arity, including predicate abstractions, subject to the implementation's
finite resource limits.

## Proposed command behavior

The byte syntax, seed handshake, object IDs, schema node kinds, names, and
reply vocabulary remain as specified in [README.md](README.md). The proposed
changes affect these two commands:

- `23 proofNode name` requires an existing proof-typed node, a fresh name,
  and successful uniform certification of the referenced proof template. On
  success it saves both the proof root and its certified symbolic conclusion,
  and replies `OK proofNode`. A nonuniform proof, an invalid root, or an
  unavailable name replies `NO` and creates no name. For example, an MP step
  whose antecedents agree only for `X = Y = 0` is rejected at this point.
- `24 name count classID...` reads exactly `count` class IDs. The name must
  identify a certified schema, `count` must equal its original proof
  template's arity, and every supplied class ID must exist. On success the
  checker expands the cached conclusion with those classes, appends the
  resulting theorem, and replies `OK historyIndex`. It does not require the
  original proof steps to be traversed again. An invalid name, type, count,
  or class ID replies `NO` and adds no theorem.

For every certified schema and every vector of classes of the required
length, the mathematical instance exists and is derivable. This includes
class abstractions and metavariables under binders. As with the existing wire
protocol, malformed input or exhaustion of a finite machine resource is an
`ERR` termination rather than a logical rejection. The formal acceptance
result assumes that suitable storage can be allocated; it does not prove that
every mathematical instance fits a finite machine.

For a certified schema, proposed opcode 24 evaluates the cached conclusion
under the supplied class substitution. It need not visit the proof certificate.
The substitution shifts class arguments beneath binders to avoid capture.
Generalization evaluates its child at the next binder depth; an axiom's own
quantifier and renaming operations are represented separately, because they do
not in general commute with class substitution. The actual set-variable
parameters of axioms remain set variables; a class argument is not silently
substituted for one of them.

[`UniformSchemata.v`](UniformSchemata.v) defines a constructive symbolic
checker and proves that every accepted certificate agrees with the old proof
inference for every class substitution and every starting binder depth. It
also proves that each resulting formula has a ZFC derivation, with no new
axioms. [`UniformSchemaRegression.v`](UniformSchemaRegression.v) and
[`UniformSchemataExamples.v`](UniformSchemataExamples.v) give the accidental
match counterexample and positive arbitrary-class and modus-ponens examples.
[`UniformProtocol.v`](UniformProtocol.v) gives a prospective transition and
dialogue semantics, and proves that every theorem in the final history of a
dialogue starting from the initial state is derivable. It also connects each
reachable schema name to its cached certificate and conclusion in both
directions, and proves acceptance of an instance with valid arguments and a
valid storage allocation.
[`UniformDag.v`](UniformDag.v) proves uniqueness and structural equality
properties of an abstract symbolic DAG; it does not yet relate that DAG to the
IIL arrays.
[`UniformEvaluation.v`](UniformEvaluation.v) proves that values produced
by completed abstract memo schedules denote the specified instantiated
formula, including under binders. For an ordered DAG it constructs a schedule
that reuses memoized node/depth pairs, with at most `node count × (starting
depth + root ID + 1)` insertions. This counts abstract symbolic insertions;
it does not bound class expansion, renaming, actual stack iterations or native
allocation. It does not yet prove that the IIL worklist implements the
schedule or completes within machine bounds.
At starting depth zero, the root ID is below the arena length, so the same
result gives at most `N²` insertions for `N` arena nodes. This is a
conservative arena-wide bound; it is not a bound on total runtime.
[`SchemaArity.v`](SchemaArity.v) proves that a certified conclusion is
independent of substitution values beyond its proof template's arity. Thus
the choice of a default for indices outside the supplied argument vector
does not affect a valid instance.

These results establish the mathematical rule, not an implementation
refinement. The imperative checker, byte-level protocol, resource bounds,
adversarial specification, and native end-to-end correctness proof must all
be updated and checked before the proposed behavior can replace the existing
contract.

The experimental [`uniform-symbols.js.in`](../../../programs/ZFCProofChecker/uniform-symbols.js.in)
is not included in the generated checker. It contains only part of the IIL
implementation, including a seeded SipHash index that compares the complete
node tuple after a hash collision. The experimental evaluator visits reachable
conclusion nodes and binder depths. Its keys now account for equal class
literals with different IDs and retain unused axiom fields, but equivalence
with the Rocq checker's structural equality has not yet been proved. The
unconnected [`uniform-memo.js.in`](../../../programs/ZFCProofChecker/uniform-memo.js.in)
provides a separate collision-checked `(node, depth)` cache for a future
evaluator. The Python model and the isolated compiled IIL tests under
[`prototype/`](../../../programs/ZFCProofChecker/prototype/) exercise the
design; they are not proofs of the production implementation.
The isolated [`test_uniform_dialogue.py`](../../../programs/ZFCProofChecker/prototype/test_uniform_dialogue.py)
temporarily wires these pieces into a generated checker and tests the proposed
commands end to end; it does not change the production generator.
The experimental certification pass currently scans the entire schema-node
prefix up to the named proof root, including unrelated nodes. Only the
instance evaluation is restricted to the reachable conclusion graph.

The collision-chain model in
[`UniformMemoChains.v`](../imperative/proof/UniformMemoChains.v) proves
properties of a mathematical scan, including checking both keys and
following collisions. A Rocq fixture relates the complete generated lookup
to that scan for arbitrary bounded chains, using the previously proved
SipHash execution and modulo operation. The stronger lookup theorem derives
the post-hash state from its initial-state assumptions and relates the result
to the original entry array. It still assumes valid initial buckets, links,
array sizes and word bounds; the complete cache has not yet been proved to
maintain those invariants.
[`test_uniform_memo.py`](../imperative/experimental/test_uniform_memo.py)
also compiles an isolated wrapper using the actual memo template and production
hash function, then kernel-checks two concrete collision executions. Neither
result proves the general imperative cache implementation or its resizing
invariants.
