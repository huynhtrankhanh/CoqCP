# ZFC with virtual classes: incomplete development

**The requested unconditional noncontradiction theorem is not proved.**
The CoqCP imperative interactive proof checker builds to C++. Its generated
Rocq definition passes independent kernel rechecking; its execution refinement
is not yet proved. A separate Gallina reference checker has checked proofs of
derivation checking, completeness, and class elimination without added axioms. The full
adversarial specification deliberately remains unsatisfied. This example is
not registered as a passing example in `adversarial-examples.json`.

For the reference checker's full contract, the remaining obligation is exactly
`SetTheory.consistent`, meaning that the defined first-order ZFC calculus does
not derive falsity. The native checker also needs its full execution refinement.
No consistency,
excluded-middle, choice, or model axiom has been added to Rocq. There are no
admitted proofs. A strict comparison between the consistency strengths of
ZFC and Rocq is outside the requested scope.

## CoqCP imperative executable

The primary executable now uses ordinary CoqCP imperative source, compiled to
C++ and Rocq. It does **not** extract the Gallina reference checker. Generate,
compile, and independently recheck it with:

```sh
python3 verification/zfc-virtual-classes/imperative/build.py \
  --output .verification/zfc-imperative
.verification/zfc-imperative/zfc-checker \
  < verification/zfc-virtual-classes/imperative/bounded-class.txt
```

[`imperative/ProofChecker.js`](imperative/ProofChecker.js) is generated from
[`generate.py`](imperative/generate.py) and adjacent templates. It uses a
canonical formula arena, explicit substitution stack, theorem history, and
immutable named class bindings. The main loop has eight nested loops of
`2^32` iterations, for at most `2^256` command iterations. Every level exits
early after EOF, opcode `0` (quit), or a fatal input/overflow error. The
substitution traversal uses the same finite cap with early completion.

Wire tokens are separated by spaces, tabs, CR or LF. Integers are unsigned
64-bit values with checked decimal parsing. Names are nonempty tokens of at
most 1024 bytes. Index arithmetic needed for binding shifts is checked before
a theorem can be added; overflow produces `ERR` and terminates. Arena indices
are checked before use. Host allocation failure is outside this development's
proof claims. There is no arbitrary-precision or unbounded completeness claim
for this finite implementation.
The token reader uses IIL's `tapeEnd` loop to scan until a token delimiter,
EOF, or an input error, without a fixed character-scan counter.

Formula ID `0` is falsity. Other formula, class, and theorem IDs are returned
as `OK id`. Rejected commands return `NO`. Theorem IDs are oldest first;
`undo` permits reuse of the removed ID. All replies are flushed immediately.

| Opcode and arguments | Action |
| --- | --- |
| `0` | Quit (`BYE`) |
| `1 i j`, `2 i j` | Construct equality or membership formulas |
| `3 p q`, `4 p` | Construct implication or universal quantification |
| `5 i`, `6 p` | Construct a set-variable class or predicate abstraction |
| `7 a b`, `8 a b` | Construct expanded class equality or membership |
| `9 c name`, `10 name` | Bind a fresh immutable class name, or look it up |
| `11 tag p q r` | Check an axiom witness and append its theorem |
| `12 ci ca`, `13 c` | Check modus ponens, or generalize a theorem |
| `14 name theorem` | Certify the named class as a set using a checked theorem |
| `15 name` | Query `CLASS` or `SET` |
| `16`, `17` | Undo a theorem, or reset theorem history |
| `18 theorem formula` | Restate a theorem after exact expanded-formula comparison |
| `19 theorem` | Return a theorem's formula ID |

The axiom tags, in order `0` through `17`, are K, S, DNE, universal
instantiation, universal distribution, equality reflexivity, left membership
substitution, right membership substitution, equality transitivity,
Extensionality, Foundation, Pairing, Union, Power Set, Infinity, Separation,
Replacement, Choice. Opcode `11` always takes three arguments after the tag;
unused arguments are ignored. Formula arguments are IDs; variable arguments
are raw de Bruijn indices. The executable has no command for adding axioms.

The supplied session constructs and names the bounded class
`{x | x ∈ s ∧ x = x}`, then certifies it as a set using Separation. Merely
constructing or naming a class leaves it `CLASS`. Set certification checks
the existence of a representing set, as defined by
[`ClassNames.is_set`](candidate/ClassNames.v). Names and valid set
certificates persist through theorem-history undo/reset.

[`imperative/logical-identity.txt`](imperative/logical-identity.txt) supplies a
short theorem proof: it derives `p → p` for `p := x = x` from K and S using two
modus ponens steps, then generalizes to `∀x, (x = x → x = x)` and checks the
conclusion by exact formula comparison. It uses no equality-reflexivity axiom.
Run either session by redirecting it into the native executable as above.

Rocq proves `ClassNames.step_safe`, `set_variables_are_sets`, and
`bounded_classes_are_sets` without added axioms. It also proves
`Arena.intern_correct` and preservation of mathematical theorem-history
soundness by the modeled inference operations. `NamedSessions` proves that
interleaving proofs, names and set certification preserves these reference
session invariants even through undo/reset, with the specified finite budget.
Its `nested_iteration_budget` theorem checks `(2^32)^8 = 2^256` in Rocq.
These results are refinement
targets; they do not yet prove execution of the generated imperative `main`.
The build reports this gap in `development-status.json`. It also checks that
`Print Assumptions` for the generated main reports no global assumptions.
Existing `Imperative.v` includes functional-extensionality lemmas, but the
generated main does not depend on those lemmas.

[`imperative/proof/Index.v`](imperative/proof/Index.v) now also proves execution
of the actual generated index-substitution procedure for all seven modes.
[`Overflow.v`](imperative/proof/Overflow.v) proves that overflow sets the error
flag: an accepted result equals the mathematical result without a fit premise.
For successful substitution, the postcondition includes preservation of the
error flag, all other arrays, stdin and stdout.
[`Lift.v`](imperative/proof/Lift.v) connects that execution result to the core
language's de Bruijn renaming under any number of enclosing binders.
[`Intern.v`](imperative/proof/Intern.v) proves that the generated arena scan
returns the first matching node.
[`Fresh.v`](imperative/proof/Fresh.v) proves the complete interning procedure
for valid metadata, a clear error flag, and an arena whose count matches its
length: it returns an existing node,
appends exactly one fresh tuple, or rejects a fresh allocation at the integer
limit. Other arrays and I/O are preserved by fresh allocation.
[`Representation.v`](imperative/proof/Representation.v) connects native arena
entries to first-order formulas. Its generated-code theorem proves that accepted
interning preserves those meanings, the arena metadata invariant, and validity
of the existing theorem history.
[`Canonical.v`](imperative/proof/Canonical.v) proves that canonical entries have
unique formula meanings and that actual interning preserves this property.
[`Stack.v`](imperative/proof/Stack.v) proves execution of the explicit traversal
stack's push procedure, with exact writes, preservation of earlier active
frames, and mandatory rejection at the counter limit.
[`PrintingFrame.v`](imperative/proof/PrintingFrame.v) proves that the actual
`ok` procedure preserves every array except `printBuffer` whenever it finishes.
The underlying frame lemma applies to any action translated from the integer
formatter's single-buffer environment, including its loops. This is a memory
preservation result; total execution and the decimal output specification
remain separate obligations.
[`Append.v`](imperative/proof/Append.v) proves the actual theorem-append
procedure's execution equation, history soundness, exact array writes, and
metadata postcondition. It covers reuse of history slots after undo/reset,
full-counter rejection, and calls made after an error flag has been set.
[`Inference.v`](imperative/proof/Inference.v) proves that native arena-ID
conditions for axiom instances, modus ponens, and generalization justify
appending the resulting theorem.
[`ModusPonens.v`](imperative/proof/ModusPonens.v) checks execution of the named
imperative modus ponens procedure: it preserves history soundness, selects
append or rejection by the actual tag and antecedent-ID comparisons, and
recognizes valid matches in a canonical arena with word-sized antecedent IDs.
The rejection formatter also has a checked memory-preservation proof.
[`InternFrame.v`](imperative/proof/InternFrame.v) proves interning preserves
the theorem count and allocated history, and characterizes allocation failure
as an error-flag update.
[`Generalization.v`](imperative/proof/Generalization.v) proves execution and
history soundness of the whole native generalization procedure, including
interning followed by append. A completed call with a clear error flag writes
the universal quantification of the selected theorem into the next history
slot and increments the active theorem count. This covers existing and fresh
formula nodes, allocation failure, and history-slot reuse.
[`State.v`](imperative/proof/State.v) combines these invariants into a session
predicate. It proves uniqueness of arena interpretations and preservation of
the session predicate by accepted interning, theorem append, generalization,
and both branches of modus ponens.
The native build independently kernel-checks these proofs and audits their
assumptions. The full formula-stack traversal and `main` refinement remain open.

Differential native validation against the separate reference executable:

```sh
python3 verification/zfc-virtual-classes/imperative/test.py \
  --binary .verification/zfc-imperative/zfc-checker \
  --reference .verification/zfc-reference/zfc-checker -v
```

This compares all 18 axiom constructors and class expansions, exercises valid
and forged inference, builds actual set certificates, checks integer-boundary
failure, and checks response flushing while stdin remains open.

## Gallina reference build

With Rocq 9.3.0, OCaml, `ocamlfind`, and Zarith installed:

```sh
python3 verification/zfc-virtual-classes/build.py --output .verification/zfc-reference
python3 verification/zfc-virtual-classes/test_checker.py \
  --binary .verification/zfc-reference/zfc-checker -v
.verification/zfc-reference/zfc-checker
```

The build copies sources into a fresh output directory, compiles all proofs,
independently runs `rocq check`, prints the assumptions of the main results,
and extracts the Gallina state machine. It also checks that the full signature
rejects the candidate for its missing `correct` field. The output's
`development-status.json` records `status: incomplete`.

Example interactive session (input lines followed by their responses):

```text
(axiom (refl 0))
OK 1
(prove false (ref 0))
REJECT 1
(prove (class-in (set 5) (class (= 0 0))) (ax (refl 5)))
OK 2
(expand (class-in (set 1) (class (forall (in 1 2)))))
(all (in 2 1))
undo
OK 1
reset
OK 0
quit
```

One S-expression is read per line. Responses are flushed before the next
command. An accepted theorem is prepended to history. Rejected submissions
preserve history. References are zero based, newest first. `undo` removes the
newest theorem; it rejects an empty history. `reset` empties history. `show`
prints the expanded formulas in history. Empty lines and lines starting with
`;` are ignored.

All indices are arbitrary-precision nonnegative integers. Binding shifts are
therefore not subject to machine-integer overflow.

| Syntax | Meaning |
| --- | --- |
| `false`, `(= i j)`, `(in i j)` | Core atomic formulas |
| `(imp p q)`, `(all p)` | Core implication and universal quantification |
| `(not p)`, `(and p q)`, `(or p q)`, `(iff p q)`, `(exists p)` | Defined core connectives |
| `(core p)` | A core formula used as a class-language statement |
| `(=> p q)`, `(forall p)` | Connectives whose operands may use virtual classes |
| `(class= a b)`, `(class-in a b)` | Class equality and membership |
| `(set i)`, `(class p)` | A set seen as a class, or a class abstraction |
| `(ax witness)`, `(ref i)` | An axiom instance or history reference |
| `(mp implication-proof antecedent-proof)`, `(gen proof)` | Proof constructors |
| `(prove statement proof)` | Submit a theorem with its certificate |
| `(axiom witness)` | Submit an axiom instance with its canonical certificate |
| `(expand statement)` | Display class elimination without adding a theorem |

Core formulas can be used as statements without an explicit `core` wrapper.
The two uses of `class` in this syntax are class abstractions, not class
variables. There is no quantification over classes.

Axiom witnesses are `ext`, `found`, `pair`, `union`, `power`, `infinity`,
`choice`, `(sep p)`, `(repl p)`, `(k p q)`, `(s p q r)`, `(dne p)`,
`(inst p j)`, `(dist p q)`, `(refl i)`, `(mem-left i j k)`,
`(mem-right i j k)`, and `(eq-trans i j k)`.

## Logic and class elimination

[`SetTheory.v`](../../theories/SetTheory.v) defines a classical Hilbert calculus
with equality, membership, implication, falsity, and a de Bruijn universal
binder. Its rules are modus ponens and generalization. Equality has reflexivity
and substitution axioms for both membership arguments and equality.

The set axioms are Extensionality, Foundation, Pairing, Union, Power Set,
Infinity, Separation, Replacement, and Choice. The two schemas admit arbitrary
formulas with arbitrary parameters. Pairing, Union, and Power Set use bounding
forms; Separation recovers their exact forms. Choice is the transversal
formulation for pairwise disjoint families of nonempty sets.

Variable `0` denotes the nearest binder, `1` the next, and so on. In an
abstraction `(class p)`, `0` is the element tested by its predicate. Parameters
and binder insertion are handled by explicit simultaneous renaming.

[`VirtualClasses.v`](../../theories/VirtualClasses.v) eliminates nested
abstractions into the core language. Class equality is extensional equality.
Class membership with an abstraction on its left requires an existential
**set** witness representing that class. Thus the checker does not turn a
proper class into a set element by treating it as a predicate argument.
Set-to-set equality and membership retain their core syntax.

The class mechanism follows the eliminable-notation interpretation described
by [Metamath's theory of classes](https://us.metamath.org/mpeuni/mmset.html#class),
including [class abstraction](https://us.metamath.org/mpeuni/df-clab.html),
[class equality](https://us.metamath.org/mpeuni/df-cleq.html), and
[class membership](https://us.metamath.org/mpeuni/df-clel.html).
This is a separate calculus and certificate format. It does not parse
Metamath databases, compressed proofs, or Metamath metavariable schemes.

## Checked results and remaining proof

[`spec/Spec.v`](spec/Spec.v) defines an independent certificate judgment and
transition relation. Its `SOLUTION.correct` requires exact acceptance and
rejection, preservation of derivability over every finite session, acceptance
of every theorem, equiconsistency of the class extension, and unconditional
non-reachability of falsity from an empty history.

The candidate contains these checked developments:

| File | Result |
| --- | --- |
| [`Elimination.v`](candidate/Elimination.v) | Proof translation in both directions, conservativity, and equiconsistency |
| [`Checker.v`](candidate/Checker.v) | Executable certificate inference and session transitions; soundness, completeness, rollback, and exact rejection |
| [`ClassNames.v`](candidate/ClassNames.v) | Immutable names, proof-based set certification, and set-existence proofs for set variables and bounded classes |
| [`NamedSessions.v`](candidate/NamedSessions.v) | Safe interleaved reference sessions, the finite-budget prefix property, and the exact loop-bound product |
| [`Arena.v`](candidate/Arena.v) | Preservation of formula meanings by interning and soundness of inference using checked arena IDs |
| [`Regression.v`](candidate/Regression.v) | Rejection of forged MP and invalid references; nested classes, capture avoidance, parameters, undo, and reset |
| [`Semantics.v`](candidate/Semantics.v) | Constructive negative semantics for classical first-order logic, soundness, and consistency from a model |
| [`StableSets.v`](candidate/StableSets.v) | Set trees with stable bisimulation; extensionality, separation, unions, powersets, natural numbers, and stable membership induction |
| [`Model.v`](candidate/Model.v) | Validation of seven ZFC axiom families in that interpretation: all except Replacement and Choice |
| [`InnerModels.v`](candidate/InnerModels.v) | Relativization, class-restricted semantics, and the bridge from an inhabited inner model to consistency |
| [`Constructibility.v`](candidate/Constructibility.v) | Definable subsets with finite parameters, a raw well-founded hierarchy, transitivity, nonemptiness, and pairing/union closure of its stable class |
| [`ConstructibleModel.v`](candidate/ConstructibleModel.v) | Validation of Extensionality, Foundation, Pairing, and Union in the restricted hierarchy class |
| [`Candidate.v`](candidate/Candidate.v) | Exported program and the proved parts of its contract |

`Checker.full_contract_iff` proves:

```coq
required step <-> SetTheory.consistent
```

This rules out an incomplete checker as a shortcut: every derivable formula,
including falsity if it were derivable, has an accepted certificate. The
remaining theorem is therefore the genuine consistency obligation.

The model construction proves ordinary object-language Foundation. Its
membership-induction theorem applies to stable extensional predicates; it
does not supply unrestricted accessibility proofs for the negatively
interpreted membership relation. That distinction matters when attempting to
construct bounds for Replacement. `Model.consistency_if_remaining_axioms`
lists Replacement and Choice as explicit, unproved premises of a sufficient
model route. It is not an unconditional consistency theorem.

The current model attempt is related to the negative-interpretation route in
[Carneiro's consistency construction, §8](https://arxiv.org/html/2609.23143v1#S8).
No result from that external formalization is imported or assumed.

The constructible-universe route is now represented by an actual `Def`
operation: each subset is given by a core formula, a finite list of parameters
from the stage, and a proof that the formula uses only those parameters.
`defined_subset_membership` proves its semantics. `bounded_environment` proves
that unused default variables have no effect. The raw hierarchy has checked
zero and one stages and transitivity; its stable union class contains the empty
set and is closed under pairing and unions.

This is still a partial construction toward `L`. Ordinal invariance, reflection,
the remaining inner-model axiom validations, and a well-ordering sufficient for
Choice are unproved. The source of an existing
[Rocq constructibility reduction](https://github.com/jeff87654/busy-beaver/blob/7fa4afad0371843f006aaec0303afb09e4404744/ZF/stdzf_r3/zfc/Z_main.v)
was inspected: its conclusion reduces a ZFC contradiction to a ZF contradiction
in a different calculus. It is not imported, and no bridge to that calculus or
outright consistency proof is claimed here.

## Trust and validation scope

The proved reference executable is the Gallina command-to-state transition function.
[`main.ml`](main.ml) supplies the unverified text parser, display, and
interactive transport. Extraction, OCaml compilation, Zarith, and this frontend
remain the native execution trust boundary. The proof does not claim byte-level
CoqCP `Action` execution or native transport verification. The primary CoqCP
imperative binary is compiled separately, without extraction; its generated
definition has been rechecked, while its execution refinement remains open.

Seven native test groups cover the interactive protocol, flushing with an open
input pipe, malformed inputs, forged proofs, class erasure, large indices, and
axiom readback against independent textbook meanings in all 16 two-element
membership structures and all eight parameter environments.
Fourteen additional native test groups cover the imperative binary, including
all axiom constructors against the reference, named set certification,
1024-byte names, EOF mid-command, invalid class binding, overflow rejection,
and modus ponens after history slots are reused by undo/reset.

The local development build's `rocq check` and assumption audit passed.
Docker/gVisor access was resolved using sudo while keeping the checker process
non-root. The strict specification was frozen with axiom policy `none`; its ID
is `e74dd27a11f150d1220e1fa664cc9335142241872e7da4b4999a92b877d80a12`.
The sandbox compiled the candidate and rejected it at `kernel-and-contract`
because `Implementation` does not satisfy `Trusted.Spec.SOLUTION`. This is
the expected failure from the missing unconditional proof, not an acceptance.
Reports are under `.verification/zfc-strict-result-sudo-v*/`; their source
hashes identify the exact development snapshots they checked. This frozen
contract checks the reference calculus and checker. It does not certify the
imperative port.

To freeze a fresh strict specification:

```sh
python3 tools/adversarial/check.py prepare \
  --spec verification/zfc-virtual-classes/spec/Spec.v \
  --bundle .verification/zfc-strict-bundle --axiom-policy none
```

If the invoking user needs Docker-socket access through sudo, the command used
here was `sudo -n runuser -u ubuntu -g docker -- python3 ...`. Running the proof
checker itself as root is rejected by its runtime policy.

The candidate must continue to fail full signature checking until
`SOLUTION.correct` is supplied with an actual unconditional proof.
