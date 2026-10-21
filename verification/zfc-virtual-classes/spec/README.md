# ZFC with virtual classes: protocol and mathematical specification

This directory specifies the checker independently of its implementation. It contains the object language, its ZFC derivation rules, virtual-class elimination, schema substitution, all command meanings, and the end-to-end observable contract. A reviewer can determine what a request must mean without reading `programs/` or the native execution proofs.

The formal entry point is [Spec.v](Spec.v), especially `required`. Its dependencies are [SetTheory.v](SetTheory.v), [VirtualClasses.v](VirtualClasses.v), [Schemata.v](Schemata.v), [Protocol.v](Protocol.v), and [Guarantees.v](Guarantees.v). The last file proves the mathematical guarantees of the declared protocol rules. These files do not import the implementation or its proof modules. CoqCP's execution definitions provide only the imperative execution and flush-observation model.

## Required mathematical guarantees

Every completed, resource-fitting canonical dialogue must terminate, produce the specified replies and flushes, and correspond to `Protocol.dialogue` starting at `Protocol.initial`. Its final logical state must also satisfy `Guarantees.safe`, an explicit part of `Spec.required`:

- Every active theorem slot denotes a formula with a derivation in `SetTheory.derives`.
- Every named theorem denotes such a derivable formula, including after undo, reset, and reuse of history slots.
- Every named class denotes a class expression. A name marked `SET` carries a derivation of that class's representing-set existence formula, `Protocol.class_setness`.
- Every named schema denotes a proof template. Whenever an instantiation check succeeds, its returned formula has a ZFC derivation.

`Guarantees.step_safe` and `Guarantees.dialogue_safe` prove these properties at every logical transition, including all prefixes of a dialogue, rather than only after the last command. `Guarantees.classes_conservative` proves that a virtual-class statement is provable exactly when its first-order expansion is derivable in the ZFC calculus. Creating a class or a formula is a syntax operation; it does not assert a theorem.

These are derivability guarantees. The contract introduces no Rocq assumption that ZFC has a model and requires no consistency or equiconsistency theorem. The ZFC axioms below are constructors of an inductive object-theory derivation judgment, not extra axioms of Rocq. The specification's mathematical theorems must themselves pass the global-assumption audit.

The contract also requires acceptance of applicable valid requests: `NO` is permitted only when no `Protocol.accepted` rule applies. Supplying an exact valid modus-ponens pair, for example, cannot be rejected merely at the implementation's discretion. This requirement is restricted to the declared resource domain, as explained below.

## Object language and proof calculus

All individual variables range over sets. Formulas have exactly five primitive forms:

```text
false                  falsity
v_i = v_j              equality
v_i in v_j             membership
p -> q                 implication
forall p               universal quantification
```

Variables use de Bruijn indices: `0` denotes the innermost bound variable, `1` the next, and so on; indices beyond the surrounding binders are free parameters. Entering a binder preserves its new index `0` and shifts the images of existing variables. Formally, `up rho 0 = 0` and `up rho (i+1) = rho i + 1`. `SetTheory.rename` applies this lifting recursively, which specifies capture-avoiding renaming.

The remaining connectives are abbreviations fixed by `SetTheory.v`:

```text
not p      := p -> false
p and q    := not (p -> not q)
p or q     := not p -> q
p iff q    := (p -> q) and (q -> p)
exists p   := not (forall (not p))
```

`SetTheory.derives` is the classical Hilbert predicate calculus with equality, plus the ZFC axiom schemes. Its only inference rules are modus ponens and generalization. The logical axiom families are K, S, double-negation elimination, universal instantiation, universal distribution with the stated shift, reflexivity, membership substitution in either argument, and equality transitivity. All free variables are parameters; generalization binds the formula's index `0`.

The nonlogical axioms are Extensionality, Foundation, Pairing, Union, Power Set, Infinity, Separation, Replacement, and Choice. Pairing, Union, Power Set, and Replacement use the bounding formulations written explicitly in `SetTheory.v`; Separation supplies exact subsets. Replacement has a functionality premise. Choice uses the pairwise-disjoint-family transversal formulation. Separation and Replacement accept arbitrary formulas of the first-order language, including parameters; they are schemes, not finitely many selected instances. The exact de Bruijn formulas in `SetTheory.v` are normative and remove ambiguity about all binder positions.

There is no command to introduce a new object-theory axiom, accept an unverified theorem, or declare a class to be a set without a checked existence theorem.

## Virtual classes and set certification

A class expression is either `set i`, meaning the class represented by the set variable `v_i`, or `abstract body`, meaning a predicate abstraction. A class's bound element occupies index `0` in its abstraction body; remaining indices are set parameters. Classes are virtual notation: there is no class universe, quantification over classes, or class comprehension axiom.

`VirtualClasses.erase` translates every extended statement to a first-order formula. With `P_A(x)` denoting the capture-avoiding expansion of class `A`'s predicate:

- Equality of two set-variable classes is ordinary equality of those set variables.
- Other class equality expands to `forall x, P_A(x) iff P_B(x)`.
- Membership with a set-variable class on the left expands to the right class's predicate at that variable.
- Membership of a general class `A` in `B` expands to `exists y, (forall x, x in y iff P_A(x)) and P_B(y)`.

The formal expansions in `VirtualClasses.v` specify all shifts needed for fresh witnesses. For `set i`, the predicate is membership in the appropriately renamed set variable. For an abstraction it is simultaneous, capture-avoiding substitution into the erased body.

`Protocol.class_setness` fixes the exact certificate conclusion checked by command `14`:

```text
set i:       exists y, y = v_i
abstract A:  exists y, forall x, x in y iff P_A(x)
```

The existing parameters are shifted under the fresh binders. Certification uses exact formula equality with that expansion. It records a proof of representability by a set; it does not add a premise to the calculus. `Guarantees.set_variable_is_set` and `Guarantees.bounded_class_is_set` supply examples: set-variable classes are sets, and a predicate restricted to membership in a set is a set by Separation. An arbitrary predicate abstraction need not have such a certificate.

## Transport, seeds, tokens, and replies

Input and output are byte streams. Space (`32`), tab (`9`), LF (`10`), and CR (`13`) separate tokens. Commands can share a line; line boundaries carry no mathematical meaning. Integers are nonempty unsigned decimal tokens in `[0, 2^64-1]`. Names are nonempty byte tokens of at most 1024 bytes, excluding separator bytes. Names are compared byte-for-byte and all object types share one namespace.

The initial exchange is mandatory:

```text
server -> client: SEED\n       [flush before reading any input]
client -> server: k0 k1\n      [two unsigned 64-bit words]
server -> client: READY\n      [flush before reading commands]
```

The two words select the 128-bit SipHash-2-4 key for formula interning. For protection against an attacker choosing formula inputs, the trusted client must choose an unpredictable key; attacker-chosen or publicly fixed keys provide no secrecy guarantee. This is an operational hashing condition, not an assumption in the logical soundness theorem. Hash collisions must never identify different formulas: equality of complete formula records determines identity.

The complete reply vocabulary is:

```text
OK <unsigned-decimal-id>\n
NO\n
CLASS\n
SET\n
THEOREM\n
SCHEMA\n
BYE\n
ERR\n
```

Every reply is flushed immediately, exactly once. `OK` uses canonical decimal output. A missing name, wrong object type, invalid mathematical reference, duplicate name, or unsuccessful proof check returns `NO`; the session continues. A missing required token, malformed or overflowing integer, oversized name, unsupported opcode, checked arithmetic overflow, or traversal-budget exhaustion returns `ERR` and terminates. Malformed or missing seeds also return `ERR` and terminate. No partially evaluated proof may be accepted on an error path.

EOF between commands terminates successfully without another reply. A final token can end at EOF. Quit consumes its own request, replies `BYE`, and leaves all later bytes unread. The command reader has no fixed command-count bound; body reads consume the same stream as the enclosing EOF loop. The implementation's input-length measure is not a protocol value.

`Protocol.request_bytes` fixes the canonical wire representation used by the formal end-to-end contract: one ASCII space between fields, canonical decimal integers, and LF after each request. `Protocol.seed_bytes` uses the same convention for the two seed words. The operational lexer accepts the separators above; the current `Spec.required` execution domain is the canonical encoding, not a proof of every malformed-stream case. Error behavior is specified here but its complete native parser refinement remains a separate obligation.

## Logical state and IDs

The logical state consists of five sequences:

1. A canonical formula arena, initially `[false]`. Thus formula ID `0` is falsity. Equal formulas have one canonical ID; previously allocated formula IDs keep their meanings.
2. A class arena, initially empty.
3. Active theorem history, initially empty. Each slot stores a formula ID. Slots are zero based, oldest first.
4. Named bindings, initially empty, with distinct class, theorem, and schema binding types.
5. A typed schema-expression arena, initially empty.

The four ID spaces—formulas, classes, history, and schema expressions—are separate. Theorem-producing commands return the appended history index. Formula/class/schema construction returns an arena ID. Naming returns the captured class ID, formula ID, or schema root, as appropriate.

Undo and reset affect only active history. A theorem name captures a formula ID rather than a history slot, so its meaning survives slot reuse. Class names and schema names also persist. A name cannot be rebound or reused for a different type. Its only permitted update is the class-certification flag changing to true. Query `15` reports this recorded certification flag; naming a set-variable class still initially records `CLASS` until certification is submitted.

Internal expansion can allocate auxiliary formulas and classes. `Protocol.allocation` and `Protocol.retained_storage` permit such caches while requiring immutable earlier arena entries and canonical formula identity. Rejection does not append a theorem, create a binding, certify a class, or add a schema node; valid auxiliary syntax may remain cached.

## Command meanings

Every field shown is required. All numeric fields must fit the unsigned range, even if that particular command or tag ignores their values.

| Request                               | Required effect or acceptance condition                                                                                                                      | Success reply                   |
| ------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------- |
| `0`                                   | Stop; preserve mathematical state; leave subsequent input unread                                                                                             | `BYE`                           |
| `1 i j`                               | Intern `v_i = v_j`                                                                                                                                           | `OK formulaID`                  |
| `2 i j`                               | Intern `v_i in v_j`                                                                                                                                          | `OK formulaID`                  |
| `3 p q`                               | Both formula IDs exist; intern their implication                                                                                                             | `OK formulaID`                  |
| `4 p`                                 | Formula ID exists; intern its universal quantification                                                                                                       | `OK formulaID`                  |
| `5 i`                                 | Allocate the virtual class `set i`                                                                                                                           | `OK classID`                    |
| `6 p`                                 | Formula ID exists; allocate `abstract (core p)`                                                                                                              | `OK classID`                    |
| `7 a b`                               | Both class IDs exist; intern their equality expansion                                                                                                        | `OK formulaID`                  |
| `8 a b`                               | Both class IDs exist; intern their membership expansion                                                                                                      | `OK formulaID`                  |
| `9 classID name`                      | Class exists and name is fresh; save uncertified class binding                                                                                               | `OK classID`                    |
| `10 name`                             | Name denotes a class; return its ID                                                                                                                          | `OK classID`                    |
| `11 tag a b c`                        | Construct the exact logical/ZFC axiom instance below, checking required formula IDs; append it to history                                                    | `OK historyIndex`               |
| `12 implicationIndex antecedentIndex` | Both active slots exist, the first is exactly `p -> q`, and the second is exactly `p`; append `q`                                                            | `OK historyIndex`               |
| `13 theoremIndex`                     | Active slot exists with formula `p`; append `forall p`                                                                                                       | `OK historyIndex`               |
| `14 name theoremIndex`                | Name denotes class `A` and active theorem is exactly `class_setness A`; certify that binding                                                                 | `OK classID`                    |
| `15 name`                             | Name denotes a class; report its stored certification flag                                                                                                   | `CLASS` or `SET`                |
| `16`                                  | History is nonempty; remove its last active entry                                                                                                            | `OK newHistoryLength`           |
| `17`                                  | Clear active history, including when already empty                                                                                                           | `OK 0`                          |
| `18 theoremIndex formulaID`           | Active theorem's formula is exactly the referenced formula; append that same theorem                                                                         | `OK historyIndex`               |
| `19 theoremIndex`                     | Active slot exists; inspect its formula ID                                                                                                                   | `OK formulaID`                  |
| `20 theoremIndex name`                | Active slot exists and name is fresh; save immutable theorem snapshot                                                                                        | `OK capturedFormulaID`          |
| `21 name`                             | Name denotes a theorem; append the captured formula to active history                                                                                        | `OK historyIndex`               |
| `22 kind a b c d`                     | Build a well-typed schema-expression node according to the table below                                                                                       | `OK expressionID`               |
| `23 proofNode name`                   | Node has proof type and name is fresh; save schema binding                                                                                                   | `OK proofNode`                  |
| `24 name count classID...`            | Name denotes a schema; read exactly `count` class IDs; count equals its arity; every class ID exists; instantiated certificate check succeeds; append result | `OK historyIndex`               |
| `25 name`                             | Name exists; report its binding type, independently of class certification                                                                                   | `CLASS`, `THEOREM`, or `SCHEMA` |
| `26 name`                             | Name denotes a schema; return required number of class arguments                                                                                             | `OK arity`                      |

A failed mathematical condition in this table returns `NO`. In particular, undo on empty history returns `NO`, and an object of the wrong named type is never coerced into the requested type. Formula construction and inspection do not add history entries. Invalid requests may leave auxiliary syntax as described above.

### Exact axiom tags for command 11

The three fields `a b c` always follow the tag. In the table, `P`, `Q`, and `R` are the formulas at the indicated IDs. Fields described as variables are raw de Bruijn indices, not formula IDs. Unused fields are still parsed as integers but are not dereferenced.

| Tag  | Family                        | Fields and formula                                                           |
| ---- | ----------------------------- | ---------------------------------------------------------------------------- |
| `0`  | K                             | `P=a`, `Q=b`; `P -> (Q -> P)`                                                |
| `1`  | S                             | `P=a`, `Q=b`, `R=c`; `(P -> (Q -> R)) -> ((P -> Q) -> (P -> R))`             |
| `2`  | Double negation               | `P=a`; `not (not P) -> P`                                                    |
| `3`  | Universal instantiation       | `P=a`, variable `j=b`; `(forall P) -> rename (instantiate j) P`              |
| `4`  | Universal distribution        | `P=a`, `Q=b`; `(forall (shift P -> Q)) -> (P -> forall Q)`                   |
| `5`  | Reflexivity                   | variable `i=a`; `v_i = v_i`                                                  |
| `6`  | Left membership substitution  | variables `i=a`, `j=b`, `k=c`; `(v_i=v_j) -> ((v_i in v_k) -> (v_j in v_k))` |
| `7`  | Right membership substitution | variables `i=a`, `j=b`, `k=c`; `(v_i=v_j) -> ((v_k in v_i) -> (v_k in v_j))` |
| `8`  | Equality transitivity         | variables `i=a`, `j=b`, `k=c`; `(v_i=v_j) -> ((v_i=v_k) -> (v_j=v_k))`       |
| `9`  | Extensionality                | fixed `SetTheory.extensionality`                                             |
| `10` | Foundation                    | fixed `SetTheory.foundation`                                                 |
| `11` | Pairing                       | fixed `SetTheory.pairing`                                                    |
| `12` | Union                         | fixed `SetTheory.union`                                                      |
| `13` | Power Set                     | fixed `SetTheory.power`                                                      |
| `14` | Infinity                      | fixed `SetTheory.infinity`                                                   |
| `15` | Separation                    | `P=a`; `SetTheory.separation P`                                              |
| `16` | Replacement                   | `P=a`; `SetTheory.replacement P`                                             |
| `17` | Choice                        | fixed `SetTheory.choice`                                                     |

Other tags fail. `instantiate j` maps the removed bound variable `0` to `j` and each former free index `n+1` to `n`; `rename` lifts this map under inner binders. `shift` is renaming by successor. The exact formulas for the set axioms, including all parameters and functionality/choice premises, are definitions in `SetTheory.v`, not implementation-selected formulas.

## Typed schemata with class metavariables

Command `22` consumes exactly five numeric fields: a kind plus four fields. Only the fields listed below are dereferenced. Every referenced expression must already exist and have the required type. Types are class (`CE`), formula (`FE`), and proof certificate (`PE`).

| Kind | Fields used                                      | Result                                        |
| ---- | ------------------------------------------------ | --------------------------------------------- |
| `0`  | `a`: metavariable index, strictly below `2^64-1` | Class metavariable `a`                        |
| `1`  | `a`: class ID                                    | Literal class                                 |
| `2`  | `a`: formula ID                                  | Literal formula                               |
| `3`  | `a`: formula-expression ID                       | Predicate abstraction; class type             |
| `4`  | `a,b`: class-expression IDs                      | Class equality; formula type                  |
| `5`  | `a,b`: class-expression IDs                      | Class membership; formula type                |
| `6`  | `a,b`: formula-expression IDs                    | Implication; formula type                     |
| `7`  | `a`: formula-expression ID                       | Universal quantification; formula type        |
| `8`  | `a`: axiom tag; `b,c,d`: its fields              | Axiom certificate; proof type                 |
| `9`  | `a,b`: proof-expression IDs                      | Modus-ponens certificate; proof type          |
| `10` | `a`: proof-expression ID                         | Generalization certificate; proof type        |
| `11` | `a`: active theorem index                        | Saved checked theorem certificate; proof type |

Other kinds fail. For kind `8`, the formula fields required by the axiom tag are formula-expression IDs rather than concrete formula IDs; raw variable fields retain the meanings in the axiom table. For example, kind `8`, tag `0` needs formula expressions in `b` and `c`; kind `8`, tag `3` needs a formula expression in `b` and a raw variable in `c`. No schema node can reference a later expression, creating a cycle.

The arity of metavariable `i` is `i+1`; the arity of a literal is zero. Combining nodes takes the maximum arity of the dependencies actually used by that constructor. Quantification, abstraction, and generalization retain dependency arity. A saved concrete theorem has arity zero. Consequently gaps in metavariable indices still require arguments up to the largest used index. `Schemata.formula_arity`, `class_arity`, `axiom_arity`, and `proof_arity` are the exact definitions.

Command `24 name count ids...` supplies the substitution `rho i =` the class at the `i`th supplied ID. Both set-variable classes and predicate abstractions are permitted. The number of arguments must equal the stored proof template's arity. Class metavariables are shifted under surrounding binders before expansion: a set-variable class shifts its variable; an abstraction shifts its parameters while preserving its bound element. Literal class/formula nodes remain the literal syntax recorded by their constructors. These rules are mutually recursive definitions in `Schemata.v` and specify precisely how capture is avoided.

Naming a well-typed proof-shaped node does not certify that every proposed substitution will pass modus ponens. Each instance recursively checks its axiom constructors, exact antecedent match, generalization, and saved theorem leaves. A failed instance returns `NO` and appends no theorem. `Guarantees.instance_sound` quantifies over every substitution, depth, and certificate: if `Schemata.infer rho depth cert = Some p`, then `SetTheory.derives p`. This is the mathematical guarantee of schema use, not merely a node-type or arity check.

## End-to-end obligations and resource scope

`Spec.required` quantifies over both seeds and all well-shaped dialogues in an external resource domain. It requires a logical dialogue witness, the explicit mathematical safety invariant, successful actual execution, the complete final stdout, and exact unread input. `Protocol.flush_schedule` additionally specifies the cumulative output and unread request suffix at every reply flush, including the initial seed prompt and ready reply. Returning the right final bytes without the required interactive flushes does not satisfy the contract.

The external `within_capacity` predicate is a resource premise. It must cover representable counters, indices and intermediate shifted variables, allocation capacity, and enough traversal work for the requested mathematical operations. It cannot be selected to mean that the submitted implementation executes correctly, or used to exclude a valid proof merely because its logical check is inconvenient. Host allocation failure is outside the imperative execution model. A full native result must identify and justify its concrete resource domain; declaring `native_contract` alone proves nothing.

The current substitution implementation uses a per-call cache keyed by source formula ID and binder depth. It computes the finite bound `5*(root formula ID+1)^2+1` with checked unsigned arithmetic, stops on an empty work stack, and treats overflow or exhaustion as fatal. This uses the invariant that composite formulas refer to earlier arena IDs. The cache uses SipHash under the handshake seed with a separate domain tag and exact key comparison. The mathematical protocol rules above are unchanged; the native cache lookup, initialization, resizing and bounded insertion helpers have execution proofs. The semantic cache invariant is also preserved by a complete cache-hit iteration and by falsity visits on both hit and miss paths. Other miss cases and return phases, the traversal work count and the complete traversal execution refinement remain open.

The specification deliberately distinguishes its contract from the current proof status. A generated definition that typechecks, passing native tests, a formula interner proof, or soundness of the abstract logical rules alone does not establish `Spec.required` for the native program. Every remaining handler, storage representation, parser-domain obligation, and final session composition must be discharged before claiming full end-to-end verification.

## Example dialogue

With arbitrary valid seed words, this dialogue proves reflexivity, saves it, resets history, recalls the saved formula, and quits:

```text
server: SEED
client: 506097522914230528 1084818905618843912
server: READY
client: 11 5 0 0 0
server: OK 0
client: 20 0 refl
server: OK 1
client: 17
server: OK 0
client: 21 refl
server: OK 0
client: 19 0
server: OK 1
client: 0
server: BYE
```

Formula `0` was already falsity, so the newly interned reflexivity formula has ID `1`. The first `OK 0` is a history index. The name stores formula ID `1`, which survives reset; recall creates active history slot `0` again. The saved formula's mathematical guarantee is `SetTheory.derives (SetTheory.equal 0 0)` throughout.

The specification can be checked without compiling either checker:

```sh
python3 verification/zfc-virtual-classes/spec/check.py --output .verification/zfc-specification
```

This compiles only the specification and its shared execution definitions, audits every theorem in `Guarantees.v` and the contract-equivalence theorem, and independently rechecks `Trusted.Spec` with the kernel. Its status file explicitly makes no claim about native implementation correctness.

For a named class that is certified as a set, the following complete client stream constructs the bounded predicate `x in v_0 and x=x`, names its abstraction, submits the corresponding Separation instance, and certifies the name. Query `15 bounded` returns `CLASS` before certification and `SET` afterwards:

```text
0 0
2 0 1
1 0 0
3 2 0
3 1 3
3 4 0
6 5
9 0 bounded
15 bounded
11 15 2 0 0
14 bounded 0
15 bounded
0
```

The next complete client stream builds and names a proof template with class metavariable `0`. It derives `forall x, (x in A -> x in A)` by K, S, modus ponens, and generalization. Kind `1`'s literal set-variable class denotes the bound `x` in the generalized body; the metavariable's supplied class is shifted under that binder. The arity query returns `OK 1`, and the final instantiation supplies class ID `0` and appends theorem slot `0`:

```text
0 0
5 0
22 0 0 0 0 0
22 1 0 0 0 0
22 5 1 0 0 0
22 6 2 2 0 0
22 8 0 2 2 0
22 8 0 2 3 0
22 8 1 2 3 2
22 9 6 5 0 0
22 9 7 4 0 0
22 10 8 0 0 0
23 9 identity
26 identity
24 identity 1 0
0
```

These example seed words are fixed for reproducibility. Both examples obey the same mandatory prompt/ready exchange and one-flush-per-reply discipline; they do not introduce an axiom or assume the claimed conclusion.
