# ZFC with virtual classes: protocol and mathematical specification

This directory specifies the checker independently of its implementation. It contains the object language, its ZFC derivation rules, virtual-class elimination, schema substitution, all command meanings, and the end-to-end observable contract. A reviewer can determine what a request must mean without reading `programs/` or the native execution proofs.

The formal entry point is [Spec.v](Spec.v), especially `required`. Its dependencies are [SetTheory.v](SetTheory.v), [VirtualClasses.v](VirtualClasses.v), [Schemata.v](Schemata.v), [Protocol.v](Protocol.v), and [Guarantees.v](Guarantees.v). The last file proves the mathematical guarantees of the declared protocol rules. These files do not import the implementation or its proof modules. CoqCP's execution definitions provide only the imperative execution and flush-observation model.

[`ByteProtocol.v`](ByteProtocol.v) separately specifies byte tokenization, consumed separators and EOF, the 1024-byte token limit, decimal digits and unsigned overflow. It proves bounds and input-consumption properties of that lexical model. For separator-terminated tokens, [`NativeByteNumber.v`](../imperative/proof/NativeByteNumber.v) connects accepted numbers to the actual native reader, and [`NativeByteBadDigit.v`](../imperative/proof/NativeByteBadDigit.v) and [`NativeByteOverflow.v`](../imperative/proof/NativeByteOverflow.v) connect bad-digit and overflow results to native rejection, under their stated buffer and initial-state bounds. For tokens ending at EOF, [`NativeByteNumberEOF.v`](../imperative/proof/NativeByteNumberEOF.v), [`NativeByteBadDigitEOF.v`](../imperative/proof/NativeByteBadDigitEOF.v), and [`NativeByteOverflowEOF.v`](../imperative/proof/NativeByteOverflowEOF.v) cover accepted numbers, bad digits, and overflow respectively. [`NativeByteNumberUnified.v`](../imperative/proof/NativeByteNumberUnified.v) unifies those three outcomes for EOF and separator termination under explicit token decomposition and reader-state premises. [`NativeByteReadNumber.generated`](../imperative/proof/NativeByteReadNumber.v) proves actual observed `readNat` refinement of the complete `ByteProtocol.read_number` model for every finite byte-valued input, with the stated initial buffer, pending-byte and error-state conditions; it covers whitespace, missing input, length errors, bad digits, overflow, valid values and exact unread suffix. [`NativePendingByteReadNumber.v`](../imperative/proof/NativePendingByteReadNumber.v) proves the same numeric outcomes when a non-separator first byte is pending. [`NativeCompleteReadNumber.generated`](../imperative/proof/NativeCompleteReadNumber.v) combines these cases with pending-separator parsing and refines the numeric byte model’s success, invalid, overlong and missing-input reports for every finite byte-valued input and every valid pending-byte state, with exact unread suffix and no change to flush observations. The report groups bad-digit and overflow errors together. The full command parser and dialogue have not yet been proved to refine the byte model; the end-to-end theorem below still uses canonical command fields. [`NativeWhitespaceSchemaArguments.consume_canonical`](../imperative/proof/NativeWhitespaceSchemaArguments.v) proves flexible separators for the variable-length schema-instantiation argument loop, with the same final state as canonical parsing; it is not yet a complete opcode-24 whitespace theorem. Separate actual-command results cover flexible argument whitespace for [`equality and membership`](../imperative/proof/NativeWhitespaceAtoms.v), [`implication`](../imperative/proof/NativeWhitespaceImp.v), [`universal quantification`](../imperative/proof/NativeWhitespaceAll.v), [`axiom selection`](../imperative/proof/NativeWhitespaceAxiom.v), [`modus ponens`](../imperative/proof/NativeWhitespaceMP.v), [`generalization`](../imperative/proof/NativeWhitespaceGeneralize.v), [`class creation`](../imperative/proof/NativeWhitespaceClassCommands.v), [`class equality`](../imperative/proof/NativeWhitespaceClassEqual.v), [`class membership`](../imperative/proof/NativeWhitespaceClassMember.v), [`inspect`](../imperative/proof/NativeWhitespaceInspect.v), and [`restate`](../imperative/proof/NativeWhitespaceRestate.v), including the applicable accepted and rejected operations and exact flushes. [`NativeWhitespaceAtomsDialogue.generated_main_flexible_seeds`](../imperative/proof/NativeWhitespaceAtomsDialogue.v) additionally proves complete equality/membership sessions with flexible argument and seed whitespace and trailing whitespace before EOF, subject to its explicit numeric and formula-count bounds; opcode encodings remain canonical without extra leading whitespace. [`NativeWhitespaceFormulaSpacedDialogue`](../imperative/proof/NativeWhitespaceFormulaSpacedDialogue.v) extends that session result to mixed equality, membership, implication and universal-quantification commands, including arbitrary separators before opcodes, rejected operations and later commands. [`NativeWhitespaceFormulaSpacedQuitDialogue`](../imperative/proof/NativeWhitespaceFormulaSpacedQuitDialogue.v) proves the same fragment ending in quit, including exact `BYE` flushing and the unread suffix. [`NativeWhitespaceProofDialogue`](../imperative/proof/NativeWhitespaceProofDialogue.v) adds generalization to the EOF-terminated mixed fragment with an explicit history-growth bound.

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

A small executable example is [`schematic-set-k.txt`](../imperative/schematic-set-k.txt). After the two seed words, `5 0` and `5 1` create the class arguments. Two kind-`0` nodes declare parameters `A` and `B`; kinds `4` and `5` form `A=A` and `A∈B`; kind `8` with tag `0` builds their K certificate. `23 4 set_k` names that certificate, and `24 set_k 2 0 1` appends the checked instance `(v₀=v₀) → ((v₀∈v₁) → (v₀=v₀))` at history index `0`. The schema expression IDs are `0` through `4`; naming returns `OK 4`, and instantiation returns `OK 0`. This command fits the set-parameter resource theorem below with grid size `25` and a formula allowance of `1050`.

## End-to-end obligations and resource scope

`Spec.required` quantifies over both seeds and all well-shaped dialogues in an external resource domain. It requires a logical dialogue witness, the explicit mathematical safety invariant, successful actual execution, the complete final stdout, and exact unread input. `Protocol.flush_schedule` additionally specifies the cumulative output and unread request suffix at every reply flush, including the initial seed prompt and ready reply. Returning the right final bytes without the required interactive flushes does not satisfy the contract.

The external `within_capacity` predicate is a resource premise. It must cover representable counters, indices and intermediate shifted variables, allocation capacity, and enough traversal work for the requested mathematical operations. It cannot be selected to mean that the submitted implementation executes correctly, or used to exclude a valid proof merely because its logical check is inconvenient. Host allocation failure is outside the imperative execution model. A full native result must identify and justify its concrete resource domain; declaring `native_contract` alone proves nothing.

### Proved native renaming domain

The complete generated renaming helper now has an execution theorem, [`RenameMemoRun.generated`](../imperative/proof/RenameMemoRun.v). For an encoded formula `p`, a variable map `rho`, and initial binder depth `b`, its result denotes

```text
rename (up^b rho) p
```

Here `up^b` means `b` repetitions of the lifting operation defined above. In particular, indices below `b` remain bound to their existing variables, and every further binder in `p` lifts the map again. The available maps cover shifts, universal instantiation, the Separation and Replacement expansions, and predicate abstraction. Their maximum index-increase allowances are:

| Renaming map                                                          | Increase allowance `delta` |
| --------------------------------------------------------------------- | -------------------------- |
| Shift by `s`                                                          | `s`                        |
| Instantiate the removed variable with index `a`                       | `a`                        |
| Separation                                                            | `1`                        |
| Replacement left or right premise                                     | `2`                        |
| Replacement image                                                     | `1`                        |
| Predicate abstraction, with parameter shift `s` and element index `a` | `max(s,a)`                 |

Let `U = 2^64-1`, `S = 2^63-1`, `r` be the source formula ID, `n` the number of existing formula nodes, and `G = (r+1)^2`. Let `B` bound every variable index occurring in the stored source formula, and let `h(p)` be its maximum nesting depth of universal binders. Thus atoms and falsity have height zero, implication takes the maximum of its children's heights, and a universal binder adds one.

The theorem proves success under these explicit input conditions:

- The input formula arena is canonical: stored records decode to their represented formulas, each represented formula has one ID, tuple records are normalized, and the seeded interner's allocation, bucket/link and reachability invariants hold. ID `0` represents falsity, ID `r` represents `p`, and every composite record's child IDs are smaller than its own ID.
- The native metadata array has at least 32 cells, the SipHash state array is nonempty, the interner capacity in metadata cell `20` is positive, and the fatal-error cell `8` is zero. The procedure arguments specify exactly `r`, `b`, the selected map, and its shift/argument values. The latter are unsigned 64-bit words.
- `5*G+1 <= U`, `n+G <= S`, `B+delta <= U`, and `b+h(p) <= U`.

These are sufficient arithmetic and representation conditions on the input. They assume no execution, successful result, consistency statement or invariant-preservation theorem. [`RenameMemoInput.v`](../imperative/proof/RenameMemoInput.v) derives `h(p) <= r` from backward child IDs, so the simpler check `b+r <= U` suffices for the depth condition. It also computes a suitable `B` as the maximum of atomic index fields in stored records with IDs at most `r`; this scans the stored source prefix and does not expand the formula's shared DAG.

From concrete per-call initialization, the actual helper terminates with the fatal-error cell still zero, an empty traversal stack, and a representable result ID denoting the capture-avoiding formula above. The formula arena remains canonical with backward child references; earlier formula IDs retain their meanings; and at most `G` nodes are added. [`RenameMemoOutput.v`](../imperative/proof/RenameMemoOutput.v) transports represented classes, active history, named objects and schema metadata through that extension. Input, output and flush observations remain unchanged. These internal-helper results provide the substitution component needed by class, axiom and schema callers. The class, axiom and schema callers and their complete protocol composition are proved below.

The per-call cache uses `(source formula ID, absolute binder depth)` keys, SipHash under the handshake seed with domain tag `5`, and exact key comparison. It begins empty with 16 slots and grows at half load. All earlier completed keys survive insertion and resizing, including when hashes collide. [`RenameMemoSchedule.v`](../imperative/proof/RenameMemoSchedule.v) counts partial runs with caching on return; [`RenameMemoScheduleRelation.v`](../imperative/proof/RenameMemoScheduleRelation.v) and [`RenameMemoEventSchedule.v`](../imperative/proof/RenameMemoEventSchedule.v) connect that scheduler to the actual native frames and cache effects. [`RenameMemoScheduleResources.v`](../imperative/proof/RenameMemoScheduleResources.v) preserves the required stack, arena and checked-growth bounds throughout the run. [`RenameMemoInitial.v`](../imperative/proof/RenameMemoInitial.v), [`RenameMemoStart.v`](../imperative/proof/RenameMemoStart.v) and [`RenameMemoLoop.v`](../imperative/proof/RenameMemoLoop.v) close initialization, native loop execution and stopping.

There are at most `G` fresh source/depth pairs and `4*G+1` active phase dispatches, followed by one empty-stack stopping dispatch. The generated loop's checked fuel `5*G+1` therefore suffices. This is a dispatch-count theorem, not a machine-instruction or elapsed-time bound: cache probing, SipHash, formula interning and resizing perform additional work. The imperative memory model uses finite lists and total growth operations; physical host allocation failure lies outside that model. Calls outside the stated sufficient domain require separate reasoning; the theorem does not establish that every such call fails. The implementation checks arithmetic overflow and treats traversal exhaustion as fatal, so an exhausted traversal cannot accept a partial result.

[`RenameMemoCallers.generated_predicate`](../imperative/proof/RenameMemoCallers.v) additionally proves the complete actual predicate helper for a valid represented class `C`. Given parameter shift `s` and element index `a`, it returns a formula ID denoting `VirtualClasses.predicate C (fun i => i+s) a`. For `C = set v`, this is `v_a in v_(v+s)`; for `C = abstract (core p)`, it is `rename rho p` with `rho 0 = a` and `rho (i+1) = i+s`, lifted under inner binders. Its common input conditions are a canonical backward formula arena with falsity at ID `0`, well-formed represented class storage and a valid class ID, at least 32 metadata cells, a nonempty SipHash state array, positive interner capacity, a zero fatal-error flag, and unsigned word values `s,a`. The helper arguments identify that class ID, shift and element index exactly. Its additional checks depend on the class form:

| Class form                      | Sufficient additional checks                                                                           | Added formula nodes |
| ------------------------------- | ------------------------------------------------------------------------------------------------------ | ------------------- |
| `set v`                         | `n <= S` and `v+s <= U`                                                                                | At most `1`         |
| Abstraction with body at ID `r` | `5*G+1 <= U`, `n+G <= S`, `B+s <= U` and `B+a <= U`, with `B` computed from the stored prefix as above | At most `G`         |

The result preserves canonical formulas, backward child references, represented classes and logical storage, with the fatal-error cell zero. This proves predicate expansion for both native class-record forms; the proved compositions into equality and membership follow below.

The complete native class-equality helper is also proved in [`RenameMemoClassEqual.v`](../imperative/proof/RenameMemoClassEqual.v). Two set-variable classes produce their core equality with at most one new formula. Otherwise the helper computes both predicates with shift `1` and element index `0`, then constructs the specified universal biconditional with at most six more formulas. The sufficient input domain requires both predicate readiness checks above and `n+g(A)+g(B)+6 <= S`, where `g(C)` is `1` for a set-variable class or its root grid bound for an abstraction. The set/set branch instead requires `n+1 <= S` and needs no shifted predicates. The result preserves backward topology, canonical IDs and logical storage. [`ClassEqualProtocol.generated_total_protocol`](../imperative/proof/ClassEqualProtocol.v) additionally proves opcode `7` through canonical separator-terminated parsing: valid class IDs produce the exact `OK id` reply and its logical class-equality allocation step; an invalid ID produces `NO` and preserves the logical state. Both cases include the exact flushed output and unread input suffix, with represented formulas, classes and active history.

The native class-membership helper is proved in [`RenameMemoClassMember.v`](../imperative/proof/RenameMemoClassMember.v). For a set-variable left class `set i`, it computes the right predicate with shift `0` and element index `i`; its allocation allowance is `g(B)`. For an abstract left class, it computes the left predicate with shift `2` and element index `0`, the right predicate with shift `1` and element index `0`, and the specified existential representing-set formula using thirteen more native interner operations. Its joint allocation allowance is `g(A)+g(B)+13`. The common representation/readiness requirements above, the relevant predicate checks, and `n+allowance <= S` suffice for each branch. The result preserves canonical IDs, backward topology and logical storage. [`ClassMemberProtocol.generated_total_protocol`](../imperative/proof/ClassMemberProtocol.v) proves the corresponding opcode `8` through canonical separator-terminated parsing, valid-class acceptance or invalid-ID rejection, exact flushed reply, unread suffix and logical protocol step, with represented formulas, classes and active history.

The native setness-formula builder is proved in [`RenameMemoClassSetness.v`](../imperative/proof/RenameMemoClassSetness.v). For `set i`, its target is `exists z, z = v_i`, represented under the new binder by `ex (equal 0 (S i))`; the sufficient domain requires `i+1 <= U` and `n+4 <= S`. For an abstraction `A`, the target is `exists z, forall x, (x in z <-> A(x))`, with the exact de Bruijn formula given by `Protocol.class_setness`. This branch computes the abstraction predicate with shift `2` and element index `0`, then uses ten native interner operations; its sufficient domain is that predicate's readiness checks and `n+g(A)+10 <= S`. Both branches preserve canonical formulas, backward references, represented classes and logical storage, with no fatal error. This theorem constructs the formula that the total canonical certification command checks below.

The actual native axiom helpers for tags `0,1,2,3,4,5,6,7,8` are proved against `SetTheory.axiom_formula`, including an object-calculus derivation of the exact result, canonical IDs, preserved topology where required, the clear fatal-error flag and the axiom success flag. K, S, double-negation elimination, reflexivity and the three equality/substitution families require at most `2,6,3,1,5,5,5` new formula nodes respectively. The relevant input formula IDs must exist; raw variable indices must be words. The sufficient arena domain includes that allowance below `S` and any requested reserve. Double-negation elimination additionally requires falsity at formula ID `0`.

Universal instantiation (tag `3`) is proved in [`AxiomInstRefinement.v`](../imperative/proof/AxiomInstRefinement.v). For body `p` at ID `r` and variable argument `j`, actual execution returns `(forall p) -> rename (instantiate j) p`, with capture avoidance under every inner binder. With `G=(r+1)^2`, its sufficient domain requires the canonical/backward source arena, falsity at ID `0`, the native metadata/SipHash readiness conditions, `5*G+1 <= U`, a variable bound `B` on every atom of `p`, `B+j <= U`, binder height at most `U`, and `n+G+2 <= S` (plus any requested reserve). The two extra nodes account for the quantified premise and outer implication. The result preserves logical registries and backward topology and has a `SetTheory.d_inst` derivation; no native rename execution is assumed as a premise.

Universal distribution (tag `4`) is proved in [`AxiomDistRefinement.v`](../imperative/proof/AxiomDistRefinement.v). For represented formulas `p,q`, actual execution builds `(forall (shift p -> q)) -> (p -> forall q)` and returns its object-calculus derivation. The shift is capture avoiding under every inner binder. With `p` at source ID `r` and `G=(r+1)^2`, the sufficient domain includes the canonical/backward arena, falsity at ID `0`, the native metadata/SipHash conditions, checked traversal fuel, source-variable and binder-depth bounds, and `n+G+5 <= S` plus any requested reserve. The five extra nodes form the final quantified implication circuit. Canonical IDs, topology, logical registries and the zero fatal-error flag are preserved.

[AxiomFixedRefinement.v](../imperative/proof/AxiomFixedRefinement.v) proves actual native helper execution for Extensionality, Foundation, Pairing, Union, Power, Infinity and Choice (tags `9–14,17`). The generic theorem constructs each native interner circuit and returns exactly `SetTheory.axiom_formula` with its object-calculus derivation, canonical storage, backward topology, logical registry preservation and zero fatal error, under an explicit formula-allocation allowance. [NativeAxiomBuilder.v](../imperative/proof/NativeAxiomBuilder.v) connects each fixed circuit to its actual generated handler. [AxiomFixedProtocol.v](../imperative/proof/AxiomFixedProtocol.v) composes all seven families through actual canonical command-11 parsing, helper execution and history append, with exact `OK` reply/flush/unread suffix, `Protocol.step` and logical safety preservation. [AxiomSeparationRefinement.v](../imperative/proof/AxiomSeparationRefinement.v) and [AxiomReplacementRefinement.v](../imperative/proof/AxiomReplacementRefinement.v) prove the native Separation and Replacement builders (tags `15,16`), with exact formulas and derivations, actual memoized renaming, canonical arena extension, topology and preserved registries. Their sufficient allocation allowances are `(root+1)^2+14` and `3*(root+1)^2+21` respectively, with explicit source-variable, binder-height and traversal-fuel bounds. [AxiomLogicalProtocol.v](../imperative/proof/AxiomLogicalProtocol.v) and [AxiomRenamingProtocol.v](../imperative/proof/AxiomRenamingProtocol.v) complete canonical command-11 acceptance composition for the other ten axiom families; together the four protocol modules cover every axiom tag. These command-level results start at the pending opcode byte and require their stated resources; the actual-main theorem below supplies startup, resource preservation and session composition.

[`AxiomReflProtocol.generated_reflexivity`](../imperative/proof/AxiomReflProtocol.v) proves the reflexivity family of command `11` through canonical separator-terminated wire parsing. Starting with the first opcode byte in the reader's pending cell, `11 5 i b c` with word-sized arguments, one formula slot of allowance and an available history slot executes the actual axiom helper and history append, replies `OK h` for the prior history length `h`, and leaves the exact tail unread. The logical step appends the canonical formula ID of `v_i = v_i`, for which an object-calculus derivation is proved. Formula/class/history representations and the logical history/name safety invariant are preserved. The fields `b,c` are parsed but unused by this axiom family. The complete startup/dialogue composition is now supplied by `NativeGeneralSession.required` below.

[`AxiomReject.v`](../imperative/proof/AxiomReject.v) proves that a selector outside `0–17` clears the axiom success flag and preserves the formula arena. [`AxiomCommand.v`](../imperative/proof/AxiomCommand.v) proves actual command dispatch, history append and replies from the four reads and helper execution; its generic interface is discharged by the reflexivity and seven fixed-ZFC protocol theorems above.

[`ClassCertifyTotal.generated_total_protocol`](../imperative/proof/ClassCertifyTotal.v) proves total command `14` for canonical separator-terminated requests with a valid name and word-sized theorem index. Existing class bindings with valid active theorem indices use the setness helper's sufficient resource domain; absent names, wrong binding kinds and invalid history indices need no setness expansion. Native canonical formula-ID equality is proved equivalent to the proposed theorem being exactly `Protocol.class_setness` of that class. A match certifies the binding and replies `OK classID`; mismatches and all invalid lookup/history cases reply `NO`. Every case includes exact flushed output and unread suffix, a logical protocol step, and represented formulas, classes, history, names and schema metadata. [`ClassCertifyInvariant.generated_total_invariant`](../imperative/proof/ClassCertifyInvariant.v) additionally preserves the four metadata/SipHash/token/print-buffer allocation lengths, zero fatal error, backward topology, well-formed class storage, logical name/history validity and unique binding keys. Classes, history and schema expressions stay fixed; formulas extend their earlier prefix.

[`SchemaClass.generated_refines`](../imperative/proof/SchemaClass.v) proves the actual internal class allocator appends the decoded class, preserves earlier records and formula meanings, returns the new class ID and retains the requested class-count reserve. Its checked overflow branch is proved separately. [`SchemaShiftClass.v`](../imperative/proof/SchemaShiftClass.v) proves zero-depth identity and positive shifts for both native class-record forms. Set-variable classes add the depth to their variable index under a word bound. Abstractions invoke actual memoized shifting under the distinguished class binder and append exactly `Schemata.shifted_class`; sufficient conditions include source-variable, binder-depth, traversal-fuel, formula-allocation and class-count bounds. Both preserve I/O. These are internal helper refinements; total descriptor construction is now covered below, while complete instance evaluation is covered below under its explicit resource condition.

[`SchemaCheck.generated_total`](../imperative/proof/SchemaCheck.v) proves actual native reference/type validation against represented schema metadata for every node index. Missing indices clear the accumulated validation flag and leave its arity accumulator unchanged. Existing nodes preserve the flag only when their stored type matches the expected type, and replace the accumulator by its maximum with that node's arity. The metadata representation, formula arena and input/output remain unchanged. This checks type and arity metadata; full descriptor meanings are established separately by `SchemaRepresentation` and total canonical construction below; complete instance evaluation is covered below under its explicit resource condition.

[`AxiomRejectionProtocol.generated_rejected`](../imperative/proof/AxiomRejectionProtocol.v) closes canonical command-11 rejection for every unsupported selector or invalid required formula reference. Its premise is the mathematical `Protocol.concrete_axiom = None`; it constructs actual command execution and the exact `NO` flush/unread suffix, preserves all five logical representations, and needs no helper-execution or allocation-success premise.

[`SchemaNodeTotal.generated_total`](../imperative/proof/SchemaNodeTotal.v) proves total canonical command `22`, including all twelve descriptor families and rejection of invalid references, wrong types, invalid metavariable indices and unknown kinds. The theorem constructively decides `Protocol.builds_node`, executes the real parser/validator/allocator/reply, and establishes the exact observed protocol transition, complete descriptor semantics, all five state representations and `Guarantees.safe`. Saved proof nodes retain their object-calculus proofs. The accepted branch needs a representable next schema ID; a separate rejection theorem does not. Canonical token/buffer/word-size premises remain explicit. This proves descriptor construction; the complete command-24 theorem and its resource domain are described below. The end-to-end theorem below composes these commands over finite canonical dialogues.

[`SchemaMarkingRun.v`](../imperative/proof/SchemaMarkingRun.v) proves actual initialization and complete dependency marking, with a mark exactly when the expression/binder-depth pair is reachable. [`SchemaEvaluationInitial.generated_body`](../imperative/proof/SchemaEvaluationInitial.v) now composes initialization, marking, all instruction families, both native loops and result publication. [`SchemaInstanceEntry.generated`](../imperative/proof/SchemaInstanceEntry.v) lifts this to actual native procedure execution with all five logical representations, preserved history/names, topology and I/O, and either the specified inferred ZFC theorem or correct instantiation failure. Its finite mathematical `fits` condition contains no program-execution premise; it remains a strong sufficient domain. [`SchemaEvaluationBudget.v`](../imperative/proof/SchemaEvaluationBudget.v) proves this condition for arbitrary literal/saved-proof/MP graphs, and [`SchemaEvaluationFree.generated`](../imperative/proof/SchemaEvaluationFree.v) gives their execution under a checked grid-size bound. [`SchemaEvaluationLinearEntry.generated`](../imperative/proof/SchemaEvaluationLinearEntry.v) covers allocating implication/universal/generalization and literal/saved-proof/MP schemas under the concrete budget `formula count + (root ID + 1)^2 <= 2^63-1`; it assumes neither `fits` nor future native success. Each processed cell allocates at most one formula in this fragment. [`SchemaEvaluationSetEntry.generated`](../imperative/proof/SchemaEvaluationSetEntry.v) adds actual class-parameter equality/membership and nonrenaming axiom schemata with the concrete bound `formula count + 42*(root ID + 1)^2 <= 2^63-1`. In this fragment every stored class is a set-variable class, reachable metavariables occur at depth zero, no abstraction-class node is evaluated, and axiom tags `3`, `4`, `15`, `16` are excluded. Implication, universal quantification, generalization, MP, literals and saved proofs remain supported wherever those restrictions hold. The theorem proves complete native procedure execution without a `fits` or helper-execution premise. Arbitrary abstraction-class substitutions, metavariables under binders and renaming axioms still need practical general budgets. [`SchemaInstanceArguments.v`](../imperative/proof/SchemaInstanceArguments.v) proves the actual canonical argument loop, exact vector storage, accumulated invalid-class rejection and preservation of all five representations. [`SchemaInstanceCommand.generated_canonical`](../imperative/proof/SchemaInstanceCommand.v) proves the complete actual command `24`, from pending opcode byte through parsing, lookup, argument validation, evaluation, history insertion or rejection and the final reply. Its `canonical_wire` theorem identifies this input with `Protocol.request_bytes`. The result includes the exact cumulative output at the reply flush, unread suffix, `Protocol.step`, all five represented logical components, zero fatal flag and `Guarantees.safe`. [`SchemaInstanceSetCommand.generated_canonical`](../imperative/proof/SchemaInstanceSetCommand.v) proves the complete command for the set-parameter fragment using only its initial schema graph, set-class condition and numeric formula/history bounds. Its parser proof derives the supplied argument meanings; the external capacity predicate contains neither `fits`, future parser states nor an assumed helper execution. The pure resource condition applies only when a named schema, correct arity and valid class arguments reach evaluation; missing names, wrong binding kinds, arity mismatches and invalid class IDs are covered as rejections. General scalar resource bounds and complete session composition are now proved below.

[`NativeStartup.main_to_commands`](../imperative/proof/NativeStartup.v) strengthens the actual seed/main prefix with all five representations of `Protocol.initial`, backward topology, exact allocation sizes and the two handshake snapshots. [`CommandSchemaFrame.v`](../imperative/proof/CommandSchemaFrame.v) preserves complete schema descriptor meanings through all native handlers except construction (`22`), including formula/class extensions and changes to names/history. [`NativeCommandFrames.v`](../imperative/proof/NativeCommandFrames.v) connects actual whole-command execution to preservation of immutable names and schema storage for nonbinding commands. [`NativeSchemaLift.v`](../imperative/proof/NativeSchemaLift.v) also handles name-changing commands, transporting complete schema meanings across their logical transitions. The total naming endpoints in [`NativeNamedCommands.v`](../imperative/proof/NativeNamedCommands.v) preserve this full state, including saved schema certificates. These provide state invariants for the complete session theorem below.

[`NativeSession.generated_seed_simple_quit`](../imperative/proof/NativeSession.v) proves complete actual `main` sessions for any finite canonical list of commands `1–4` followed by quit. Its premises are valid unsigned seeds/arguments and `1 + number of requests <= 2^63-1`; there is no execution premise. The result includes the complete seed/reply flush schedule, `Protocol.dialogue`, all five state representations, logical safety, final stdout and the exact unread quit suffix. This formula-construction fragment does not establish the general proof-checker session contract.

[`NativeSessionProof.generated_seed_simple_reflexivity_quit`](../imperative/proof/NativeSessionProof.v) extends the complete session result with an actual proof operation: any finite canonical commands `1–4`, reflexivity `11 5 variable 0 0`, then quit. Under `number of prefix requests + 2 <= 2^63-1`, it proves actual main execution and all flushes, logical safety, all five representations, and the final theorem at history index `0` with an object-calculus derivation. This earlier theorem covers theorem production; the all-opcode session theorem below supplies general composition.

[`NativeFullDispatcher.generated_canonical`](../imperative/proof/NativeFullDispatcher.v) covers every positive opcode `1–26` from a well-shaped canonical request at the pending-byte boundary. Under the stated graph and resource conditions it constructs actual execution, the exact single reply/flush and unread suffix, `Protocol.step`, all five native state representations, final input/output, and preserved logical safety. The conditions for class expansion, axiom construction, certification and schema instantiation are explicit mathematical resource premises; no successful-helper-execution premise is used. The boundary theorems also cover mathematical rejection.

[`NativeDialogueComposition.v`](../imperative/proof/NativeDialogueComposition.v) supplies a finite-session and actual-main composition theorem, including `Spec.required`, conditional on its concrete command/initialization interfaces. `NativeGeneralSession.required` discharges the interfaces using preserved graph, name-storage, formula, class and index bounds. Whole-arena index bounds now cover actual substitution, all axiom builders and all twelve schema families. [`SchemaEvaluationIndexSchedule.v`](../imperative/proof/SchemaEvaluationIndexSchedule.v) computes a finite capacity check; the general command-24 theorem uses its scalar resource domain without an older `fits` premise.

[`NativeBasicSession.required`](../imperative/proof/NativeBasicSession.v) closes `Spec.required` for arbitrary sessions of the twenty basic commands (`1–6`, `9`, `10`, `12`, `13`, `15–21`, `23`, `25`, `26`), quit and EOF under explicit numeric count/name-storage bounds. This is a concrete actual-main theorem; it has no command-interface or successful-execution premise. The all-opcode theorem below extends this earlier fragment.

**The end-to-end contract is proved for canonical sessions in the explicit numeric domain.** [`NativeGeneralSession.required`](../imperative/proof/NativeGeneralSession.v) proves `Spec.required` for all 26 positive opcodes, all eighteen axiom tags, EOF and quit. [`NativeVerifiedDomain.native_required`](../imperative/proof/NativeVerifiedDomain.v) binds the union of this domain and the practical set-schema domain to the exact generated entry point and initial arrays. The theorem constructs successful actual execution, every flush snapshot, cumulative output and the exact unread suffix, and establishes `Guarantees.safe` for the final state. Its public premises are unsigned seeds, `Forall Protocol.shape` and the finite Boolean budget check described next. It assumes no successful execution, helper outcome, command-interface theorem or future-state readiness condition. No Rocq axioms or admissions are added.

Additional byte-level cases have separate actual-main proofs. [`NativeWhitespaceDialogue.required`](../imperative/proof/NativeWhitespaceDialogue.v) proves an arbitrary canonical dialogue in the verified capacity domain with arbitrary runs of spaces, tabs, CRs or LFs before the first seed and between the two canonical seed numbers, and an independently chosen separator after each seed. It proves exact flush observations. [`NativeMalformedSeedExample.v`](../imperative/proof/NativeMalformedSeedExample.v) covers a missing seed, an overflowing first seed, and any single non-digit, non-separator byte as the first seed, second seed (with first seed zero), or first opcode (with both seeds zero), each with exact `ERR` output and flushes. [`NativeWhitespaceSuffixDialogue.generated_main`](../imperative/proof/NativeWhitespaceSuffixDialogue.v) combines arbitrary leading/inter-seed separator runs with either capacity plan and proves that a canonical positive-command prefix followed by quit leaves an arbitrary byte suffix exactly unread, including at every flush. [`NativeBadSeed.actual_bad_first_seed`](../imperative/proof/NativeBadSeed.v) additionally proves exact actual-main error behavior for a separator-terminated first seed token of up to 1024 bytes whose decimal prefix fits a word and is followed by a non-digit, with arbitrary remaining token bytes and input suffix. [`NativeOverflowSeed.actual_overflow_first_seed`](../imperative/proof/NativeOverflowSeed.v) establishes the corresponding actual-main result when the next digit first overflows an unsigned word. [`NativeTooLongSeed.actual_too_long_first_seed`](../imperative/proof/NativeTooLongSeed.v) proves that an overlong first seed with no leading separators consumes exactly its first 1025 non-separator bytes, emits `ERR`, and leaves the remainder unread. [`NativeTooLongSecondSeed.actual_too_long_second_seed`](../imperative/proof/NativeTooLongSecondSeed.v) covers the second seed following a canonical first seed and a space. [`NativeTooLongOpcodeMain.v`](../imperative/proof/NativeTooLongOpcodeMain.v) covers an overlong first opcode after valid canonical seeds. [`NativeMalformedOpcodeMain.v`](../imperative/proof/NativeMalformedOpcodeMain.v) covers a separator-terminated first opcode with a fitting decimal prefix followed by a non-digit or first overflowing digit, with no leading whitespace. [`NativeAllWhitespaceDialogue.v`](../imperative/proof/NativeAllWhitespaceDialogue.v) combines arbitrary separator runs around the seed handshake and before each positive command under either capacity plan, including EOF termination or quit with arbitrary whitespace before quit and an arbitrary unread suffix. [`NativeAllTrailingWhitespace.eof`](../imperative/proof/NativeAllTrailingWhitespace.v) additionally allows any finite run of separators after the last command before EOF, and proves that it causes no extra reply or flush while preserving the represented logical state. [`NativeMalformedPrefixDialogue.flexible_seed`](../imperative/proof/NativeMalformedPrefixDialogue.v) covers a separator-terminated malformed or overflowing opcode after any verified positive-command prefix under either capacity plan, with exact `ERR` output, flush observations and unread suffix. Its seed values use canonical digits with flexible surrounding whitespace, and the malformed opcode starts immediately after the prefix. [`NativeMalformedWhitespaceUnified.generated_main`](../imperative/proof/NativeMalformedWhitespaceUnified.v) combines the empty and nonempty whitespace cases before a malformed opcode, together with flexible seed whitespace. [`NativeWhitespaceMalformedEOFDialogue.flexible_seeds`](../imperative/proof/NativeWhitespaceMalformedEOFDialogue.v) covers the EOF-terminated malformed-opcode case after a nonempty whitespace prefix. [`NativeWhitespaceTooLongDialogue.flexible_seeds`](../imperative/proof/NativeWhitespaceTooLongDialogue.v) covers overlong opcodes after a nonempty whitespace prefix, including the exact unread suffix. [`NativeAnyWhitespaceErrorDialogue`](../imperative/proof/NativeAnyWhitespaceErrorDialogue.v) combines empty and nonempty whitespace prefixes for these malformed, EOF-terminated and overlong opcode cases. Seed digits and the fields within each command remain canonically encoded. These results do not yet constitute a general malformed-stream parser theorem.

### Exact proved resource domain

The contract's resource predicate is [`NativeVerifiedDomain.within_capacity`](../imperative/proof/NativeVerifiedDomain.v): the Boolean OR of two pure finite checks on the request list, [`NativeBudgetPlan.domain`](../imperative/proof/NativeBudgetPlan.v) and [`NativeSetBudgetPlan.domain`](../imperative/proof/NativeSetBudgetPlan.v). A dialogue needs to pass either entire check; the two plans are not switched between commands. The predicate evaluates the practical set-schema check first and only evaluates the general check if that fails. The general fallback can still be expensive to compute. These are mathematical sufficient checks for the theorem; bounds are not additional protocol fields. The checker independently performs its native overflow and traversal-fuel checks. The general plan is described first. The union is a sufficient domain, not a complete characterization of all workloads that can succeed. It may reject feasible schema instances because it bounds every possible grid cell conservatively. Malformed byte streams are outside `Forall Protocol.shape`; their `ERR` behavior remains covered by native parser regressions.

Let `U = 2^64−1`, `J = 2^63−1`, and `N` be the maximum numeric argument anywhere in the request list, or zero when there are none. The check starts with seven natural-number bounds: formula count `F=1`, variable-index bound `I=max(3,N)`, class count `C=0`, history count `H=0`, binding count `T=0`, expression count `E=0`, and permanent name bytes `L=0`. It processes positive commands in order, stops at quit, and accepts EOF. The bounds advance as follows; the input `N` stays fixed.

| Opcode                  | Next formula bound                                         | Next index bound                                            |
| ----------------------- | ---------------------------------------------------------- | ----------------------------------------------------------- |
| `1–4`, `13`             | `F+1`                                                      | `max(I,N)`                                                  |
| `7`                     | `F+2F²+13`                                                 | `I+2`                                                       |
| `8`                     | `F+2F²+13`                                                 | `2I+3`                                                      |
| `11`, tag `t`           | `F+A(t,F)`                                                 | `I+3N+4`                                                    |
| `14`                    | `F+F²+10`                                                  | `I+2`                                                       |
| `22`                    | `F`                                                        | `I`                                                         |
| `24`                    | iterate `x ↦ x+3x²+42` exactly `E²` times, starting at `F` | iterate `x ↦ 2x+E+3N+4` exactly `E²` times, starting at `I` |
| Other positive commands | `F`                                                        | `max(I,N)`                                                  |

[`NativeFastDomain.native_required`](../imperative/proof/NativeFastDomain.v) provides an equivalent contract whose general fallback checks the schema formula and index recurrences using binary integers and stops as soon as either exceeds its word limit. Its equivalence to the original predicate is proved in [`BoundedIteration.v`](../imperative/proof/BoundedIteration.v). When those preflights succeed it still invokes the original natural-number check, so this does not establish a general execution-time bound for evaluating the predicate. [`NativeFastExample.v`](../imperative/proof/NativeFastExample.v) checks a concrete expanding-schema rejection by computation.

The axiom allocation allowance `A(t,F)` is `2,6,3,F²+2,F²+5,1,5,5,5,10,15,8,10,9,33,F²+14,3F²+21,42` for tags `0–17`, respectively, and zero for unsupported tags. Since the arena starts with falsity, `F` stays positive. Classes advance to `C+E²` on opcode `24`, and to `C+1` on other positive commands. Expressions advance to `E+1` only on `22`. Every positive command advances `H` and `T` by one and `L` by 1024, even when its actual history/name storage does not grow.

Before advancing a positive command, the check requires `F≤J`, next `F≤J`, next `I≤U`, and `C+1,H+1,T+1,E+1,L+1024≤U`. It also checks the opcode range and argument bound. The following additional sufficient guards use the bounds _before_ that command:

- `7`: `F+2F²+6≤J`, `5F²+1≤U`, `I+2≤U`.
- `8`: `F+2F²+13≤J`, `5F²+1≤U`, `2I+3≤U`.
- `11`: `F+A(t,F)≤J`, `5F²+1≤U`, `I+N+2≤U`.
- `14`: `F+F²+10≤J`, `5F²+1≤U`, `I+2≤U`.
- `24`: its next formula/index bounds fit `J`/`U`, `5(next F)²+1≤U`, and `C+E²+1≤U`.

[`NativeUniformResources.v`](../imperative/proof/NativeUniformResources.v) proves that these guards imply the native helpers' resource conditions. [`NativeUniformCommand.v`](../imperative/proof/NativeUniformCommand.v) proves the resulting bounds after each actual command. The session proof carries them through the loop. Thus the capacity premise is an explicit arithmetic check, not an assumption that the implementation behaves correctly.

[`NativeGeneralExamples.checked_session`](../imperative/proof/NativeGeneralExamples.v) supplies a non-vacuous example: a named set-variable class, reflexivity theorem, named saved-theorem schema, accepted instantiation, theorem naming/recall and a rejected mismatching certificate. Its computed formula bounds are `2`, then `56` after instantiation, then `3202` after certification; the actual schema reply is proved to be `OK 1`.

### Practical plan for set-valued class parameters

The second check admits meaningful class-metavariable schemas without repeatedly squaring the formula bound. Every stored class must remain a set-variable class, and every reachable schema cell stays at binder depth zero. These are maintained invariants proved from the request restrictions, not assumptions about later states. It admits basic commands `1–5`, `9`, `10`, `12`, `13`, `15–21`, `23`, `25`, `26` (excluding class abstraction `6`), direct axiom command `11` except tags `3`, `4`, `15`, `16`, schema construction `22` except kinds `3`, `7`, `10` and those same four axiom tags within kind `8`, and schema instantiation `24`. Quit and EOF are allowed. Commands `7`, `8`, and `14` use the general plan instead; equality and membership _schema nodes_ (kinds `4` and `5`) are admitted by this practical plan.

Start with `F=1` and `C=H=T=E=L=0`. For each positive command, set the next formula bound to `F+42E²` for `24`, to `F+42` for `11`, to `F` for `22`, and to `F+1` otherwise. Set `C,H,T` to their previous bounds plus one, increase `E` only on `22`, and increase `L` by 1024. Before advancing, require the allowed-command condition above, opcode at most 26, current and next formula bounds at most `J`, and `C+1,H+1,T+1,E+1,L+1024` at most `U`. As in the general plan, stop checking at quit and accept EOF. Canonical shape separately requires all numeric arguments to fit unsigned words and all names to be valid.

[`NativeClassSchemaExample.checked_session`](../imperative/proof/NativeClassSchemaExample.v) proves actual seeded execution of [`schematic-set-k.txt`](../imperative/schematic-set-k.txt): two class metavariables, equality and membership nodes, a named K proof template of arity two, and successful instantiation with reply `OK 0`. Its capacity check is proved by computation. Its logical dialogue lemma forces that reply for every permitted storage-retention choice, so the example cannot be satisfied by merely rejecting the schema.

The allowance `42E²` bounds actual formula allocation for all possible cells of this flat schema grid, including failed checks. Instantiation preserves the exact class arena, and the proof carries these quantitative facts through the actual command loop. No substitution traversal or variable-index envelope is needed for this branch because it excludes operations requiring renaming. Both branches prove the same `Spec.required`, including mandatory acceptance when the applicable mathematical rule succeeds, exact I/O and `Guarantees.safe`. The restriction is on the **proved capacity domain**, not on the implemented protocol: other schema families remain implemented and can be proved through the general branch when its check passes.

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
