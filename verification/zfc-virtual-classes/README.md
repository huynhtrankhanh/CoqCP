# ZFC and virtual-class proof checker

The primary implementation is [programs/ZFCProofChecker.js](../../programs/ZFCProofChecker.js), written in IIL and compiled to C++ and Rocq. Its [module configuration](../../programs/ZFCProofChecker.module.json) participates in the normal dual-target CI build. Regenerate it with:

```sh
python3 programs/ZFCProofChecker/generate.py
npm --prefix compiler run build
node compiler/dist/cli.js '?json' programs/ZFCProofChecker.module.json
g++ -std=c++20 -O2 generated-cpp/ZFCProofChecker.cpp -o /tmp/zfc-checker
```

The command reader runs until EOF with `tapeEnd`; it also exits on quit or a fatal error. There is no fixed command-count limit. `tapeEnd` binds an `int8` byte, and body reads advance the same tape. The explicit, pure substitution traversal has its own finite work budget; exhausting it is a fatal error, never permission to accept a partial substitution.

## Seed handshake and bytes

Before reading input, the checker prints `SEED\n` and flushes. Send two unsigned 64-bit decimal words `k0 k1\n`. The checker installs them as the 128-bit SipHash key and prints `READY\n`, flushed before commands are read. Missing, malformed or overflowing seed words produce `ERR\n` and terminate. For example:

```text
checker: SEED
client:  506097522914230528 1084818905618843912
checker: READY
client:  11 5 0 0 0
checker: OK 0
client:  20 0 reflexive
checker: OK 1
client:  0
checker: BYE
```

Choose an unpredictable key in a trusted client when defending against adversarial formula inputs; a public or attacker-chosen key does not provide the same hash-flooding protection. Fixed seeds in examples and tests are for reproducibility.

All input is token based, with space, tab, CR and LF separators. Commands may share a line, and a final token may end at EOF. Integers must be decimal values from 0 through `2^64-1`; signs and other characters are rejected. Names are nonempty byte tokens of at most 1024 bytes. A missing argument, malformed integer, oversized name, unsupported opcode, checked arithmetic overflow, or traversal exhaustion produces `ERR\n` and terminates. Invalid IDs, wrong object types, duplicate names and failed proof checks produce `NO\n`; the checker continues.

Every reply ends in LF and is flushed immediately. EOF between commands produces no additional reply. `0` produces `BYE\n`, stops immediately and leaves subsequent bytes unread. Host allocation failures are outside the formal execution model.

## Requests and replies

Formula ID `0` is falsity. Formula, class, history and schema-expression IDs occupy separate arenas. History IDs are zero based, oldest first; undo/reset permits reuse of history slots. Formula/class/schema-expression arenas remain allocated. Successful construction returns `OK id\n`. Proof operations return the appended history index. Naming operations return the captured formula/class/schema-root ID.

| Request | Effect |
| --- | --- |
| `0` | Quit |
| `1 i j`, `2 i j` | Construct equality or membership of set variables |
| `3 p q`, `4 p` | Construct implication or universal quantification |
| `5 i`, `6 p` | Construct a set-variable class or predicate abstraction |
| `7 a b`, `8 a b` | Expand class equality or membership into a core formula |
| `9 classID name`, `10 name` | Define a class name, or retrieve its class ID |
| `11 tag a b c` | Check an axiom instance and append its theorem |
| `12 implicationIndex antecedentIndex` | Modus ponens, with exact antecedent matching |
| `13 theoremIndex` | Generalize a theorem |
| `14 name theoremIndex` | Certify a named class as a set using a checked representing-set existence theorem |
| `15 name` | Return `CLASS` or `SET` for a class name |
| `16`, `17` | Undo the latest theorem, or reset active history |
| `18 theoremIndex formulaID` | Append only if the exact formula matches |
| `19 theoremIndex` | Return its formula ID |
| `20 theoremIndex name` | Save an immutable theorem snapshot |
| `21 name` | Append the theorem snapshot to current history |
| `22 kind a b c d` | Construct a typed schema-expression node; see below |
| `23 proofNode name` | Name a schema certificate |
| `24 name count classID...` | Supply exactly `count` class arguments and check a schema instance |
| `25 name` | Return `CLASS`, `THEOREM` or `SCHEMA` |
| `26 name` | Return a schema's required argument count as `OK count` |

All names share one immutable namespace. A theorem name captures its formula, not a mutable history index; it remains valid after undo/reset and slot reuse. Class names, set certifications and named schemata also persist. A class cannot be used as a theorem name or vice versa. Merely naming a class does not certify that it is a set.

The axiom tags `0` through `17` are K, S, DNE, universal instantiation, universal distribution, equality reflexivity, left membership substitution, right membership substitution, equality transitivity, Extensionality, Foundation, Pairing, Union, Power, Infinity, Separation, Replacement and Choice. Opcode `11` always takes three numeric arguments after the tag. Formula parameters are formula IDs; variable parameters are raw de Bruijn indices. There is no command to add an axiom.

## Class-metavariable schemata

Opcode `22` always consumes a kind and four numeric fields. Unused fields may be zero. Its result is a schema-expression ID. All dependencies must be earlier nodes, and their types are checked.

| Kind | Fields used | Result type and meaning |
| --- | --- | --- |
| `0` | `a = metavariable index` | Class metavariable |
| `1` | `a = class ID` | Literal class |
| `2` | `a = formula ID` | Literal core formula |
| `3` | `a = formula node` | Class abstraction |
| `4`, `5` | `a,b = class nodes` | Formula: class equality or membership |
| `6` | `a,b = formula nodes` | Formula: implication |
| `7` | `a = formula node` | Formula: universal quantification |
| `8` | `a = axiom tag; b,c,d = its arguments` | Certificate: axiom instance |
| `9` | `a,b = certificate nodes` | Certificate: modus ponens |
| `10` | `a = certificate node` | Certificate: generalization |
| `11` | `a = current history index` | Certificate: immutable theorem snapshot |

For kind `8`, formula arguments are **schema-formula node IDs**; variable arguments remain raw indices, using the same tag convention as opcode `11`. The schema arity is one plus its largest reachable metavariable index, or zero if none occurs. Unreachable earlier nodes do not contribute. Literal classes/formulas use the de Bruijn context of their position; metavariable substitutions preserve their outside parameters by shifting them under universal quantifiers, generalization and class-abstraction binders.

A named schema is a proof-certificate template, not an unchecked theorem assertion. Each application expands its class arguments and rechecks every reachable axiom/inference node. Ill-typed nodes cannot be constructed, and an invalid MP template is rejected when instantiated. Only the checked root theorem is appended; intermediate proof nodes never enter public history. A failed instance leaves theorem history and names unchanged, although private formula/class allocations may remain. Wrong argument counts and bad class IDs consume the declared arguments and return `NO`, preserving token synchronization.

[schematic-identity.txt](imperative/schematic-identity.txt) derives and names the schema `∀x, (x ∈ C → x ∈ C)` from K/S and MP, applies it to a class and names its resulting theorem. [bounded-class.txt](imperative/bounded-class.txt) names a bounded class and certifies it as a set using Separation. Example files include a reproducible seed handshake input.

## Interning and validation

Formula interning uses **SipHash-2-4** of the 24 bytes encoding `(tag,a,b)` as three little-endian 64-bit words. Bucket heads and node links use ID-plus-one so zero is the empty sentinel. Collision resolution compares all three original words. The table doubles at load factor one and rebuilds links without moving formula IDs. Lookup/insertion is expected amortized constant time; a bucket collision never establishes formula equality. Class/schema construction reuses this same canonical formula arena.

The actual IIL hash is checked against the published SipHash 24-byte test vector and 66 additional independent oracle cases. The Rocq build checks the published vector for the actual generated hash procedure. [SipHash.v](imperative/proof/SipHash.v) additionally proves the general execution refinement for every seed and tuple: termination, the full digest, the bucket index and its bounds, preservation of every other array and metadata cell, and unchanged input/output. [HashScan.v](imperative/proof/HashScan.v) proves the generated collision-chain scan terminates, returns only exact tuple matches, and finds every reachable match within its iteration budget under descending-link bounds. [InternTail.v](imperative/proof/InternTail.v) proves the actual generated insertion continuation, including overflow rejection, preserved earlier IDs and descending links. [HashTable.v](imperative/proof/HashTable.v) proves bucket reachability and uniqueness survive insertion, a scan miss implies freshness, and canonical lookup returns the original ID. [Rehash.v](imperative/proof/Rehash.v) proves the generated rehash iteration executes SipHash and preserves processed-entry reachability. These proofs do not assume that hashing is injective. Native tests cover collisions, repeated rehashing, immutable IDs, names, schema typing, capture avoidance, failed instances, seed failures, EOF and interactive flushing.

```sh
python3 verification/zfc-virtual-classes/imperative/test_siphash.py
python3 verification/zfc-virtual-classes/imperative/build.py --output .verification/zfc-native
python3 verification/zfc-virtual-classes/build.py --output .verification/zfc-reference
python3 verification/zfc-virtual-classes/imperative/test.py \
  --binary .verification/zfc-native/zfc-checker \
  --reference .verification/zfc-reference/zfc-checker -v
```

## Formal contract and current proof boundary

[spec/Spec.v](spec/Spec.v) is the primary **end-to-end** contract. [Protocol.v](spec/Protocol.v) defines the request shapes and byte encoding, seed exchange, all 27 command meanings, immutable names and histories, schema certificates, canonical formula allocation, rejection, exact replies, successful termination, input remaining after quit/EOF, and the cumulative stdout and unread input at **every flush**. The capacity domain is a trusted resource premise, not a candidate-selected implementation or a successful-execution premise. The generated build creates `Code/NativeContract.v`, binding this contract to the actual generated entry point and initial arrays. Canonical, resource-fitting dialogues are its present formal domain; parser-error regressions additionally exercise malformed streams.

[candidate/SchemataSoundness.v](candidate/SchemataSoundness.v) proves that every accepted instantiated schema has a ZFC derivation, without global assumptions. [Reference.v](spec/Reference.v) retains the separate Gallina certificate-checker contract. Its complete derivation-checking, session-safety and completeness proofs now satisfy that scoped signature. Class elimination and checked set certification remain proved. The S-expression reference frontend is an independent testing oracle for the core/class language, not the native numeric protocol.

**The full native end-to-end execution refinement is still open.** Current generated-code proofs cover index substitution, overflow, stack push, formatter memory preservation, general SipHash execution, collision-chain lookup, insertion and individual rehash iterations. The table invariants establish freshness, uniqueness and canonical lookup. The complete rehash loop, full interner composition and formula representation, schema evaluator, parser/command composition and final main theorem still require execution refinements. The previous execution proofs tied to the removed linear interner no longer describe this implementation and have been removed from the active tree. The build records the remaining native obligations and does not claim adversarial acceptance. No extra Rocq axioms or admitted proofs are added.

The set-model/constructibility research and consistency obligations were removed from the active development at the user's request. The prior work remains recoverable from Git revision `f8f5c24`.
