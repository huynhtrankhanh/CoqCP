(** * rocq#22389 — nested mutual cofixpoints are all checked at one rectree

    rocq-prover/rocq#22389, filed 2026-08-20 13:22 UTC by `yannl35133`, **OPEN**,
    fix PR unmerged.  The issue body says *"Found by an LLM and @dselsam"*.

    ** Category (a): a closed proof of `False` with every audit channel silent

    Upstream's statement: *"Even if they don't have the same types, all mutual
    cofixpoints that are nested are checked at the same ambient rectree.
    Generally, we don't support recursive calls in nested mutual cofixpoints
    outside of the main cofix."*

    The inner block declares `f : C I` and `g : D (C I) I`, whose recursive trees
    differ.  Both are checked against the tree of the enclosing `CoFixpoint
    cycle`, so `g`'s occurrence of `cycle` under the **inductive** constructor
    `ic` is accepted as if it were a corecursive occurrence in `f`'s tree.  That
    builds an infinitely deep `I`, and a structural `Fixpoint` over it returns
    `False`.

    `Unset Elimination Schemes` here is cosmetic, not load-bearing: without it
    the file still compiles to the same `False`, printing six copies of the
    `register-all` warning about `I` being nested through `C`.  Measured both
    ways on 9.2.

    ** Measured on Rocq 9.2 (OCaml 4.14.2), the current stable release

      - `coqc AuditBlindNestedCofix.v`    exit 0
      - `Print Assumptions contradiction` `Closed under the global context`
      - `rocqchk` (default)               `Modules were successfully checked`, exit 0
      - `rocqchk -bytecode-compiler yes`  `Modules were successfully checked`, exit 0
      - `rocqchk -o`                      `* Axioms: <none>`,
                                          `* ... unsafe (co)fixpoints: <none>`
      - plain `Require` downstream        survives; see AuditBlindSextet.v

    Same on Rocq Platform 9.0.1: exit 0, clean audit, `coqchk` clean in both modes.

    ** Control, and it is one token

    `AuditBlindControls.v` module `C89` writes `f` — the inner block's own name —
    where this file writes `cycle`, in both positions of `g`'s body.  The
    construction is otherwise identical, and the same `coqc` rejects it:

      Recursive definition of g is ill-formed.
      In environment
      cycle : C I
      f : C I
      g : D (C I) I
      Recursive call on a non-recursive argument of constructor "f".
      Recursive definition is: "dc (C I) I f (ic f)".

    So the guard is checking `g`; it just checks the *outer* name against the
    inner block's tree.  Spelling the same occurrence with the inner name puts it
    back inside the tree that is actually being used, and the check fires. *)

Unset Elimination Schemes.

CoInductive D (X Y : Type) := dc : X -> Y -> D X Y.
CoInductive C (A : Type) := cc : C A -> D (C A) A -> C A.
Inductive I : Type := ic : C I -> I.

CoFixpoint cycle : C I :=
  (cofix f : C I := cc I f g
   with g : D (C I) I := dc (C I) I cycle (ic cycle)
   for f).

Fixpoint empty (i : I) : False :=
  match i with
  | ic c => match c with
    | cc _ _ d => match d with
      | dc _ _ _ j => empty j
      end end end.

Definition contradiction : False := empty (ic cycle).

(** Expected: [Closed under the global context]. *)
Print Assumptions contradiction.
