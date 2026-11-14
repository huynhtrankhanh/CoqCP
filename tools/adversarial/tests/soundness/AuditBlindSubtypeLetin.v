(** * rocq#22387 — module subtyping ignores where a `let` sits among the arguments

    rocq-prover/rocq#22387, filed 2026-08-20 13:17 UTC by `SkySkimmer`, **OPEN**,
    fix PR unmerged.  Reported the same way as #22378 — *"Reported by OpenAI by
    email to a random core team member"*.

    ** This file is the census's NEAR MISS, and that is its whole job

    `AuditBlindSextet.v` claims that **six** of the nine `kind: inconsistency`
    issues of 2026-08-20 match rocq#21839 on every audit channel at once.  #22387
    is the seventh candidate and the one that decides whether the count is six or
    seven.  It fails on two channels, both measured here, and so it is kept out
    of the consumer and kept in the repository.

    ** The mechanism

    Module subtyping compares the *whole* constructor type, and
    `forall x : nat, let z := 0 in T` converts with `let z := 0 in forall x : nat, T`.
    `match` does not agree: it cares about the order of the `let` among the real
    arguments.  So `A` is accepted as an implementation of `S` while
    `match A.c 1 with A.c x z => z end` reduces to `1` inside the functor and to
    `0` outside it.

    ** Where it fails the census, measured on Rocq 9.2

    1. **It is not flag-free.**  `Unset Elimination Schemes` is load-bearing.
       Delete that one line and the same `coqc` rejects the construction at
       `Module Applied : R := F A.`:

         Signature components for field T_rect do not match:
         the body of definitions differs: expected
         "fun (P : A.T -> Type) (c : forall x : nat, let z := 0 in P (A.c x))
            (t : A.T) => match t as t0 return P t0 with | A.c x _ => c x end"
         but found
         "fun (P : A.T -> Type) (c : let z := 0 in forall x : nat, P (A.c x))
            (t : A.T) => match t as t0 return P t0 with | A.c _ x => c x end".

       That is a one-token control and it is worth reading closely: what catches
       the defect is not the subtyping check on `T` — which passes — but the
       subtyping check on the **generated** `T_rect`, whose body records the
       argument order that `T`'s type had thrown away.  The safeguard here is a
       derived definition, and switching off its generation switches it off.

    2. **`rocqchk` owns a working safeguard against it, and the seal is what
       hides it.**  This is the substantive disqualifier, and it is the one that
       separates #22387 from rocq#21839 in kind rather than in degree.

       As written, `rocqchk` and `rocqchk -bytecode-compiler yes` both print
       `Modules were successfully checked` at exit 0 — because `Module Applied :
       R := F A` writes `Applied`'s components into the `.vo` **with no bodies**.
       There is nothing left for the checker to re-check.  `rocqchk -o` says so
       out loud, alone among the seven candidates:

         * Axioms:
             AuditBlindSubtypeLetin.Applied.result

       That line is *not* the checker noticing anything.  Measured here: an
       honest sealed module — `Module Type R. Parameter ok : True. End R.` with a
       real implementation — produces the identical line, `* Axioms:
       Honest.Sealed.ok`.  The line reports sealing, not assumption.

       Delete the ascription and the picture changes completely.  With
       `Module Applied := F A.` the `False` still follows by conversion, `coqc` is
       still exit 0, `Print Assumptions contradiction` still says `Closed under
       the global context` — and `rocqchk` **rejects** the `.vo`:

         Fatal Error: Type error: ActualType

       at **exit 129**, in the default mode and under
       `-bytecode-compiler yes` alike.  Measured on 9.2 in this directory's
       scratch, and independently recorded in
       ../ModuleSystem/LetinOrderSubtypingUnsealed.v.

       So the independent checker *can* catch rocq#22387: it re-typechecks the
       substituted functor body and finds `I` checked against a type that has
       become `False`.  rocq#21839 has no such safeguard anywhere.  Counting
       #22387 as a peer would mean counting a construction whose only safeguard
       against the checker is that the module system stopped handing it a body.

       (`Print Assumptions contradiction` says `Closed under the global context`
       throughout, on both files.  The two audits therefore disagree about what
       `Applied.result` is, in both the sealed and the honest case, and neither
       disagreement is about soundness.)

    ** The channels as this file stands, on Rocq 9.2 and on Rocq Platform 9.0.1

      - `coqc AuditBlindSubtypeLetin.v`   exit 0 on both
      - `Print Assumptions contradiction` `Closed under the global context` on both
      - `rocqchk` (default)               `Modules were successfully checked`, exit 0
      - `rocqchk -bytecode-compiler yes`  `Modules were successfully checked`, exit 0
      - plain `Require` downstream        survives, with a clean `Print Assumptions`

    So it is a genuine live proof of `False` on both installed releases, and a
    serious one.  It is simply not a peer of rocq#21839 on *all* five tests, and
    the catalog should not count it as one.

    The module-system directory carries the full treatment of this issue —
    ../ModuleSystem/LetinOrderSubtyping.v and its three companions.  This file
    exists only to hold the census's negative measurement in the same place as
    the census. *)

Unset Elimination Schemes.

Module Type S.
  Inductive T := c (x : nat) (z : nat := 0).
End S.

Module A.
  Inductive T := c (z : nat := 0) (x : nat).
End A.

Module F (X : S).
  Definition result :
    match (match X.c 1 with X.c x z => z end) with
    | O => True | S _ => False end := I.
End F.

Module Type R. Parameter result : False. End R.

Module Applied : R := F A.

Definition contradiction : False := Applied.result.

(** Expected: [Closed under the global context] — and `rocqchk -o` disagrees. *)
Print Assumptions contradiction.
