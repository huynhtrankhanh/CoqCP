(** * rocq#22382 — the guard checker's uniform-argument finder counts let-binders

    rocq-prover/rocq#22382, filed 2026-08-20 13:04 UTC by `yannl35133`, **OPEN**,
    fix PR unmerged.  The issue body says *"Found by an LLM and @dselsam"*.

    ** Category (a): a closed proof of `False` with every audit channel silent

    `find_uniform_parameters` starts counting arguments at the first binders
    "irrespective of whether these binder really are lambdas".  The inner `fix`
    below opens with `(carry : nat := seed)`, a **let**, and the count is off by
    one from there on.  The recursive call `inner carry rest` therefore passes
    `carry` where `p` is expected, and the analysis treats a position as uniform
    that is not.  `russell 2` becomes a type inhabited by its own negation.

    ** Measured on Rocq 9.2 (OCaml 4.14.2), the current stable release

      - `coqc AuditBlindUniformArgs.v`    exit 0
      - `Print Assumptions contradiction` `Closed under the global context`
      - `rocqchk` (default)               `Modules were successfully checked`, exit 0
      - `rocqchk -bytecode-compiler yes`  `Modules were successfully checked`, exit 0
      - `rocqchk -o`                      `* Axioms: <none>`,
                                          `* ... unsafe (co)fixpoints: <none>`
      - plain `Require` downstream        survives; see AuditBlindSextet.v

    Same on Rocq Platform 9.0.1: exit 0, clean audit, `coqchk` clean in both modes.

    Note that `rocqchk`'s own summary line for this class —
    `Constants/Inductives relying on unsafe (co)fixpoints: <none>` — is *true* and
    still misleading.  Nothing here is marked unsafe: the guard checker ran and
    said yes.

    ** Control

    `AuditBlindControls.v` module `C82` deletes the `carry` let-binder and passes
    `seed` at the call site instead — the same recursion, one binder fewer — and
    the same `coqc` rejects it:

      Recursive definition of russell is ill-formed.
      ...
      Recursive call to russell has principal argument equal to
      "p" instead of one of the following variables: "smaller" "m".

    So the guard checker is awake, and it is the let-binder that blinds it.

    ** Upstream also gives a second, source-only reproducer

    A `#[refine] Fixpoint` closed by an interactive `fix rec 2`.  It exhibits the
    same miscount without producing a `False`, and is not carried here. *)

Definition relay (outer : nat -> Type) (seed : nat) : nat -> nat -> Type :=
  fix inner (carry : nat := seed) (p m : nat) {struct m} : Type :=
    match m with
    | O => outer p -> False
    | S rest => inner carry rest
    end.

Fixpoint russell (n : nat) : Type :=
  match n with
  | O => True
  | S smaller => relay russell n smaller smaller
  end.

Definition diagonal (x : russell 2) : False := x x.

Definition contradiction : False := diagonal diagonal.

(** Expected: [Closed under the global context]. *)
Print Assumptions contradiction.
