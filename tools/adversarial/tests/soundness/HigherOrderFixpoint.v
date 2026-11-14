(** * rocq#21683 -- guard checker: higher-order recursive call through a fixpoint

    THIS FILE IS EXPECTED TO BE REJECTED.  It is a regression witness, not a
    build target.  On an affected Coq it compiles and yields an axiom-free
    [False]; on a fixed one the guard checker rejects [russell].

    Category (per ../../README.md): IMPLEMENTATION DEFECT (fixed).

    The defect: the guard checker accepted a fixpoint that passes *itself* as a
    higher-order argument to another fixpoint, which then applies it to a
    non-subterm of the structural argument.  [russell] recurses through
    [iterate_to_neg], whose [f] parameter carries no subterm information, so the
    call [f seed] escapes the check even though [seed] is not smaller.

    That makes [russell 1] convertible with its own negation:

      russell 1  =  iterate_to_neg russell 1 1
                 =  iterate_to_neg russell 0 1
                 =  russell 1 -> False

    which is Russell's paradox as a type, and [delta delta] inhabits [False].

    Upstream: <https://github.com/rocq-prover/rocq/issues/21683>
      filed 2026-02-28, closed 2026-03-04.  Found autonomously by Opus 4.6;
      one of the seven proofs of [False] reported in
      <https://tristan.st/blog/in_search_of_falsehood>.

    Verified with [coqc] on The Rocq Prover 9.2 (OCaml 4.14.2):

      REJECTED at [russell], exit code 1, with

        Recursive definition of russell is ill-formed.
        Recursive call to russell has principal argument equal to
        "seed" instead of "m".

    Affected versions per the upstream report: the issue was filed against
    then-current Rocq and fixed within days; this repository has only 9.2, so
    the acceptance side of the matrix is cited, not reproduced.
*)

Fixpoint iterate_to_neg (f : nat -> Type) (n : nat) (seed : nat) : Type :=
  match n with
  | O => f seed -> False
  | S m => iterate_to_neg f m seed
  end.

(** The guard checker must reject this.  Everything after it is unreachable on
    a fixed toolchain and is kept to document what acceptance would cost. *)
Fixpoint russell (n : nat) : Type :=
  match n with
  | O => True
  | S m => iterate_to_neg russell 1 (S m)
  end.

Definition delta (x : russell 1) : False := x x.

Definition omega : False := delta delta.

Print Assumptions omega.
(* On an affected toolchain: "Closed under the global context" -- an
   axiom-free proof of False. *)
