(** * rocq#21685 -- module alias chains corrupt the delta-resolver

    THIS FILE IS EXPECTED TO BE REJECTED (or, on an affected toolchain, to
    prove [False]).  Regression witness, not a build target.

    Category (per ../../README.md): IMPLEMENTATION DEFECT (fixed).

    Coq's module system is the second cluster of 2026 soundness bugs, alongside
    the guard checker (../GuardChecker/).  Lean has no analogue of either
    subsystem, which is why this whole directory has no Lean counterpart.

    The defect: resolving [Module Alias := Inner] inside a functor, reached
    through a multi-step alias chain ([A' := A], [B' := A'.B]), corrupts the
    delta-resolver.  Two *different* instantiations of the same functor --
    [B'.F M_true] and [B'.F M_false] -- then have [Alias.x] identified, so
    [true = false] is provable by [reflexivity] while [vm_compute] still
    distinguishes the two sides.  The disagreement between the two evaluators
    is the whole construction.

    Upstream: <https://github.com/rocq-prover/rocq/issues/21685>
      filed 2026-02-28, closed.  Found autonomously by Opus 4.6; one of the
      seven proofs of [False] in <https://tristan.st/blog/in_search_of_falsehood>.

    Verified with [coqc] on The Rocq Prover 9.2 (OCaml 4.14.2): the construction
    FAILS -- exit code 1, with

      Error: Unable to unify "R'.Alias.x" with "R.Alias.x".

    [reflexivity] no longer identifies the two functor instantiations.  That
    failure is the fix working: the delta-resolver keeps them distinct, so the
    conversion check and [vm_compute] agree again.
*)

Module Type T. Parameter n : bool. End T.
Module M_true.  Definition n := true.  End M_true.
Module M_false. Definition n := false. End M_false.

Module A. Module B. Module F (E : T).
  Module Inner. Definition x := E.n. End Inner.
  Module Alias := Inner.
End F. End B. End A.

Module A' := A.
Module B' := A'.B.
Module R  := B'.F M_true.
Module R' := B'.F M_false.

(** On an affected toolchain the [assert] succeeds by [reflexivity] -- the
    delta-resolver has identified [R.Alias.x] with [R'.Alias.x] -- and
    [vm_compute] then reduces them to [true] and [false], closing [False]. *)
Lemma boom : False.
Proof.
  assert (H : R.Alias.x = R'.Alias.x) by reflexivity.
  vm_compute in H. discriminate H.
Qed.

Print Assumptions boom.
(* On an affected toolchain: "Closed under the global context". *)
