From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash Intern InternBounded Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module InternGrowth.
Import IndexExecution SipHashExecution.
Theorem at_most_one s final bs ns fs next : NativeRepresentation.canonical_arena s fs ->
  meta_value s 8 = 0 -> Z.of_nat (length fs) <= 9223372036854775807 ->
  exec (funcdef_0__intern bs ns) s = Some (tt,final) -> NativeRepresentation.canonical_arena final next ->
  (length next <= S (length fs))%nat.
Proof.
  intros Harena Herror Hcapacity Hrun Hnext.
  destruct (InternBounded.generated_intern_bounded s bs ns (length fs) (proj1 Harena) Herror Hcapacity)
    as [actual [Hactual [_ Hcanonical]]].
  rewrite Hrun in Hactual. injection Hactual as <-.
  destruct Hcanonical as [_ [count [index [Hshape [Htable Hrest]]]]].
  pose proof (proj1 (proj2 Htable)) as Hcount.
  pose proof (proj1 (proj2 (proj1 Hnext))) as Hnextcount.
  destruct Hshape as [->|[-> Hindex]]; lia.
Qed.
End InternGrowth.
