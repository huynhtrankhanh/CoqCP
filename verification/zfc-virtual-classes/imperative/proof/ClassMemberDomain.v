From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import VirtualClasses.
From NativeProof Require Import ArenaFrame RenameMemoCallers RenameMemoClassMember RenameMemoParseDomain.
From Stdlib Require Import Lists.List.
Module ClassMemberDomain.
Theorem member_ready s t fs a b cls_a cls_b : ArenaFrame.storage s t ->
  RenameMemoClassMember.ready s fs a b cls_a cls_b -> RenameMemoClassMember.ready t fs a b cls_a cls_b.
Proof.
  intros Hframe Hready. destruct cls_a; cbn [RenameMemoClassMember.ready] in *.
  - eapply RenameMemoParseDomain.predicate_ready; eassumption.
  - destruct Hready as [Ha Hb]. split; eapply RenameMemoParseDomain.predicate_ready; eassumption.
Qed.
Theorem member_work s t a b cls_a cls_b : ArenaFrame.storage s t ->
  RenameMemoClassMember.work t a b cls_a cls_b=RenameMemoClassMember.work s a b cls_a cls_b.
Proof.
  intro Hframe. destruct cls_a; cbn [RenameMemoClassMember.work];
    now rewrite ?(RenameMemoParseDomain.growth_same s t a Hframe),(RenameMemoParseDomain.growth_same s t b Hframe).
Qed.
End ClassMemberDomain.
