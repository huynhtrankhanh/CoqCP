From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import InternalIO.
From stdpp Require Import numbers list.
Module InternalIOProcedures.
Import InternalIO.
Theorem sipRound_io bs ns : array_ro (funcdef_0__sipRound bs ns).
Proof.
  unfold funcdef_0__sipRound. apply eliminate_ro. unfold funcdef_0__sipRound_body. ro.
Qed.
Local Opaque funcdef_0__sipRound.
Theorem sipWord_io bs ns : array_ro (funcdef_0__sipWord bs ns).
Proof.
  pose proof sipRound_io as Hdep0.
  unfold funcdef_0__sipWord. apply eliminate_ro. unfold funcdef_0__sipWord_body. ro.
Qed.
Local Opaque funcdef_0__sipWord.
Theorem formulaHash_io bs ns : array_ro (funcdef_0__formulaHash bs ns).
Proof.
  pose proof sipRound_io as Hdep0.
  pose proof sipWord_io as Hdep1.
  unfold funcdef_0__formulaHash. apply eliminate_ro. unfold funcdef_0__formulaHash_body. ro.
Qed.
Local Opaque funcdef_0__formulaHash.
Theorem rehashFormulas_io bs ns : array_ro (funcdef_0__rehashFormulas bs ns).
Proof.
  pose proof formulaHash_io as Hdep0.
  unfold funcdef_0__rehashFormulas. apply eliminate_ro. unfold funcdef_0__rehashFormulas_body. ro.
Qed.
Local Opaque funcdef_0__rehashFormulas.
Theorem intern_io bs ns : array_ro (funcdef_0__intern bs ns).
Proof.
  pose proof formulaHash_io as Hdep0.
  pose proof rehashFormulas_io as Hdep1.
  unfold funcdef_0__intern. apply eliminate_ro. unfold funcdef_0__intern_body. ro.
Qed.
Local Opaque funcdef_0__intern.
Theorem push_io bs ns : array_ro (funcdef_0__push bs ns).
Proof.
  unfold funcdef_0__push. apply eliminate_ro. unfold funcdef_0__push_body. ro.
Qed.
Local Opaque funcdef_0__push.
Theorem renameIndex_io bs ns : array_ro (funcdef_0__renameIndex bs ns).
Proof.
  unfold funcdef_0__renameIndex. apply eliminate_ro. unfold funcdef_0__renameIndex_body. ro.
Qed.
Local Opaque funcdef_0__renameIndex.
Theorem renameCacheGet_io bs ns : array_ro (funcdef_0__renameCacheGet bs ns).
Proof. pose proof (formulaHash_io) as Hhash. unfold funcdef_0__renameCacheGet. apply eliminate_ro. unfold funcdef_0__renameCacheGet_body. ro. Qed.
Local Opaque funcdef_0__renameCacheGet.
Theorem renameCacheGrow_io bs ns : array_ro (funcdef_0__renameCacheGrow bs ns).
Proof. pose proof (formulaHash_io) as Hhash. unfold funcdef_0__renameCacheGrow. apply eliminate_ro. unfold funcdef_0__renameCacheGrow_body. ro. Qed.
Local Opaque funcdef_0__renameCacheGrow.
Theorem renameCachePut_io bs ns : array_ro (funcdef_0__renameCachePut bs ns).
Proof. pose proof (formulaHash_io) as Hhash. pose proof (renameCacheGrow_io) as Hgrow. unfold funcdef_0__renameCachePut. apply eliminate_ro. unfold funcdef_0__renameCachePut_body. ro. Qed.
Local Opaque funcdef_0__renameCachePut.
Theorem rename_io bs ns : array_ro (funcdef_0__rename bs ns).
Proof. pose proof (renameCacheGet_io) as HrenameCacheGet.  pose proof (renameCachePut_io) as HrenameCachePut.
  pose proof push_io as Hdep0.
  pose proof renameIndex_io as Hdep1.
  pose proof intern_io as Hdep2.
  unfold funcdef_0__rename. apply eliminate_ro. unfold funcdef_0__rename_body. ro.
Qed.
Local Opaque funcdef_0__rename.
Theorem predicate_io bs ns : array_ro (funcdef_0__predicate bs ns).
Proof.
  pose proof intern_io as Hdep0.
  pose proof rename_io as Hdep1.
  unfold funcdef_0__predicate. apply eliminate_ro. unfold funcdef_0__predicate_body. ro.
Qed.
Local Opaque funcdef_0__predicate.
Theorem classEqual_io bs ns : array_ro (funcdef_0__classEqual bs ns).
Proof.
  pose proof intern_io as Hdep0.
  pose proof predicate_io as Hdep1.
  unfold funcdef_0__classEqual. apply eliminate_ro. unfold funcdef_0__classEqual_body. ro.
Qed.
Local Opaque funcdef_0__classEqual.
Theorem classMember_io bs ns : array_ro (funcdef_0__classMember bs ns).
Proof.
  pose proof intern_io as Hdep0.
  pose proof predicate_io as Hdep1.
  unfold funcdef_0__classMember. apply eliminate_ro. unfold funcdef_0__classMember_body. ro.
Qed.
Local Opaque funcdef_0__classMember.
Theorem setness_io bs ns : array_ro (funcdef_0__setness bs ns).
Proof.
  pose proof intern_io as Hdep0.
  pose proof predicate_io as Hdep1.
  unfold funcdef_0__setness. apply eliminate_ro. unfold funcdef_0__setness_body. ro.
Qed.
Local Opaque funcdef_0__setness.
Theorem axiom_io bs ns : array_ro (funcdef_0__axiom bs ns).
Proof.
  pose proof intern_io as Hdep0.
  pose proof rename_io as Hdep1.
  unfold funcdef_0__axiom. apply eliminate_ro. unfold funcdef_0__axiom_body. ro.
Qed.
Local Opaque funcdef_0__axiom.
Theorem rename_preserves s bs ns final observations after :
  execObserved (funcdef_0__rename bs ns) (s,observations) = Some (tt,(final,after)) -> preserves s final.
Proof. apply observed_preserves. apply rename_io. Qed.
Theorem predicate_preserves s bs ns final observations after :
  execObserved (funcdef_0__predicate bs ns) (s,observations) = Some (tt,(final,after)) -> preserves s final.
Proof. apply observed_preserves. apply predicate_io. Qed.
End InternalIOProcedures.
