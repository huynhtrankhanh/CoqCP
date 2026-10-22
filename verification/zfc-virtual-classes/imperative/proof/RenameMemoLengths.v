From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import ArrayLengthFrame InternLengths.
From stdpp Require Import numbers list.
Module RenameMemoLengths.
Import ArrayLengthFrame.
(* Stores may change contents; only growth of the watched allocation is
   excluded. In particular, metadata and SipHash lengths remain observable
   representation facts even though both arrays contain mutable scratch. *)
Definition protected watched := watched<>arraydef_0__renameMemo /\
  watched<>arraydef_0__renameMemoScratch /\ watched<>arraydef_0__frames /\
  watched<>arraydef_0__formulaBuckets /\ watched<>arraydef_0__formulas /\ watched<>arraydef_0__formulaLinks.
Local Opaque funcdef_0__formulaHash funcdef_0__intern.
Theorem cacheGet_ro watched bs ns : array_ro watched (funcdef_0__renameCacheGet bs ns).
Proof.
  pose proof (InternLengths.formulaHash_ro watched) as Hhash.
  unfold funcdef_0__renameCacheGet. apply eliminate_ro. unfold funcdef_0__renameCacheGet_body. ro.
Qed.
Local Opaque funcdef_0__renameCacheGet.
Theorem cacheGrow_ro watched : watched<>arraydef_0__renameMemo -> watched<>arraydef_0__renameMemoScratch ->
  forall bs ns, array_ro watched (funcdef_0__renameCacheGrow bs ns).
Proof.
  intros Hmemo Hscratch bs ns. pose proof (InternLengths.formulaHash_ro watched) as Hhash.
  unfold funcdef_0__renameCacheGrow. apply eliminate_ro. unfold funcdef_0__renameCacheGrow_body. ro.
Qed.
Local Opaque funcdef_0__renameCacheGrow.
Theorem cachePut_ro watched : watched<>arraydef_0__renameMemo -> watched<>arraydef_0__renameMemoScratch ->
  forall bs ns, array_ro watched (funcdef_0__renameCachePut bs ns).
Proof.
  intros Hmemo Hscratch bs ns. pose proof (InternLengths.formulaHash_ro watched) as Hhash.
  pose proof (cacheGrow_ro watched Hmemo Hscratch) as Hgrow.
  unfold funcdef_0__renameCachePut. apply eliminate_ro. unfold funcdef_0__renameCachePut_body. ro.
Qed.
Local Opaque funcdef_0__renameCachePut.
Theorem push_ro watched : watched<>arraydef_0__frames -> forall bs ns, array_ro watched (funcdef_0__push bs ns).
Proof. intros Hframes bs ns. unfold funcdef_0__push. apply eliminate_ro. unfold funcdef_0__push_body. ro. Qed.
Local Opaque funcdef_0__push.
Theorem renameIndex_ro watched bs ns : array_ro watched (funcdef_0__renameIndex bs ns).
Proof. unfold funcdef_0__renameIndex. apply eliminate_ro. unfold funcdef_0__renameIndex_body. ro. Qed.
Local Opaque funcdef_0__renameIndex.
Theorem rename_ro watched : protected watched -> forall bs ns, array_ro watched (funcdef_0__rename bs ns).
Proof.
  intros [Hmemo [Hscratch [Hframes [Hbuckets [Hformulas Hlinks]]]]] bs ns.
  pose proof (cacheGet_ro watched) as Hget. pose proof (cachePut_ro watched Hmemo Hscratch) as Hput.
  pose proof (push_ro watched Hframes) as Hpush. pose proof (renameIndex_ro watched) as Hindex.
  pose proof (InternLengths.intern_ro watched Hbuckets Hformulas Hlinks) as Hintern.
  unfold funcdef_0__rename. apply eliminate_ro. unfold funcdef_0__rename_body. ro.
Qed.
Local Opaque funcdef_0__rename.
Theorem predicate_ro watched : protected watched -> forall bs ns, array_ro watched (funcdef_0__predicate bs ns).
Proof.
  intros Hprotected bs ns. pose proof (rename_ro watched Hprotected) as Hrename.
  destruct Hprotected as [Hmemo [Hscratch [Hframes [Hbuckets [Hformulas Hlinks]]]]].
  pose proof (InternLengths.intern_ro watched Hbuckets Hformulas Hlinks) as Hintern.
  unfold funcdef_0__predicate. apply eliminate_ro. unfold funcdef_0__predicate_body. ro.
Qed.
Local Opaque funcdef_0__predicate.
Theorem rename_length s bs ns observations final after watched : protected watched ->
  execObserved (funcdef_0__rename bs ns) (s,observations)=Some (tt,(final,after)) ->
  length (memory final watched)=length (memory s watched).
Proof. intros Hprotected. apply observed_preserves. now apply rename_ro. Qed.
Theorem predicate_length s bs ns observations final after watched : protected watched ->
  execObserved (funcdef_0__predicate bs ns) (s,observations)=Some (tt,(final,after)) ->
  length (memory final watched)=length (memory s watched).
Proof. intros Hprotected. apply observed_preserves. now apply predicate_ro. Qed.
Theorem observed_lengths s bs ns observations final after :
  execObserved (funcdef_0__rename bs ns) (s,observations)=Some (tt,(final,after)) ->
  length (memory final arraydef_0__meta)=length (memory s arraydef_0__meta) /\
  length (memory final arraydef_0__sipState)=length (memory s arraydef_0__sipState).
Proof.
  intro Hrun. split; eapply rename_length; [repeat split; discriminate|exact Hrun|repeat split; discriminate|exact Hrun].
Qed.
Theorem predicate_observed_lengths s bs ns observations final after :
  execObserved (funcdef_0__predicate bs ns) (s,observations)=Some (tt,(final,after)) ->
  length (memory final arraydef_0__meta)=length (memory s arraydef_0__meta) /\
  length (memory final arraydef_0__sipState)=length (memory s arraydef_0__sipState).
Proof.
  intro Hrun. split; eapply predicate_length; [repeat split; discriminate|exact Hrun|repeat split; discriminate|exact Hrun].
Qed.
End RenameMemoLengths.
