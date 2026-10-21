From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameMemoTable RenameMemoLookup RenameMemoBuffers RenameMemoResize
  RenameMemoRebuild ObservedLocal Observation LocalObservation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoBufferFacts.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoBuffers RenameMemoResize.
Definition cleared s size:=clear_many (scratch_grown s size) 0 size.
Definition copied s size:=copy_many (memo_grown s size) 0 size.
Lemma clear_many_io s start fuel : stdin (clear_many s start fuel)=stdin s /\ stdout (clear_many s start fuel)=stdout s.
Proof. induction fuel as [|fuel IH] in s,start|-*; [split; reflexivity|]. cbn [clear_many]. exact (IH (write_scratch s start (0,0,0,0)) (S start)). Qed.
Lemma copy_many_io s start fuel : stdin (copy_many s start fuel)=stdin s /\ stdout (copy_many s start fuel)=stdout s.
Proof. induction fuel as [|fuel IH] in s,start|-*; [split; reflexivity|]. cbn [copy_many]. exact (IH (write_memo s start (scratch s start)) (S start)). Qed.
Lemma cleared_other s size name : name<>arraydef_0__renameMemoScratch -> memory (cleared s size) name=memory s name.
Proof. intro Hname. unfold cleared. rewrite clear_many_other by exact Hname. now apply scratch_grown_other. Qed.
Lemma copied_other s size name : name<>arraydef_0__renameMemo -> memory (copied s size) name=memory s name.
Proof. intro Hname. unfold copied. rewrite copy_many_other by exact Hname. now apply memo_grown_other. Qed.
Lemma cleared_meta s size cell : meta_value (cleared s size) cell=meta_value s cell.
Proof. unfold meta_value. now rewrite cleared_other by discriminate. Qed.
Lemma copied_meta s size cell : meta_value (copied s size) cell=meta_value s cell.
Proof. unfold meta_value. now rewrite copied_other by discriminate. Qed.
Lemma cleared_table s size : RenameMemoLookup.table (cleared s size)=RenameMemoLookup.table s.
Proof. unfold RenameMemoLookup.table. now rewrite cleared_other by discriminate. Qed.
Lemma copied_scratch s size : scratch (copied s size)=scratch s.
Proof. unfold scratch. now rewrite copied_other by discriminate. Qed.
Lemma cleared_capacity s size : (size<=length (memory (cleared s size) arraydef_0__renameMemoScratch))%nat.
Proof. unfold cleared. rewrite clear_many_length. apply scratch_capacity. Qed.
Lemma copied_capacity s size : (size<=length (memory (copied s size) arraydef_0__renameMemo))%nat.
Proof. unfold copied. rewrite copy_many_length. apply memo_capacity. Qed.
Lemma cleared_empty s size : forall index, (index<size)%nat -> scratch (cleared s size) index=(0,0,0,0).
Proof. intros index Hindex. unfold cleared. apply clear_many_inside; [apply scratch_capacity|lia]. Qed.
Lemma copied_entry s size index : (index<size)%nat -> RenameMemoLookup.table (copied s size) index=scratch s index.
Proof.
  intro Hindex. unfold RenameMemoLookup.table,copied. rewrite copy_many_inside by (try apply memo_capacity; lia).
  unfold scratch. now rewrite memo_grown_other by discriminate.
Qed.
Lemma cleared_io s size : stdin (cleared s size)=stdin s /\ stdout (cleared s size)=stdout s.
Proof. unfold cleared. exact (clear_many_io (scratch_grown s size) 0 size). Qed.
Lemma copied_io s size : stdin (copied s size)=stdin s /\ stdout (copied s size)=stdout s.
Proof. unfold copied. exact (copy_many_io (memo_grown s size) 0 size). Qed.
Theorem cleared_ready s count size :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> (count<=length (memory s arraydef_0__renameMemo))%nat ->
  (0<size)%nat -> Z.of_nat size<=maximum -> RenameMemoRebuild.ready (cleared s size) count size.
Proof.
  intros Hmeta Hsip Hpositive Herror Hmemo Hsize Hword. unfold RenameMemoRebuild.ready.
  rewrite !cleared_other by discriminate. rewrite !cleared_meta.
  repeat split; try assumption. apply cleared_capacity.
Qed.
Lemma clear_nf total remaining : InternalObservation.local_nf (loop remaining (clear_body total)).
Proof. apply InternalObservation.loop_nf. intro index. unfold clear_body,clearing. InternalObservation.nf. Qed.
Lemma copy_nf total remaining : InternalObservation.local_nf (loop remaining (copy_body total)).
Proof. apply InternalObservation.loop_nf. intro index. unfold copy_body,copying. InternalObservation.nf. Qed.
Theorem generated_clear_observed (f : Frame) size observations :
  (size<=length (memory (machine f) arraydef_0__renameMemoScratch))%nat ->
  execLocalObserved (clearing (Z.of_nat size)) (f,observations)=Some (tt,(setMachine f (clear_many (machine f) 0 size),observations)).
Proof.
  intro Hsize. rewrite clearing_is_loop,Nat2Z.id.
  apply LocalObservation.plain_observed; [apply clear_nf|]. apply generated_clear_loop; [reflexivity|exact Hsize].
Qed.
Theorem generated_copy_observed (f : Frame) size observations :
  (size<=length (memory (machine f) arraydef_0__renameMemoScratch))%nat ->
  (size<=length (memory (machine f) arraydef_0__renameMemo))%nat ->
  execLocalObserved (copying (Z.of_nat size)) (f,observations)=Some (tt,(setMachine f (copy_many (machine f) 0 size),observations)).
Proof.
  intros Hscratch Hmemo. rewrite copying_is_loop,Nat2Z.id.
  apply LocalObservation.plain_observed; [apply copy_nf|]. apply generated_copy_loop; [reflexivity|exact Hscratch|exact Hmemo].
Qed.
End RenameMemoBufferFacts.
