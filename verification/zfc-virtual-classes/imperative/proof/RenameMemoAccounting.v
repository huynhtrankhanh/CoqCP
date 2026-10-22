From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash Intern IndexFrame FormulaEncoding RenameMemoLookup RenameMemoInvariant RenameMemoContents
  RenameMemoOccupancy RenameMemoStack RenameMemoJoin RenameMemoFalsity RenameMemoPut.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoAccounting.
Import IndexExecution SipHashExecution.
Definition passive s t := RenameMemoLookup.table t=RenameMemoLookup.table s /\
  meta_value t 29=meta_value s 29 /\ meta_value t 30=meta_value s 30.
Lemma passive_trans s t u : passive s t -> passive t u -> passive s u.
Proof. unfold passive. intros. intuition congruence. Qed.
Lemma passive_covers s t count : passive s t ->
  RenameMemoContents.covers (RenameMemoLookup.table s) count (RenameMemoLookup.table t) count.
Proof. intros [Htable _] query Hhas. now rewrite Htable. Qed.
Definition completed s count t size query :=
  RenameMemoContents.covers (RenameMemoLookup.table s) count (RenameMemoLookup.table t) size /\
  RenameMemoContents.has (RenameMemoLookup.table t) size query /\ meta_value t 30<=meta_value s 30+1.
Lemma completed_before s middle t count size query : passive s middle ->
  completed middle count t size query -> completed s count t size query.
Proof. intros [Htable [_ Hlive]] [Hcovered [Hnew Hupper]]. unfold completed. now rewrite Htable,Hlive in *.
Qed.
Lemma completed_source s fs count t size source depth root :
  FormulaEncoding.unique fs -> word root -> nth_error fs (Z.to_nat root)=Some source ->
  completed s count t size (root,Z.of_nat depth) ->
  forall other, word other -> nth_error fs (Z.to_nat other)=Some source -> completed s count t size (other,Z.of_nat depth).
Proof.
  intros Hunique Hroot Hsource Hcomplete other Hother Hsame.
  assert (Hid : root=other).
  { apply FormulaEncoding.natural_index_injective; try assumption. eapply Hunique; eassumption. }
  now rewrite <-Hid.
Qed.
Lemma lookup s query count : passive s (RenameMemoLookup.result_state s query count).
Proof.
  destruct (RenameMemoLookup.result_frame s query count) as [Ha [Hm _]]. split.
  - unfold RenameMemoLookup.table. now rewrite Ha by discriminate.
  - split; apply Hm; lia.
Qed.
Lemma intern s t : InternExecution.logical_frame s t -> passive s t.
Proof.
  intros [Ha [Hm _]]. split; [unfold RenameMemoLookup.table; now rewrite Ha by discriminate|]. split; apply Hm; lia.
Qed.
Lemma stack s t : RenameMemoStack.stack_frame s t -> passive s t.
Proof.
  intros [Ha [Hm _]]. split; [unfold RenameMemoLookup.table; now rewrite Ha by discriminate|]. split; apply Hm; lia.
Qed.
Lemma index s m i depth shift arg : passive s (IndexFrame.result_state s m i depth shift arg).
Proof.
  split; [unfold RenameMemoLookup.table; now rewrite IndexFrame.result_other by discriminate|]. split; apply IndexFrame.result_meta_other; lia.
Qed.
Lemma popped s top : passive s (RenameMemoJoin.popped s top).
Proof.
  unfold RenameMemoJoin.popped. split; [unfold RenameMemoLookup.table; now rewrite store_meta_other by discriminate|]. split; apply meta_store_other; lia.
Qed.
Theorem complete s root depth top count meaning observations : RenameMemoInvariant.valid s count meaning ->
  (Z.of_nat count/2<=meta_value s 30 -> Z.of_nat count<=9223372036854775807) ->
  meaning (root,depth) (meta_value s 0) ->
  exists stored size,
    execObserved (funcdef_0__renameCachePut (fun _=>false) (RenameMemoFalsity.arguments root depth (meta_value s 0)))
      (RenameMemoJoin.popped s top,observations)=Some (tt,(stored,observations)) /\
    (size=count \/ size=(2*count)%nat) /\ RenameMemoInvariant.valid stored size meaning /\
    meta_value stored 0=meta_value s 0 /\ meta_value stored 10=Z.of_nat top /\
    RenameMemoPut.storage_frame (RenameMemoJoin.popped s top) stored /\ RenameMemoInvariant.storage_frame s stored /\
    meta_value stored 30<=meta_value s 30+1 /\
    RenameMemoContents.has (RenameMemoLookup.table stored) size (root,depth) /\
    RenameMemoContents.covers (RenameMemoLookup.table s) count (RenameMemoLookup.table stored) size.
Proof.
  intros Hvalid Hfits Hmeaning.
  destruct (RenameMemoJoin.generated_completion s root depth top count meaning observations Hvalid Hfits Hmeaning)
    as (stored & size & Hrun & Hchoice & Hpost & Hvalue & Htop & Hframe & Hstorage).
  pose proof (popped s top) as [Hpoptable [Hpopsize Hpopcount]].
  assert (Hpopvalid : RenameMemoInvariant.valid (RenameMemoJoin.popped s top) count meaning) by now apply RenameMemoJoin.popped_valid.
  assert (Hpopfits : Z.of_nat count/2<=meta_value (RenameMemoJoin.popped s top) 30 -> Z.of_nat count<=9223372036854775807)
    by now rewrite Hpopcount.
  destruct (RenameMemoContents.executed _ stored (fun _=>false) (RenameMemoFalsity.arguments root depth (meta_value s 0)) count observations meaning
    Hpopvalid Hpopfits Hrun) as [actual [Hcapacity [Hnew Hcovered]]].
  assert (Hsame : actual=size) by (pose proof (RenameMemoInvariant.capacity_value _ _ _ Hpost); lia). subst actual.
  pose proof (RenameMemoOccupancy.executed _ stored (fun _=>false) (RenameMemoFalsity.arguments root depth (meta_value s 0)) count observations meaning
    Hpopvalid Hpopfits Hrun) as Hupper. rewrite Hpopcount in Hupper.
  destruct (RenameMemoFalsity.arguments_values root depth (meta_value s 0)) as [Hnode [Hdepth Hresult]]. rewrite Hnode,Hdepth in Hnew.
  exists stored,size. split; [exact Hrun|]. split; [exact Hchoice|]. split; [exact Hpost|]. split; [exact Hvalue|].
  split; [exact Htop|]. split; [exact Hframe|]. split; [exact Hstorage|]. split; [exact Hupper|]. split; [exact Hnew|].
  unfold RenameMemoContents.covers in *. now rewrite Hpoptable in Hcovered.
Qed.
End RenameMemoAccounting.
