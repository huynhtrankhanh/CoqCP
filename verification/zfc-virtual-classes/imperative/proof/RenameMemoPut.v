From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameMemoTable RenameMemoLookup RenameMemoPlacement RenameMemoCapacity RenameMemoInsert RenameMemoGrow RenameMemoResize RenameMemoRebuild
  ObservedLocal Observation NativePrimitives.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoPut.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInsert.
Local Opaque funcdef_0__renameCacheGrow funcdef_0__formulaHash hash_state.
Definition prefix : LocalAction unit := ltac:(
  let code:=eval unfold funcdef_0__renameCachePut_body in funcdef_0__renameCachePut_body in
  lazymatch code with bind ?first ?next => exact first end).
Definition tail : LocalAction unit := ltac:(
  let code:=eval unfold funcdef_0__renameCachePut_body in funcdef_0__renameCachePut_body in
  lazymatch code with bind ?first ?next => exact (next tt) end).
Lemma body_actual : funcdef_0__renameCachePut_body=prefix >>= (fun _=>tail).
Proof. reflexivity. Qed.
Lemma body_prefix (f : Frame) observations :
  execLocalObserved funcdef_0__renameCachePut_body (f,observations)=
  optionBind (execLocalObserved prefix (f,observations)) (fun response=>execLocalObserved tail (snd response)).
Proof. rewrite body_actual,local_bind. reflexivity. Qed.
Lemma prefix_execution (f : Frame) observations : (31<length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved prefix (f,observations)=
  if bool_decide (meta_value (machine f) 30<meta_value (machine f) 29/2)
  then Some (tt,(f,observations))
  else optionBind (execObserved (funcdef_0__renameCacheGrow (fun _=>false) (fun _=>0)) (machine f,observations))
    (fun response=>Some (tt,(setMachine f (fst (snd response)),snd (snd response)))).
Proof.
  intro Hmeta. destruct f as [s bs ns]. cbn [machine] in *. unfold prefix.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];
      eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hmeta])
    |progress replace (Z.to_nat 30) with 30%nat by reflexivity
    |progress replace (Z.to_nat 29) with 29%nat by reflexivity
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools divIntUnsigned decide decide_rel]
    |match goal with |- context [numbers.Z.eq_dec ?a ?b] => destruct (numbers.Z.eq_dec a b); [exfalso; lia|] end];
  destruct bool_decide; cbn [negb]; [reflexivity|].
  repeat first [progress cbn [optionBind fst snd machine]
    |NativePrimitives.primitive ltac:(fun frame name slot=>fail)].
  destruct (execObserved (funcdef_0__renameCacheGrow (fun _=>false) (fun _=>0)) (s,observations)) as [[[] [after trace]]|]; reflexivity.
Qed.
Theorem generated_resize_composition s grown bs ns observations :
  (31<length (memory s arraydef_0__meta))%nat ->
  (31<length (memory grown arraydef_0__meta))%nat ->
  meta_value s 29/2<=meta_value s 30 -> meta_value grown 30<meta_value grown 29/2 ->
  execObserved (funcdef_0__renameCacheGrow (fun _=>false) (fun _=>0)) (s,observations)=Some (tt,(grown,observations)) ->
  execObserved (funcdef_0__renameCachePut bs ns) (s,observations)=
  execObserved (funcdef_0__renameCachePut bs ns) (grown,observations).
Proof.
  intros Hmeta Hgmeta Hload Hgload Hgrow.
  unfold funcdef_0__renameCachePut. rewrite !ObservedLocal.eliminate_correct.
  rewrite !body_prefix,!prefix_execution by assumption.
  cbn [machine].
  rewrite (bool_decide_false (meta_value s 30<meta_value s 29/2)) by lia.
  rewrite (bool_decide_true (meta_value grown 30<meta_value grown 29/2)) by exact Hgload.
  rewrite Hgrow. reflexivity.
Qed.
Lemma result_live_upper s k result count slot : (0<count)%nat ->
  (count<=length (memory s arraydef_0__renameMemo))%nat -> placement s k count=Some slot ->
  (RenameMemoCapacity.live (RenameMemoLookup.table (result_state_below_half s k result count)) count<=
    S (RenameMemoCapacity.live (RenameMemoLookup.table s) count))%nat.
Proof.
  intros Hpositive Hmemo Hplace.
  transitivity (RenameMemoCapacity.live (RenameMemoTable.put (RenameMemoLookup.table s) slot (fst k,snd k,result,1)) count).
  - apply Nat.eq_le_incl. apply RenameMemoCapacity.live_ext. intros; now apply result_table.
  - rewrite RenameMemoCapacity.live_put.
    + destruct bool_decide; lia.
    + exact (proj1 (RenameMemoPlacement.place_sound (RenameMemoLookup.table s) count k
        (RenameMemoLookup.hash_start s k count) count slot Hpositive (RenameMemoLookup.hash_start_bound s k count Hpositive) Hplace)).
Qed.
Lemma result_sip_length s k result count :
  length (memory (result_state_below_half s k result count) arraydef_0__sipState)=length (memory s arraydef_0__sipState).
Proof.
  unfold result_state_below_half. destruct (placement s k count).
  - unfold update_result. destruct bool_decide; [rewrite store_meta_other by discriminate|];
      rewrite store_entry_other by discriminate;
      exact (RenameMemoRebuild.hashed_sip_length s (fst k,snd k,0,0)).
  - rewrite store_meta_other by discriminate. exact (RenameMemoRebuild.hashed_sip_length s (fst k,snd k,0,0)).
Qed.
Definition storage_frame s t :=
  (forall name, name<>arraydef_0__meta -> name<>arraydef_0__sipState -> name<>arraydef_0__renameMemo ->
    name<>arraydef_0__renameMemoScratch -> memory t name=memory s name) /\
  (forall cell, cell<>8%nat -> cell<>21%nat -> cell<>28%nat -> cell<>29%nat -> cell<>30%nat -> meta_value t cell=meta_value s cell) /\
  length (memory t arraydef_0__meta)=length (memory s arraydef_0__meta) /\
  length (memory t arraydef_0__sipState)=length (memory s arraydef_0__sipState) /\
  stdin t=stdin s /\ stdout t=stdout s.
Lemma frame_trans s t u : storage_frame s t -> storage_frame t u -> storage_frame s u.
Proof.
  intros [Ha [Hm [Hl [Hs [Hi Ho]]]]] [Ha' [Hm' [Hl' [Hs' [Hi' Ho']]]]].
  split; [intros; now rewrite Ha',Ha by assumption|]. split; [intros; now rewrite Hm',Hm by assumption|]. repeat split; congruence.
Qed.
Lemma insert_frame s k result count : storage_frame s (result_state_below_half s k result count).
Proof.
  destruct (result_frame s k result count) as [Ha [Hm [Hl [Hi Ho]]]].
  split; [intros; now apply Ha|]. split; [intros; now apply Hm|].
  repeat split; try assumption. apply result_sip_length.
Qed.
Lemma grow_frame s grown count meaning : RenameMemoGrow.postcondition s grown count meaning -> storage_frame s grown.
Proof.
  intro Hpost. destruct (RenameMemoGrow.post_frame _ _ _ _ Hpost) as [Ha [Hm [Hl [Hs [Hi Ho]]]]].
  split; [exact Ha|]. split; [intros; now apply Hm|]. repeat split; assumption.
Qed.
Record postcondition s t size meaning : Prop := {
  post_capacity : meta_value t 29=Z.of_nat size;
  post_allocated : (size<=length (memory t arraydef_0__renameMemo))%nat;
  post_frame : storage_frame s t;
  post_nonfatal : meta_value t 8=0;
  post_live : meta_value t 30=Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table t) size);
  post_load : meta_value t 30<=Z.of_nat size/2;
  post_meaning : RenameMemoTable.represents (RenameMemoLookup.table t) size meaning;
  post_indexed : RenameMemoLookup.indexed t size
}.
Lemma post_reframe s grown final size meaning : storage_frame s grown -> postcondition grown final size meaning ->
  postcondition s final size meaning.
Proof.
  intros Hframe [Hcapacity Hallocated Hframe' Herror Hlive Hload Hmeaning Hindexed]. constructor; try assumption.
  now apply frame_trans with (t:=grown).
Qed.
Theorem generated_below_half_contract s bs ns count observations meaning :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> meta_value s 29=Z.of_nat count -> (0<count)%nat ->
  Z.of_nat count<=maximum -> meta_value s 30<Z.of_nat count/2 ->
  (count<=length (memory s arraydef_0__renameMemo))%nat ->
  meta_value s 30=Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table s) count) ->
  RenameMemoTable.represents (RenameMemoLookup.table s) count meaning ->
  meaning (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) (ns vardef_0__renameCachePut_value) ->
  RenameMemoLookup.indexed s count ->
  exists final, execObserved (funcdef_0__renameCachePut bs ns) (s,observations)=Some (tt,(final,observations)) /\
    postcondition s final count meaning.
Proof.
  intros Hmeta Hsip Hpositive Herror Hcount Hnonzero Hword Hload Hmemo Hlive Hmeaning Hresult Hindexed.
  set (k:=(ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth)).
  destruct (placement_available s k count Hnonzero (below_half_room s count Hlive Hload)) as [slot Hplace].
  set (final:=result_state_below_half s k (ns vardef_0__renameCachePut_value) count).
  exists final. split; [now apply generated_below_half|]. constructor.
  - destruct (result_frame s k (ns vardef_0__renameCachePut_value) count) as [_ [Hm _]].
    change (meta_value (result_state_below_half s k (ns vardef_0__renameCachePut_value) count) 29=Z.of_nat count).
    rewrite Hm by lia. exact Hcount.
  - unfold final. now rewrite result_memo_length.
  - apply insert_frame.
  - now apply result_nonfatal with (slot:=slot).
  - apply result_live_count with (slot:=slot); try assumption. now apply below_half_increment_word with (count:=count).
  - pose proof (result_live_upper s k (ns vardef_0__renameCachePut_value) count slot Hnonzero Hmemo Hplace) as Hupper.
    assert (Haccurate : meta_value final 30=Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table final) count)).
    { apply result_live_count with (slot:=slot); try assumption. now apply below_half_increment_word with (count:=count). }
    rewrite Haccurate. unfold final. lia.
  - now apply result_meaning.
  - now apply result_indexed.
Qed.
Theorem generated_invariant s bs ns count observations meaning :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> meta_value s 29=Z.of_nat count -> (2<=count)%nat ->
  Z.of_nat count<=9223372036854775807 -> meta_value s 30<=Z.of_nat count/2 ->
  (count<=length (memory s arraydef_0__renameMemo))%nat ->
  meta_value s 30=Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table s) count) ->
  RenameMemoTable.represents (RenameMemoLookup.table s) count meaning ->
  meaning (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) (ns vardef_0__renameCachePut_value) ->
  RenameMemoLookup.indexed s count ->
  exists final size, execObserved (funcdef_0__renameCachePut bs ns) (s,observations)=Some (tt,(final,observations)) /\
    (size=count \/ size=(2*count)%nat) /\ postcondition s final size meaning.
Proof.
  intros Hmeta Hsip Hpositive Herror Hcount Hnonzero Hword Hload Hmemo Hlive Hmeaning Hresult Hindexed.
  destruct (Z_lt_dec (meta_value s 30) (Z.of_nat count/2)) as [Hsmall|Hlarge].
  - destruct (generated_below_half_contract s bs ns count observations meaning Hmeta Hsip Hpositive Herror Hcount
      ltac:(lia) ltac:(unfold maximum; lia) Hsmall Hmemo Hlive Hmeaning Hresult Hindexed) as [final [Hrun Hpost]].
    exists final,count. split; [exact Hrun|]. split; [now left|exact Hpost].
  - destruct (RenameMemoGrow.generated_invariant s (fun _=>false) (fun _=>0) count observations meaning Hmeta Hsip Hpositive Herror
      Hcount ltac:(lia) Hword Hmemo Hmeaning) as [grown [Hgrow Hpost]].
    destruct (RenameMemoGrow.post_frame _ _ _ _ Hpost) as [Ha [Hm [Hl [Hs [Hi Ho]]]]].
    assert (Hgmeta : (31<length (memory grown arraydef_0__meta))%nat) by (now rewrite Hl).
    assert (Hgsip : (0<length (memory grown arraydef_0__sipState))%nat) by (now rewrite Hs).
    assert (Hgpositive : 0<meta_value grown 20) by (rewrite Hm by lia; exact Hpositive).
    assert (Hglive : meta_value grown 30=Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table grown) (2*count))).
    { rewrite Hm by lia. rewrite RenameMemoGrow.post_live with (s:=s) (count:=count) (meaning:=meaning) by exact Hpost. exact Hlive. }
    assert (Hdouble : Z.of_nat (2*count)/2=Z.of_nat count).
    { rewrite <-RenameMemoResize.double_value,Z.div_mul by lia. reflexivity. }
    assert (Hgload : meta_value grown 30<Z.of_nat (2*count)/2).
    { rewrite Hm by lia. rewrite Hdouble. pose proof (Z.div_mod (Z.of_nat count) 2 ltac:(lia)).
      pose proof (Z.mod_pos_bound (Z.of_nat count) 2 ltac:(lia)). lia. }
    destruct (generated_below_half_contract grown bs ns (2*count) observations meaning Hgmeta Hgsip Hgpositive
      (RenameMemoGrow.post_nonfatal _ _ _ _ Hpost) (RenameMemoGrow.post_capacity _ _ _ _ Hpost) ltac:(lia)
      ltac:(rewrite <-RenameMemoResize.double_value; exact (proj2 (RenameMemoResize.double_word count Hword))) Hgload
      (RenameMemoGrow.post_allocated _ _ _ _ Hpost) Hglive (RenameMemoGrow.post_meaning _ _ _ _ Hpost) Hresult
      (RenameMemoGrow.post_indexed _ _ _ _ Hpost)) as [final [Hrun Hfinal]].
    exists final,(2*count)%nat. split.
    + rewrite (generated_resize_composition s grown bs ns observations Hmeta Hgmeta ltac:(rewrite Hcount; lia)
        ltac:(rewrite (RenameMemoGrow.post_capacity _ _ _ _ Hpost); exact Hgload) Hgrow). exact Hrun.
    + split; [now right|]. exact (post_reframe s grown final (2*count) meaning (grow_frame s grown count meaning Hpost) Hfinal).
Qed.
End RenameMemoPut.
