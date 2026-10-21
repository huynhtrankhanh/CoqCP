From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameMemoTable RenameMemoLookup RenameMemoCapacity RenameMemoInit RenameMemoControl
  ObservedLocal Observation NativePrimitives.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoHit.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInit RenameMemoControl.
Definition loaded (f : Frame) top root depth phase left_id tag a b :=
  setNum (setNum (setNum (setNum (setNum (setNum (setNum (setNum f
    vardef_0__rename_top (Z.of_nat top)) vardef_0__rename_current root)
    vardef_0__rename_depth depth) vardef_0__rename_phase phase) vardef_0__rename_left left_id)
    vardef_0__rename_tag tag) vardef_0__rename_a a) vardef_0__rename_b b.
Definition arguments root depth := update (update (fun _=>0) vardef_0__renameCacheGet_node root) vardef_0__renameCacheGet_depth depth.
Definition hit_state looked top := store_meta (store_meta looked 0 (meta_value looked 31)) 10 (Z.of_nat top).
Definition hit_frame (f : Frame) looked top root depth left_id tag a b := setMachine (loaded f top root depth 0 left_id tag a b) (hit_state looked top).
Local Opaque funcdef_0__renameCacheGet funcdef_0__renameCachePut funcdef_0__intern funcdef_0__push funcdef_0__renameIndex Imperative.update.
Theorem generated_hit_composition (f : Frame) looked top root depth left_id tag a b observations :
  (31<length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 10=Z.of_nat (S top) -> meta_value (machine f) 8=0 -> Z.of_nat (S top)<=maximum ->
  (top<length (memory (machine f) arraydef_0__frames))%nat ->
  List.nth top (memory (machine f) arraydef_0__frames) (0,0,0,0)=(root,depth,0,left_id) ->
  (Z.to_nat root<length (memory (machine f) arraydef_0__formulas))%nat ->
  List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0)=(tag,a,b) ->
  execObserved (funcdef_0__renameCacheGet (fun _=>false) (arguments root depth)) (machine f,observations)=Some (tt,(looked,observations)) ->
  (31<length (memory looked arraydef_0__meta))%nat -> meta_value looked 31<>maximum ->
  execLocalObserved iteration (f,observations)=Some (KeepGoing,(hit_frame f looked top root depth left_id tag a b,observations)).
Proof.
  intros Hmeta Hcount Herror Hword Hframes Hframe Hformulas Hformula Hlookup Hlookmeta Hhit.
  assert (Htop : coerceInt (Z.of_nat (S top)-1) 64=Z.of_nat top).
  { replace (Z.of_nat (S top)-1) with (Z.of_nat top) by lia. apply coerce_word. unfold word. lia. }
  destruct f as [s bs ns]. cbn [machine] in *. unfold iteration,iteration_at.
  repeat first [progress cbn [optionBind fst snd negb]
    |progress rewrite drop_assoc |progress rewrite drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine]; repeat rewrite store_meta_length;
      lazymatch name with
      |arraydef_0__meta=>first
        [eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hmeta]
        |eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hlookmeta]]
      |arraydef_0__frames=>first [exact Hframes|rewrite Nat2Z.id; exact Hframes]
      |arraydef_0__formulas=>exact Hformulas end)
    |match goal with |- context [List.nth ?index (memory s arraydef_0__frames) ?zero]=>
      let expression:=constr:(List.nth index (memory s arraydef_0__frames) zero) in
      assert (Hsame : expression=(root,depth,0,left_id)) by exact Hframe; rewrite Hsame; clear Hsame end
    |match goal with |- context [List.nth ?index (memory s arraydef_0__formulas) ?zero]=>
      let expression:=constr:(List.nth index (memory s arraydef_0__formulas) zero) in
      assert (Hsame : expression=(tag,a,b)) by exact Hformula; rewrite Hsame; clear Hsame end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__renameCacheGet ?bp ?np) ?state]=>
      let expression:=constr:(@execObserved I T EI R (funcdef_0__renameCacheGet bp np) state) in
      assert (Hrun : expression=Some (tt,(looked,observations))) by exact Hlookup; rewrite Hrun; clear Hrun end
    |match goal with |- context [dropWithinLoop (bind (Done _ _ _ ?value) ?next)]=>
      let expression:=constr:(dropWithinLoop (bind (Done _ _ _ value) next)) in change expression with (dropWithinLoop (next value)) end
    |progress replace (Z.to_nat 31) with 31%nat by reflexivity
    |progress replace (Z.to_nat 10) with 10%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress rewrite Hcount |progress rewrite Herror |progress rewrite Htop |progress rewrite Nat2Z.id
    |progress rewrite updated_same |progress rewrite updated_other by discriminate
    |match goal with |- context [bool_decide ?P]=>first
      [progress rewrite (bool_decide_true P) by (try congruence; unfold maximum in *; lia)
      |progress rewrite (bool_decide_false P) by (try congruence; unfold maximum in *; lia)] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools subInt]
  ]. unfold hit_frame,hit_state,loaded. reflexivity.
Qed.
Definition storage_frame s t :=
  (forall name, name<>arraydef_0__meta -> name<>arraydef_0__sipState -> memory t name=memory s name) /\
  (forall cell, cell<>0%nat -> cell<>10%nat -> cell<>21%nat -> cell<>28%nat -> cell<>31%nat -> meta_value t cell=meta_value s cell) /\
  length (memory t arraydef_0__meta)=length (memory s arraydef_0__meta) /\ stdin t=stdin s /\ stdout t=stdout s.
Theorem hit_frame_storage s looked top : RenameMemoLookup.storage_frame s looked -> storage_frame s (hit_state looked top).
Proof.
  intros [Ha [Hm [Hl [Hi Ho]]]]. unfold storage_frame,hit_state. split.
  - intros name Hmeta Hsip. rewrite !store_meta_other by exact Hmeta. now apply Ha.
  - split.
    + intros cell H0 H10 H21 H28 H31. rewrite !meta_store_other by assumption. now apply Hm.
    + split; [now rewrite !store_meta_length|]. split; assumption.
Qed.
Lemma frame_table s t : storage_frame s t -> RenameMemoLookup.table t=RenameMemoLookup.table s.
Proof. intros [Ha _]. unfold RenameMemoLookup.table. now rewrite Ha by discriminate. Qed.
Lemma frame_hash s t count query : storage_frame s t -> RenameMemoLookup.hash_start t query count=RenameMemoLookup.hash_start s query count.
Proof. intros [_ [Hm _]]. unfold RenameMemoLookup.hash_start. now rewrite !Hm by lia. Qed.
Theorem frame_cache s t count meaning : storage_frame s t ->
  RenameMemoTable.represents (RenameMemoLookup.table s) count meaning -> RenameMemoLookup.indexed s count ->
  RenameMemoTable.represents (RenameMemoLookup.table t) count meaning /\ RenameMemoLookup.indexed t count /\
  meta_value t 8=meta_value s 8 /\ meta_value t 29=meta_value s 29 /\ meta_value t 30=meta_value s 30 /\
  RenameMemoCapacity.live (RenameMemoLookup.table t) count=RenameMemoCapacity.live (RenameMemoLookup.table s) count /\
  length (memory t arraydef_0__renameMemo)=length (memory s arraydef_0__renameMemo).
Proof.
  intros Hframe Hmeaning Hindexed. pose proof (frame_table s t Hframe) as Htable.
  destruct Hframe as [Ha [Hm [Hl [Hi Ho]]]]. split; [now rewrite Htable|]. split.
  - intros index Hindex Hoccupied. rewrite Htable in Hoccupied |- *.
    rewrite (frame_hash s t count _ ltac:(unfold storage_frame; repeat split; assumption)). now apply Hindexed.
  - split; [now apply Hm|]. split; [now apply Hm|]. split; [now apply Hm|].
    split; [now rewrite Htable|]. now rewrite Ha by discriminate.
Qed.
Definition parameters (before after : Frame) := forall variable,
  In variable [vardef_0__rename_node;vardef_0__rename_mode;vardef_0__rename_shift;vardef_0__rename_arg;
    vardef_0__rename_initialDepth;vardef_0__rename_width;vardef_0__rename_pairs;vardef_0__rename_budget] ->
  nums after variable=nums before variable.
Theorem hit_parameters (f : Frame) looked top root depth left_id tag a b :
  parameters f (hit_frame f looked top root depth left_id tag a b).
Proof.
  intros variable Hin. repeat destruct Hin as [<-|Hin]; try contradiction;
    unfold hit_frame,loaded; destruct f; cbv beta iota zeta delta [setMachine setNum nums bools machine];
    now repeat rewrite updated_other by discriminate.
Qed.
Theorem generated_hit s bs ns top root depth left_id tag a b count value observations meaning :
  (31<length (memory s arraydef_0__meta))%nat ->
  meta_value s 10=Z.of_nat (S top) -> meta_value s 8=0 -> Z.of_nat (S top)<=maximum ->
  (top<length (memory s arraydef_0__frames))%nat ->
  List.nth top (memory s arraydef_0__frames) (0,0,0,0)=(root,depth,0,left_id) ->
  (Z.to_nat root<length (memory s arraydef_0__formulas))%nat ->
  List.nth (Z.to_nat root) (memory s arraydef_0__formulas) (0,0,0)=(tag,a,b) ->
  (0<length (memory s arraydef_0__sipState))%nat -> 0<meta_value s 20 ->
  meta_value s 29=Z.of_nat count -> (0<count)%nat -> Z.of_nat count<=maximum ->
  (count<=length (memory s arraydef_0__renameMemo))%nat ->
  RenameMemoTable.represents (RenameMemoLookup.table s) count meaning ->
  RenameMemoLookup.lookup s (root,depth) count=Some value -> value<>maximum ->
  exists final, execLocalObserved iteration ({|machine:=s;bools:=bs;nums:=ns|},observations)=Some (KeepGoing,(final,observations)) /\
    meaning (root,depth) value /\ meta_value (machine final) 0=value /\ meta_value (machine final) 10=Z.of_nat top /\
    storage_frame s (machine final) /\ parameters {|machine:=s;bools:=bs;nums:=ns|} final.
Proof.
  intros Hmeta Hcount Herror Hword Hframes Hframe Hformulas Hformula Hsip Hpositive Hcapacity Hnonzero HmemoWord Hmemo Hmeaning Hfound Hsentinel.
  set (looked:=RenameMemoLookup.result_state s (root,depth) count).
  assert (Hlookup : execObserved (funcdef_0__renameCacheGet (fun _=>false) (arguments root depth)) (s,observations)=Some (tt,(looked,observations))).
  { pose proof (RenameMemoLookup.generated_lookup_exact s (fun _=>false) (arguments root depth) count observations Hmeta Hsip Hpositive Hcapacity Hnonzero HmemoWord Hmemo) as Hrun.
    cbv beta iota zeta delta [arguments] in Hrun.
    rewrite updated_same,updated_other,updated_same in Hrun by discriminate. exact Hrun. }
  assert (Hvalue : meta_value looked 31=value).
  { unfold looked. rewrite RenameMemoLookup.result_value,Hfound by exact Hmeta. reflexivity. }
  destruct (RenameMemoLookup.result_frame s (root,depth) count) as [Ha [Hm [Hl [Hi Ho]]]].
  assert (Hlookmeta : (31<length (memory looked arraydef_0__meta))%nat) by (unfold looked; now rewrite Hl).
  exists (hit_frame {|machine:=s;bools:=bs;nums:=ns|} looked top root depth left_id tag a b). split.
  - apply generated_hit_composition; try assumption. now rewrite Hvalue.
  - split.
    + exact (RenameMemoTable.scan_meaning (RenameMemoLookup.table s) count meaning (root,depth)
        (RenameMemoLookup.hash_start s (root,depth) count) count value Hnonzero
        (RenameMemoLookup.hash_start_bound s (root,depth) count Hnonzero) Hmeaning Hfound).
    + split.
      * change (meta_value (hit_state looked top) 0=value). unfold hit_state.
        rewrite meta_store_other by lia. rewrite meta_store_same by lia. exact Hvalue.
      * split.
        -- change (meta_value (hit_state looked top) 10=Z.of_nat top). unfold hit_state.
           apply meta_store_same. rewrite store_meta_length. lia.
        -- split.
           ++ apply hit_frame_storage. apply RenameMemoLookup.result_frame.
           ++ apply hit_parameters.
Qed.
End RenameMemoHit.
