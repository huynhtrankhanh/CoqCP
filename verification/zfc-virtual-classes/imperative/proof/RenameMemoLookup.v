From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ArrayFacts RenameMemoTable
  ObservedLocal Observation LocalObservation NativePrimitives.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module RenameMemoLookup.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet.
Definition LocalAction R := Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet)
  withLocalVariablesReturnValue R.
Definition table (s : Machine) index : RenameMemoTable.entry :=
  List.nth index (memory s arraydef_0__renameMemo) (0,0,0,0).
Definition key (f : Frame) := (nums f vardef_0__renameCacheGet_node,nums f vardef_0__renameCacheGet_depth).
Definition advance (f : Frame) size slot :=
  setNum f vardef_0__renameCacheGet_slot (Z.of_nat (RenameMemoTable.next size slot)).
Definition found (f : Frame) value := setMachine f (store_meta (machine f) 31 value).
Definition probe_body : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__renameCacheGet_body in funcdef_0__renameCacheGet_body in
  match code with context [loop _ ?body] =>
    let body := eval cbn zeta in body in exact body
  end).
Theorem generated_probe (f : Frame) remaining size slot e :
  (0 < size)%nat -> Z.of_nat size <= maximum -> (slot < size)%nat ->
  (size <= length (memory (machine f) arraydef_0__renameMemo))%nat ->
  (31 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__renameCacheGet_slot = Z.of_nat slot ->
  nums f vardef_0__renameCacheGet_size = Z.of_nat size -> table (machine f) slot = e ->
  execLocal (probe_body remaining) f =
    if bool_decide (RenameMemoTable.occupied e = 0) then Some (Stop,f)
    else if bool_decide (RenameMemoTable.matches e (key f)) then
      Some (Stop,found f (RenameMemoTable.value e))
    else Some (KeepGoing,advance f size slot).
Proof.
  intros Hpositive Hword Hslot Htable Hmeta Hindex Hsize Hentry.
  assert (Hincrement : word (Z.of_nat slot + 1)) by (unfold word; lia).
  destruct e as [[[node depth] value] occupied].
  destruct f as [s bs ns]. cbn [machine nums] in *.
  unfold table in Hentry.
  destruct (Z.eq_dec occupied 0); destruct (Z.eq_dec node (ns vardef_0__renameCacheGet_node));
    destruct (Z.eq_dec depth (ns vardef_0__renameCacheGet_depth)).
  all: unfold probe_body; cbn zeta.
  all: cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    shortCircuitAnd retrieve numberLocalGet numberLocalSet store break addInt modIntUnsigned
    execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
    Imperative.update decide decide_rel
    variableIndexEqualityDecidablevarsfuncdef_0__renameCacheGet varsfuncdef_0__renameCacheGet_rec
    RenameMemoTable.occupied RenameMemoTable.matches RenameMemoTable.node RenameMemoTable.depth
    RenameMemoTable.value key found advance RenameMemoTable.next].
  all: repeat first [progress rewrite Hindex |progress rewrite Hsize
    |progress rewrite (coerce_word _ Hincrement) |progress rewrite Nat2Z.id
    |progress rewrite nth_lt_default with (default := (0,0,0,0))
    |match goal with Hrawentry : @List.nth _ _ _ _ = ?entry |-
        context [@List.nth ?T ?index ?entries ?zero] =>
      let Hraw := fresh "Hraw" in
      assert (Hraw : @List.nth T index entries zero = entry) by exact Hrawentry;
      rewrite Hraw; clear Hraw end
    |progress rewrite Hentry
    |match goal with |- context [bool_decide ?P] => first
      [progress rewrite (bool_decide_true P) by (first [congruence|lia|tauto])
      |progress rewrite (bool_decide_false P) by (first [congruence|lia|tauto])] end
    |progress cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
      shortCircuitAnd retrieve numberLocalGet numberLocalSet store break addInt modIntUnsigned
      execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
      Imperative.update decide decide_rel
      variableIndexEqualityDecidablevarsfuncdef_0__renameCacheGet varsfuncdef_0__renameCacheGet_rec]
    |match goal with |- context [Nat.lt_dec ?i ?n] => destruct (Nat.lt_dec i n); [|exfalso; lia] end
    |match goal with |- context [numbers.Z.eq_dec ?a ?b] => destruct (numbers.Z.eq_dec a b); [exfalso; lia|] end
    |case_decide; [|lia]].
  all: try reflexivity.
  all: rewrite Nat2Z.inj_mod,Nat2Z.inj_succ; reflexivity.
Qed.
Definition parameters (initial final : Frame) :=
  nums final vardef_0__renameCacheGet_node = nums initial vardef_0__renameCacheGet_node /\
  nums final vardef_0__renameCacheGet_depth = nums initial vardef_0__renameCacheGet_depth /\
  nums final vardef_0__renameCacheGet_size = nums initial vardef_0__renameCacheGet_size.
Lemma advance_key f size slot : key (advance f size slot) = key f.
Proof. destruct f. reflexivity. Qed.
Lemma advance_parameters f size slot : parameters f (advance f size slot).
Proof. destruct f. repeat split; reflexivity. Qed.
Lemma parameters_trans f g h : parameters f g -> parameters g h -> parameters f h.
Proof. unfold parameters. intros [Hn [Hd Hs]] [Hn' [Hd' Hs']]. repeat split; congruence. Qed.
Theorem generated_scan fuel (f : Frame) size slot :
  (0 < size)%nat -> Z.of_nat size <= maximum -> (slot < size)%nat ->
  (size <= length (memory (machine f) arraydef_0__renameMemo))%nat ->
  (31 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__renameCacheGet_slot = Z.of_nat slot ->
  nums f vardef_0__renameCacheGet_size = Z.of_nat size ->
  exists final, execLocal (loop fuel probe_body) f = Some (tt,final) /\
    parameters f final /\
    machine final = match RenameMemoTable.scan (table (machine f)) size (key f) slot fuel with
      | Some value => store_meta (machine f) 31 value | None => machine f end.
Proof.
  induction fuel as [|fuel IH] in f,slot |- *.
  - intros. exists f. split; [reflexivity|]. split; [repeat split; reflexivity|reflexivity].
  - intros Hpositive Hword Hslot Htable Hmeta Hindex Hsize.
    rewrite loop_S,execLocal_bind.
    rewrite (generated_probe f fuel size slot (table (machine f) slot) Hpositive Hword Hslot Htable Hmeta Hindex Hsize eq_refl).
    cbn [RenameMemoTable.scan].
    destruct (bool_decide (RenameMemoTable.occupied (table (machine f) slot) = 0)) eqn:Hempty.
    + exists f. split; [reflexivity|]. split; [repeat split; reflexivity|reflexivity].
    + destruct (bool_decide (RenameMemoTable.matches (table (machine f) slot) (key f))) eqn:Hmatch.
      * exists (found f (RenameMemoTable.value (table (machine f) slot))).
        split; [reflexivity|]. split; [repeat split; reflexivity|reflexivity].
      * cbn [optionBind fst snd].
        destruct (IH (advance f size slot) (RenameMemoTable.next size slot) Hpositive Hword
          (RenameMemoTable.next_bound size slot Hpositive) Htable Hmeta eq_refl ltac:(exact Hsize))
          as [final [Hrun [Hparameters Hmachine]]].
        exists final. split; [exact Hrun|]. split.
        -- eapply parameters_trans; [apply advance_parameters|exact Hparameters].
        -- rewrite advance_key in Hmachine. exact Hmachine.
Qed.
Lemma scan_no_flush fuel : InternalObservation.local_nf (loop fuel probe_body).
Proof. apply InternalObservation.loop_nf. intro remaining. unfold probe_body. InternalObservation.nf. Qed.
Theorem generated_scan_observed fuel (f : Frame) size slot observations :
  (0 < size)%nat -> Z.of_nat size <= maximum -> (slot < size)%nat ->
  (size <= length (memory (machine f) arraydef_0__renameMemo))%nat ->
  (31 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__renameCacheGet_slot = Z.of_nat slot ->
  nums f vardef_0__renameCacheGet_size = Z.of_nat size ->
  exists final, execLocalObserved (loop fuel probe_body) (f,observations) = Some (tt,(final,observations)) /\
    parameters f final /\
    machine final = match RenameMemoTable.scan (table (machine f)) size (key f) slot fuel with
      | Some value => store_meta (machine f) 31 value | None => machine f end.
Proof.
  intros Hpositive Hword Hslot Htable Hmeta Hindex Hsize.
  destruct (generated_scan fuel f size slot Hpositive Hword Hslot Htable Hmeta Hindex Hsize)
    as [final [Hrun Hresult]]. exists final. split; [|exact Hresult].
  exact (LocalObservation.plain_observed _ f observations tt final (scan_no_flush fuel) Hrun).
Qed.
Definition prepared s (k : RenameMemoTable.key) :=
  hash_state (store_meta s 31 maximum) 5 (fst k) (snd k).
Lemma hash_meta_length s tag a b :
  length (memory (hash_state s tag a b) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold hash_state. rewrite !store_meta_length,hash_work_other by discriminate. reflexivity. Qed.
Lemma prepared_meta_length s k :
  length (memory (prepared s k) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold prepared. rewrite hash_meta_length,store_meta_length. reflexivity. Qed.
Lemma prepared_table s k : table (prepared s k) = table s.
Proof.
  unfold table,prepared. rewrite hash_preserves_array by discriminate.
  now rewrite store_meta_other by discriminate.
Qed.
Lemma prepared_memo s k : memory (prepared s k) arraydef_0__renameMemo = memory s arraydef_0__renameMemo.
Proof. unfold prepared. rewrite hash_preserves_array by discriminate. now rewrite store_meta_other by discriminate. Qed.
Lemma prepared_miss s k : (31 < length (memory s arraydef_0__meta))%nat -> meta_value (prepared s k) 31 = maximum.
Proof. intro Hmeta. unfold prepared. rewrite hash_preserves_meta by lia. now apply meta_store_same. Qed.
Lemma prepared_meta_other s k i : i <> 21%nat -> i <> 28%nat -> i <> 31%nat ->
  meta_value (prepared s k) i = meta_value s i.
Proof. intros H21 H28 H31. unfold prepared. rewrite hash_preserves_meta by assumption. now apply meta_store_other. Qed.
Definition start_frame (f : Frame) count :=
  setNum (setMachine (setNum f vardef_0__renameCacheGet_size (Z.of_nat count)) (prepared (machine f) (key f)))
    vardef_0__renameCacheGet_slot (meta_value (prepared (machine f) (key f)) 28 mod Z.of_nat count).
Definition body_with (scan : Z -> LocalAction unit) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__renameCacheGet_body in funcdef_0__renameCacheGet_body in
  match code with context [bind (numberLocalGet _ _ _ vardef_0__renameCacheGet_size) ?next] =>
    let candidate := eval cbn beta in (next 0%Z) in
    lazymatch candidate with loop _ _ =>
      let abstracted := eval pattern next in code in
      lazymatch abstracted with ?family _ => exact (family scan) end
    end
  end).
Lemma body_actual : funcdef_0__renameCacheGet_body = body_with (fun count=>loop (Z.to_nat count) probe_body).
Proof. reflexivity. Qed.
Lemma hash_observed s bs ns observations :
  (28 < length (memory s arraydef_0__meta))%nat -> (0 < length (memory s arraydef_0__sipState))%nat ->
  0 < meta_value s 20 ->
  execObserved (funcdef_0__formulaHash bs ns) (s,observations) =
    Some (tt,(hash_state s (ns vardef_0__formulaHash_tag) (ns vardef_0__formulaHash_a) (ns vardef_0__formulaHash_b),observations)).
Proof.
  intros Hmeta Hsip Hpositive. apply observed_plain; [apply InternalObservation.formulaHash_nf|].
  now apply generated_hash.
Qed.
Local Opaque funcdef_0__formulaHash hash_state.
Theorem generated_body_composition scan (f after : Frame) count observations :
  (31 < length (memory (machine f) arraydef_0__meta))%nat ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  0 < meta_value (machine f) 20 -> meta_value (machine f) 29 = Z.of_nat count -> (0 < count)%nat ->
  execLocalObserved (scan (Z.of_nat count)) (start_frame f count,observations) = Some (tt,(after,observations)) ->
  execLocalObserved (body_with scan) (f,observations) = Some (tt,(after,observations)).
Proof.
  intros Hmeta Hsip Hpositive Hcount Hnonzero Hscan. destruct f as [s bs ns]. cbn [machine] in *.
  unfold body_with.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine setNum];
       repeat first [rewrite store_meta_length |rewrite hash_meta_length]; eapply Nat.le_lt_trans with (m := 31%nat); [cbn; lia|exact Hmeta])
    |progress rewrite hash_observed by
       (cbn [machine setMachine setNum]; rewrite ?store_meta_length,?store_meta_other by discriminate;
        try rewrite meta_store_other by lia; first [exact Hsip|exact Hpositive|lia])
    |progress replace (Z.to_nat 31) with 31%nat by reflexivity
    |progress replace (Z.to_nat 29) with 29%nat by reflexivity
    |progress replace (Z.to_nat 28) with 28%nat by reflexivity
    |progress rewrite meta_store_other by lia
    |progress rewrite Hcount
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools key
       Imperative.update decide decide_rel
       variableIndexEqualityDecidablevarsfuncdef_0__renameCacheGet varsfuncdef_0__renameCacheGet_rec
       variableIndexEqualityDecidablevarsfuncdef_0__formulaHash varsfuncdef_0__formulaHash_rec modIntUnsigned]
    |match goal with |- context [numbers.Z.eq_dec ?a ?b] => destruct (numbers.Z.eq_dec a b); [exfalso; lia|] end
    |match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (scan ?n) ?state] =>
       let expression := constr:(@execLocalObserved I T EI V EV R (scan n) state) in
       let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(after,observations))) by exact Hscan;
       rewrite Hrun; clear Hrun end
  ]. reflexivity.
Qed.
Lemma prepared_hash s k : (31 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat ->
  meta_value (prepared s k) 28 = siphash24 (meta_value s 26) (meta_value s 27) 5 (fst k) (snd k).
Proof.
  intros Hmeta Hsip. unfold prepared. rewrite hash_result.
  - now rewrite !meta_store_other by lia.
  - rewrite store_meta_length. lia.
  - rewrite store_meta_other by discriminate. exact Hsip.
Qed.
Definition hash_start s (k : RenameMemoTable.key) count :=
  Z.to_nat (siphash24 (meta_value s 26) (meta_value s 27) 5 (fst k) (snd k) mod Z.of_nat count).
Lemma hash_start_bound s k count : (0 < count)%nat -> (hash_start s k count < count)%nat.
Proof.
  intros Hcount. unfold hash_start.
  pose proof (Z.mod_pos_bound (siphash24 (meta_value s 26) (meta_value s 27) 5 (fst k) (snd k))
    (Z.of_nat count) ltac:(lia)) as Hmod.
  pose proof (Z2Nat.id _ (proj1 Hmod)). lia.
Qed.
Lemma start_key f count : key (start_frame f count) = key f.
Proof. destruct f. reflexivity. Qed.
Lemma start_size f count : nums (start_frame f count) vardef_0__renameCacheGet_size = Z.of_nat count.
Proof. destruct f. reflexivity. Qed.
Lemma start_slot f count : (31 < length (memory (machine f) arraydef_0__meta))%nat ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat -> (0 < count)%nat ->
  nums (start_frame f count) vardef_0__renameCacheGet_slot = Z.of_nat (hash_start (machine f) (key f) count).
Proof.
  intros Hmeta Hsip Hcount. change (meta_value (prepared (machine f) (key f)) 28 mod Z.of_nat count = Z.of_nat (hash_start (machine f) (key f) count)).
  rewrite prepared_hash by assumption. unfold hash_start. rewrite Z2Nat.id; [reflexivity|].
  apply Z.mod_pos_bound. lia.
Qed.
Definition lookup s k count := RenameMemoTable.scan (table s) count k (hash_start s k count) count.
Definition result_state s k count := match lookup s k count with
  | Some value => store_meta (prepared s k) 31 value | None => prepared s k end.
Theorem generated_lookup_exact s bs ns count observations :
  (31 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat -> 0 < meta_value s 20 ->
  meta_value s 29 = Z.of_nat count -> (0 < count)%nat -> Z.of_nat count <= maximum ->
  (count <= length (memory s arraydef_0__renameMemo))%nat ->
  let k := (ns vardef_0__renameCacheGet_node,ns vardef_0__renameCacheGet_depth) in
  execObserved (funcdef_0__renameCacheGet bs ns) (s,observations) =
    Some (tt,(result_state s k count,observations)).
Proof.
  intros Hmeta Hsip Hpositive Hcount Hnonzero Hword Htable k.
  set (initial := ({|machine := s; bools := bs; nums := ns|} : Frame)).
  set (start := start_frame initial count).
  assert (Hstartmachine : machine start = prepared s k) by reflexivity.
  destruct (generated_scan_observed count start count (hash_start s k count) observations Hnonzero Hword
    (hash_start_bound s k count Hnonzero)
    ltac:(rewrite Hstartmachine,prepared_memo; exact Htable)
    ltac:(rewrite Hstartmachine,prepared_meta_length; exact Hmeta)
    ltac:(exact (start_slot initial count Hmeta Hsip Hnonzero)) (start_size initial count))
    as [final [Hscan [Hparameters Hmachine]]].
  assert (HscanZ : execLocalObserved (loop (Z.to_nat (Z.of_nat count)) probe_body) (start,observations) = Some (tt,(final,observations))).
  { now rewrite Nat2Z.id. }
  pose proof (generated_body_composition (fun n=>loop (Z.to_nat n) probe_body) initial final count observations
    Hmeta Hsip Hpositive Hcount Hnonzero HscanZ) as Hbody.
  rewrite <-body_actual in Hbody.
  assert (Hfinal : machine final = result_state s k count).
  { assert (Hkey : key start = k) by (apply start_key).
    rewrite Hstartmachine,prepared_table,Hkey in Hmachine. exact Hmachine. }
  unfold funcdef_0__renameCacheGet. rewrite ObservedLocal.eliminate_correct.
  match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state] =>
    let expression := constr:(@execLocalObserved I T EI V EV R code state) in
    let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(final,observations))) by exact Hbody;
    rewrite Hrun
  end.
  cbn [optionBind fst snd]. now rewrite Hfinal.
Qed.
Definition storage_frame s t :=
  (forall name, name <> arraydef_0__meta -> name <> arraydef_0__sipState -> memory t name = memory s name) /\
  (forall i, i <> 21%nat -> i <> 28%nat -> i <> 31%nat -> meta_value t i = meta_value s i) /\
  length (memory t arraydef_0__meta) = length (memory s arraydef_0__meta) /\
  stdin t = stdin s /\ stdout t = stdout s.
Lemma prepared_frame s k : storage_frame s (prepared s k).
Proof.
  split.
  - intros name Hmeta Hsip. unfold prepared. rewrite hash_preserves_array by assumption. now apply store_meta_other.
  - split; [intros; now apply prepared_meta_other|]. split; [apply prepared_meta_length|].
    unfold prepared. split; reflexivity.
Qed.
Lemma store_frame s v : storage_frame s (store_meta s 31 v).
Proof.
  split; [intros; now apply store_meta_other|]. split; [intros; now apply meta_store_other|].
  split; [apply store_meta_length|]. split; reflexivity.
Qed.
Lemma frame_trans s t u : storage_frame s t -> storage_frame t u -> storage_frame s u.
Proof.
  intros [Ha [Hm [Hl [Hi Ho]]]] [Ha' [Hm' [Hl' [Hi' Ho']]]].
  split; [intros; now rewrite Ha',Ha by assumption|].
  split; [intros; now rewrite Hm',Hm by assumption|]. repeat split; congruence.
Qed.
Theorem result_frame s k count : storage_frame s (result_state s k count).
Proof.
  unfold result_state. destruct (lookup s k count); [|apply prepared_frame].
  eapply frame_trans; [apply prepared_frame|apply store_frame].
Qed.
Theorem result_value s k count : (31 < length (memory s arraydef_0__meta))%nat ->
  meta_value (result_state s k count) 31 = match lookup s k count with Some value=>value |None=>maximum end.
Proof.
  intro Hmeta. unfold result_state. destruct (lookup s k count); [|now apply prepared_miss].
  apply meta_store_same. now rewrite prepared_meta_length.
Qed.
Theorem lookup_sound s count k result : (0 < count)%nat -> lookup s k count = Some result ->
  exists index, (index < count)%nat /\ RenameMemoTable.occupied (table s index) <> 0 /\
    RenameMemoTable.matches (table s index) k /\ RenameMemoTable.value (table s index) = result.
Proof. intros Hpositive Hlookup. exact (RenameMemoTable.scan_sound (table s) count k (hash_start s k count) count result Hpositive (hash_start_bound s k count Hpositive) Hlookup). Qed.
Definition indexed s count := forall index, (index < count)%nat -> RenameMemoTable.occupied (table s index) <> 0 ->
  exists distance, (distance < count)%nat /\
    RenameMemoTable.accessible (table s) count
      (hash_start s (RenameMemoTable.node (table s index),RenameMemoTable.depth (table s index)) count) index distance.
Theorem lookup_complete s count k index : indexed s count -> (index < count)%nat ->
  RenameMemoTable.occupied (table s index) <> 0 -> RenameMemoTable.matches (table s index) k ->
  exists result, lookup s k count = Some result.
Proof.
  intros Hindexed Hindex Hoccupied Hmatches.
  destruct (Hindexed index Hindex Hoccupied) as [distance [Hdistance Hpath]].
  assert (Hkey : (RenameMemoTable.node (table s index),RenameMemoTable.depth (table s index)) = k).
  { destruct k as [kn kd]. destruct Hmatches as [Hn Hd]. cbn in Hn,Hd. now rewrite Hn,Hd. }
  rewrite Hkey in Hpath. exact (RenameMemoTable.scan_complete (table s) count k _ index distance count Hpath Hdistance Hoccupied Hmatches).
Qed.
Theorem lookup_miss_absent s count k : indexed s count -> lookup s k count = None ->
  forall index, (index < count)%nat -> RenameMemoTable.occupied (table s index) <> 0 ->
    ~ RenameMemoTable.matches (table s index) k.
Proof.
  intros Hindexed Hmiss index Hindex Hoccupied Hmatches.
  destruct (lookup_complete s count k index Hindexed Hindex Hoccupied Hmatches) as [result Hhit]. congruence.
Qed.
Theorem generated_lookup_refines s bs ns count observations :
  (31 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat -> 0 < meta_value s 20 ->
  meta_value s 29 = Z.of_nat count -> (0 < count)%nat -> Z.of_nat count <= maximum ->
  (count <= length (memory s arraydef_0__renameMemo))%nat ->
  let k := (ns vardef_0__renameCacheGet_node,ns vardef_0__renameCacheGet_depth) in
  exists final, execObserved (funcdef_0__renameCacheGet bs ns) (s,observations) = Some (tt,(final,observations)) /\
    storage_frame s final /\
    meta_value final 31 = match lookup s k count with Some value=>value |None=>maximum end.
Proof.
  intros Hmeta Hsip Hpositive Hcount Hnonzero Hword Htable k.
  exists (result_state s k count). split; [now apply generated_lookup_exact|].
  split; [apply result_frame|now apply result_value].
Qed.
Theorem generated_hit_sound s bs ns count observations meaning :
  (31 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat -> 0 < meta_value s 20 ->
  meta_value s 29 = Z.of_nat count -> (0 < count)%nat -> Z.of_nat count <= maximum ->
  (count <= length (memory s arraydef_0__renameMemo))%nat ->
  RenameMemoTable.represents (table s) count meaning ->
  let k := (ns vardef_0__renameCacheGet_node,ns vardef_0__renameCacheGet_depth) in
  exists final, execObserved (funcdef_0__renameCacheGet bs ns) (s,observations) = Some (tt,(final,observations)) /\
    storage_frame s final /\ (meta_value final 31 <> maximum -> meaning k (meta_value final 31)).
Proof.
  intros Hmeta Hsip Hpositive Hcount Hnonzero Hword Htable Hmeaning k.
  destruct (generated_lookup_refines s bs ns count observations Hmeta Hsip Hpositive Hcount Hnonzero Hword Htable)
    as [final [Hrun [Hframe Hvalue]]]. exists final. split; [exact Hrun|]. split; [exact Hframe|].
  change (meta_value final 31 = match lookup s k count with Some value=>value |None=>maximum end) in Hvalue.
  intros Hhit. destruct (lookup s k count) as [result|] eqn:Hlookup; [|congruence]. rewrite Hvalue.
  exact (RenameMemoTable.scan_meaning (table s) count meaning k (hash_start s k count) count result
    Hnonzero (hash_start_bound s k count Hnonzero) Hmeaning Hlookup).
Qed.
Theorem generated_hit_iff s bs ns count observations :
  (31 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat -> 0 < meta_value s 20 ->
  meta_value s 29 = Z.of_nat count -> (0 < count)%nat -> Z.of_nat count <= maximum ->
  (count <= length (memory s arraydef_0__renameMemo))%nat -> indexed s count ->
  (forall index, (index < count)%nat -> RenameMemoTable.occupied (table s index) <> 0 ->
    RenameMemoTable.value (table s index) <> maximum) ->
  let k := (ns vardef_0__renameCacheGet_node,ns vardef_0__renameCacheGet_depth) in
  exists final, execObserved (funcdef_0__renameCacheGet bs ns) (s,observations) = Some (tt,(final,observations)) /\
    storage_frame s final /\
    (meta_value final 31 <> maximum <-> exists index, (index < count)%nat /\
      RenameMemoTable.occupied (table s index) <> 0 /\ RenameMemoTable.matches (table s index) k).
Proof.
  intros Hmeta Hsip Hpositive Hcount Hnonzero Hword Htable Hindexed Hsentinel k.
  destruct (generated_lookup_refines s bs ns count observations Hmeta Hsip Hpositive Hcount Hnonzero Hword Htable)
    as [final [Hrun [Hframe Hvalue]]]. exists final. split; [exact Hrun|]. split; [exact Hframe|].
  change (meta_value final 31 = match lookup s k count with Some value=>value |None=>maximum end) in Hvalue.
  split.
  - intros Hhit. destruct (lookup s k count) as [result|] eqn:Hlookup; [|congruence].
    destruct (lookup_sound s count k result Hnonzero Hlookup) as [index [Hindex [Hoccupied [Hmatches Hresult]]]].
    exists index. split; [exact Hindex|]. split; assumption.
  - intros [index [Hindex [Hoccupied Hmatches]]].
    destruct (lookup_complete s count k index Hindexed Hindex Hoccupied Hmatches) as [result Hlookup].
    rewrite Hlookup in Hvalue. rewrite Hvalue.
    destruct (lookup_sound s count k result Hnonzero Hlookup) as [found_index [Hfound [Hfound_occupied [Hmatch Hresult]]]].
    rewrite <-Hresult. now apply Hsentinel.
Qed.
End RenameMemoLookup.





