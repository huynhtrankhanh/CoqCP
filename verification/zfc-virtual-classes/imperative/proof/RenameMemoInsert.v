From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow SipHash ArrayFacts RenameMemoTable RenameMemoLookup RenameMemoPlacement RenameMemoCapacity
  ObservedLocal Observation LocalObservation NativePrimitives.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoInsert.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut.
Definition LocalAction R := Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut)
  withLocalVariablesReturnValue R.
Definition key (f : Frame) := (nums f vardef_0__renameCachePut_node,nums f vardef_0__renameCachePut_depth).
Definition value (f : Frame) := nums f vardef_0__renameCachePut_value.
Definition store_entry (s : Machine) (slot : nat) (k : RenameMemoTable.key) (result : Z) :=
  withMemory s (modifyArray (memory s) arraydef_0__renameMemo slot (fst k,snd k,result,1)).
Lemma modify_memo_meta (values : forall name, list (arrayType _ environment1 name)) slot
  (e : RenameMemoTable.entry) : modifyArray values arraydef_0__renameMemo slot e arraydef_0__meta = values arraydef_0__meta.
Proof. reflexivity. Qed.
Definition update_result s slot k result :=
  if bool_decide (RenameMemoTable.occupied (RenameMemoLookup.table s slot) = 0%Z)
  then store_meta (store_entry s slot k result) 30 (coerceInt (meta_value s 30 + 1) 64)
  else store_entry s slot k result.
Definition advance (f : Frame) size slot := setNum f vardef_0__renameCachePut_slot (Z.of_nat (RenameMemoTable.next size slot)).
Definition placed (f : Frame) slot :=
  setNum (setMachine f (update_result (machine f) slot (key f) (value f))) vardef_0__renameCachePut_placed 1.
Definition probe_body : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__renameCachePut_body in funcdef_0__renameCachePut_body in
  match code with context [loop _ ?body] => let body := eval cbn zeta in body in exact body end).
Theorem generated_probe (f : Frame) remaining size slot e :
  (0 < size)%nat -> Z.of_nat size <= maximum -> (slot < size)%nat ->
  (size <= length (memory (machine f) arraydef_0__renameMemo))%nat ->
  (30 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__renameCachePut_slot = Z.of_nat slot ->
  nums f vardef_0__renameCachePut_size = Z.of_nat size -> RenameMemoLookup.table (machine f) slot = e ->
  execLocal (probe_body remaining) f =
    if bool_decide (RenameMemoTable.occupied e = 0) then Some (Stop,placed f slot)
    else if bool_decide (RenameMemoTable.matches e (key f)) then Some (Stop,placed f slot)
    else Some (KeepGoing,advance f size slot).
Proof.
  intros Hpositive Hword Hslot Htable Hmeta Hindex Hsize Hentry.
  assert (Hincrement : word (Z.of_nat slot + 1)) by (unfold word; lia).
  destruct e as [[[node depth] oldvalue] occupied].
  destruct f as [s bs ns]. cbn [machine nums] in *.
  unfold RenameMemoLookup.table in Hentry.
  destruct (Z.eq_dec occupied 0); destruct (Z.eq_dec node (ns vardef_0__renameCachePut_node));
    destruct (Z.eq_dec depth (ns vardef_0__renameCachePut_depth)).
  all: unfold probe_body; cbn zeta.
  all: cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    shortCircuitAnd retrieve numberLocalGet numberLocalSet store break addInt modIntUnsigned
    execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
    Imperative.update decide decide_rel
    variableIndexEqualityDecidablevarsfuncdef_0__renameCachePut varsfuncdef_0__renameCachePut_rec
    RenameMemoTable.occupied RenameMemoTable.matches RenameMemoTable.node RenameMemoTable.depth
    RenameMemoTable.value key value placed advance RenameMemoTable.next].
  all: repeat first [progress rewrite Hindex |progress rewrite Hsize
    |progress rewrite (coerce_word _ Hincrement) |progress rewrite Nat2Z.id
    |progress rewrite nth_lt_default with (default := (0,0,0,0))
    |progress rewrite nth_lt_default with (default := 0)
    |match goal with Hrawentry : @List.nth _ _ _ _ = ?entry |-
        context [@List.nth ?T ?index ?entries ?zero] =>
      let Hraw := fresh "Hraw" in assert (Hraw : @List.nth T index entries zero = entry) by exact Hrawentry;
      rewrite Hraw; clear Hraw end
    |progress rewrite Hentry
    |match goal with |- context [bool_decide ?P] => first
      [progress rewrite (bool_decide_true P) by (first [congruence|lia|tauto])
      |progress rewrite (bool_decide_false P) by (first [congruence|lia|tauto])] end
    |progress cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
      shortCircuitAnd retrieve numberLocalGet numberLocalSet store break addInt modIntUnsigned
      execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
      Imperative.update decide decide_rel
      variableIndexEqualityDecidablevarsfuncdef_0__renameCachePut varsfuncdef_0__renameCachePut_rec]
    |progress rewrite modify_memo_meta
    |progress cbn [memory withMemory modifyArray]
    |match goal with |- context [Nat.lt_dec ?i ?n] => destruct (Nat.lt_dec i n); [|exfalso; lia] end
    |match goal with |- context [numbers.Z.eq_dec ?a ?b] => destruct (numbers.Z.eq_dec a b); [exfalso; lia|] end
    |case_decide; [|lia]].
  all: unfold update_result, RenameMemoLookup.table, RenameMemoTable.occupied.
  all: cbn [machine key value nums].
  all: try rewrite Hentry.
  all: repeat first [rewrite bool_decide_true by assumption |rewrite bool_decide_false by assumption].
  all: try reflexivity.
  all: try (rewrite Nat2Z.inj_mod,Nat2Z.inj_succ; reflexivity).
Qed.
Definition parameters (initial final : Frame) :=
  nums final vardef_0__renameCachePut_node = nums initial vardef_0__renameCachePut_node /\
  nums final vardef_0__renameCachePut_depth = nums initial vardef_0__renameCachePut_depth /\
  nums final vardef_0__renameCachePut_value = nums initial vardef_0__renameCachePut_value /\
  nums final vardef_0__renameCachePut_size = nums initial vardef_0__renameCachePut_size.
Lemma advance_key f size slot : key (advance f size slot) = key f.
Proof. destruct f. reflexivity. Qed.
Lemma advance_value f size slot : value (advance f size slot) = value f.
Proof. destruct f. reflexivity. Qed.
Lemma advance_parameters f size slot : parameters f (advance f size slot).
Proof. destruct f. repeat split; reflexivity. Qed.
Lemma parameters_trans f g h : parameters f g -> parameters g h -> parameters f h.
Proof. unfold parameters. intros [Hn [Hd [Hv Hs]]] [Hn' [Hd' [Hv' Hs']]]. repeat split; congruence. Qed.
Theorem generated_scan fuel (f : Frame) size slot :
  (0 < size)%nat -> Z.of_nat size <= maximum -> (slot < size)%nat ->
  (size <= length (memory (machine f) arraydef_0__renameMemo))%nat ->
  (30 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__renameCachePut_slot = Z.of_nat slot ->
  nums f vardef_0__renameCachePut_size = Z.of_nat size -> nums f vardef_0__renameCachePut_placed = 0 ->
  exists final, execLocal (loop fuel probe_body) f = Some (tt,final) /\
    parameters f final /\
    nums final vardef_0__renameCachePut_placed =
      match RenameMemoPlacement.place (RenameMemoLookup.table (machine f)) size (key f) slot fuel with Some _=>1 |None=>0 end /\
    machine final = match RenameMemoPlacement.place (RenameMemoLookup.table (machine f)) size (key f) slot fuel with
      | Some index => update_result (machine f) index (key f) (value f) | None => machine f end.
Proof.
  induction fuel as [|fuel IH] in f,slot |- *.
  - intros Hpositive Hword Hslot Htable Hmeta Hindex Hsize Hplaced.
    exists f. split; [reflexivity|]. split; [repeat split; reflexivity|]. split; [exact Hplaced|reflexivity].
  - intros Hpositive Hword Hslot Htable Hmeta Hindex Hsize Hplaced.
    rewrite loop_S,execLocal_bind.
    rewrite (generated_probe f fuel size slot (RenameMemoLookup.table (machine f) slot) Hpositive Hword Hslot Htable Hmeta Hindex Hsize eq_refl).
    cbn [RenameMemoPlacement.place].
    destruct (bool_decide (RenameMemoTable.occupied (RenameMemoLookup.table (machine f) slot) = 0)) eqn:Hempty.
    + exists (placed f slot). split; [reflexivity|]. split; [repeat split; reflexivity|]. split; reflexivity.
    + destruct (bool_decide (RenameMemoTable.matches (RenameMemoLookup.table (machine f) slot) (key f))) eqn:Hmatch.
      * exists (placed f slot). split; [reflexivity|]. split; [repeat split; reflexivity|]. split; reflexivity.
      * cbn [optionBind fst snd].
        destruct (IH (advance f size slot) (RenameMemoTable.next size slot) Hpositive Hword
          (RenameMemoTable.next_bound size slot Hpositive) Htable Hmeta eq_refl ltac:(exact Hsize) ltac:(exact Hplaced))
          as [final [Hrun [Hparameters [Hflag Hmachine]]]].
        exists final. split; [exact Hrun|]. split.
        -- eapply parameters_trans; [apply advance_parameters|exact Hparameters].
        -- rewrite advance_key in Hflag. split; [exact Hflag|]. rewrite advance_key,advance_value in Hmachine. exact Hmachine.
Qed.
Lemma scan_no_flush fuel : InternalObservation.local_nf (loop fuel probe_body).
Proof. apply InternalObservation.loop_nf. intro remaining. unfold probe_body. InternalObservation.nf. Qed.
Theorem generated_scan_observed fuel (f : Frame) size slot observations :
  (0 < size)%nat -> Z.of_nat size <= maximum -> (slot < size)%nat ->
  (size <= length (memory (machine f) arraydef_0__renameMemo))%nat ->
  (30 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__renameCachePut_slot = Z.of_nat slot ->
  nums f vardef_0__renameCachePut_size = Z.of_nat size -> nums f vardef_0__renameCachePut_placed = 0 ->
  exists final, execLocalObserved (loop fuel probe_body) (f,observations) = Some (tt,(final,observations)) /\
    parameters f final /\
    nums final vardef_0__renameCachePut_placed =
      match RenameMemoPlacement.place (RenameMemoLookup.table (machine f)) size (key f) slot fuel with Some _=>1 |None=>0 end /\
    machine final = match RenameMemoPlacement.place (RenameMemoLookup.table (machine f)) size (key f) slot fuel with
      | Some index => update_result (machine f) index (key f) (value f) | None => machine f end.
Proof.
  intros Hpositive Hword Hslot Htable Hmeta Hindex Hsize Hplaced.
  destruct (generated_scan fuel f size slot Hpositive Hword Hslot Htable Hmeta Hindex Hsize Hplaced)
    as [final [Hrun Hresult]]. exists final. split; [|exact Hresult].
  exact (LocalObservation.plain_observed _ f observations tt final (scan_no_flush fuel) Hrun).
Qed.
Lemma store_entry_meta_length s slot k result :
  length (memory (store_entry s slot k result) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold store_entry. cbn [memory withMemory]. now rewrite modify_memo_meta. Qed.
Lemma update_meta_length s slot k result :
  length (memory (update_result s slot k result) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof.
  unfold update_result. destruct bool_decide; [rewrite store_meta_length|]; apply store_entry_meta_length.
Qed.
Definition prepared s (k : RenameMemoTable.key) := hash_state s 5 (fst k) (snd k).
Definition start_frame (f : Frame) count :=
  setNum (setNum (setMachine (setNum f vardef_0__renameCachePut_size (Z.of_nat count)) (prepared (machine f) (key f)))
    vardef_0__renameCachePut_slot (meta_value (prepared (machine f) (key f)) 28 mod Z.of_nat count))
    vardef_0__renameCachePut_placed 0.
Definition finish_frame (f : Frame) := if bool_decide (nums f vardef_0__renameCachePut_placed = 0)
  then setMachine f (store_meta (machine f) 8 1) else f.
Definition body_with (scan : Z -> LocalAction unit) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__renameCachePut_body in funcdef_0__renameCachePut_body in
  match code with context [bind (numberLocalGet _ _ _ vardef_0__renameCachePut_size) ?next] =>
    let candidate := eval cbn beta in (next 0%Z) in
    lazymatch candidate with loop _ _ =>
      let abstracted := eval pattern next in code in
      lazymatch abstracted with ?family _ => exact (family scan) end
    end
  end).
Lemma body_actual : funcdef_0__renameCachePut_body = body_with (fun count=>loop (Z.to_nat count) probe_body).
Proof. reflexivity. Qed.
Local Opaque funcdef_0__formulaHash funcdef_0__renameCacheGrow hash_state.
Theorem generated_body_below_half scan (f after : Frame) count observations :
  (31 < length (memory (machine f) arraydef_0__meta))%nat ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  0 < meta_value (machine f) 20 -> meta_value (machine f) 8 = 0 ->
  meta_value (machine f) 29 = Z.of_nat count -> (0 < count)%nat ->
  meta_value (machine f) 30 < Z.of_nat count / 2 ->
  (31 < length (memory (machine after) arraydef_0__meta))%nat ->
  execLocalObserved (scan (Z.of_nat count)) (start_frame f count,observations) = Some (tt,(after,observations)) ->
  execLocalObserved (body_with scan) (f,observations) = Some (tt,(finish_frame after,observations)).
Proof.
  intros Hmeta Hsip Hpositive Herror Hcount Hnonzero Hload Hafter Hscan.
  destruct f as [s bs ns]. cbn [machine] in *. unfold body_with.
  let run := ltac:(repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine setNum];
       repeat first [rewrite store_meta_length |rewrite RenameMemoLookup.hash_meta_length];
       first [eapply Nat.le_lt_trans with (m := 31%nat); [cbn; lia|exact Hmeta]
             |eapply Nat.le_lt_trans with (m := 31%nat); [cbn; lia|exact Hafter]])
    |progress rewrite RenameMemoLookup.hash_observed by
       (cbn [machine setMachine setNum]; first [exact Hsip|exact Hpositive|lia])
    |progress replace (Z.to_nat 30) with 30%nat by reflexivity
    |progress replace (Z.to_nat 29) with 29%nat by reflexivity
    |progress replace (Z.to_nat 28) with 28%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress rewrite Hcount |progress rewrite Herror
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (first [exact Hload|reflexivity|assumption])
       |progress rewrite (bool_decide_false P) by (first [assumption|discriminate])] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools key
       Imperative.update decide decide_rel divIntUnsigned modIntUnsigned
       variableIndexEqualityDecidablevarsfuncdef_0__renameCachePut varsfuncdef_0__renameCachePut_rec
       variableIndexEqualityDecidablevarsfuncdef_0__formulaHash varsfuncdef_0__formulaHash_rec]
    |match goal with |- context [numbers.Z.eq_dec ?a ?b] => destruct (numbers.Z.eq_dec a b); [exfalso; lia|] end
    |match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (scan ?n) ?state] =>
       let expression := constr:(@execLocalObserved I T EI V EV R (scan n) state) in
       let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(after,observations))) by exact Hscan;
       rewrite Hrun; clear Hrun end]) in
  run; destruct (Z.eq_dec (nums after vardef_0__renameCachePut_placed) 0);
  unfold finish_frame; run; reflexivity.
Qed.
Lemma prepared_table s k : RenameMemoLookup.table (prepared s k) = RenameMemoLookup.table s.
Proof. unfold RenameMemoLookup.table,prepared. now rewrite hash_preserves_array by discriminate. Qed.
Lemma prepared_memo s k : memory (prepared s k) arraydef_0__renameMemo = memory s arraydef_0__renameMemo.
Proof. unfold prepared. now rewrite hash_preserves_array by discriminate. Qed.
Lemma start_key f count : key (start_frame f count) = key f.
Proof. destruct f. reflexivity. Qed.
Lemma start_value f count : value (start_frame f count) = value f.
Proof. destruct f. reflexivity. Qed.
Lemma start_size f count : nums (start_frame f count) vardef_0__renameCachePut_size = Z.of_nat count.
Proof. destruct f. reflexivity. Qed.
Lemma start_placed f count : nums (start_frame f count) vardef_0__renameCachePut_placed = 0.
Proof. destruct f. reflexivity. Qed.
Lemma start_slot f count : (31 < length (memory (machine f) arraydef_0__meta))%nat ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat -> (0 < count)%nat ->
  nums (start_frame f count) vardef_0__renameCachePut_slot = Z.of_nat (RenameMemoLookup.hash_start (machine f) (key f) count).
Proof.
  intros Hmeta Hsip Hcount.
  change (meta_value (hash_state (machine f) 5 (fst (key f)) (snd (key f))) 28 mod Z.of_nat count =
    Z.of_nat (RenameMemoLookup.hash_start (machine f) (key f) count)).
  rewrite hash_result by (try assumption; lia). unfold RenameMemoLookup.hash_start.
  rewrite Z2Nat.id; [reflexivity|]. apply Z.mod_pos_bound. lia.
Qed.
Definition placement s k count :=
  RenameMemoPlacement.place (RenameMemoLookup.table s) count k (RenameMemoLookup.hash_start s k count) count.
Definition result_state_below_half s k result count := match placement s k count with
  | Some slot => update_result (prepared s k) slot k result
  | None => store_meta (prepared s k) 8 1 end.
Theorem generated_below_half s bs ns count observations :
  (31 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat -> 0 < meta_value s 20 -> meta_value s 8 = 0 ->
  meta_value s 29 = Z.of_nat count -> (0 < count)%nat -> Z.of_nat count <= maximum ->
  meta_value s 30 < Z.of_nat count / 2 -> (count <= length (memory s arraydef_0__renameMemo))%nat ->
  let k := (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) in
  execObserved (funcdef_0__renameCachePut bs ns) (s,observations) =
    Some (tt,(result_state_below_half s k (ns vardef_0__renameCachePut_value) count,observations)).
Proof.
  intros Hmeta Hsip Hpositive Herror Hcount Hnonzero Hword Hload Htable k.
  set (initial := ({|machine := s; bools := bs; nums := ns|} : Frame)).
  set (start := start_frame initial count).
  assert (Hstartmachine : machine start = prepared s k) by reflexivity.
  destruct (generated_scan_observed count start count (RenameMemoLookup.hash_start s k count) observations Hnonzero Hword
    (RenameMemoLookup.hash_start_bound s k count Hnonzero)
    ltac:(rewrite Hstartmachine,prepared_memo; exact Htable)
    ltac:(rewrite Hstartmachine; unfold prepared; rewrite RenameMemoLookup.hash_meta_length; lia)
    ltac:(exact (start_slot initial count Hmeta Hsip Hnonzero)) (start_size initial count) (start_placed initial count))
    as [final [Hscan [Hparameters [Hflag Hmachine]]]].
  assert (Hkey : key start = k) by (apply start_key).
  assert (Hvalue : value start = ns vardef_0__renameCachePut_value) by (apply start_value).
  rewrite Hstartmachine,prepared_table,Hkey in Hflag,Hmachine. rewrite Hvalue in Hmachine.
  change (nums final vardef_0__renameCachePut_placed = match placement s k count with Some _=>1 |None=>0 end) in Hflag.
  change (machine final = match placement s k count with
    |Some slot=>update_result (prepared s k) slot k (ns vardef_0__renameCachePut_value) |None=>prepared s k end) in Hmachine.
  assert (Hafter : (31 < length (memory (machine final) arraydef_0__meta))%nat).
  { rewrite Hmachine. destruct (placement s k count); [rewrite update_meta_length|];
      unfold prepared; now rewrite RenameMemoLookup.hash_meta_length. }
  assert (HscanZ : execLocalObserved (loop (Z.to_nat (Z.of_nat count)) probe_body) (start,observations) = Some (tt,(final,observations))).
  { now rewrite Nat2Z.id. }
  pose proof (generated_body_below_half (fun n=>loop (Z.to_nat n) probe_body) initial final count observations
    Hmeta Hsip Hpositive Herror Hcount Hnonzero Hload Hafter HscanZ) as Hbody.
  rewrite <-body_actual in Hbody.
  assert (Hfinal : machine (finish_frame final) = result_state_below_half s k (ns vardef_0__renameCachePut_value) count).
  { unfold finish_frame,result_state_below_half. rewrite Hflag. destruct (placement s k count).
    - rewrite bool_decide_false by discriminate. exact Hmachine.
    - rewrite bool_decide_true by reflexivity. cbn [machine setMachine]. exact (f_equal (fun state=>store_meta state 8 1) Hmachine). }
  unfold funcdef_0__renameCachePut. rewrite ObservedLocal.eliminate_correct.
  match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state] =>
    let expression := constr:(@execLocalObserved I T EI V EV R code state) in
    let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(finish_frame final,observations))) by exact Hbody;
    rewrite Hrun
  end.
  cbn [optionBind fst snd]. now rewrite Hfinal.
Qed.
Lemma store_entry_other s slot k result name : name <> arraydef_0__renameMemo ->
  memory (store_entry s slot k result) name = memory s name.
Proof. destruct name; intro Hname; try congruence; reflexivity. Qed.
Lemma store_entry_meta s slot k result cell : meta_value (store_entry s slot k result) cell = meta_value s cell.
Proof. unfold meta_value. now rewrite store_entry_other by discriminate. Qed.
Lemma store_entry_table s slot k result index :
  (slot < length (memory s arraydef_0__renameMemo))%nat ->
  RenameMemoLookup.table (store_entry s slot k result) index =
    RenameMemoTable.put (RenameMemoLookup.table s) slot (fst k,snd k,result,1) index.
Proof.
  intros Hslot. unfold RenameMemoLookup.table,store_entry,RenameMemoTable.put. cbn [memory withMemory].
  change (List.nth index (<[slot := (fst k,snd k,result,1)]> (memory s arraydef_0__renameMemo)) (0,0,0,0) =
    if Nat.eq_dec index slot then (fst k,snd k,result,1) else List.nth index (memory s arraydef_0__renameMemo) (0,0,0,0)).
  destruct (Nat.eq_dec index slot) as [->|Hother].
  - now apply OverflowExecution.nth_insert_same.
  - now apply ArrayFacts.nth_insert_other.
Qed.
Lemma update_table s slot k result index :
  (slot < length (memory s arraydef_0__renameMemo))%nat ->
  RenameMemoLookup.table (update_result s slot k result) index =
    RenameMemoTable.put (RenameMemoLookup.table s) slot (fst k,snd k,result,1) index.
Proof.
  intros Hslot. unfold update_result. destruct bool_decide; [|now apply store_entry_table].
  unfold RenameMemoLookup.table at 1. rewrite store_meta_other by discriminate. now apply store_entry_table.
Qed.
Lemma update_meta_other s slot k result cell : cell <> 30%nat ->
  meta_value (update_result s slot k result) cell = meta_value s cell.
Proof.
  intros Hcell. unfold update_result. destruct bool_decide; [rewrite meta_store_other by exact Hcell|]; apply store_entry_meta.
Qed.
Theorem result_table s k result count slot : (0 < count)%nat ->
  (count <= length (memory s arraydef_0__renameMemo))%nat -> placement s k count = Some slot ->
  forall index, RenameMemoLookup.table (result_state_below_half s k result count) index =
    RenameMemoTable.put (RenameMemoLookup.table s) slot (fst k,snd k,result,1) index.
Proof.
  intros Hpositive Htable Hplace index. unfold result_state_below_half. rewrite Hplace.
  rewrite update_table,prepared_table; [reflexivity|]. rewrite prepared_memo.
  pose proof (proj1 (RenameMemoPlacement.place_sound (RenameMemoLookup.table s) count k
    (RenameMemoLookup.hash_start s k count) count slot Hpositive
    (RenameMemoLookup.hash_start_bound s k count Hpositive) Hplace)). lia.
Qed.
Theorem result_represents s k result count slot meaning : (0 < count)%nat ->
  (count <= length (memory s arraydef_0__renameMemo))%nat -> placement s k count = Some slot ->
  RenameMemoTable.represents (RenameMemoLookup.table s) count meaning -> meaning k result ->
  RenameMemoTable.represents (RenameMemoLookup.table (result_state_below_half s k result count)) count meaning.
Proof.
  intros Hpositive Htable Hplace Hmeaning Hresult.
  apply RenameMemoPlacement.represents_ext with
    (table := RenameMemoTable.put (RenameMemoLookup.table s) slot (fst k,snd k,result,1)).
  - intro index. symmetry. now apply result_table.
  - now apply RenameMemoTable.put_represents.
Qed.
Theorem result_nonfatal s k result count slot : meta_value s 8 = 0 -> placement s k count = Some slot ->
  meta_value (result_state_below_half s k result count) 8 = 0.
Proof.
  intros Herror Hplace. unfold result_state_below_half. rewrite Hplace,update_meta_other by lia.
  unfold prepared. rewrite hash_preserves_meta by lia. exact Herror.
Qed.
Definition storage_frame s t :=
  (forall name, name <> arraydef_0__meta -> name <> arraydef_0__sipState -> name <> arraydef_0__renameMemo ->
    memory t name = memory s name) /\
  (forall cell, cell <> 8%nat -> cell <> 21%nat -> cell <> 28%nat -> cell <> 30%nat -> meta_value t cell = meta_value s cell) /\
  length (memory t arraydef_0__meta) = length (memory s arraydef_0__meta) /\
  stdin t = stdin s /\ stdout t = stdout s.
Theorem result_frame s k result count : storage_frame s (result_state_below_half s k result count).
Proof.
  unfold result_state_below_half. destruct (placement s k count).
  - split.
    + intros name Hmeta Hsip Hmemo. unfold update_result. destruct bool_decide;
        [rewrite store_meta_other by exact Hmeta|]; rewrite store_entry_other by exact Hmemo;
        unfold prepared; now apply hash_preserves_array.
    + split.
      * intros cell H8 H21 H28 H30. rewrite update_meta_other by exact H30. unfold prepared. now apply hash_preserves_meta.
      * split; [rewrite update_meta_length; unfold prepared; apply RenameMemoLookup.hash_meta_length|].
        unfold update_result. destruct bool_decide; split; reflexivity.
  - split.
    + intros name Hmeta Hsip Hmemo. rewrite store_meta_other by exact Hmeta. unfold prepared. now apply hash_preserves_array.
    + split.
      * intros cell H8 H21 H28 H30. rewrite meta_store_other by exact H8. unfold prepared. now apply hash_preserves_meta.
      * split; [rewrite store_meta_length; unfold prepared; apply RenameMemoLookup.hash_meta_length|]. split; reflexivity.
Qed.
Theorem result_meaning s k result count meaning : (0 < count)%nat ->
  (count <= length (memory s arraydef_0__renameMemo))%nat ->
  RenameMemoTable.represents (RenameMemoLookup.table s) count meaning -> meaning k result ->
  RenameMemoTable.represents (RenameMemoLookup.table (result_state_below_half s k result count)) count meaning.
Proof.
  intros Hpositive Htable Hmeaning Hresult. destruct (placement s k count) as [slot|] eqn:Hplace.
  - now apply result_represents with (slot:=slot).
  - unfold result_state_below_half. rewrite Hplace. unfold RenameMemoLookup.table at 1.
    rewrite store_meta_other by discriminate. fold (RenameMemoLookup.table (prepared s k)).
    now rewrite prepared_table.
Qed.
Lemma result_hash_start s k result count query :
  RenameMemoLookup.hash_start (result_state_below_half s k result count) query count = RenameMemoLookup.hash_start s query count.
Proof.
  unfold RenameMemoLookup.hash_start. destruct (result_frame s k result count) as [_ [Hmeta _]].
  rewrite !Hmeta by lia. reflexivity.
Qed.
Theorem result_indexed s k result count : (0 < count)%nat ->
  (count <= length (memory s arraydef_0__renameMemo))%nat -> RenameMemoLookup.indexed s count ->
  RenameMemoLookup.indexed (result_state_below_half s k result count) count.
Proof.
  intros Hpositive Htable Hindexed. destruct (placement s k count) as [slot|] eqn:Hplace.
  - assert (Hmodel : RenameMemoPlacement.indexed_by
      (RenameMemoTable.put (RenameMemoLookup.table s) slot (fst k,snd k,result,1)) count
      (fun query=>RenameMemoLookup.hash_start s query count)).
    { apply RenameMemoPlacement.placed_indexed with (start:=RenameMemoLookup.hash_start s k count);
        [exact Hpositive|now apply RenameMemoLookup.hash_start_bound|reflexivity|exact Hindexed|exact Hplace]. }
    assert (Hstored : RenameMemoPlacement.indexed_by
      (RenameMemoLookup.table (result_state_below_half s k result count)) count
      (fun query=>RenameMemoLookup.hash_start s query count)).
    { apply RenameMemoPlacement.indexed_ext with
        (table:=RenameMemoTable.put (RenameMemoLookup.table s) slot (fst k,snd k,result,1)); [|exact Hmodel].
      intro index. symmetry. now apply result_table. }
    intros index Hindex Hoccupied. rewrite result_hash_start. exact (Hstored index Hindex Hoccupied).
  - assert (Hsame : RenameMemoLookup.table (result_state_below_half s k result count) = RenameMemoLookup.table s).
    { unfold result_state_below_half. rewrite Hplace. unfold RenameMemoLookup.table at 1.
      rewrite store_meta_other by discriminate. exact (prepared_table s k). }
    intros index Hindex Hoccupied. rewrite Hsame in Hoccupied |- *. rewrite result_hash_start.
    exact (Hindexed index Hindex Hoccupied).
Qed.
Theorem generated_below_half_preserves s bs ns count observations meaning :
  (31 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat -> 0 < meta_value s 20 -> meta_value s 8 = 0 ->
  meta_value s 29 = Z.of_nat count -> (0 < count)%nat -> Z.of_nat count <= maximum ->
  meta_value s 30 < Z.of_nat count / 2 -> (count <= length (memory s arraydef_0__renameMemo))%nat ->
  let k := (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) in
  RenameMemoTable.represents (RenameMemoLookup.table s) count meaning ->
  meaning k (ns vardef_0__renameCachePut_value) -> RenameMemoLookup.indexed s count ->
  exists final, execObserved (funcdef_0__renameCachePut bs ns) (s,observations) = Some (tt,(final,observations)) /\
    storage_frame s final /\ RenameMemoTable.represents (RenameMemoLookup.table final) count meaning /\
    RenameMemoLookup.indexed final count.
Proof.
  intros Hmeta Hsip Hpositive Herror Hcount Hnonzero Hword Hload Htable k Hmeaning Hresult Hindexed.
  exists (result_state_below_half s k (ns vardef_0__renameCachePut_value) count).
  split; [now apply generated_below_half|]. split; [apply result_frame|].
  split; [now apply result_meaning|now apply result_indexed].
Qed.
Theorem placement_available s k count : (0 < count)%nat ->
  (RenameMemoCapacity.live (RenameMemoLookup.table s) count < count)%nat ->
  exists slot, placement s k count = Some slot.
Proof.
  intros Hpositive Hroom. apply RenameMemoCapacity.room_place;
    [now apply RenameMemoLookup.hash_start_bound|exact Hroom].
Qed.
Theorem below_half_room s count : meta_value s 30 = Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table s) count) ->
  meta_value s 30 < Z.of_nat count / 2 -> (RenameMemoCapacity.live (RenameMemoLookup.table s) count < count)%nat.
Proof.
  intros Hcount Hload. pose proof (Z.div_mod (Z.of_nat count) 2 ltac:(lia)) as Hdivision.
  pose proof (Z.mod_pos_bound (Z.of_nat count) 2 ltac:(lia)) as Hmod. lia.
Qed.
Theorem generated_below_half_nonfatal s bs ns count observations meaning :
  (31 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat -> 0 < meta_value s 20 -> meta_value s 8 = 0 ->
  meta_value s 29 = Z.of_nat count -> (0 < count)%nat -> Z.of_nat count <= maximum ->
  meta_value s 30 < Z.of_nat count / 2 -> (count <= length (memory s arraydef_0__renameMemo))%nat ->
  meta_value s 30 = Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table s) count) ->
  let k := (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) in
  RenameMemoTable.represents (RenameMemoLookup.table s) count meaning ->
  meaning k (ns vardef_0__renameCachePut_value) -> RenameMemoLookup.indexed s count ->
  exists final, execObserved (funcdef_0__renameCachePut bs ns) (s,observations) = Some (tt,(final,observations)) /\
    meta_value final 8 = 0 /\ storage_frame s final /\
    RenameMemoTable.represents (RenameMemoLookup.table final) count meaning /\ RenameMemoLookup.indexed final count.
Proof.
  intros Hmeta Hsip Hpositive Herror Hcount Hnonzero Hword Hload Htable Hlive k Hmeaning Hresult Hindexed.
  destruct (placement_available s k count Hnonzero (below_half_room s count Hlive Hload)) as [slot Hplace].
  exists (result_state_below_half s k (ns vardef_0__renameCachePut_value) count).
  split; [now apply generated_below_half|]. split; [now apply result_nonfatal with (slot:=slot)|].
  split; [apply result_frame|]. split; [now apply result_meaning|now apply result_indexed].
Qed.
Theorem result_live_count s k result count slot : (31 < length (memory s arraydef_0__meta))%nat ->
  (0 < count)%nat -> (count <= length (memory s arraydef_0__renameMemo))%nat -> placement s k count = Some slot ->
  meta_value s 30 = Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table s) count) ->
  word (meta_value s 30 + 1) ->
  meta_value (result_state_below_half s k result count) 30 =
    Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table (result_state_below_half s k result count)) count).
Proof.
  intros Hmeta Hpositive Htable Hplace Hcount Hword.
  pose proof (proj1 (RenameMemoPlacement.place_sound (RenameMemoLookup.table s) count k
    (RenameMemoLookup.hash_start s k count) count slot Hpositive
    (RenameMemoLookup.hash_start_bound s k count Hpositive) Hplace)) as Hslot.
  assert (Hlive : RenameMemoCapacity.live (RenameMemoLookup.table (result_state_below_half s k result count)) count =
    (RenameMemoCapacity.live (RenameMemoLookup.table s) count +
      if bool_decide (RenameMemoTable.occupied (RenameMemoLookup.table s slot) = 0%Z) then 1 else 0)%nat).
  { transitivity (RenameMemoCapacity.live
      (RenameMemoTable.put (RenameMemoLookup.table s) slot (fst k,snd k,result,1)) count).
    - apply RenameMemoCapacity.live_ext. intros index Hindex. now apply result_table.
    - now apply RenameMemoCapacity.live_put. }
  rewrite Hlive. unfold result_state_below_half. rewrite Hplace.
  unfold update_result. rewrite prepared_table.
  destruct (bool_decide (RenameMemoTable.occupied (RenameMemoLookup.table s slot) = 0%Z)).
  - rewrite meta_store_same by (rewrite store_entry_meta_length; unfold prepared; rewrite RenameMemoLookup.hash_meta_length; lia).
    unfold prepared. rewrite hash_preserves_meta by lia. rewrite coerce_word by exact Hword.
    rewrite Nat2Z.inj_add. cbn. lia.
  - rewrite store_entry_meta. unfold prepared. rewrite hash_preserves_meta by lia.
    rewrite Nat.add_0_r. exact Hcount.
Qed.
Lemma below_half_increment_word s count : Z.of_nat count <= maximum ->
  meta_value s 30 = Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table s) count) ->
  meta_value s 30 < Z.of_nat count / 2 -> word (meta_value s 30 + 1).
Proof.
  intros Hword Hlive Hload. unfold word. pose proof (below_half_room s count Hlive Hload). lia.
Qed.
Theorem result_memo_length s k result count :
  length (memory (result_state_below_half s k result count) arraydef_0__renameMemo) =
    length (memory s arraydef_0__renameMemo).
Proof.
  unfold result_state_below_half. destruct (placement s k count) as [slot|].
  - unfold update_result. destruct bool_decide; [rewrite store_meta_other by discriminate|];
      unfold store_entry; cbn [memory withMemory];
      change (length (<[slot := (fst k,snd k,result,1)]> (memory (prepared s k) arraydef_0__renameMemo)) = length (memory s arraydef_0__renameMemo));
      rewrite length_insert,prepared_memo; reflexivity.
  - rewrite store_meta_other by discriminate. now rewrite prepared_memo.
Qed.
Theorem generated_below_half_invariant s bs ns count observations meaning :
  (31 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat -> 0 < meta_value s 20 -> meta_value s 8 = 0 ->
  meta_value s 29 = Z.of_nat count -> (0 < count)%nat -> Z.of_nat count <= maximum ->
  meta_value s 30 < Z.of_nat count / 2 -> (count <= length (memory s arraydef_0__renameMemo))%nat ->
  meta_value s 30 = Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table s) count) ->
  let k := (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) in
  RenameMemoTable.represents (RenameMemoLookup.table s) count meaning ->
  meaning k (ns vardef_0__renameCachePut_value) -> RenameMemoLookup.indexed s count ->
  exists final, execObserved (funcdef_0__renameCachePut bs ns) (s,observations) = Some (tt,(final,observations)) /\
    meta_value final 8 = 0 /\ storage_frame s final /\
    RenameMemoTable.represents (RenameMemoLookup.table final) count meaning /\ RenameMemoLookup.indexed final count /\
    meta_value final 30 = Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table final) count) /\
    (count <= length (memory final arraydef_0__renameMemo))%nat.
Proof.
  intros Hmeta Hsip Hpositive Herror Hcount Hnonzero Hword Hload Htable Hlive k Hmeaning Hresult Hindexed.
  destruct (placement_available s k count Hnonzero (below_half_room s count Hlive Hload)) as [slot Hplace].
  exists (result_state_below_half s k (ns vardef_0__renameCachePut_value) count).
  split; [now apply generated_below_half|]. split; [now apply result_nonfatal with (slot:=slot)|].
  split; [apply result_frame|]. split; [now apply result_meaning|]. split; [now apply result_indexed|].
  split.
  - apply result_live_count with (slot:=slot); try assumption. now apply below_half_increment_word with (count:=count).
  - now rewrite result_memo_length.
Qed.
End RenameMemoInsert.









