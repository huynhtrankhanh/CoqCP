From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash NameLookup ObservedLocal NativePrimitives.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NameSearchExecution.
Import IndexExecution SipHashExecution NameLookupExecution ObservedLocal.
Definition binding_at (s : Machine) i := List.nth i (memory s arraydef_0__bindings) (0,0,0,0,0).
Definition valid_entries s count := (count <= length (memory s arraydef_0__bindings))%nat /\
  forall i, (i < count)%nat -> exists offset size value flag kind,
    binding_at s i = (offset,Z.of_nat size,value,flag,kind) /\ 0 <= offset /\ word (offset + Z.of_nat size) /\
    (Z.to_nat offset + size <= length (memory s arraydef_0__names))%nat.
Definition entry_test s size i := let '(offset,stored_size,_,_,_) := binding_at s i in
  bool_decide (stored_size = Z.of_nat size) && equal_suffix s (Z.to_nat offset) size size.
Definition entry_matches s size i := let '(offset,stored_size,_,_,_) := binding_at s i in
  stored_size = Z.of_nat size /\ forall j, (j < size)%nat ->
    List.nth (Z.to_nat offset + j) (memory s arraydef_0__names) 0 = List.nth j (memory s arraydef_0__token) 0.
Lemma entry_test_spec s size i : entry_test s size i = true <-> entry_matches s size i.
Proof.
  unfold entry_test,entry_matches. destruct (binding_at s i) as [[[[offset stored_size] value] flag] kind].
  rewrite andb_true_iff,bool_decide_eq_true,equal_suffix_spec by lia. rewrite Nat.sub_diag. split.
  - intros [Hsize Hbytes]. split; [exact Hsize|]. intros j Hj. apply Hbytes. lia.
  - intros [Hsize Hbytes]. split; [exact Hsize|]. intros j Hj. apply Hbytes. lia.
Qed.
Fixpoint find_native s count size remaining := match remaining with
| O => None
| S rest => if entry_test s size (count - S rest)%nat then Some (count - S rest)%nat else find_native s count size rest
end.
Theorem find_none s count size remaining : (remaining <= count)%nat ->
  (find_native s count size remaining = None <-> forall i, (count - remaining <= i < count)%nat -> ~ entry_matches s size i).
Proof.
  induction remaining as [|remaining IH]; intro Hbound.
  - cbn [find_native]. split; [intros _ i Hi; lia|reflexivity].
  - cbn [find_native]. destruct (entry_test s size (count - S remaining)) eqn:Htest.
    + split; [discriminate|]. intro Hnone. exfalso. apply (Hnone (count - S remaining)%nat ltac:(lia)). now apply entry_test_spec.
    + rewrite IH by lia. split.
      * intros Hnone i Hi. destruct (Nat.eq_dec i (count - S remaining)%nat) as [->|Hother].
        -- intro Hmatch. apply entry_test_spec in Hmatch. congruence.
        -- apply Hnone. lia.
      * intros Hnone i Hi. apply Hnone. lia.
Qed.
Theorem find_some s count size remaining index : (remaining <= count)%nat -> find_native s count size remaining = Some index ->
  (count - remaining <= index < count)%nat /\ entry_matches s size index /\
  forall i, (count - remaining <= i < index)%nat -> ~ entry_matches s size i.
Proof.
  induction remaining as [|remaining IH]; [discriminate|]. intros Hbound. cbn [find_native].
  destruct (entry_test s size (count - S remaining)) eqn:Htest.
  - intro H. injection H as <-. split; [lia|]. split; [now apply entry_test_spec|]. intros i Hi. lia.
  - intro Hfound. destruct (IH ltac:(lia) Hfound) as [Hrange [Hmatch Hfirst]].
    split; [lia|]. split; [exact Hmatch|]. intros i Hi.
    destruct (Nat.eq_dec i (count - S remaining)%nat) as [->|Hother].
    + intro Hmatch'. apply entry_test_spec in Hmatch'. congruence.
    + apply Hfirst. lia.
Qed.
Theorem find_complete s count size remaining index : (remaining <= count)%nat ->
  (count - remaining <= index < count)%nat -> entry_matches s size index -> exists result, find_native s count size remaining = Some result.
Proof.
  intros Hbound Hrange Hmatch. destruct (find_native s count size remaining) as [result|] eqn:Hfound; [now exists result|].
  exfalso. exact ((proj1 (find_none s count size remaining Hbound) Hfound) index Hrange Hmatch).
Qed.
Theorem generated_scan (f : NameLookupExecution.Frame) count size remaining observations :
  (remaining <= count)%nat -> (6 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 6 = Z.of_nat size -> (size <= length (memory (machine f) arraydef_0__token))%nat ->
  valid_entries (machine f) count ->
  exists final, execLocalObserved (loop remaining (outer_body (Z.of_nat count))) (f,observations) = Some (tt,(final,observations)) /\
    machine final = match find_native (machine f) count size remaining with
      | Some index => store_meta (machine f) 0 (Z.of_nat index) | None => machine f end.
Proof.
  induction remaining as [|remaining IH] in f |- *.
  - intros Hremaining Hmeta Hsize Htoken Hvalid. exists f. split; reflexivity.
  - intros Hremaining Hmeta Hsize Htoken Hvalid.
    set (i := (count - S remaining)%nat).
    assert (Hi : (i < count)%nat) by (unfold i; lia).
    assert (Hindex : entry_index (Z.of_nat count) remaining = Z.of_nat i) by (unfold entry_index,i; lia).
    destruct Hvalid as [Hcapacity Hvalid].
    destruct (Hvalid i Hi) as [offset [descriptor_size [value [flag [kind [Hentry [Hoffset [Hword Hnames]]]]]]]].
    assert (Hbinding : (Z.to_nat (entry_index (Z.of_nat count) remaining) < length (memory (machine f) arraydef_0__bindings))%nat)
      by (rewrite Hindex,Nat2Z.id; lia).
    assert (Hraw : List.nth (Z.to_nat (entry_index (Z.of_nat count) remaining)) (memory (machine f) arraydef_0__bindings) (0,0,0,0,0) =
      (offset,Z.of_nat descriptor_size,value,flag,kind)).
    { rewrite Hindex,Nat2Z.id. exact Hentry. }
    destruct (Nat.eq_dec descriptor_size size) as [Heq|Hne].
    + subst descriptor_size.
      pose proof (generated_entry f (Z.of_nat count) remaining size offset value flag kind observations
        Hmeta Hsize Hoffset Hword Hnames Htoken Hbinding Hraw) as Hrow.
      assert (Htest : entry_test (machine f) size i = equal_suffix (machine f) (Z.to_nat offset) size size).
      { unfold entry_test. rewrite Hentry. rewrite bool_decide_true by reflexivity. reflexivity. }
      rewrite loop_S,ObservedLocal.local_bind,Hrow. unfold entry_result. cbn [fst snd].
      cbn [find_native]. fold i. rewrite Htest.
      destruct (equal_suffix (machine f) (Z.to_nat offset) size size) eqn:Hbytes.
      * exists (setMachine (setNum f vardef_0__lookup_equal 1) (store_meta (machine f) 0 (entry_index (Z.of_nat count) remaining))).
        split; [reflexivity|]. cbn [machine setMachine]. now rewrite Hindex.
      * set (next := setNum (setNum f vardef_0__lookup_equal 1) vardef_0__lookup_equal 0).
        destruct (IH next ltac:(lia) Hmeta Hsize Htoken (conj Hcapacity Hvalid)) as [final [Hrun Hmachine]].
        exists final. split; [exact Hrun|exact Hmachine].
    + pose proof (generated_entry_length_mismatch f (Z.of_nat count) remaining size descriptor_size offset value flag kind observations
        Hmeta Hsize Hne Hbinding Hraw) as Hrow.
      assert (Htest : entry_test (machine f) size i = false).
      { unfold entry_test. rewrite Hentry. rewrite bool_decide_false by lia. reflexivity. }
      rewrite loop_S,ObservedLocal.local_bind,Hrow. cbn [optionBind fst snd].
      cbn [find_native]. fold i. rewrite Htest.
      apply IH; try assumption; [lia|split; assumption].
Qed.
Definition prepared s := store_meta s 0 maximum.
Lemma prepared_binding s i : binding_at (prepared s) i = binding_at s i.
Proof. unfold binding_at,prepared. now rewrite store_meta_other by discriminate. Qed.
Lemma prepared_bytes s offset size remaining : equal_suffix (prepared s) offset size remaining = equal_suffix s offset size remaining.
Proof.
  induction remaining as [|remaining IH]; [reflexivity|]. cbn [equal_suffix].
  unfold prepared in *.
  rewrite (store_meta_other s 0 maximum arraydef_0__names ltac:(discriminate)),
    (store_meta_other s 0 maximum arraydef_0__token ltac:(discriminate)). now rewrite IH.
Qed.
Lemma prepared_test s size i : entry_test (prepared s) size i = entry_test s size i.
Proof.
  unfold entry_test. rewrite prepared_binding. destruct (binding_at s i) as [[[[offset stored_size] value] flag] kind]. now rewrite prepared_bytes.
Qed.
Lemma prepared_find s count size remaining : find_native (prepared s) count size remaining = find_native s count size remaining.
Proof. induction remaining as [|remaining IH]; [reflexivity|]. cbn [find_native]. now rewrite prepared_test,IH. Qed.
Lemma prepared_valid s count : valid_entries s count -> valid_entries (prepared s) count.
Proof.
  unfold valid_entries. intros [Hcapacity Hvalid]. split.
  - unfold prepared. rewrite store_meta_other by discriminate. exact Hcapacity.
  - intros i Hi. destruct (Hvalid i Hi) as [offset [size [value [flag [kind [Hentry [Hoffset [Hword Hnames]]]]]]]].
    exists offset,size,value,flag,kind. rewrite prepared_binding. split; [exact Hentry|]. split; [exact Hoffset|].
    split; [exact Hword|]. unfold prepared. rewrite store_meta_other by discriminate. exact Hnames.
Qed.
Definition body_with (scan : Z -> NameLookupExecution.LocalAction unit) : NameLookupExecution.LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__lookup_body in funcdef_0__lookup_body in
  match code with context [bind (bind (Done _ _ _ 4%Z) _) ?next] =>
    let candidate := eval cbn beta in (next 0%Z) in
    lazymatch candidate with loop _ _ =>
      let abstracted := eval pattern next in code in
      lazymatch abstracted with ?family _ => exact (family scan) end
    end
  end).
Lemma body_actual : funcdef_0__lookup_body = body_with (fun count => loop (Z.to_nat count) (outer_body count)).
Proof. reflexivity. Qed.
Theorem generated_body_composition scan (f after : NameLookupExecution.Frame) count observations :
  (6 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 4 = Z.of_nat count ->
  execLocalObserved (scan (Z.of_nat count)) (setMachine f (prepared (machine f)),observations) = Some (tt,(after,observations)) ->
  execLocalObserved (body_with scan) (f,observations) = Some (tt,(after,observations)).
Proof.
  intros Hmeta Hcount Hscan. destruct f as [s bs ns]. cbn [machine] in *. unfold body_with.
  repeat first [progress cbn [optionBind fst snd]
    |progress fold (prepared s)
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       unfold prepared; rewrite ?store_meta_length; eapply Nat.le_lt_trans with (m := 6%nat); [cbn; lia|exact Hmeta])
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 4) with 4%nat by reflexivity
    |progress unfold prepared at 1
    |progress rewrite meta_store_other by lia
    |progress rewrite Hcount
    |match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (scan ?n) ?state] =>
        let expression := constr:(@execLocalObserved I T EI V EV R (scan n) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(after,observations))) by exact Hscan;
        rewrite Hrun; clear Hrun end
    |progress cbv beta iota zeta delta [machine setMachine nums bools]
  ]. reflexivity.
Qed.
Definition storage_frame s t :=
  (forall name, name <> arraydef_0__meta -> memory t name = memory s name) /\
  (forall i, i <> 0%nat -> meta_value t i = meta_value s i) /\ stdin t = stdin s /\ stdout t = stdout s.
Lemma store_frame s value : storage_frame s (store_meta s 0 value).
Proof.
  split; [intros; now apply store_meta_other|]. split; [intros; now apply meta_store_other|]. split; reflexivity.
Qed.
Lemma frame_trans s t u : storage_frame s t -> storage_frame t u -> storage_frame s u.
Proof.
  intros [Ha [Hm [Hi Ho]]] [Ha' [Hm' [Hi' Ho']]]. split; [intros; now rewrite Ha',Ha by assumption|].
  split; [intros; now rewrite Hm',Hm by assumption|]. split; congruence.
Qed.
Definition lookup_correct s final result :=
  meta_value final 0 = match result with Some index => Z.of_nat index | None => maximum end /\ storage_frame s final.
Theorem generated_lookup_with_capacity s bs ns count size observations :
  (6 < length (memory s arraydef_0__meta))%nat -> meta_value s 4 = Z.of_nat count -> meta_value s 6 = Z.of_nat size ->
  (size <= length (memory s arraydef_0__token))%nat -> valid_entries s count ->
  exists final, execObserved (funcdef_0__lookup bs ns) (s,observations) = Some (tt,(final,observations)) /\
    lookup_correct s final (find_native s count size count) /\
    length (memory final arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof.
  intros Hmeta Hcount Hsize Htoken Hvalid.
  set (initial := ({|machine := s; bools := bs; nums := ns|} : NameLookupExecution.Frame)).
  set (start := setMachine initial (prepared s)).
  assert (Hpreparedmeta : (6 < length (memory (prepared s) arraydef_0__meta))%nat) by (unfold prepared; now rewrite store_meta_length).
  assert (Hpreparedsize : meta_value (prepared s) 6 = Z.of_nat size) by (unfold prepared; rewrite meta_store_other by lia; exact Hsize).
  assert (Hpreparedtoken : (size <= length (memory (prepared s) arraydef_0__token))%nat) by (unfold prepared; rewrite store_meta_other by discriminate; exact Htoken).
  destruct (generated_scan start count size count observations ltac:(lia) Hpreparedmeta Hpreparedsize Hpreparedtoken (prepared_valid s count Hvalid))
    as [after [Hscan Hmachine]].
  assert (HscanZ : execLocalObserved (loop (Z.to_nat (Z.of_nat count)) (outer_body (Z.of_nat count))) (start,observations) = Some (tt,(after,observations))).
  { now rewrite Nat2Z.id. }
  pose proof (generated_body_composition (fun count => loop (Z.to_nat count) (outer_body count)) initial after count observations Hmeta Hcount HscanZ) as Hbody.
  rewrite <-body_actual in Hbody. unfold initial in Hbody.
  exists (machine after). split.
  - unfold funcdef_0__lookup. rewrite ObservedLocal.eliminate_correct.
    match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state] =>
      let expression := constr:(@execLocalObserved I T EI V EV R code state) in
      let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(after,observations))) by exact Hbody;
      rewrite Hrun; reflexivity
    end.
  - split.
    + change (machine after = match find_native (prepared s) count size count with
      | Some index => store_meta (prepared s) 0 (Z.of_nat index) | None => prepared s end) in Hmachine.
      rewrite prepared_find in Hmachine. unfold lookup_correct. rewrite Hmachine.
      destruct (find_native s count size count) as [index|].
      * split.
        -- apply meta_store_same. unfold prepared. rewrite store_meta_length. lia.
        -- eapply frame_trans; [exact (store_frame s maximum)|apply store_frame].
      * split; [apply meta_store_same; lia|apply store_frame].
    + change (machine after = match find_native (prepared s) count size count with
        | Some index => store_meta (prepared s) 0 (Z.of_nat index) | None => prepared s end) in Hmachine.
      rewrite Hmachine. destruct (find_native (prepared s) count size count);
        unfold prepared; now rewrite !store_meta_length.
Qed.
Theorem generated_lookup s bs ns count size observations :
  (6 < length (memory s arraydef_0__meta))%nat -> meta_value s 4 = Z.of_nat count -> meta_value s 6 = Z.of_nat size ->
  (size <= length (memory s arraydef_0__token))%nat -> valid_entries s count ->
  exists final, execObserved (funcdef_0__lookup bs ns) (s,observations) = Some (tt,(final,observations)) /\
    lookup_correct s final (find_native s count size count).
Proof.
  intros Hmeta Hcount Hsize Htoken Hvalid.
  destruct (generated_lookup_with_capacity s bs ns count size observations Hmeta Hcount Hsize Htoken Hvalid)
    as [final [Hrun [Hcorrect Hlength]]]. exists final. split; assumption.
Qed.
Theorem found_below_sentinel s count size index : Z.of_nat count <= maximum ->
  find_native s count size count = Some index -> 0 <= Z.of_nat index < maximum.
Proof.
  intros Hword Hfound. pose proof (proj1 (find_some s count size count index ltac:(lia) Hfound)). lia.
Qed.
End NameSearchExecution.
