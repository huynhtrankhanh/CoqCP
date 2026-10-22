From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives ArenaFrame Intern InternLengths
  FormulaEncoding FormulaTopology Representation FormulaCircuit FormulaCircuitProperties AxiomCircuits AxiomRefl AxiomDNE HashTable RenameMemoControl.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomDNERefinement.
Import IndexExecution SipHashExecution ObservedLocal AxiomDNE.
Theorem generated_helper s bs ns built ids p_id observations :
  (13 < length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag=2 -> ns vardef_0__axiom_p=p_id -> p_id<meta_value s 1 ->
  FormulaCircuit.executes observations AxiomCircuits.dne_plan (cleared s) [0;p_id] built ids ->
  execObserved (funcdef_0__axiom bs ns) (s,observations) = Some (tt,(finished built,observations)).
Proof.
  intros Hmeta Htag Hp Hpbound Htrace.
  pose proof (generated_body {|machine:=s;bools:=bs;nums:=ns|} built ids p_id observations Hmeta Htag Hp Hpbound Htrace) as Hbody.
  unfold AxiomDNE.Frame in Hbody.
  unfold funcdef_0__axiom. rewrite eliminate_correct.
  destruct (execLocalObserved funcdef_0__axiom_body ({|machine:=s;bools:=bs;nums:=ns|},observations)) as [[value [after snapshots]]|] eqn:Hraw in Hbody |- *;
    [destruct value|]; exact Hbody.
Qed.
Lemma storage_topology s t count : ArenaFrame.storage s t -> FormulaTopology.ordered s count -> FormulaTopology.ordered t count.
Proof.
  intros [_ [Ha _]] Hordered parent child Hparent Hchild. apply Hordered; [exact Hparent|].
  unfold HashTableInvariant.tuple_at in *. now rewrite Ha in Hchild by discriminate.
Qed.
Theorem generated_refines s bs ns fs p_id p reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13 < length (memory s arraydef_0__meta))%nat -> nth_error fs 0=Some SetTheory.falsity ->
  word p_id -> nth_error fs (Z.to_nat p_id)=Some p ->
  Z.of_nat (length fs+3+reserve)<=9223372036854775807 ->
  ns vardef_0__axiom_tag=2 -> ns vardef_0__axiom_p=p_id ->
  exists final next index, execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (SetTheory.axiom_formula (SetTheory.DNE p)) /\
    SetTheory.derives (SetTheory.axiom_formula (SetTheory.DNE p)) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ meta_value final 13=1 /\
    AxiomRefl.logical_frame s final /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered final (length next) /\ (length next<=length fs+3)%nat.
Proof.
  intros Harena Hordered Herror Hmeta Hfalse Hpword Hp Hbudget Htag Hpinput.
  assert (Hstorage : ArenaFrame.storage s (cleared s)).
  { unfold cleared. apply ArenaFrame.storage_meta; lia. }
  assert (Hclear : NativeRepresentation.canonical_arena (cleared s) fs).
  { exact (ArenaFrame.storage_arena s (cleared s) fs Hstorage Harena). }
  assert (Hclearerror : meta_value (cleared s) 8=0).
  { unfold cleared. rewrite meta_store_other by discriminate. exact Herror. }
  assert (Hclearordered : FormulaTopology.ordered (cleared s) (length fs)).
  { exact (storage_topology s (cleared s) (length fs) Hstorage Hordered). }
  destruct (AxiomCircuits.construct_dne (cleared s) fs p_id p reserve observations Hclear Hclearordered Hclearerror Hfalse Hpword Hp Hbudget)
    as [built [next [ids [Htrace [Hframe [Hnext [Hflag [Hrep [Hprefix [Hreserve [Htopology Hgrowth]]]]]]]]]]].
  destruct (AxiomCircuits.dne_result observations (cleared s) p_id built ids next p Htrace Hrep) as [Hresultword [Hmeaning Hderives]].
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hlength.
  assert (Hbuilt : (13<length (memory built arraydef_0__meta))%nat).
  { rewrite Hlength. unfold cleared. now rewrite store_meta_length. }
  assert (Hpbound : p_id<meta_value s 1).
  { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
    assert (Hbound : (Z.to_nat p_id<length fs)%nat) by (apply nth_error_Some;congruence).
    apply Nat2Z.inj_lt in Hbound. unfold word in Hpword. rewrite Z2Nat.id in Hbound by lia. lia. }
  assert (Hresult : meta_value (finished built) 0=meta_value built 0).
  { unfold finished. rewrite meta_store_other by discriminate. now rewrite meta_store_same by lia. }
  exists (finished built),next,(Z.to_nat (meta_value built 0)). split.
  - eapply generated_helper; eassumption.
  - split; [exact (ArenaFrame.storage_arena built (finished built) next (AxiomRefl.finished_storage built) Hnext)|].
    split.
    + rewrite Hresult,Z2Nat.id;[reflexivity|unfold word in Hresultword;lia].
    + split.
      * rewrite Z2Nat.id;[exact Hresultword|unfold word in Hresultword;lia].
      * split;[exact Hmeaning|]. split;[exact Hderives|]. split;[exact Hprefix|]. split.
        -- unfold finished. rewrite !meta_store_other by discriminate. exact Hflag.
        -- split.
           ++ unfold finished. rewrite meta_store_same;[reflexivity|rewrite store_meta_length;exact Hbuilt].
           ++ split;[exact (AxiomRefl.frame s built Hframe)|]. split;[exact Hreserve|]. split.
              ** exact (storage_topology built (finished built) (length next) (AxiomRefl.finished_storage built) Htopology).
              ** exact Hgrowth.
Qed.
End AxiomDNERefinement.
