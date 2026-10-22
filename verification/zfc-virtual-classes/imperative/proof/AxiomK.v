From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives ArenaFrame Intern InternLengths
  FormulaEncoding FormulaTopology Representation FormulaCircuit FormulaCircuitProperties AxiomCircuits RenameMemoControl AxiomRefl HashTable.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomK.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom.
Definition cleared s := store_meta s 13 0.
Definition finished s := store_meta (store_meta s 0 (meta_value s 0)) 13 1.
Local Opaque funcdef_0__intern funcdef_0__rename Imperative.update.
Theorem generated_body (f : Frame) built ids p_id q_id observations :
  (13 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__axiom_tag=0 -> nums f vardef_0__axiom_p=p_id -> nums f vardef_0__axiom_q=q_id ->
  p_id<meta_value (machine f) 1 -> q_id<meta_value (machine f) 1 ->
  FormulaCircuit.executes observations AxiomCircuits.k_plan (cleared (machine f)) [p_id;q_id] built ids ->
  optionBind (execLocalObserved funcdef_0__axiom_body (f,observations))
    (fun r=>Some (tt,(machine (fst (snd r)),snd (snd r)))) = Some (tt,(finished built,observations)).
Proof.
  intros Hmeta Htag Hp Hq Hpbound Hqbound Htrace.
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hfinalmeta.
  assert (Hbuiltmeta:(13<length (memory built arraydef_0__meta))%nat)
    by (rewrite Hfinalmeta;unfold cleared;rewrite store_meta_length;exact Hmeta).
  unfold AxiomCircuits.k_plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold funcdef_0__axiom_body.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot=>first [exact Hmeta|exact Hbuiltmeta|assumption|rewrite !store_meta_length;first [exact Hmeta|exact Hbuiltmeta]|cbn [machine setMachine setNum];rewrite ?store_meta_length;lia])
    |match goal with H : execObserved (funcdef_0__intern _ _) _ = Some (tt,(?after,?trace)) |-
         context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(after,trace))) by exact H; rewrite Hrun; clear Hrun end
    |progress rewrite Htag |progress rewrite Hp |progress rewrite Hq
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress rewrite meta_store_other by lia
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by first [exact Hpbound|exact Hqbound|lia] |progress rewrite (bool_decide_false P) by lia] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence |progress rewrite (decide_False (P:=P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ]. reflexivity.
Qed.
Lemma unit_projection {A B} (result:option (unit*A)) (project:A->B) :
  optionBind result (fun response=>Some (fst response,project (snd response))) =
  optionBind result (fun response=>Some (tt,project (snd response))).
Proof. destruct result as [[[] state]|];reflexivity. Qed.
Theorem generated_helper s bs ns built ids p_id q_id observations :
  (13 < length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag=0 -> ns vardef_0__axiom_p=p_id -> ns vardef_0__axiom_q=q_id ->
  p_id<meta_value s 1 -> q_id<meta_value s 1 ->
  FormulaCircuit.executes observations AxiomCircuits.k_plan (cleared s) [p_id;q_id] built ids ->
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(finished built,observations)).
Proof.
  intros Hmeta Htag Hp Hq Hpbound Hqbound Htrace.
  unfold funcdef_0__axiom. rewrite ObservedLocal.eliminate_correct.
  pose proof (generated_body {|machine:=s;bools:=bs;nums:=ns|} built ids p_id q_id observations
    Hmeta Htag Hp Hq Hpbound Hqbound Htrace) as Hbody.
  rewrite (unit_projection
    (execLocalObserved funcdef_0__axiom_body ({|machine:=s;bools:=bs;nums:=ns|},observations))
    (fun state=>(machine (fst state),snd state))). exact Hbody.
Qed.
Lemma clearing_storage s : ArenaFrame.storage s (cleared s).
Proof. unfold cleared. apply ArenaFrame.storage_meta; lia. Qed.
Lemma finishing_storage s : ArenaFrame.storage s (finished s).
Proof. unfold finished. ArenaFrame.storage_steps. Qed.
Lemma storage_topology s t count : ArenaFrame.storage s t -> FormulaTopology.ordered s count -> FormulaTopology.ordered t count.
Proof.
  intros [_ [Harrays _]] Hordered. apply (FormulaTopology.same s t count Hordered).
  intros parent Hparent. unfold HashTableInvariant.tuple_at. now rewrite Harrays by discriminate.
Qed.
Lemma finishing_result s : (13<length (memory s arraydef_0__meta))%nat ->
  meta_value (finished s) 13=1 /\ meta_value (finished s) 8=meta_value s 8 /\ meta_value (finished s) 0=meta_value s 0.
Proof.
  intro Hmeta. unfold finished. split; [apply meta_store_same;rewrite store_meta_length;exact Hmeta|].
  split; [rewrite !meta_store_other by lia;reflexivity|].
  rewrite meta_store_other by lia. apply meta_store_same. lia.
Qed.
Theorem generated_refines s bs ns fs p_id q_id p q reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag=0 -> ns vardef_0__axiom_p=p_id -> ns vardef_0__axiom_q=q_id ->
  word p_id -> word q_id -> nth_error fs (Z.to_nat p_id)=Some p -> nth_error fs (Z.to_nat q_id)=Some q ->
  Z.of_nat (length fs+2+reserve)<=9223372036854775807 ->
  exists built next,
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(finished built,observations)) /\
    NativeRepresentation.canonical_arena (finished built) next /\
    meta_value (finished built) 13=1 /\ meta_value (finished built) 8=0 /\
    word (meta_value (finished built) 0) /\
    nth_error next (Z.to_nat (meta_value (finished built) 0))=Some (SetTheory.axiom_formula (SetTheory.K p q)) /\
    SetTheory.derives (SetTheory.axiom_formula (SetTheory.K p q)) /\
    (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered (finished built) (length next) /\ (length next<=length fs+2)%nat /\
    AxiomRefl.logical_frame s (finished built).
Proof.
  intros Harena Hordered Herror Hmeta Htag Hp Hq Hpword Hqword Hplookup Hqlookup Hbudget.
  pose proof (clearing_storage s) as Hclear.
  pose proof (ArenaFrame.storage_arena s (cleared s) fs Hclear Harena) as Hcleared_arena.
  pose proof (storage_topology s (cleared s) (length fs) Hclear Hordered) as Hcleared_ordered.
  assert (Hcleared_error:meta_value (cleared s) 8=0) by (unfold cleared;rewrite meta_store_other by lia;exact Herror).
  destruct (AxiomCircuits.construct_k (cleared s) fs p_id q_id p q reserve observations
    Hcleared_arena Hcleared_ordered Hcleared_error Hpword Hqword Hplookup Hqlookup Hbudget)
    as (built & next & ids & Htrace & Hframe & Hnext & Hflag & Hrep & Hprefix & Hreserve & Htopology & Hgrowth).
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hlength.
  assert (Hbuiltmeta:(13<length (memory built arraydef_0__meta))%nat)
    by (rewrite Hlength;unfold cleared;rewrite store_meta_length;exact Hmeta).
  destruct (AxiomCircuits.k_result observations (cleared s) p_id q_id built ids next p q Htrace Hrep)
    as (Hword & Hmeaning & Hderives).
  destruct (finishing_result built Hbuiltmeta) as (Hsuccess & Hresult_error & Hresult).
  assert (Hpbound:p_id<meta_value s 1).
  { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
    pose proof (proj1 Hpword) as Hpnonneg.
    assert (Hlt:(Z.to_nat p_id<length fs)%nat) by (apply nth_error_Some;congruence).
    apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by exact Hpnonneg. lia. }
  assert (Hqbound:q_id<meta_value s 1).
  { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
    pose proof (proj1 Hqword) as Hqnonneg.
    assert (Hlt:(Z.to_nat q_id<length fs)%nat) by (apply nth_error_Some;congruence).
    apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by exact Hqnonneg. lia. }
  exists built,next. split; [eapply generated_helper;eassumption|].
  split; [exact (ArenaFrame.storage_arena built (finished built) next (finishing_storage built) Hnext)|].
  split; [exact Hsuccess|]. split; [congruence|]. split; [now rewrite Hresult|].
  split; [now rewrite Hresult|]. split; [exact Hderives|]. split; [exact Hprefix|].
  split; [exact Hreserve|]. split; [eapply storage_topology;[apply finishing_storage|exact Htopology]|].
  split; [exact Hgrowth|exact (AxiomRefl.frame s built Hframe)].
Qed.
End AxiomK.
