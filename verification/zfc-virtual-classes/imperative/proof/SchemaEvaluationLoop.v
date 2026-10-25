From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  SchemaEvaluation SchemaMarking SchemaEvaluationControl SchemaGraph.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationLoop.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := SchemaEvaluation.Frame.
Definition LocalAction := SchemaEvaluation.LocalAction.
Definition LoopAction := SchemaEvaluation.LoopAction.

Lemma drop_return (code:LoopAction unit) f observations :
  execLocalObserved (dropWithinLoop (code>>=fun _=>Done _ _ _ tt)) (f,observations)=
  execLocalObserved (dropWithinLoop code) (f,observations).
Proof.
  induction code as [value|effect cont IH] in f,observations|-*.
  - destruct value. reflexivity.
  - destruct effect as [effect| |];try reflexivity.
    cbn [bind dropWithinLoop Action_rect execLocalObserved].
    destruct (localStepObserved effect (f,observations)) as [[value [middle trace]]|];cbn [optionBind fst snd];
      [apply IH|reflexivity].
Qed.

Definition inner_with width remaining outer_remaining (work:LoopAction unit) : LocalAction LoopOutcome := ltac:(
  let code:=eval cbv beta iota zeta delta [SchemaEvaluation.inner_body] in
    (SchemaEvaluation.inner_body width remaining outer_remaining) in
  let selected:=eval cbv beta iota zeta delta [SchemaEvaluation.marked_body] in
    (SchemaEvaluation.marked_body width remaining outer_remaining) in
  let family:=eval pattern selected in code in lazymatch family with ?family _=>exact (family work) end).
Lemma actual_inner width remaining outer_remaining :
  SchemaEvaluation.inner_body width remaining outer_remaining=
    inner_with width remaining outer_remaining (SchemaEvaluation.marked_body width remaining outer_remaining).
Proof. reflexivity. Qed.

Lemma generated_stopped (f:Frame) width remaining outer_remaining work observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  (meta_value (machine f) 18=0 \/ meta_value (machine f) 8<>0) ->
  execLocalObserved (inner_with width remaining outer_remaining work) (f,observations)=Some (Stop,(f,observations)).
Proof.
  intros Hmeta Hstop. unfold inner_with.
  repeat first [progress cbn [optionBind fst snd negb bind nums setNum machine]
    |progress rewrite drop_assoc|progress rewrite drop_lift|progress rewrite drop_lift_final
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];lia)
    |progress replace (Z.to_nat 18) with 18%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity].
  destruct Hstop as [Hzero|Herror].
  - rewrite Hzero. reflexivity.
  - destruct (bool_decide (meta_value (machine f) 18=0));[reflexivity|].
    repeat first [progress cbn [optionBind fst snd negb bind nums setNum machine]
      |progress rewrite drop_assoc|progress rewrite drop_lift|progress rewrite drop_lift_final
      |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];lia)].
    rewrite bool_decide_true by exact Herror. reflexivity.
Qed.

Lemma generated_cell (f:Frame) width remaining outer_remaining stride node d key work observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 18<>0 -> meta_value (machine f) 8=0 ->
  nums f vardef_0__schemaInstance_width=Z.of_nat stride ->
  SchemaEvaluation.depth width outer_remaining=Z.of_nat node -> SchemaEvaluation.depth width remaining=Z.of_nat d ->
  key=(node*stride+d)%nat -> Z.of_nat key<=maximum ->
  (key<length (memory (machine f) arraydef_0__schemaMarks))%nat ->
  execLocalObserved (inner_with width remaining outer_remaining work) (f,observations)=
    if bool_decide (SchemaMarking.cell (machine f) key<>0) then
      execLocalObserved (dropWithinLoop work) (setNum f vardef_0__schemaInstance_key (Z.of_nat key),observations)
    else Some (KeepGoing,(setNum f vardef_0__schemaInstance_key (Z.of_nat key),observations)).
Proof.
  intros Hmeta Hvalid Herror Hwidth Hnode Hd Hkey Hword Hbound.
  assert (Hmul:coerceInt (Z.of_nat node*Z.of_nat stride) 64=Z.of_nat (node*stride)).
  { rewrite <-Nat2Z.inj_mul. apply coerce_word. unfold word. lia. }
  assert (Hsum:coerceInt (Z.of_nat (node*stride)+Z.of_nat d) 64=Z.of_nat key).
  { rewrite <-Nat2Z.inj_add,<-Hkey. apply coerce_word. unfold word. lia. }
  unfold SchemaEvaluation.depth in Hnode,Hd. unfold inner_with.
  repeat first [progress cbn [optionBind fst snd negb bind nums setNum machine]
    |progress rewrite drop_assoc|progress rewrite drop_lift|progress rewrite drop_lift_final
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setNum];rewrite ?Nat2Z.id;first [exact Hbound|lia])
    |progress unfold addInt at 1|progress unfold multInt at 1
    |progress rewrite Herror|progress rewrite Hwidth|progress rewrite Hnode|progress rewrite Hd
    |progress rewrite Hmul|progress rewrite Hsum|progress rewrite Nat2Z.id
    |progress rewrite (bool_decide_false (meta_value (machine f) 18=0)) by exact Hvalid
    |progress rewrite (bool_decide_false (0<>0)) by congruence
    |multimatch goal with |- context [bool_decide ?P] => first
      [progress rewrite (bool_decide_true P) by congruence|progress rewrite (bool_decide_false P) by congruence] end
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress replace (coerceInt 0 8) with 0 by reflexivity
    |progress replace (Z.to_nat 18) with 18%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress change (List.nth key (memory (machine f) arraydef_0__schemaMarks) 0) with (SchemaMarking.cell (machine f) key)
    ].
  destruct (bool_decide (SchemaMarking.cell (machine f) key<>0));[apply drop_return|reflexivity].
Qed.
Lemma generated_row_stopped (f:Frame) width remaining observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  (meta_value (machine f) 18=0 \/ meta_value (machine f) 8<>0) ->
  execLocalObserved (SchemaEvaluation.outer_body width remaining) (f,observations)=Some (Stop,(f,observations)).
Proof.
  intros Hmeta Hstop. unfold SchemaEvaluation.outer_body.
  repeat first [progress cbn [optionBind fst snd negb bind nums setNum machine]
    |progress rewrite drop_assoc|progress rewrite drop_lift|progress rewrite drop_lift_final
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];lia)
    |progress replace (Z.to_nat 18) with 18%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity].
  destruct Hstop as [Hzero|Herror].
  - rewrite Hzero. reflexivity.
  - destruct (bool_decide (meta_value (machine f) 18=0));[reflexivity|].
    repeat first [progress cbn [optionBind fst snd negb bind nums setNum machine]
      |progress rewrite drop_assoc|progress rewrite drop_lift|progress rewrite drop_lift_final
      |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];lia)].
    rewrite bool_decide_true by exact Herror. reflexivity.
Qed.

Definition row_work width remaining : Z->LocalAction unit := ltac:(
 let code:=eval cbv beta iota zeta delta [SchemaEvaluation.outer_body] in (SchemaEvaluation.outer_body width remaining) in
 lazymatch code with dropWithinLoop ?raw=>
 let rest:=SchemaMarking.drop_statements 1%nat raw in
 lazymatch rest with bind (liftToWithinLoop (bind _ ?next)) _=>exact next end end).
Definition outer_with width remaining (work:Z->LocalAction unit) : LocalAction LoopOutcome := ltac:(
 let code:=eval cbv beta iota zeta delta [SchemaEvaluation.outer_body] in (SchemaEvaluation.outer_body width remaining) in
 lazymatch code with dropWithinLoop ?raw=>
 let rest:=SchemaMarking.drop_statements 1%nat raw in
 lazymatch rest with bind (liftToWithinLoop (bind _ ?next)) _=>
 let family:=eval pattern next in code in
 lazymatch family with ?family _=>exact (family work) end end end).
Lemma actual_outer width remaining :
 SchemaEvaluation.outer_body width remaining=outer_with width remaining (row_work width remaining).
Proof. reflexivity. Qed.
Lemma actual_row_work width remaining :
 row_work width remaining width=loop (Z.to_nat width) (fun inner=>SchemaEvaluation.inner_body width inner remaining).
Proof. reflexivity. Qed.
Lemma generated_row_with (f:Frame) width remaining stride work observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 18<>0 -> meta_value (machine f) 8=0 ->
  nums f vardef_0__schemaInstance_width=Z.of_nat stride ->
  execLocalObserved (outer_with width remaining work) (f,observations)=
  optionBind (execLocalObserved (work (Z.of_nat stride)) (f,observations))
    (fun response=>Some (KeepGoing,snd response)).
Proof.
  intros Hmeta Hvalid Herror Hwidth. unfold outer_with.
  repeat first [progress cbn [optionBind fst snd negb bind nums setNum machine]
    |progress rewrite drop_assoc|progress rewrite drop_lift|progress rewrite drop_lift_final
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];lia)
    |progress rewrite Hwidth|progress rewrite Nat2Z.id|progress rewrite Herror
    |progress rewrite (bool_decide_false (meta_value (machine f) 18=0)) by exact Hvalid
    |progress rewrite (bool_decide_false (0<>0)) by congruence
    |progress replace (Z.to_nat 18) with 18%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity].
  reflexivity.
Qed.
Lemma generated_row (f:Frame) width remaining stride observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 18<>0 -> meta_value (machine f) 8=0 ->
  nums f vardef_0__schemaInstance_width=Z.of_nat stride -> width=Z.of_nat stride ->
  execLocalObserved (SchemaEvaluation.outer_body width remaining) (f,observations)=
  optionBind (execLocalObserved (loop stride (fun inner=>SchemaEvaluation.inner_body width inner remaining)) (f,observations))
    (fun response=>Some (KeepGoing,snd response)).
Proof.
 intros Hmeta Hvalid Herror Hwidth ->. rewrite actual_outer.
 rewrite (generated_row_with f (Z.of_nat stride) remaining stride _ observations Hmeta Hvalid Herror Hwidth).
 rewrite actual_row_work,Nat2Z.id. reflexivity.
Qed.

Lemma loop_stopped count (body:nat->LocalAction LoopOutcome) f observations :
 (forall remaining,(remaining<count)%nat -> execLocalObserved (body remaining) (f,observations)=Some (Stop,(f,observations))) ->
 execLocalObserved (loop count body) (f,observations)=Some (tt,(f,observations)).
Proof.
 destruct count as [|count];[reflexivity|]. intro Hstop.
 rewrite loop_S,local_bind,Hstop by lia. reflexivity.
Qed.

Theorem loop_progress total (body:nat->LocalAction LoopOutcome) (P:nat->Frame->Prop) (Q:Frame->Prop) :
 (forall remaining f observations,(remaining<total)%nat -> Q f ->
   execLocalObserved (body remaining) (f,observations)=Some (Stop,(f,observations))) ->
 (forall remaining f observations,(remaining<total)%nat -> P (total-S remaining)%nat f ->
   exists after,execLocalObserved (body remaining) (f,observations)=Some (KeepGoing,(after,observations)) /\
     (P (total-remaining)%nat after \/ Q after)) ->
 forall count f observations,(count<=total)%nat -> P (total-count)%nat f ->
 exists after,execLocalObserved (loop count body) (f,observations)=Some (tt,(after,observations)) /\
   (P total after \/ Q after).
Proof.
 intros Hstop Hstep count. induction count as [|count IH];intros f observations Hcount HP.
 - exists f. split;[reflexivity|]. left. now rewrite Nat.sub_0_r in HP.
 - destruct (Hstep count f observations ltac:(lia) HP) as (middle & Hrun & [Hnext|Hrejected]).
   + destruct (IH middle observations ltac:(lia) Hnext) as (after & Htail & Hpost).
     exists after. split;[|exact Hpost]. rewrite loop_S,local_bind,Hrun. exact Htail.
   + exists middle. split;[|now right]. rewrite loop_S,local_bind,Hrun.
     cbn [optionBind fst snd]. apply loop_stopped. intros remaining Hremaining. apply Hstop;[lia|exact Hrejected].
Qed.

Theorem generated_grid stride (P:nat->Frame->Prop) (Q:Frame->Prop) :
 (forall key f,P key f ->
   (19<length (memory (machine f) arraydef_0__meta))%nat /\
   meta_value (machine f) 18<>0 /\ meta_value (machine f) 8=0 /\
   nums f vardef_0__schemaInstance_width=Z.of_nat stride) ->
 (forall f,Q f -> (19<length (memory (machine f) arraydef_0__meta))%nat /\
   (meta_value (machine f) 18=0 \/ meta_value (machine f) 8<>0)) ->
 (forall node depth remaining outer_remaining f observations,
   (node<stride)%nat -> (depth<stride)%nat ->
   SchemaEvaluation.depth (Z.of_nat stride) remaining=Z.of_nat depth ->
   SchemaEvaluation.depth (Z.of_nat stride) outer_remaining=Z.of_nat node ->
   P (node*stride+depth)%nat f ->
   exists after,execLocalObserved (SchemaEvaluation.inner_body (Z.of_nat stride) remaining outer_remaining)
     (f,observations)=Some (KeepGoing,(after,observations)) /\
     (P (S (node*stride+depth))%nat after \/ Q after)) ->
 forall f observations,P 0%nat f ->
 exists after,execLocalObserved (loop stride (SchemaEvaluation.outer_body (Z.of_nat stride)))
   (f,observations)=Some (tt,(after,observations)) /\ (P (stride*stride)%nat after \/ Q after).
Proof.
 intros Hactive Hhalted Hcell f observations HP.
 eapply (loop_progress stride (SchemaEvaluation.outer_body (Z.of_nat stride))
   (fun row frame=>P (row*stride)%nat frame) Q).
 - intros remaining before trace Hremaining Hbad. destruct (Hhalted before Hbad) as [Hmeta Hstop].
   now apply generated_row_stopped.
 - intros outer_remaining before trace Houter Hbefore.
   set (node:=(stride-S outer_remaining)%nat).
   assert (Hnode:(node<stride)%nat) by (unfold node;lia).
   assert (HnodeDepth:SchemaEvaluation.depth (Z.of_nat stride) outer_remaining=Z.of_nat node).
   { unfold SchemaEvaluation.depth,node. lia. }
   assert (Hinner:exists after,execLocalObserved
     (loop stride (fun remaining=>SchemaEvaluation.inner_body (Z.of_nat stride) remaining outer_remaining))
       (before,trace)=Some (tt,(after,trace)) /\ (P (node*stride+stride)%nat after \/ Q after)).
   { eapply (loop_progress stride (fun remaining=>SchemaEvaluation.inner_body (Z.of_nat stride) remaining outer_remaining)
       (fun depth frame=>P (node*stride+depth)%nat frame) Q).
     - intros remaining current current_trace Hremaining Hbad. destruct (Hhalted current Hbad) as [Hmeta Hstop].
       rewrite actual_inner. now apply generated_stopped.
     - intros remaining current current_trace Hremaining Hcurrent.
       destruct (Hcell node (stride-S remaining)%nat remaining outer_remaining current current_trace
         Hnode ltac:(lia) ltac:(unfold SchemaEvaluation.depth;lia) HnodeDepth Hcurrent)
         as (after & Hrun & Hpost).
       exists after. split;[exact Hrun|]. replace (node*stride+(stride-remaining))%nat
         with (S (node*stride+(stride-S remaining)))%nat by lia. exact Hpost.
     - lia.
     - rewrite Nat.sub_diag,Nat.add_0_r. exact Hbefore. }
   destruct Hinner as (after & Hrun & Hpost).
   destruct (Hactive (node*stride)%nat before Hbefore) as [Hmeta [Hvalid [Herror Hwidth]]].
   exists after. split.
   + rewrite (generated_row before (Z.of_nat stride) outer_remaining stride trace Hmeta Hvalid Herror Hwidth eq_refl),Hrun.
     reflexivity.
   + replace ((stride-outer_remaining)*stride)%nat with (node*stride+stride)%nat by (unfold node;nia). exact Hpost.
 - lia.
 - rewrite Nat.sub_diag. exact HP.
Qed.
End SchemaEvaluationLoop.
