From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure CommandSteps NativePrimitives CommandDispatch ReplyNO SchemaMetadata.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module CommandNameSchemaExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Definition binding_arguments value : varsfuncdef_0__bindName -> Z :=
  update (update (fun _ => 0) vardef_0__bindName_value value) vardef_0__bindName_kind 2.
Definition frame_after (f : Frame) arg final value := setMachine (setNum (setMachine f arg) vardef_0__command_a value) final.
Local Opaque funcdef_0__readToken funcdef_0__bindName funcdef_0__no.
Theorem generated_handler reader (f : Frame) arg named final value observations after_observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(arg,observations)) ->
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  (17 < length (memory arg arraydef_0__meta))%nat ->
  meta_value arg 11 = value -> meta_value arg 14 = 1 -> meta_value arg 8 = 0 ->
  execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (arg,observations) = Some (tt,(named,observations)) ->
  (17 < length (memory named arraydef_0__meta))%nat -> meta_value named 14 = 1 -> meta_value named 8 = 0 ->
  value < meta_value named 16 ->
  (Z.to_nat value < length (memory named arraydef_0__schemaNodes))%nat ->
  snd (fst (SchemaMetadata.node_at named (Z.to_nat value))) = 2 ->
  execObserved (funcdef_0__bindName (fun _ => false) (binding_arguments value)) (named,observations) = Some (tt,(final,after_observations)) ->
  execLocalObserved (CommandStructure.handler_23 reader) (f,observations) = Some (tt,(frame_after f arg final value,after_observations)).
Proof.
  intros Hreader Hinitial Hinitialerror Hargmeta Hnumber Hargvalid Hargerror Hreadname Hmeta Hvalid Herror Hreference Hnodebound Htype Hbinding.
  destruct f as [s bs ns]. cbn [machine] in *. unfold CommandStructure.handler_23.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       lazymatch name with
       |arraydef_0__schemaNodes => exact Hnodebound
       |arraydef_0__meta => first [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hargmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hinitial]] end)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (reader br nr) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(arg,observations))) by exact Hreader;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__readToken ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__readToken br nr) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(named,observations))) by exact Hreadname;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__bindName ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__bindName br nr) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(final,after_observations))) by exact Hbinding;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [snd (fst (List.nth ?index ?nodes ?zero))] =>
       let expression := constr:(snd (fst (List.nth index nodes zero))) in
       let Hfield := fresh "Hfield" in assert (Hfield : expression = 2) by exact Htype;
       rewrite Hfield; clear Hfield end
    |progress rewrite Hnumber |progress rewrite Hargvalid |progress rewrite Hargerror
    |progress rewrite Hinitialerror |progress rewrite Hvalid |progress rewrite Herror
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 16) with 16%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. unfold frame_after. reflexivity.
Qed.
Theorem generated_command s bs ns op arg named final value observations after_observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(op,observations)) ->
  (17 < length (memory op arraydef_0__meta))%nat -> meta_value op 11 = 23 -> meta_value op 14 = 1 -> meta_value op 8 = 0 ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (op,observations) = Some (tt,(arg,observations)) ->
  (17 < length (memory arg arraydef_0__meta))%nat -> meta_value arg 11 = value -> meta_value arg 14 = 1 -> meta_value arg 8 = 0 ->
  execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (arg,observations) = Some (tt,(named,observations)) ->
  (17 < length (memory named arraydef_0__meta))%nat -> meta_value named 14 = 1 -> meta_value named 8 = 0 ->
  value < meta_value named 16 ->
  (Z.to_nat value < length (memory named arraydef_0__schemaNodes))%nat ->
  snd (fst (SchemaMetadata.node_at named (Z.to_nat value))) = 2 ->
  execObserved (funcdef_0__bindName (fun _ => false) (binding_arguments value)) (named,observations) = Some (tt,(final,after_observations)) ->
  (8 < length (memory final arraydef_0__meta))%nat -> meta_value final 8 = 0 ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,after_observations)).
Proof.
  intros Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hnumber Hargvalid Hargerror Hreadname Hmeta Hvalid Herror Hreference Hnodebound Htype Hbinding Hfinalmeta Hfinalerror.
  set (initial := CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} op 23).
  set (after := frame_after initial arg final value).
  apply (CommandDispatch.generated_positive_command s bs ns after op 23 observations after_observations); try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandStructure.handler_23 funcdef_0__readNat) (initial,observations) = Some (tt,(after,after_observations))).
    eapply generated_handler; eassumption.
Qed.

Theorem generated_rejected_handler reader (f : Frame) arg named value observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(arg,observations)) ->
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  (17 < length (memory arg arraydef_0__meta))%nat ->
  meta_value arg 11 = value -> meta_value arg 14 = 1 -> meta_value arg 8 = 0 ->
  execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (arg,observations) = Some (tt,(named,observations)) ->
  (17 < length (memory named arraydef_0__meta))%nat -> meta_value named 14 = 1 -> meta_value named 8 = 0 ->
  meta_value named 16 <= value ->
  execLocalObserved (CommandStructure.handler_23 reader) (f,observations) =
    Some (tt,(frame_after f arg (ReplyNOExecution.reply_state named) value,
      observations ++ [{|flushedOutput := stdout named ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin named|}])).
Proof.
  intros Hreader Hinitial Hinitialerror Hargmeta Hnumber Hargvalid Hargerror Hreadname Hmeta Hvalid Herror Hreference.
  destruct f as [s bs ns]. cbn [machine] in *. unfold CommandStructure.handler_23.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       first [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hargmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hinitial]])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (reader br nr) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(arg,observations))) by exact Hreader;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__readToken ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__readToken br nr) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(named,observations))) by exact Hreadname;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bo ?no) (?current,?trace)] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__no bo no) (current,trace)) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(ReplyNOExecution.reply_state current,
          trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin current|}]))) by
          exact (ReplyNOExecution.generated_no current bo no trace);
        rewrite Hrun; clear Hrun end
    |progress rewrite Hnumber |progress rewrite Hargvalid |progress rewrite Hargerror
    |progress rewrite Hinitialerror |progress rewrite Hvalid |progress rewrite Herror
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 16) with 16%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. unfold frame_after. reflexivity.
Qed.
Theorem generated_rejected_command s bs ns op arg named value observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(op,observations)) ->
  (17 < length (memory op arraydef_0__meta))%nat -> meta_value op 11 = 23 -> meta_value op 14 = 1 -> meta_value op 8 = 0 ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (op,observations) = Some (tt,(arg,observations)) ->
  (17 < length (memory arg arraydef_0__meta))%nat -> meta_value arg 11 = value -> meta_value arg 14 = 1 -> meta_value arg 8 = 0 ->
  execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (arg,observations) = Some (tt,(named,observations)) ->
  (17 < length (memory named arraydef_0__meta))%nat -> meta_value named 14 = 1 -> meta_value named 8 = 0 ->
  meta_value named 16 <= value ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(ReplyNOExecution.reply_state named,
    observations ++ [{|flushedOutput := stdout named ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin named|}])).
Proof.
  intros Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hnumber Hargvalid Hargerror Hreadname Hmeta Hvalid Herror Hreference.
  set (initial := CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} op 23).
  set (after := frame_after initial arg (ReplyNOExecution.reply_state named) value).
  apply (CommandDispatch.generated_positive_command s bs ns after op 23 observations
    (observations ++ [{|flushedOutput := stdout named ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin named|}])); try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandStructure.handler_23 funcdef_0__readNat) (initial,observations) = Some (tt,(after,
      observations ++ [{|flushedOutput := stdout named ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin named|}]))).
    eapply generated_rejected_handler; eassumption.
  - change (8 < length (memory named arraydef_0__meta))%nat. lia.
Qed.
Theorem generated_wrong_type_handler reader (f : Frame) arg named value type observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(arg,observations)) ->
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  (17 < length (memory arg arraydef_0__meta))%nat ->
  meta_value arg 11 = value -> meta_value arg 14 = 1 -> meta_value arg 8 = 0 ->
  execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (arg,observations) = Some (tt,(named,observations)) ->
  (17 < length (memory named arraydef_0__meta))%nat -> meta_value named 14 = 1 -> meta_value named 8 = 0 ->
  value < meta_value named 16 ->
  (Z.to_nat value < length (memory named arraydef_0__schemaNodes))%nat ->
  snd (fst (SchemaMetadata.node_at named (Z.to_nat value))) = type -> type <> 2 ->
  execLocalObserved (CommandStructure.handler_23 reader) (f,observations) =
    Some (tt,(frame_after f arg (ReplyNOExecution.reply_state named) value,
      observations ++ [{|flushedOutput := stdout named ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin named|}])).
Proof.
  intros Hreader Hinitial Hinitialerror Hargmeta Hnumber Hargvalid Hargerror Hreadname Hmeta Hvalid Herror Hreference Hnodebound Htype Hnotproof.
  destruct f as [s bs ns]. cbn [machine] in *. unfold CommandStructure.handler_23.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       lazymatch name with
       |arraydef_0__schemaNodes => exact Hnodebound
       |arraydef_0__meta => first [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hargmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hinitial]] end)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (reader br nr) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(arg,observations))) by exact Hreader;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__readToken ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__readToken br nr) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(named,observations))) by exact Hreadname;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bo ?no) (?current,?trace)] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__no bo no) (current,trace)) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(ReplyNOExecution.reply_state current,
          trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin current|}]))) by
          exact (ReplyNOExecution.generated_no current bo no trace);
        rewrite Hrun; clear Hrun end
    |match goal with |- context [snd (fst (List.nth ?index ?nodes ?zero))] =>
       let expression := constr:(snd (fst (List.nth index nodes zero))) in
       let Hfield := fresh "Hfield" in assert (Hfield : expression = type) by exact Htype;
       rewrite Hfield; clear Hfield end
    |progress rewrite Hnumber |progress rewrite Hargvalid |progress rewrite Hargerror
    |progress rewrite Hinitialerror |progress rewrite Hvalid |progress rewrite Herror
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 16) with 16%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. unfold frame_after. reflexivity.
Qed.
Theorem generated_wrong_type_command s bs ns op arg named value type observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(op,observations)) ->
  (17 < length (memory op arraydef_0__meta))%nat -> meta_value op 11 = 23 -> meta_value op 14 = 1 -> meta_value op 8 = 0 ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (op,observations) = Some (tt,(arg,observations)) ->
  (17 < length (memory arg arraydef_0__meta))%nat -> meta_value arg 11 = value -> meta_value arg 14 = 1 -> meta_value arg 8 = 0 ->
  execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (arg,observations) = Some (tt,(named,observations)) ->
  (17 < length (memory named arraydef_0__meta))%nat -> meta_value named 14 = 1 -> meta_value named 8 = 0 ->
  value < meta_value named 16 ->
  (Z.to_nat value < length (memory named arraydef_0__schemaNodes))%nat ->
  snd (fst (SchemaMetadata.node_at named (Z.to_nat value))) = type -> type <> 2 ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(ReplyNOExecution.reply_state named,
    observations ++ [{|flushedOutput := stdout named ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin named|}])).
Proof.
  intros Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hnumber Hargvalid Hargerror Hreadname Hmeta Hvalid Herror Hreference Hnodebound Htype Hnotproof.
  set (initial := CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} op 23).
  set (after := frame_after initial arg (ReplyNOExecution.reply_state named) value).
  apply (CommandDispatch.generated_positive_command s bs ns after op 23 observations
    (observations ++ [{|flushedOutput := stdout named ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin named|}])); try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandStructure.handler_23 funcdef_0__readNat) (initial,observations) = Some (tt,(after,
      observations ++ [{|flushedOutput := stdout named ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin named|}]))).
    eapply generated_wrong_type_handler; eassumption.
  - change (8 < length (memory named arraydef_0__meta))%nat. lia.
Qed.
End CommandNameSchemaExecution.
