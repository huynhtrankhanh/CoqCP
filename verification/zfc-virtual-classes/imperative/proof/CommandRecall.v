From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure NativePrimitives ReplyOK ReplyNO CommandDispatch FormulaProjection ClassStorage HistoryRefinement NameRepresentation AppendTheorem HistoryStorage ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module CommandRecallExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Definition reply (found : bool) kind count := if found then if Z.eq_dec kind 1 then Protocol.OK count else Protocol.NO else Protocol.NO.
Definition result looked (found : bool) kind count id := if found then if Z.eq_dec kind 1 then HistoryStorage.result looked count (Z.of_nat id) else ReplyNOExecution.reply_state looked else ReplyNOExecution.reply_state looked.
Local Opaque funcdef_0__readToken funcdef_0__lookup funcdef_0__appendTheorem funcdef_0__no.
Theorem generated_handler reader (f : Frame) named looked (found : bool) index offset size count id flag kind observations :
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(named,observations)) ->
  (17 < length (memory named arraydef_0__meta))%nat -> meta_value named 14 = 1 -> meta_value named 8 = 0 ->
  execObserved (funcdef_0__lookup (fun _ => false) (fun _ => 0)) (named,observations) = Some (tt,(looked,observations)) ->
  (17 < length (memory looked arraydef_0__meta))%nat -> meta_value looked 0 = (if found then Z.of_nat index else maximum) ->
  0 <= Z.of_nat index < maximum ->
  (found = true -> index < length (memory looked arraydef_0__bindings))%nat ->
  (found = true -> List.nth index (memory looked arraydef_0__bindings) (0,0,0,0,0) = (offset,size,Z.of_nat id,flag,kind)) ->
  (20 <= length (memory looked arraydef_0__printBuffer))%nat -> Z.of_nat id <= maximum -> meta_value looked 3 = Z.of_nat count -> Z.of_nat count < maximum -> meta_value looked 8 = 0 ->
  execLocalObserved (CommandStructure.handler_21 reader) (f,observations) =
    Some (tt,(setMachine f (result looked found kind count id), observations ++
      [{|flushedOutput := stdout looked ++ Protocol.reply_bytes (reply found kind count); unreadInput := stdin looked|}])).
Proof.
  intros Hinitial Hinitialerror Hread Hnamedmeta Hvalid Herror Hlookup Hmeta Hresult Hindex Hbound Hnth Hbuffer Hword Hcount Hcountword Hclear.
  destruct f as [s bs ns]. cbn [machine] in *. unfold maximum in *.
  let solve_run := ltac:(
    unfold CommandStructure.handler_21;
    repeat first [progress cbn [optionBind fst snd negb]
      |progress specialize (Hbound eq_refl) |progress specialize (Hnth eq_refl)
      |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id;
         lazymatch name with
         |arraydef_0__bindings => exact Hbound
         |arraydef_0__meta => first [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta]
           |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hnamedmeta]
           |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hinitial]] end)
      |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__readToken ?br ?nr) ?state] =>
          let expression := constr:(@execObserved I T EI R (funcdef_0__readToken br nr) state) in
          let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(named,observations))) by exact Hread;
          rewrite Hrun; clear Hrun end
      |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__lookup ?br ?nr) ?state] =>
          let expression := constr:(@execObserved I T EI R (funcdef_0__lookup br nr) state) in
          let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(looked,observations))) by exact Hlookup;
          rewrite Hrun; clear Hrun end
      |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__appendTheorem ?bo ?no) (?current,?trace)] =>
          let expression := constr:(@execObserved I T EI R (funcdef_0__appendTheorem bo no) (current,trace)) in
          let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(HistoryStorage.result current count (Z.of_nat id),
            trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes (Protocol.OK count); unreadInput := stdin current|}]))) by
              (apply (AppendTheoremExecution.generated_append current bo no count (Z.of_nat id) trace);
               [lia|exact Hbuffer|exact Hclear|exact Hcount|exact Hcountword|reflexivity]);
          rewrite Hrun; clear Hrun end
      |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bo ?no) (?current,?trace)] =>
          let expression := constr:(@execObserved I T EI R (funcdef_0__no bo no) (current,trace)) in
          let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(ReplyNOExecution.reply_state current,
            trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin current|}]))) by
              exact (ReplyNOExecution.generated_no current bo no trace);
          rewrite Hrun; clear Hrun end
      |progress rewrite Hinitialerror |progress rewrite Hvalid |progress rewrite Herror |progress rewrite Hresult
      |progress rewrite Nat2Z.id |progress rewrite Hnth
      |progress replace (Z.to_nat 0) with 0%nat by reflexivity
      |progress replace (Z.to_nat 14) with 14%nat by reflexivity
      |progress replace (Z.to_nat 8) with 8%nat by reflexivity
      |match goal with |- context [bool_decide ?P] => first
         [progress rewrite (bool_decide_true P) by (try congruence; lia)
         |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
      |match goal with |- context [decide ?P] => first
         [progress rewrite (decide_True (P := P)) by congruence
         |progress rewrite (decide_False (P := P)) by congruence] end
      |progress cbv beta iota zeta delta [machine setMachine nums bools]
    ]; reflexivity) in
  unfold result,reply; destruct found; [destruct (Z.eq_dec kind 1) as [->|Hkind]|]; cbn in Hresult; solve_run.
Qed.

Lemma result_meta_length looked found kind count id :
  length (memory (result looked found kind count id) arraydef_0__meta) = length (memory looked arraydef_0__meta).
Proof. unfold result. destruct found; [destruct (Z.eq_dec kind 1)|]; [apply HistoryStorage.result_meta_length|reflexivity|reflexivity]. Qed.
Lemma result_other looked found kind count id name : name <> arraydef_0__meta -> name <> arraydef_0__printBuffer -> name <> arraydef_0__theorems ->
  memory (result looked found kind count id) name = memory looked name.
Proof. intros Hm Hp Ht. unfold result. destruct found; [destruct (Z.eq_dec kind 1)|]; [now apply HistoryStorage.result_other|reflexivity|reflexivity]. Qed.
Lemma result_meta_other looked found kind count id i : i <> 3%nat -> meta_value (result looked found kind count id) i = meta_value looked i.
Proof. intro Hi. unfold result. destruct found; [destruct (Z.eq_dec kind 1)|]; [now apply HistoryStorage.result_meta_other|reflexivity|reflexivity]. Qed.
Lemma result_projection looked found kind count id : FormulaProjection.storage looked (result looked found kind count id).
Proof.
  unfold result. destruct found; [destruct (Z.eq_dec kind 1)|]; [apply HistoryStorage.result_projection| |];
    apply FormulaProjection.strong_storage; apply ArenaFrame.storage_output.
Qed.
Lemma result_bindings looked found kind count id bindings : NameRepresentation.represents looked bindings ->
  NameRepresentation.represents (result looked found kind count id) bindings.
Proof. unfold NameRepresentation.represents. rewrite !result_meta_other by lia. rewrite !result_other by discriminate. trivial. Qed.
Lemma result_classes looked found kind count id fs classes : ClassStorage.represents looked fs classes ->
  ClassStorage.represents (result looked found kind count id) fs classes.
Proof. intros [Hcount Hclasses]. split; [rewrite result_meta_other by lia; exact Hcount|now rewrite result_other by discriminate]. Qed.
Definition history_after logical (found : bool) kind id :=
  if found then if Z.eq_dec kind 1 then Protocol.with_history logical (Protocol.history logical ++ [id]) else logical else logical.
Lemma result_history looked logical found kind id : (3 < length (memory looked arraydef_0__meta))%nat -> HistoryRefinement.represents looked logical ->
  HistoryRefinement.represents (result looked found kind (length (Protocol.history logical)) id) (history_after logical found kind id).
Proof.
  intros Hmeta Hhistory. unfold result,history_after. destruct found; [destruct (Z.eq_dec kind 1)|];
    [now apply HistoryStorage.append_represents|exact Hhistory|exact Hhistory].
Qed.
Theorem generated_command s bs ns op named looked (found : bool) index offset size count id flag kind observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(op,observations)) ->
  (17 < length (memory op arraydef_0__meta))%nat -> meta_value op 11 = 21 -> meta_value op 14 = 1 -> meta_value op 8 = 0 ->
  execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (op,observations) = Some (tt,(named,observations)) ->
  (17 < length (memory named arraydef_0__meta))%nat -> meta_value named 14 = 1 -> meta_value named 8 = 0 ->
  execObserved (funcdef_0__lookup (fun _ => false) (fun _ => 0)) (named,observations) = Some (tt,(looked,observations)) ->
  (17 < length (memory looked arraydef_0__meta))%nat -> meta_value looked 0 = (if found then Z.of_nat index else maximum) ->
  0 <= Z.of_nat index < maximum ->
  (found = true -> index < length (memory looked arraydef_0__bindings))%nat ->
  (found = true -> List.nth index (memory looked arraydef_0__bindings) (0,0,0,0,0) = (offset,size,Z.of_nat id,flag,kind)) ->
  (20 <= length (memory looked arraydef_0__printBuffer))%nat -> Z.of_nat id <= maximum -> meta_value looked 3 = Z.of_nat count -> Z.of_nat count < maximum -> meta_value looked 8 = 0 ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(result looked found kind count id, observations ++
    [{|flushedOutput := stdout looked ++ Protocol.reply_bytes (reply found kind count); unreadInput := stdin looked|}])).
Proof.
  intros Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hvalid Herror Hlookup Hmeta Hresult Hindex Hbound Hnth Hbuffer Hword Hcount Hcountword Hclear.
  set (initial := CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} op 21).
  set (after := setMachine initial (result looked found kind count id)).
  apply (CommandDispatch.generated_positive_command s bs ns after op 21 observations
    (observations ++ [{|flushedOutput := stdout looked ++ Protocol.reply_bytes (reply found kind count); unreadInput := stdin looked|}])); try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandStructure.handler_21 funcdef_0__readNat) (initial,observations) = Some (tt,(after,
      observations ++ [{|flushedOutput := stdout looked ++ Protocol.reply_bytes (reply found kind count); unreadInput := stdin looked|}]))).
    eapply generated_handler; eassumption.
  - change (8 < length (memory (result looked found kind count id) arraydef_0__meta))%nat.
    rewrite result_meta_length. lia.
  - change (meta_value (result looked found kind count id) 8 = 0). rewrite result_meta_other by lia. exact Hclear.
Qed.
End CommandRecallExecution.
