From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure NativePrimitives CommandText ReplyOK ReplyNO CommandChain CommandDispatch FormulaProjection ClassStorage HistoryRefinement NameRepresentation CommandSteps ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module CommandNameQueryExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Inductive query := Setness | Kind.
Definition opcode q : Z := match q with Setness => 15 | Kind => 25 end.
Definition handler q reader := match q with Setness => CommandStructure.handler_15 reader | Kind => CommandStructure.handler_25 reader end.
Definition reply q (found : bool) kind flag := if found then match q with
| Setness => if Z.eq_dec kind 0 then if Z.eq_dec flag 1 then Protocol.SET else Protocol.CLASS else Protocol.NO
| Kind => if Z.eq_dec kind 0 then Protocol.CLASS else if Z.eq_dec kind 1 then Protocol.THEOREM else Protocol.SCHEMA end else Protocol.NO.
Definition result (looked : Machine) q found kind flag := withOutput looked (stdout looked ++ Protocol.reply_bytes (reply q found kind flag)).
Local Opaque funcdef_0__readToken funcdef_0__lookup funcdef_0__ok funcdef_0__no.
Theorem generated_handler q reader (f : Frame) named looked (found : bool) index offset size id flag kind observations :
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(named,observations)) ->
  (17 < length (memory named arraydef_0__meta))%nat -> meta_value named 14 = 1 -> meta_value named 8 = 0 ->
  execObserved (funcdef_0__lookup (fun _ => false) (fun _ => 0)) (named,observations) = Some (tt,(looked,observations)) ->
  (17 < length (memory looked arraydef_0__meta))%nat -> meta_value looked 0 = (if found then Z.of_nat index else maximum) ->
  0 <= Z.of_nat index < maximum ->
  (found = true -> index < length (memory looked arraydef_0__bindings))%nat ->
  (found = true -> List.nth index (memory looked arraydef_0__bindings) (0,0,0,0,0) = (offset,size,Z.of_nat id,flag,kind)) ->
  (20 <= length (memory looked arraydef_0__printBuffer))%nat -> Z.of_nat id <= maximum -> (kind = 0 \/ kind = 1 \/ kind = 2) ->
  execLocalObserved (handler q reader) (f,observations) =
    Some (tt,(setMachine f (result looked q found kind flag), observations ++
      [{|flushedOutput := stdout looked ++ Protocol.reply_bytes (reply q found kind flag); unreadInput := stdin looked|}])).
Proof.
  intros Hinitial Hinitialerror Hread Hnamedmeta Hvalid Herror Hlookup Hmeta Hresult Hindex Hbound Hnth Hbuffer Hword Hkindrange.
  destruct f as [s bs ns]. cbn [machine] in *. unfold maximum in *.
  let solve_run := ltac:(
    unfold handler,CommandStructure.handler_15,CommandStructure.handler_25;
    repeat first [progress cbn [optionBind fst snd negb]
      |progress rewrite ObservedLocal.drop_assoc |progress rewrite ObservedLocal.drop_lift
      |progress rewrite dropWithinLoop_1
      |CommandSteps.primitive ltac:(fun frame slot => fail 0)
      |progress specialize (Hbound eq_refl) |progress specialize (Hnth eq_refl)
      |match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (loopString ?str ?callback) (?frame,?trace)] =>
          let expression := constr:(@execLocalObserved I T EI V EV R (loopString str callback) (frame,trace)) in
          let Htext := fresh "Htext" in
          assert (Htext : expression = Some (tt,(setMachine frame (withOutput (machine frame)
            (stdout (machine frame) ++ CommandText.bytes str)),trace))) by exact (CommandText.text_execution str frame trace);
          rewrite Htext; clear Htext end
      |progress rewrite CommandQuitExecution.output_meta
      |progress rewrite CommandText.output_memory
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
    ]; cbn [Protocol.reply_bytes CommandText.bytes result withOutput stdout stdin setMachine machine nums bools]; repeat rewrite <-app_assoc; reflexivity) in
  unfold result,reply; destruct q;
    [destruct found;
      [destruct Hkindrange as [Hkind|[Hkind|Hkind]]; subst kind;
        [destruct (Z.eq_dec flag 1); cbn in Hresult; solve_run
        |cbn in Hresult; solve_run
        |cbn in Hresult; solve_run]
      |cbn in Hresult; solve_run]
    |destruct found;
      [destruct Hkindrange as [Hkind|[Hkind|Hkind]]; subst kind; cbn in Hresult; solve_run
      |cbn in Hresult; solve_run]].
Qed.

Lemma result_projection looked q found kind flag : FormulaProjection.storage looked (result looked q found kind flag).
Proof. apply FormulaProjection.strong_storage. apply ArenaFrame.storage_output. Qed.
Lemma result_meta looked q found kind flag i : meta_value (result looked q found kind flag) i = meta_value looked i.
Proof. reflexivity. Qed.
Lemma result_bindings looked q found kind flag bindings : NameRepresentation.represents looked bindings ->
  NameRepresentation.represents (result looked q found kind flag) bindings.
Proof. exact (fun H => H). Qed.
Lemma result_classes looked q found kind flag fs classes : ClassStorage.represents looked fs classes ->
  ClassStorage.represents (result looked q found kind flag) fs classes.
Proof. exact (fun H => H). Qed.
Lemma result_history looked q found kind flag logical : HistoryRefinement.represents looked logical ->
  HistoryRefinement.represents (result looked q found kind flag) logical.
Proof. exact (fun H => H). Qed.
Lemma actual_handler q reader : CommandChain.handler_for reader (opcode q) = handler q reader.
Proof. destruct q; reflexivity. Qed.
Theorem generated_command q s bs ns op named looked (found : bool) index offset size id flag kind observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(op,observations)) ->
  (17 < length (memory op arraydef_0__meta))%nat -> meta_value op 11 = opcode q -> meta_value op 14 = 1 -> meta_value op 8 = 0 ->
  execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (op,observations) = Some (tt,(named,observations)) ->
  (17 < length (memory named arraydef_0__meta))%nat -> meta_value named 14 = 1 -> meta_value named 8 = 0 ->
  execObserved (funcdef_0__lookup (fun _ => false) (fun _ => 0)) (named,observations) = Some (tt,(looked,observations)) ->
  (17 < length (memory looked arraydef_0__meta))%nat -> meta_value looked 0 = (if found then Z.of_nat index else maximum) ->
  0 <= Z.of_nat index < maximum ->
  (found = true -> index < length (memory looked arraydef_0__bindings))%nat ->
  (found = true -> List.nth index (memory looked arraydef_0__bindings) (0,0,0,0,0) = (offset,size,Z.of_nat id,flag,kind)) ->
  (20 <= length (memory looked arraydef_0__printBuffer))%nat -> Z.of_nat id <= maximum -> (kind = 0 \/ kind = 1 \/ kind = 2) -> meta_value looked 8 = 0 ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(result looked q found kind flag, observations ++
    [{|flushedOutput := stdout looked ++ Protocol.reply_bytes (reply q found kind flag); unreadInput := stdin looked|}])).
Proof.
  intros Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hvalid Herror Hlookup Hmeta Hresult Hindex Hbound Hnth Hbuffer Hword Hkindrange Hclear.
  set (initial := CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} op (opcode q)).
  set (after := setMachine initial (result looked q found kind flag)).
  apply (CommandDispatch.generated_positive_command s bs ns after op (opcode q) observations
    (observations ++ [{|flushedOutput := stdout looked ++ Protocol.reply_bytes (reply q found kind flag); unreadInput := stdin looked|}])); try assumption.
  - destruct q; cbn [opcode]; lia.
  - reflexivity.
  - rewrite actual_handler. change (execLocalObserved (handler q funcdef_0__readNat) (initial,observations) = Some (tt,(after,
      observations ++ [{|flushedOutput := stdout looked ++ Protocol.reply_bytes (reply q found kind flag); unreadInput := stdin looked|}]))).
    eapply generated_handler; eassumption.
  - change (8 < length (memory (result looked q found kind flag) arraydef_0__meta))%nat.
    change (8 < length (memory looked arraydef_0__meta))%nat. lia.
Qed.
End CommandNameQueryExecution.
