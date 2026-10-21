From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure CommandSteps CommandChain CommandDispatch ReplyOK.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module FormulaAtomsExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Definition arguments opcode a b := update (update (update (fun _ => 0) vardef_0__intern_tag opcode) vardef_0__intern_a a) vardef_0__intern_b b.
Definition frame_after (f : Frame) internstate index a b :=
  setMachine (setNum (setNum f vardef_0__command_a a) vardef_0__command_b b) (ReplyOKExecution.reply_state internstate index).
Local Opaque funcdef_0__ok funcdef_0__no funcdef_0__intern.
Theorem generated_handler_1 reader (f : Frame) firststate secondstate internstate index a b observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(firststate,observations)) ->
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  (17 < length (memory firststate arraydef_0__meta))%nat ->
  meta_value firststate 11 = a -> meta_value firststate 14 = 1 -> meta_value firststate 8 = 0 ->
  execObserved (reader (fun _ => false) (fun _ => 0)) (firststate,observations) = Some (tt,(secondstate,observations)) ->
  (17 < length (memory secondstate arraydef_0__meta))%nat ->
  meta_value secondstate 11 = b -> meta_value secondstate 14 = 1 -> meta_value secondstate 8 = 0 ->
  execObserved (funcdef_0__intern (fun _ => false) (arguments 1 a b)) (secondstate,observations) = Some (tt,(internstate,observations)) ->
  (17 < length (memory internstate arraydef_0__meta))%nat ->
  (20 <= length (memory internstate arraydef_0__printBuffer))%nat ->
  meta_value internstate 8 = 0 -> meta_value internstate 0 = Z.of_nat index -> Z.of_nat index <= maximum ->
  execLocalObserved (CommandStructure.handler_1 reader) (f,observations) = Some (tt,(frame_after f internstate index a b,
    observations ++ [{|flushedOutput := stdout internstate ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin internstate|}])).
Proof.
  intros HreadA Hinitial Hinitialerror Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror Hintern Hpostmeta Hbuffer Hposterror Hresult Hword.
  destruct f as [s bs ns]. cbn [machine] in *.
  unfold CommandStructure.handler_1.
  repeat first [progress cbn [optionBind fst snd]
    |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine];
       first [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hpostmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hsecondmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hfirstmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hinitial]])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (?reader_fn ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (reader_fn br nr) state) in
        first [let Hread := fresh "Hread" in assert (Hread : expression = Some (tt,(firststate,observations))) by exact HreadA;
               rewrite Hread; clear Hread
          |let Hread := fresh "Hread" in assert (Hread : expression = Some (tt,(secondstate,observations))) by exact HreadB;
               rewrite Hread; clear Hread] end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
        let Hi := fresh "Hi" in assert (Hi : expression = Some (tt,(internstate,observations))) by exact Hintern;
        rewrite Hi; clear Hi end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__ok ?bo ?no) (?current,?trace)] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__ok bo no) (current,trace)) in
        let Hok := fresh "Hok" in assert (Hok : expression = Some (tt,(ReplyOKExecution.reply_state current index,
          trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin current|}]))) by
          (apply (ReplyOKExecution.generated_ok current bo no index trace); [reflexivity|exact Hword|exact Hbuffer]);
        rewrite Hok; clear Hok end
    |match goal with |- context [meta_value firststate 11] => progress rewrite Hfirstnumber end
    |match goal with |- context [meta_value secondstate 11] => progress rewrite Hsecondnumber end
    |match goal with |- context [meta_value firststate 14] => progress rewrite Hfirstvalid end
    |match goal with |- context [meta_value secondstate 14] => progress rewrite Hsecondvalid end
    |match goal with |- context [meta_value firststate 8] => progress rewrite Hfirsterror end
    |match goal with |- context [meta_value secondstate 8] => progress rewrite Hseconderror end
    |match goal with |- context [meta_value internstate 8] => progress rewrite Hposterror end
    |match goal with |- context [meta_value internstate 0] => progress rewrite Hresult end
    |match goal with |- context [meta_value s 8] => progress rewrite Hinitialerror end
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 1) with 1%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ].
  unfold frame_after; reflexivity.
Qed.
Theorem generated_handler_2 reader (f : Frame) firststate secondstate internstate index a b observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(firststate,observations)) ->
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  (17 < length (memory firststate arraydef_0__meta))%nat ->
  meta_value firststate 11 = a -> meta_value firststate 14 = 1 -> meta_value firststate 8 = 0 ->
  execObserved (reader (fun _ => false) (fun _ => 0)) (firststate,observations) = Some (tt,(secondstate,observations)) ->
  (17 < length (memory secondstate arraydef_0__meta))%nat ->
  meta_value secondstate 11 = b -> meta_value secondstate 14 = 1 -> meta_value secondstate 8 = 0 ->
  execObserved (funcdef_0__intern (fun _ => false) (arguments 2 a b)) (secondstate,observations) = Some (tt,(internstate,observations)) ->
  (17 < length (memory internstate arraydef_0__meta))%nat ->
  (20 <= length (memory internstate arraydef_0__printBuffer))%nat ->
  meta_value internstate 8 = 0 -> meta_value internstate 0 = Z.of_nat index -> Z.of_nat index <= maximum ->
  execLocalObserved (CommandStructure.handler_2 reader) (f,observations) = Some (tt,(frame_after f internstate index a b,
    observations ++ [{|flushedOutput := stdout internstate ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin internstate|}])).
Proof.
  intros HreadA Hinitial Hinitialerror Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror Hintern Hpostmeta Hbuffer Hposterror Hresult Hword.
  destruct f as [s bs ns]. cbn [machine] in *.
  unfold CommandStructure.handler_2.
  repeat first [progress cbn [optionBind fst snd]
    |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine];
       first [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hpostmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hsecondmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hfirstmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hinitial]])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (?reader_fn ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (reader_fn br nr) state) in
        first [let Hread := fresh "Hread" in assert (Hread : expression = Some (tt,(firststate,observations))) by exact HreadA;
               rewrite Hread; clear Hread
          |let Hread := fresh "Hread" in assert (Hread : expression = Some (tt,(secondstate,observations))) by exact HreadB;
               rewrite Hread; clear Hread] end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
        let Hi := fresh "Hi" in assert (Hi : expression = Some (tt,(internstate,observations))) by exact Hintern;
        rewrite Hi; clear Hi end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__ok ?bo ?no) (?current,?trace)] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__ok bo no) (current,trace)) in
        let Hok := fresh "Hok" in assert (Hok : expression = Some (tt,(ReplyOKExecution.reply_state current index,
          trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin current|}]))) by
          (apply (ReplyOKExecution.generated_ok current bo no index trace); [reflexivity|exact Hword|exact Hbuffer]);
        rewrite Hok; clear Hok end
    |match goal with |- context [meta_value firststate 11] => progress rewrite Hfirstnumber end
    |match goal with |- context [meta_value secondstate 11] => progress rewrite Hsecondnumber end
    |match goal with |- context [meta_value firststate 14] => progress rewrite Hfirstvalid end
    |match goal with |- context [meta_value secondstate 14] => progress rewrite Hsecondvalid end
    |match goal with |- context [meta_value firststate 8] => progress rewrite Hfirsterror end
    |match goal with |- context [meta_value secondstate 8] => progress rewrite Hseconderror end
    |match goal with |- context [meta_value internstate 8] => progress rewrite Hposterror end
    |match goal with |- context [meta_value internstate 0] => progress rewrite Hresult end
    |match goal with |- context [meta_value s 8] => progress rewrite Hinitialerror end
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 1) with 1%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ].
  unfold frame_after; reflexivity.
Qed.
Theorem generated_handler opcode reader (f : Frame) firststate secondstate internstate index a b observations :
  (opcode = 1 \/ opcode = 2) ->
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(firststate,observations)) ->
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  (17 < length (memory firststate arraydef_0__meta))%nat ->
  meta_value firststate 11 = a -> meta_value firststate 14 = 1 -> meta_value firststate 8 = 0 ->
  execObserved (reader (fun _ => false) (fun _ => 0)) (firststate,observations) = Some (tt,(secondstate,observations)) ->
  (17 < length (memory secondstate arraydef_0__meta))%nat ->
  meta_value secondstate 11 = b -> meta_value secondstate 14 = 1 -> meta_value secondstate 8 = 0 ->
  execObserved (funcdef_0__intern (fun _ => false) (arguments opcode a b)) (secondstate,observations) = Some (tt,(internstate,observations)) ->
  (17 < length (memory internstate arraydef_0__meta))%nat ->
  (20 <= length (memory internstate arraydef_0__printBuffer))%nat ->
  meta_value internstate 8 = 0 -> meta_value internstate 0 = Z.of_nat index -> Z.of_nat index <= maximum ->
  execLocalObserved (CommandChain.handler_for reader opcode) (f,observations) = Some (tt,(frame_after f internstate index a b,
    observations ++ [{|flushedOutput := stdout internstate ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin internstate|}])).
Proof.
  intros Hcase HreadA Hinitial Hinitialerror Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror Hintern Hpostmeta Hbuffer Hposterror Hresult Hword.
  destruct Hcase as [Hcase|Hcase]; subst opcode;
    [eapply generated_handler_1|eapply generated_handler_2]; eassumption.
Qed.
Theorem generated_command opcode s bs ns opstate firststate secondstate internstate index a b observations :
  (opcode = 1 \/ opcode = 2) ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(opstate,observations)) ->
  (17 < length (memory opstate arraydef_0__meta))%nat ->
  meta_value opstate 11 = opcode -> meta_value opstate 14 = 1 -> meta_value opstate 8 = 0 ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (opstate,observations) = Some (tt,(firststate,observations)) ->
  (17 < length (memory firststate arraydef_0__meta))%nat ->
  meta_value firststate 11 = a -> meta_value firststate 14 = 1 -> meta_value firststate 8 = 0 ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (firststate,observations) = Some (tt,(secondstate,observations)) ->
  (17 < length (memory secondstate arraydef_0__meta))%nat ->
  meta_value secondstate 11 = b -> meta_value secondstate 14 = 1 -> meta_value secondstate 8 = 0 ->
  execObserved (funcdef_0__intern (fun _ => false) (arguments opcode a b)) (secondstate,observations) = Some (tt,(internstate,observations)) ->
  (17 < length (memory internstate arraydef_0__meta))%nat ->
  (20 <= length (memory internstate arraydef_0__printBuffer))%nat ->
  meta_value internstate 8 = 0 -> meta_value internstate 0 = Z.of_nat index -> Z.of_nat index <= maximum ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(ReplyOKExecution.reply_state internstate index,
    observations ++ [{|flushedOutput := stdout internstate ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin internstate|}])).
Proof.
  intros Hcase Hopcode Hmeta Hnumber Hvalid Herror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror Hintern Hpostmeta Hbuffer Hposterror Hresult Hword.
  set (initial := CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} opstate opcode).
  set (after := frame_after initial internstate index a b).
  apply (CommandDispatch.generated_positive_command s bs ns after opstate opcode observations
    (observations ++ [{|flushedOutput := stdout internstate ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin internstate|}]));
    try assumption.
  - destruct Hcase; lia.
  - reflexivity.
  - change (execLocalObserved (CommandChain.handler_for funcdef_0__readNat opcode) (initial,observations) =
      Some (tt,(after,observations ++ [{|flushedOutput := stdout internstate ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin internstate|}]))).
    eapply generated_handler with (firststate := firststate) (secondstate := secondstate); eassumption.
  - change (8 < length (memory (ReplyOKExecution.reply_state internstate index) arraydef_0__meta))%nat.
    rewrite ReplyOKExecution.reply_other by discriminate. lia.
  - change (meta_value (ReplyOKExecution.reply_state internstate index) 8 = 0).
    unfold meta_value. rewrite ReplyOKExecution.reply_other by discriminate. exact Hposterror.
Qed.
End FormulaAtomsExecution.
