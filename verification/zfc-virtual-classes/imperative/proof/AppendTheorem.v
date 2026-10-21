From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash InternTail NativePrimitives ObservedLocal HistoryStorage ReplyOK.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module AppendTheoremExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem.
Lemma reply_meta s n i : meta_value (ReplyOKExecution.reply_state s n) i = meta_value s i.
Proof. unfold meta_value. now rewrite ReplyOKExecution.reply_other by discriminate. Qed.
Local Opaque funcdef_0__ok.
Theorem generated_body (f : Frame) n node observations :
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  (20 <= length (memory (machine f) arraydef_0__printBuffer))%nat ->
  meta_value (machine f) 8 = 0 -> meta_value (machine f) 3 = Z.of_nat n -> Z.of_nat n < maximum ->
  nums f vardef_0__appendTheorem_node = node ->
  execLocalObserved funcdef_0__appendTheorem_body (f,observations) = Some (tt,(setMachine f (HistoryStorage.result (machine f) n node),
    observations ++ [{|flushedOutput := stdout (machine f) ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin (machine f)|}])).
Proof.
  intros Hmeta Hbuffer Herror Hcount Hword Hnode. destruct f as [s bs ns]. cbn [machine nums] in *.
  assert (Hnext : coerceInt (Z.of_nat n + 1) 64 = Z.of_nat (S n)).
  { rewrite coerce_word by (unfold word; lia). lia. }
  assert (Hcountword : Z.of_nat n <= maximum) by lia. unfold maximum in Hword.
  unfold funcdef_0__appendTheorem_body.
  repeat first [progress cbn [optionBind fst snd]
    |progress unfold addInt at 1
    |progress fold (HistoryStorage.grown s n)
    |progress change (withMemory (HistoryStorage.grown s n)
       (modifyArray (memory (HistoryStorage.grown s n)) arraydef_0__theorems n node)) with (HistoryStorage.written s n node)
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       lazymatch name with
       | arraydef_0__meta =>
           repeat first [rewrite ReplyOKExecution.reply_other by discriminate
             |rewrite HistoryStorage.grown_other by discriminate |rewrite HistoryStorage.written_other by discriminate];
           eapply Nat.le_lt_trans with (m := 8%nat); [cbn; lia|exact Hmeta]
       | arraydef_0__theorems => unfold HistoryStorage.grown; cbn [withMemory memory];
           rewrite growArrays_same, growList_length; rewrite ?Nat2Z.id; lia
       end)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__ok ?bo ?no) (?current,?trace)] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__ok bo no) (current,trace)) in
        let Hok := fresh "Hok" in assert (Hok : expression = Some (tt,(ReplyOKExecution.reply_state current n,
          trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin current|}]))) by
          (apply (ReplyOKExecution.generated_ok current bo no n trace);
            [reflexivity|exact Hcountword|rewrite HistoryStorage.written_other by discriminate; exact Hbuffer]);
        rewrite Hok; clear Hok end
    |progress rewrite reply_meta
    |progress rewrite HistoryStorage.grown_meta
    |progress rewrite HistoryStorage.written_meta
    |progress rewrite Herror
    |progress rewrite Hcount
    |progress rewrite Hnode
    |progress rewrite Hnext
    |progress rewrite Nat2Z.id
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 3) with 3%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. reflexivity.
Qed.
Theorem generated_append s bs ns n node observations :
  (8 < length (memory s arraydef_0__meta))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 8 = 0 -> meta_value s 3 = Z.of_nat n -> Z.of_nat n < maximum ->
  ns vardef_0__appendTheorem_node = node ->
  execObserved (funcdef_0__appendTheorem bs ns) (s,observations) = Some (tt,(HistoryStorage.result s n node,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin s|}])).
Proof.
  intros Hmeta Hbuffer Herror Hcount Hword Hnode. unfold funcdef_0__appendTheorem.
  rewrite ObservedLocal.eliminate_correct.
  pose proof (generated_body {|machine := s; bools := bs; nums := ns|} n node observations Hmeta Hbuffer Herror Hcount Hword Hnode) as Hrun.
  unfold Frame in Hrun. rewrite Hrun. reflexivity.
Qed.
End AppendTheoremExecution.
