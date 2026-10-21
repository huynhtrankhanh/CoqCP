From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash HashTable NativePrimitives ObservedLocal HistoryStorage AppendTheorem ReplyNO.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ModusPonensExecution.
Import IndexExecution SipHashExecution HashTableInvariant ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens.
Definition after (f : Frame) n node consequent :=
  setMachine (setNum f vardef_0__modusPonens_node (Z.of_nat node))
    (HistoryStorage.result (machine f) n consequent).
Local Opaque funcdef_0__appendTheorem funcdef_0__no.
Theorem generated_body (f : Frame) n i j node antecedent consequent observations :
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  (20 <= length (memory (machine f) arraydef_0__printBuffer))%nat ->
  meta_value (machine f) 8 = 0 -> meta_value (machine f) 3 = Z.of_nat n -> Z.of_nat n < maximum ->
  (i < length (memory (machine f) arraydef_0__theorems))%nat ->
  (j < length (memory (machine f) arraydef_0__theorems))%nat ->
  (node < length (memory (machine f) arraydef_0__formulas))%nat ->
  List.nth i (memory (machine f) arraydef_0__theorems) 0 = Z.of_nat node ->
  List.nth j (memory (machine f) arraydef_0__theorems) 0 = antecedent ->
  tuple_at (machine f) node = (3,antecedent,consequent) ->
  nums f vardef_0__modusPonens_implication = Z.of_nat i ->
  nums f vardef_0__modusPonens_antecedent = Z.of_nat j ->
  execLocalObserved funcdef_0__modusPonens_body (f,observations) = Some (tt,(after f n node consequent,
    observations ++ [{|flushedOutput := stdout (machine f) ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin (machine f)|}])).
Proof.
  intros Hmeta Hbuffer Herror Hcount Hword Hi Hj Hnode Hlookupi Hlookupj Htuple Hni Hnj.
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold tuple_at in Htuple.
  unfold funcdef_0__modusPonens_body.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id;
       lazymatch name with
       | arraydef_0__meta => eapply Nat.le_lt_trans with (m := 8%nat); [cbn; lia|exact Hmeta]
       | arraydef_0__theorems => first [exact Hi|exact Hj]
       | arraydef_0__formulas => exact Hnode
       end)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__appendTheorem ?ba ?na) (?current,?trace)] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__appendTheorem ba na) (current,trace)) in
        let Happend := fresh "Happend" in assert (Happend : expression = Some (tt,(HistoryStorage.result current n consequent,
          trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin current|}]))) by
          (apply (AppendTheoremExecution.generated_append current ba na n consequent trace); try assumption; reflexivity);
        rewrite Happend; clear Happend end
    |progress rewrite Hni |progress rewrite Hnj |progress rewrite Nat2Z.id
    |progress rewrite Hlookupi |progress rewrite Hlookupj |progress rewrite Htuple
    |match goal with |- context [bool_decide ?P] => progress rewrite (bool_decide_true P) by reflexivity end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. unfold after. reflexivity.
Qed.
Theorem generated_modusPonens s bs ns n i j node antecedent consequent observations :
  (8 < length (memory s arraydef_0__meta))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 8 = 0 -> meta_value s 3 = Z.of_nat n -> Z.of_nat n < maximum ->
  (i < length (memory s arraydef_0__theorems))%nat ->
  (j < length (memory s arraydef_0__theorems))%nat ->
  (node < length (memory s arraydef_0__formulas))%nat ->
  List.nth i (memory s arraydef_0__theorems) 0 = Z.of_nat node ->
  List.nth j (memory s arraydef_0__theorems) 0 = antecedent ->
  tuple_at s node = (3,antecedent,consequent) ->
  ns vardef_0__modusPonens_implication = Z.of_nat i ->
  ns vardef_0__modusPonens_antecedent = Z.of_nat j ->
  execObserved (funcdef_0__modusPonens bs ns) (s,observations) = Some (tt,(HistoryStorage.result s n consequent,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin s|}])).
Proof.
  intros Hmeta Hbuffer Herror Hcount Hword Hi Hj Hnode Hlookupi Hlookupj Htuple Hni Hnj.
  unfold funcdef_0__modusPonens. rewrite ObservedLocal.eliminate_correct.
  pose proof (generated_body {|machine := s; bools := bs; nums := ns|} n i j node antecedent consequent observations
    Hmeta Hbuffer Herror Hcount Hword Hi Hj Hnode Hlookupi Hlookupj Htuple Hni Hnj) as Hrun.
  unfold Frame in Hrun. rewrite Hrun. reflexivity.
Qed.
Theorem generated_rejected_body (f : Frame) i j node antecedent tag left right observations :
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  (i < length (memory (machine f) arraydef_0__theorems))%nat ->
  (j < length (memory (machine f) arraydef_0__theorems))%nat ->
  (node < length (memory (machine f) arraydef_0__formulas))%nat ->
  List.nth i (memory (machine f) arraydef_0__theorems) 0 = Z.of_nat node ->
  List.nth j (memory (machine f) arraydef_0__theorems) 0 = antecedent ->
  tuple_at (machine f) node = (tag,left,right) ->
  (tag <> 3 \/ left <> antecedent) ->
  nums f vardef_0__modusPonens_implication = Z.of_nat i ->
  nums f vardef_0__modusPonens_antecedent = Z.of_nat j ->
  execLocalObserved funcdef_0__modusPonens_body (f,observations) = Some (tt,(setMachine (setNum f vardef_0__modusPonens_node (Z.of_nat node)) (ReplyNOExecution.reply_state (machine f)),
    observations ++ [{|flushedOutput := stdout (machine f) ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin (machine f)|}])).
Proof.
  intros Hmeta Hi Hj Hnode Hlookupi Hlookupj Htuple Hbad Hni Hnj.
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold tuple_at in Htuple.
  unfold funcdef_0__modusPonens_body.
  let solve_run := ltac:(repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id;
       lazymatch name with
       | arraydef_0__meta => eapply Nat.le_lt_trans with (m := 8%nat); [cbn; lia|exact Hmeta]
       | arraydef_0__theorems => first [exact Hi|exact Hj]
       | arraydef_0__formulas => exact Hnode
       end)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bn ?nn) (?current,?trace)] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__no bn nn) (current,trace)) in
        let Hno := fresh "Hno" in assert (Hno : expression = Some (tt,(ReplyNOExecution.reply_state current,
          trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin current|}]))) by
          (exact (ReplyNOExecution.generated_no current bn nn trace)); rewrite Hno; clear Hno end
    |progress rewrite Hni |progress rewrite Hnj |progress rewrite Nat2Z.id
    |progress rewrite Hlookupi |progress rewrite Hlookupj |progress rewrite Htuple
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by reflexivity
       |progress rewrite (bool_decide_false P) by congruence] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]) in
  destruct (Z.eq_dec tag 3) as [Htag|Htag]; [subst tag; destruct Hbad as [Habsurd|Hleft]; [contradiction|]|];
  solve_run; reflexivity.
Qed.
End ModusPonensExecution.
