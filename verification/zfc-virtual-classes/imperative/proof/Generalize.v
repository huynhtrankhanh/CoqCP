From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash NativePrimitives ObservedLocal HistoryStorage AppendTheorem FormulaAll.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module GeneralizeExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__generalize.
Definition arguments := FormulaAllExecution.arguments.
Local Opaque funcdef_0__intern funcdef_0__appendTheorem.
Theorem generated_body (f : Frame) internstate n i fid index observations :
  (i < length (memory (machine f) arraydef_0__theorems))%nat ->
  List.nth i (memory (machine f) arraydef_0__theorems) 0 = fid ->
  nums f vardef_0__generalize_theorem = Z.of_nat i ->
  execObserved (funcdef_0__intern (fun _ => false) (arguments fid)) (machine f,observations) = Some (tt,(internstate,observations)) ->
  (8 < length (memory internstate arraydef_0__meta))%nat ->
  (20 <= length (memory internstate arraydef_0__printBuffer))%nat ->
  meta_value internstate 8 = 0 -> meta_value internstate 3 = Z.of_nat n -> Z.of_nat n < maximum ->
  meta_value internstate 0 = Z.of_nat index ->
  execLocalObserved funcdef_0__generalize_body (f,observations) = Some (tt,(setMachine f (HistoryStorage.result internstate n (Z.of_nat index)),
    observations ++ [{|flushedOutput := stdout internstate ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin internstate|}])).
Proof.
  intros Hi Hlookup Hnum Hintern Hmeta Hbuffer Herror Hcount Hword Hindex.
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold funcdef_0__generalize_body.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id;
       lazymatch name with
       | arraydef_0__meta => eapply Nat.le_lt_trans with (m := 8%nat); [cbn; lia|exact Hmeta]
       | arraydef_0__theorems => exact Hi
       end)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(internstate,observations))) by exact Hintern;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__appendTheorem ?ba ?na) (?current,?trace)] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__appendTheorem ba na) (current,trace)) in
        let Happend := fresh "Happend" in assert (Happend : expression = Some (tt,(HistoryStorage.result current n (Z.of_nat index),
          trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin current|}]))) by
          (apply (AppendTheoremExecution.generated_append current ba na n (Z.of_nat index) trace); try assumption; reflexivity);
        rewrite Happend; clear Happend end
    |progress rewrite Hnum |progress rewrite Nat2Z.id |progress rewrite Hlookup
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity |progress rewrite Hindex
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. reflexivity.
Qed.
Theorem generated_generalize s bs ns internstate n i fid index observations :
  (i < length (memory s arraydef_0__theorems))%nat -> List.nth i (memory s arraydef_0__theorems) 0 = fid ->
  ns vardef_0__generalize_theorem = Z.of_nat i ->
  execObserved (funcdef_0__intern (fun _ => false) (arguments fid)) (s,observations) = Some (tt,(internstate,observations)) ->
  (8 < length (memory internstate arraydef_0__meta))%nat ->
  (20 <= length (memory internstate arraydef_0__printBuffer))%nat ->
  meta_value internstate 8 = 0 -> meta_value internstate 3 = Z.of_nat n -> Z.of_nat n < maximum ->
  meta_value internstate 0 = Z.of_nat index ->
  execObserved (funcdef_0__generalize bs ns) (s,observations) = Some (tt,(HistoryStorage.result internstate n (Z.of_nat index),
    observations ++ [{|flushedOutput := stdout internstate ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin internstate|}])).
Proof.
  intros Hi Hlookup Hnum Hintern Hmeta Hbuffer Herror Hcount Hword Hindex.
  unfold funcdef_0__generalize. rewrite ObservedLocal.eliminate_correct.
  pose proof (generated_body {|machine := s; bools := bs; nums := ns|} internstate n i fid index observations
    Hi Hlookup Hnum Hintern Hmeta Hbuffer Herror Hcount Hword Hindex) as Hrun.
  unfold Frame in Hrun. rewrite Hrun. reflexivity.
Qed.
End GeneralizeExecution.
