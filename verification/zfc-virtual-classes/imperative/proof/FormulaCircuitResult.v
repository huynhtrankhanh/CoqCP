From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash FormulaCircuit.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module FormulaCircuitResult.
Import IndexExecution SipHashExecution.
Lemma wire_count observations plan s ids final result : FormulaCircuit.executes observations plan s ids final result ->
  length result=(length ids+length plan)%nat.
Proof.
  intro Htrace. induction Htrace as [s ids|op tail s ids middle id final result Hrun Hvalue Hmeta Htail IH].
  - cbn [length]. lia.
  - rewrite IH,length_app. cbn [length]. lia.
Qed.
Lemma last_slot observations plan s ids final result : FormulaCircuit.executes observations plan s ids final result ->
  plan<>[] -> nth_error result (length ids+length plan-1)=Some (meta_value final 0).
Proof.
  intro Htrace. induction Htrace as [s ids|op tail s ids middle id final result Hrun Hvalue Hmeta Htail IH].
  - contradiction.
  - intro Hnonempty. destruct tail as [|head rest].
    + inversion Htail;subst. cbn [length].
      replace (length ids+1-1)%nat with (length ids) by lia.
      rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. cbn [nth_error]. reflexivity.
    + specialize (IH ltac:(discriminate)).
      rewrite length_app in IH. cbn [length] in IH |- *. replace (length ids+S (S (length rest))-1)%nat
        with (length ids+1+S (length rest)-1)%nat by lia. exact IH.
Qed.
Theorem meaning observations plan s ids final result fs values p :
  FormulaCircuit.executes observations plan s ids final result -> plan<>[] -> FormulaCircuit.represents fs result values ->
  nth_error values (length ids+length plan-1)=Some p ->
  word (meta_value final 0) /\ nth_error fs (Z.to_nat (meta_value final 0))=Some p.
Proof.
  intros Htrace Hnonempty Hrep Htarget.
  pose proof (FormulaCircuit.wire fs result values (length ids+length plan-1) p Hrep Htarget) as Hwire.
  pose proof (last_slot _ _ _ _ _ _ Htrace Hnonempty) as Hlast.
  rewrite (List.nth_error_nth _ _ 0 Hlast) in Hwire. exact Hwire.
Qed.
End FormulaCircuitResult.
