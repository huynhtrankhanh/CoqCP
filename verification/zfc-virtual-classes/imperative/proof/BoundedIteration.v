From CoqCP Require Import Options.
From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat ZArith.ZArith Lia.
Import ListNotations.
From Trusted Require Import Protocol.
From NativeProof Require Import SchemaUniformBudget SchemaEvaluationBoundedCell NativeBudgetPlan NativeUniformCommand NativeRequestBounds Index.
Module BoundedIteration.
Fixpoint iterate (step:nat->nat) count current := match count with
 | O=>current | S rest=>step (iterate step rest current) end.
Fixpoint checked (step:nat->nat) limit count current :=
 if Nat.leb current limit then match count with
 | O=>Some current | S rest=>checked step limit rest (step current) end else None.
Lemma iterate_shift step count current :
 iterate step count (step current)=step (iterate step count current).
Proof. induction count as [|count IH];cbn [iterate];[reflexivity|now rewrite IH]. Qed.
Lemma iterate_grows step count current : (forall x,(x<=step x)%nat) ->
 (current<=iterate step count current)%nat.
Proof. intro Hstep. induction count as [|count IH];cbn [iterate];[lia|]. specialize (Hstep (iterate step count current)). lia. Qed.
Theorem checked_exact step limit count current : (forall x,(x<=step x)%nat) ->
 checked step limit count current =
 if Nat.leb (iterate step count current) limit then Some (iterate step count current) else None.
Proof.
 intro Hstep. induction count as [|count IH] in current|-*.
 - cbn [checked iterate]. now destruct (Nat.leb current limit).
 - cbn [checked]. destruct (Nat.leb current limit) eqn:Hcurrent.
   + rewrite IH,iterate_shift. reflexivity.
   + apply Nat.leb_gt in Hcurrent. cbn [iterate].
     pose proof (iterate_grows step count current Hstep) as Hgrows.
     pose proof (Hstep (iterate step count current)) as Hnext.
     assert (Hfail : Nat.leb (step (iterate step count current)) limit = false) by (apply Nat.leb_gt;lia).
     now rewrite Hfail.
Qed.
Lemma formula_iterate initial count :
 iterate SchemaUniformBudget.formula_next count initial = SchemaUniformBudget.formula_after initial count.
Proof. induction count as [|count IH];cbn [iterate SchemaUniformBudget.formula_after];[reflexivity|now rewrite IH]. Qed.
Lemma index_iterate E N initial count :
 iterate (SchemaUniformBudget.index_next E N) count initial = SchemaUniformBudget.index_after E N initial count.
Proof. induction count as [|count IH];cbn [iterate SchemaUniformBudget.index_after];[reflexivity|now rewrite IH]. Qed.
Theorem checked_formula_exact limit count initial :
 checked SchemaUniformBudget.formula_next limit count initial =
 if Nat.leb (SchemaUniformBudget.formula_after initial count) limit
 then Some (SchemaUniformBudget.formula_after initial count) else None.
Proof.
 rewrite checked_exact by (intro x;unfold SchemaUniformBudget.formula_next;lia).
 now rewrite formula_iterate.
Qed.
Theorem checked_index_exact E N limit count initial :
 checked (SchemaUniformBudget.index_next E N) limit count initial =
 if Nat.leb (SchemaUniformBudget.index_after E N initial count) limit
 then Some (SchemaUniformBudget.index_after E N initial count) else None.
Proof.
 rewrite checked_exact by (intro x;unfold SchemaUniformBudget.index_next;lia).
 now rewrite index_iterate.
Qed.
Fixpoint iterateZ (step:Z->Z) count current := match count with
 | O=>current | S rest=>step (iterateZ step rest current) end.
Fixpoint checkedZ (step:Z->Z) (limit:Z) count current :=
 if Z.leb current limit then match count with
 | O=>Some current | S rest=>checkedZ step limit rest (step current) end else None.
Lemma iterateZ_shift step count current :
 iterateZ step count (step current)=step (iterateZ step count current).
Proof. induction count as [|count IH];cbn [iterateZ];[reflexivity|now rewrite IH]. Qed.
Lemma iterateZ_grows step count current : (forall x,(x<=step x)%Z) ->
 (current<=iterateZ step count current)%Z.
Proof. intro Hstep. induction count as [|count IH];cbn [iterateZ];[lia|]. specialize (Hstep (iterateZ step count current)). lia. Qed.
Theorem checkedZ_exact step limit count current : (forall x,(x<=step x)%Z) ->
 checkedZ step limit count current =
 if Z.leb (iterateZ step count current) limit then Some (iterateZ step count current) else None.
Proof.
 intro Hstep. induction count as [|count IH] in current|-*.
 - cbn [checkedZ iterateZ]. now destruct (Z.leb current limit).
 - cbn [checkedZ]. destruct (Z.leb current limit) eqn:Hcurrent.
   + rewrite IH,iterateZ_shift. reflexivity.
   + apply Z.leb_gt in Hcurrent. cbn [iterateZ].
     pose proof (iterateZ_grows step count current Hstep) as Hgrows.
     pose proof (Hstep (iterateZ step count current)) as Hnext.
     assert (Hfail : Z.leb (step (iterateZ step count current)) limit = false) by (apply Z.leb_gt;lia).
     now rewrite Hfail.
Qed.
Definition formulaZ x := (x+3*x*x+42)%Z.
Definition indexZ E N x := (2*Z.max 0 x+Z.of_nat E+3*Z.of_nat N+4)%Z.
Lemma formulaZ_conversion initial count :
 iterateZ formulaZ count (Z.of_nat initial) = Z.of_nat (SchemaUniformBudget.formula_after initial count).
Proof.
 induction count as [|count IH];cbn [iterateZ SchemaUniformBudget.formula_after];[reflexivity|].
 rewrite IH. unfold formulaZ,SchemaUniformBudget.formula_next. repeat rewrite Nat2Z.inj_add. repeat rewrite Nat2Z.inj_mul. lia.
Qed.
Lemma indexZ_conversion E N initial count :
 iterateZ (indexZ E N) count (Z.of_nat initial) = Z.of_nat (SchemaUniformBudget.index_after E N initial count).
Proof.
 induction count as [|count IH];cbn [iterateZ SchemaUniformBudget.index_after];[reflexivity|].
 rewrite IH. unfold indexZ,SchemaUniformBudget.index_next. rewrite Z.max_r by lia. repeat rewrite Nat2Z.inj_add. repeat rewrite Nat2Z.inj_mul. lia.
Qed.
Theorem checked_formulaZ_exact limit count initial :
 checkedZ formulaZ limit count (Z.of_nat initial) =
 if Z.leb (Z.of_nat (SchemaUniformBudget.formula_after initial count)) limit
 then Some (Z.of_nat (SchemaUniformBudget.formula_after initial count)) else None.
Proof.
 rewrite checkedZ_exact by (intro x;unfold formulaZ;nia). now rewrite formulaZ_conversion.
Qed.
Theorem checked_indexZ_exact E N limit count initial :
 checkedZ (indexZ E N) limit count (Z.of_nat initial) =
 if Z.leb (Z.of_nat (SchemaUniformBudget.index_after E N initial count)) limit
 then Some (Z.of_nat (SchemaUniformBudget.index_after E N initial count)) else None.
Proof.
 rewrite checkedZ_exact.
 - now rewrite indexZ_conversion.
 - intro x. unfold indexZ. destruct (Z_le_dec 0 x) as [H|H].
   + rewrite Z.max_r by lia. lia.
   + rewrite Z.max_l by lia. lia.
Qed.
Definition fast_head argument_cap before request :=
 if Nat.eqb (Protocol.opcode request) 24 then
 match checkedZ formulaZ SchemaEvaluationBoundedCell.bound (SchemaUniformBudget.slots (NativeBudgetPlan.expressions before))
       (Z.of_nat (NativeBudgetPlan.formulas before)) with
 | None=>false | Some _=>
 match checkedZ (indexZ (NativeBudgetPlan.expressions before) argument_cap) IndexExecution.maximum
       (SchemaUniformBudget.slots (NativeBudgetPlan.expressions before)) (Z.of_nat (NativeBudgetPlan.indices before)) with
 | None=>false | Some _=>NativeBudgetPlan.head_check argument_cap before request end end
 else NativeBudgetPlan.head_check argument_cap before request.
Lemma head_formula_check argument_cap before request : Protocol.opcode request=24%nat ->
 NativeBudgetPlan.head_check argument_cap before request=true ->
 Z.leb (Z.of_nat (SchemaUniformBudget.formula_after (NativeBudgetPlan.formulas before)
    (SchemaUniformBudget.slots (NativeBudgetPlan.expressions before)))) SchemaEvaluationBoundedCell.bound=true.
Proof.
 intros Hop Hcheck. apply Z.leb_le.
 pose proof (NativeBudgetPlan.result_formula_room _ _ _ (NativeBudgetPlan.head_conditions _ _ _ Hcheck)) as H.
 unfold NativeBudgetPlan.step,NativeUniformCommand.formula_end in H. rewrite Hop in H. exact H.
Qed.
Lemma head_index_check argument_cap before request : Protocol.opcode request=24%nat ->
 NativeBudgetPlan.head_check argument_cap before request=true ->
 Z.leb (Z.of_nat (SchemaUniformBudget.index_after (NativeBudgetPlan.expressions before) argument_cap (NativeBudgetPlan.indices before)
    (SchemaUniformBudget.slots (NativeBudgetPlan.expressions before)))) IndexExecution.maximum=true.
Proof.
 intros Hop Hcheck. apply Z.leb_le.
 pose proof (NativeBudgetPlan.result_index_room _ _ _ (NativeBudgetPlan.head_conditions _ _ _ Hcheck)) as H.
 unfold NativeBudgetPlan.step,NativeUniformCommand.index_end in H. rewrite Hop in H. exact H.
Qed.
Theorem fast_head_exact argument_cap before request :
 fast_head argument_cap before request=NativeBudgetPlan.head_check argument_cap before request.
Proof.
 unfold fast_head. destruct (Nat.eqb (Protocol.opcode request) 24) eqn:Hop;[|reflexivity].
 apply Nat.eqb_eq in Hop. rewrite checked_formulaZ_exact,checked_indexZ_exact.
 destruct (Z.leb (Z.of_nat (SchemaUniformBudget.formula_after (NativeBudgetPlan.formulas before)
   (SchemaUniformBudget.slots (NativeBudgetPlan.expressions before)))) SchemaEvaluationBoundedCell.bound) eqn:Hformula.
 - destruct (Z.leb (Z.of_nat (SchemaUniformBudget.index_after (NativeBudgetPlan.expressions before) argument_cap (NativeBudgetPlan.indices before)
     (SchemaUniformBudget.slots (NativeBudgetPlan.expressions before)))) IndexExecution.maximum) eqn:Hindex;[reflexivity|].
   destruct (NativeBudgetPlan.head_check argument_cap before request) eqn:Hhead;[|reflexivity].
   pose proof (head_index_check argument_cap before request Hop Hhead). congruence.
 - destruct (NativeBudgetPlan.head_check argument_cap before request) eqn:Hhead;[|reflexivity].
   pose proof (head_formula_check argument_cap before request Hop Hhead). congruence.
Qed.
Fixpoint fast_check argument_cap before requests := match requests with
 | []=>true | request::tail=>if Nat.eqb (Protocol.opcode request) 0 then true else
   if fast_head argument_cap before request then fast_check argument_cap (NativeBudgetPlan.step argument_cap request before) tail else false end.
Theorem fast_check_exact argument_cap before requests :
 fast_check argument_cap before requests=NativeBudgetPlan.check argument_cap before requests.
Proof.
 induction requests as [|request tail IH] in before|-*;[reflexivity|].
 cbn [fast_check NativeBudgetPlan.check]. destruct (Nat.eqb (Protocol.opcode request) 0);[reflexivity|].
 rewrite fast_head_exact. destruct (NativeBudgetPlan.head_check argument_cap before request);[now rewrite IH|reflexivity].
Qed.
Definition fast_domain requests := let N:=NativeRequestBounds.maximum requests in
 fast_check N (NativeBudgetPlan.initial N) requests=true.
Theorem fast_domain_exact requests : fast_domain requests <-> NativeBudgetPlan.domain requests.
Proof. unfold fast_domain,NativeBudgetPlan.domain. now rewrite fast_check_exact. Qed.
End BoundedIteration.
