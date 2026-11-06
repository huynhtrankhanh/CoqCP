From CoqCP Require Import Options Imperative Execution.
From Trusted Require Import Protocol CapacityGeneral.
From Submission Require Import Index SipHash NativeRequestBounds NativeBudgetPlan NativeUniformCommand NativeUniformResources SchemaUniformBudget SchemaEvaluationIndexBudget SchemaEvaluationBoundedCell AxiomTaggedInvariant.
From Stdlib Require Import Lists.List ZArith.ZArith.
From stdpp Require Import numbers list.
Module AdversarialGeneralCapacityBridge.
Definition convert (c:CapacityGeneral.caps) := NativeBudgetPlan.Caps
 (CapacityGeneral.formulas c) (CapacityGeneral.indices c) (CapacityGeneral.classes c) (CapacityGeneral.history c)
 (CapacityGeneral.bindings c) (CapacityGeneral.expressions c) (CapacityGeneral.names c).
Lemma numbers values : CapacityGeneral.numbers_max values=NativeRequestBounds.numbers_max values.
Proof. induction values;cbn [CapacityGeneral.numbers_max NativeRequestBounds.numbers_max];congruence. Qed.
Lemma maximum requests : CapacityGeneral.maximum requests=NativeRequestBounds.maximum requests.
Proof. induction requests as [|request requests IH];cbn [CapacityGeneral.maximum NativeRequestBounds.maximum];[reflexivity|]. now rewrite numbers,IH. Qed.
Lemma formula_after n k : CapacityGeneral.formula_after n k=SchemaUniformBudget.formula_after n k.
Proof. induction k as [|k IH];cbn [CapacityGeneral.formula_after SchemaUniformBudget.formula_after];[reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma index_after E N n k : CapacityGeneral.index_after E N n k=SchemaUniformBudget.index_after E N n k.
Proof. induction k as [|k IH];cbn [CapacityGeneral.index_after SchemaUniformBudget.index_after];[reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma step N request c : convert(CapacityGeneral.step N request c)=NativeBudgetPlan.step N request (convert c).
Proof.
 destruct c. unfold convert,CapacityGeneral.step,NativeBudgetPlan.step.
 cbn [CapacityGeneral.formulas CapacityGeneral.indices CapacityGeneral.classes CapacityGeneral.history CapacityGeneral.bindings CapacityGeneral.expressions CapacityGeneral.names NativeBudgetPlan.formulas NativeBudgetPlan.indices NativeBudgetPlan.classes NativeBudgetPlan.history NativeBudgetPlan.bindings NativeBudgetPlan.expressions NativeBudgetPlan.names].
 unfold CapacityGeneral.formula_end,CapacityGeneral.index_end,CapacityGeneral.class_end,CapacityGeneral.expression_end,
 NativeUniformCommand.formula_end,NativeUniformCommand.index_end,NativeUniformCommand.class_end,NativeUniformCommand.expression_end.
 unfold CapacityGeneral.slots,SchemaUniformBudget.slots. rewrite formula_after,index_after.
 unfold CapacityGeneral.formula_target,NativeUniformCommand.formula_target,CapacityGeneral.index_target,NativeUniformCommand.index_target,
 CapacityGeneral.axiom_bound,SchemaEvaluationIndexBudget.axiom_cost,CapacityGeneral.axiom_cost,AxiomTaggedInvariant.cost.
 reflexivity.
Qed.
Lemma resources request F B C E N : CapacityGeneral.resources request F B C E N=NativeUniformResources.check request F B C E N.
Proof.
 unfold CapacityGeneral.resources,NativeUniformResources.check. destruct (Protocol.opcode request);try reflexivity.
 all: repeat match goal with |- context [match ?xs with _=>_ end] => destruct xs end;try reflexivity.
 all: unfold CapacityGeneral.guard,NativeUniformResources.guard,CapacityGeneral.wordmax,IndexExecution.maximum,CapacityGeneral.signedmax,CapacityGeneral.axiom_bound,SchemaEvaluationIndexBudget.axiom_cost,CapacityGeneral.axiom_cost,AxiomTaggedInvariant.cost,CapacityGeneral.slots,SchemaUniformBudget.slots.
 all: try rewrite formula_after;try rewrite index_after;reflexivity.
Qed.
Lemma head N c request : CapacityGeneral.head_check N c request=NativeBudgetPlan.head_check N (convert c) request.
Proof.
 unfold CapacityGeneral.head_check,NativeBudgetPlan.head_check,CapacityGeneral.common,NativeBudgetPlan.common.
 rewrite numbers,<-step. rewrite resources. destruct c;reflexivity.
Qed.
Lemma check N c requests : CapacityGeneral.check N c requests=NativeBudgetPlan.check N (convert c) requests.
Proof.
 revert c. induction requests as [|request requests IH];intro c;cbn [CapacityGeneral.check NativeBudgetPlan.check];[reflexivity|].
 destruct (Nat.eqb (Protocol.opcode request) 0);[reflexivity|]. rewrite head,<-step,IH. reflexivity.
Qed.
Theorem domain requests : CapacityGeneral.domain requests <-> NativeBudgetPlan.domain requests.
Proof. unfold CapacityGeneral.domain,NativeBudgetPlan.domain. rewrite maximum,check. reflexivity. Qed.
End AdversarialGeneralCapacityBridge.
