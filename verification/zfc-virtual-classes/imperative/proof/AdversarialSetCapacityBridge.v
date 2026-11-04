From CoqCP Require Import Options Imperative Execution.
From Trusted Require Import Protocol CapacitySet.
From NativeProof Require Import Index SipHash NativeBasicDispatcher NativeFullDispatcher NativeRequestBounds NativeSetBudgetPlan NativeSchemaFlat AxiomTaggedInvariant SchemaEvaluationSetCell.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Bool.Bool Lia.
Import ListNotations.
Open Scope Z_scope.
Module AdversarialSetCapacityBridge.
Definition convert (c:CapacitySet.caps) : NativeSetBudgetPlan.caps :=
 NativeSetBudgetPlan.Caps (CapacitySet.formulas c) (CapacitySet.classes c) (CapacitySet.history c)
  (CapacitySet.bindings c) (CapacitySet.expressions c) (CapacitySet.names c).
Lemma basic_spec opcode : CapacitySet.basic opcode=true <-> NativeBasicDispatcher.supported opcode.
Proof.
 unfold CapacitySet.basic,NativeBasicDispatcher.supported,NativeBasicDispatcher.two,NativeBasicDispatcher.one,
  NativeBasicDispatcher.zero,NativeBasicDispatcher.named,NativeBasicDispatcher.query.
 rewrite existsb_exists. split.
 - intros (x & Hin & Heq). apply Nat.eqb_eq in Heq. subst x. cbn [List.In] in Hin. intuition congruence.
 - intro H. exists opcode. split;[cbn [List.In];intuition congruence|apply Nat.eqb_refl].
Qed.
Lemma basic_false opcode : ~NativeBasicDispatcher.supported opcode -> CapacitySet.basic opcode=false.
Proof. intros H. destruct(CapacitySet.basic opcode) eqn:E;[apply basic_spec in E;contradiction|reflexivity]. Qed.
Lemma admissible request : CapacitySet.admissible request=NativeSetBudgetPlan.admissible request.
Proof.
 unfold CapacitySet.admissible,NativeSetBudgetPlan.admissible.
 destruct(NativeFullDispatcher.supported_dec(Protocol.opcode request)) as [H|H].
 - rewrite (proj2 (basic_spec _) H). reflexivity.
 - rewrite (basic_false _ H). destruct(Protocol.opcode request);reflexivity.
Qed.
Lemma convert_initial : convert CapacitySet.initial=NativeSetBudgetPlan.initial.
Proof. reflexivity. Qed.
Lemma convert_step request before : convert(CapacitySet.step request before)=NativeSetBudgetPlan.step request (convert before).
Proof. destruct before. reflexivity. Qed.
Lemma head_check before request : CapacitySet.head_check before request=NativeSetBudgetPlan.head_check (convert before) request.
Proof.
 unfold CapacitySet.head_check,NativeSetBudgetPlan.head_check. rewrite admissible, <-convert_step.
 destruct before. reflexivity.
Qed.
Theorem check before requests : CapacitySet.check before requests=NativeSetBudgetPlan.check (convert before) requests.
Proof.
 induction requests as [|request tail IH] in before|-*;[reflexivity|]. cbn [CapacitySet.check NativeSetBudgetPlan.check].
 destruct(Nat.eqb(Protocol.opcode request)0);[reflexivity|]. rewrite head_check,<-convert_step,IH. reflexivity.
Qed.
Theorem domain requests : CapacitySet.domain requests <-> NativeSetBudgetPlan.domain requests.
Proof. unfold CapacitySet.domain,NativeSetBudgetPlan.domain. rewrite check,convert_initial. reflexivity. Qed.
End AdversarialSetCapacityBridge.
