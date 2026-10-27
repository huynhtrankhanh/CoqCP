From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal Observation Intern InternBounded InternInvariant HashTable
 FormulaCircuit SchemaEvaluationIndexBounds SchemaEvaluationIndexCircuit Representation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaEvaluationIndexCircuitTrace.
Import IndexExecution SipHashExecution.
Lemma count_is_length s fs : NativeRepresentation.canonical_arena s fs ->
 Z.to_nat (meta_value s 1)=length fs.
Proof. intro H. rewrite (proj1 (proj2 (proj1 H))),Nat2Z.id. reflexivity. Qed.
Lemma trace_bound observations plan s ids final result count bound :
 FormulaCircuit.executes observations plan s ids final result ->
 InternInvariant.table s count -> meta_value s 8=0 ->
 SchemaEvaluationIndexBounds.raw_arena s count bound ->
 Z.of_nat (count+length plan)<=9223372036854775807 ->
 Forall (SchemaEvaluationIndexCircuit.operation_bound bound) plan ->
 SchemaEvaluationIndexBounds.raw_arena final (Z.to_nat (meta_value final 1)) bound.
Proof.
 intro Htrace. induction Htrace as [s ids|op tail s ids middle id final result Hrun Hvalue Hmeta Htail IH] in count|-*.
 - intros Htable Herror Hraw Hcapacity Hops. rewrite (proj1 (proj2 Htable)),Nat2Z.id. exact Hraw.
 - intros Htable Herror Hraw Hcapacity Hops. inversion Hops as [|head rest Hop HopsTail];subst head rest.
   assert (Hcurrent:Z.of_nat count<=9223372036854775807) by (rewrite Nat2Z.inj_add in Hcapacity;lia).
   destruct (InternBounded.generated_intern_bounded s (fun _=>false) (FormulaCircuit.parameters ids op) count Htable Herror Hcurrent)
     as (actual & Hactual & Hframe & Hcanonical).
   assert (Hobserved:execObserved (funcdef_0__intern (fun _=>false) (FormulaCircuit.parameters ids op))
     (s,observations)=Some(tt,(actual,observations))).
   { apply observed_plain;[apply InternalObservation.intern_nf|exact Hactual]. }
   rewrite Hrun in Hobserved. injection Hobserved as HactualEq. subst actual.
   pose proof (SchemaEvaluationIndexBounds.intern_canonical s middle count _ bound Hcanonical Hraw
     (SchemaEvaluationIndexCircuit.parameters_bound ids op bound Hop)) as HmiddleRaw.
   destruct Hcanonical as [HmiddleError [middleCount [index [Hshape [HmiddleTable Hrest]]]]].
   pose proof (proj1 (proj2 HmiddleTable)) as HmiddleCount.
   rewrite HmiddleCount,Nat2Z.id in HmiddleRaw.
   apply (IH middleCount HmiddleTable HmiddleError HmiddleRaw);[|exact HopsTail].
   cbn [length] in Hcapacity. destruct Hshape as [->|[-> _]];lia.
Qed.
Lemma trace_arena observations plan s ids final result fs next bound :
 FormulaCircuit.executes observations plan s ids final result ->
 NativeRepresentation.canonical_arena s fs -> meta_value s 8=0 ->
 SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
 Z.of_nat (length fs+length plan)<=9223372036854775807 ->
 Forall (SchemaEvaluationIndexCircuit.operation_bound bound) plan ->
 NativeRepresentation.canonical_arena final next -> SchemaEvaluationIndexBounds.raw_arena final (length next) bound.
Proof.
 intros Htrace Harena Herror Hraw Hcapacity Hops Hnext.
 rewrite <- (count_is_length final next Hnext).
 exact (trace_bound observations plan s ids final result (length fs) bound Htrace (proj1 Harena) Herror Hraw Hcapacity Hops).
Qed.
End SchemaEvaluationIndexCircuitTrace.
