From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Intern FormulaEncoding FormulaTopology Representation
  FormulaCircuit FormulaCircuitProperties.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomCircuits.
Import IndexExecution SipHashExecution.

(* The wire order is the actual order of calls in the native axiom builder. *)
Definition k_plan := [FormulaCircuit.implies 1 0; FormulaCircuit.implies 0 2].
Definition k_values p q := [p;q;SetTheory.implies q p;
  SetTheory.axiom_formula (SetTheory.K p q)].
Definition s_plan := [FormulaCircuit.implies 1 2; FormulaCircuit.implies 0 3;
  FormulaCircuit.implies 0 1; FormulaCircuit.implies 0 2;
  FormulaCircuit.implies 5 6; FormulaCircuit.implies 4 7].
Definition s_values p q r := [p;q;r;SetTheory.implies q r;
  SetTheory.implies p (SetTheory.implies q r);SetTheory.implies p q;
  SetTheory.implies p r;SetTheory.implies (SetTheory.implies p q) (SetTheory.implies p r);
  SetTheory.axiom_formula (SetTheory.Srule p q r)].
Definition dne_plan := [FormulaCircuit.implies 1 0; FormulaCircuit.implies 2 0;
  FormulaCircuit.implies 3 1].
Definition dne_values p := [SetTheory.falsity;p;SetTheory.neg p;SetTheory.neg (SetTheory.neg p);
  SetTheory.axiom_formula (SetTheory.DNE p)].
Lemma k_infer p q : FormulaCircuit.infer k_plan [p;q] = Some (k_values p q).
Proof. reflexivity. Qed.
Lemma s_infer p q r : FormulaCircuit.infer s_plan [p;q;r] = Some (s_values p q r).
Proof. reflexivity. Qed.
Lemma dne_infer p : FormulaCircuit.infer dne_plan [SetTheory.falsity;p] = Some (dne_values p).
Proof. reflexivity. Qed.
Lemma k_fits : Forall FormulaCircuit.fits k_plan.
Proof. repeat constructor. Qed.
Lemma s_fits : Forall FormulaCircuit.fits s_plan.
Proof. repeat constructor. Qed.
Lemma dne_fits : Forall FormulaCircuit.fits dne_plan.
Proof. repeat constructor. Qed.

Definition constructed observations plan initial_ids values reserve s fs final next result_ids :=
  FormulaCircuit.executes observations plan s initial_ids final result_ids /\
  InternExecution.logical_frame s final /\ NativeRepresentation.canonical_arena final next /\
  meta_value final 8=0 /\ FormulaCircuit.represents next result_ids values /\
  (exists extra,next=fs++extra) /\
  Z.of_nat (length next+reserve)<=9223372036854775807 /\
  FormulaTopology.ordered final (length next) /\ (length next<=length fs+length plan)%nat.

Theorem construct_k s fs p_id q_id p q reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  word p_id -> word q_id -> nth_error fs (Z.to_nat p_id)=Some p -> nth_error fs (Z.to_nat q_id)=Some q ->
  Z.of_nat (length fs+2+reserve)<=9223372036854775807 ->
  exists final next result_ids,
    constructed observations k_plan [p_id;q_id] (k_values p q) reserve s fs final next result_ids.
Proof.
  intros Harena Hordered Herror Hpword Hqword Hp Hq Hbudget.
  apply (FormulaCircuitProperties.complete k_plan s fs [p_id;q_id] [p;q] (k_values p q) reserve observations Harena Hordered Herror).
  - constructor; [auto|]. constructor; [auto|constructor].
  - apply k_fits.
  - apply k_infer.
  - exact Hbudget.
Qed.
Theorem construct_s s fs p_id q_id r_id p q r reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  word p_id -> word q_id -> word r_id ->
  nth_error fs (Z.to_nat p_id)=Some p -> nth_error fs (Z.to_nat q_id)=Some q -> nth_error fs (Z.to_nat r_id)=Some r ->
  Z.of_nat (length fs+6+reserve)<=9223372036854775807 ->
  exists final next result_ids,
    constructed observations s_plan [p_id;q_id;r_id] (s_values p q r) reserve s fs final next result_ids.
Proof.
  intros Harena Hordered Herror Hpword Hqword Hrword Hp Hq Hr Hbudget.
  apply (FormulaCircuitProperties.complete s_plan s fs [p_id;q_id;r_id] [p;q;r] (s_values p q r) reserve observations Harena Hordered Herror).
  - constructor; [auto|]. constructor; [auto|]. constructor; [auto|constructor].
  - apply s_fits.
  - apply s_infer.
  - exact Hbudget.
Qed.
Theorem construct_dne s fs p_id p reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs 0=Some SetTheory.falsity -> word p_id -> nth_error fs (Z.to_nat p_id)=Some p ->
  Z.of_nat (length fs+3+reserve)<=9223372036854775807 ->
  exists final next result_ids,
    constructed observations dne_plan [0;p_id] (dne_values p) reserve s fs final next result_ids.
Proof.
  intros Harena Hordered Herror Hfalse Hpword Hp Hbudget.
  apply (FormulaCircuitProperties.complete dne_plan s fs [0;p_id] [SetTheory.falsity;p] (dne_values p) reserve observations Harena Hordered Herror).
  - constructor; [split; [unfold word,maximum; lia|exact Hfalse]|]. constructor; [auto|constructor].
  - apply dne_fits.
  - apply dne_infer.
  - exact Hbudget.
Qed.

(* These lemmas identify the native result slot, rather than only an abstract
   wire, and establish an object-theory derivation of its formula. *)
Theorem k_result observations s p_id q_id final ids next p q :
  FormulaCircuit.executes observations k_plan s [p_id;q_id] final ids ->
  FormulaCircuit.represents next ids (k_values p q) ->
  word (meta_value final 0) /\
  nth_error next (Z.to_nat (meta_value final 0))=Some (SetTheory.axiom_formula (SetTheory.K p q)) /\
  SetTheory.derives (SetTheory.axiom_formula (SetTheory.K p q)).
Proof.
  intros Htrace Hrep.
  pose proof (FormulaCircuit.wire next ids (k_values p q) 3
    (SetTheory.axiom_formula (SetTheory.K p q)) Hrep eq_refl) as Hwire.
  unfold k_plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  cbn [List.nth app] in Hwire. destruct Hwire as [Hword Hmeaning].
  split; [exact Hword|]. split; [exact Hmeaning|apply SetTheory.d_k].
Qed.
Theorem s_result observations s p_id q_id r_id final ids next p q r :
  FormulaCircuit.executes observations s_plan s [p_id;q_id;r_id] final ids ->
  FormulaCircuit.represents next ids (s_values p q r) ->
  word (meta_value final 0) /\
  nth_error next (Z.to_nat (meta_value final 0))=Some (SetTheory.axiom_formula (SetTheory.Srule p q r)) /\
  SetTheory.derives (SetTheory.axiom_formula (SetTheory.Srule p q r)).
Proof.
  intros Htrace Hrep.
  pose proof (FormulaCircuit.wire next ids (s_values p q r) 8
    (SetTheory.axiom_formula (SetTheory.Srule p q r)) Hrep eq_refl) as Hwire.
  unfold s_plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  cbn [List.nth app] in Hwire. destruct Hwire as [Hword Hmeaning].
  split; [exact Hword|]. split; [exact Hmeaning|apply SetTheory.d_s].
Qed.
Theorem dne_result observations s p_id final ids next p :
  FormulaCircuit.executes observations dne_plan s [0;p_id] final ids ->
  FormulaCircuit.represents next ids (dne_values p) ->
  word (meta_value final 0) /\
  nth_error next (Z.to_nat (meta_value final 0))=Some (SetTheory.axiom_formula (SetTheory.DNE p)) /\
  SetTheory.derives (SetTheory.axiom_formula (SetTheory.DNE p)).
Proof.
  intros Htrace Hrep.
  pose proof (FormulaCircuit.wire next ids (dne_values p) 4
    (SetTheory.axiom_formula (SetTheory.DNE p)) Hrep eq_refl) as Hwire.
  unfold dne_plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  cbn [List.nth app] in Hwire. destruct Hwire as [Hword Hmeaning].
  split; [exact Hword|]. split; [exact Hmeaning|apply SetTheory.d_dne].
Qed.
End AxiomCircuits.
