From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  SchemaEvaluation SchemaEvaluationControl SchemaMarking ArrayFacts InternTail Overflow.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaPair.
Import IndexExecution SipHashExecution ObservedLocal SchemaEvaluationControl.
Definition Frame := SchemaEvaluation.Frame.
Definition LoopAction := SchemaEvaluation.LoopAction.
Ltac raw_handler handler width remaining outer_remaining :=
 let code:=eval cbv beta iota zeta delta [handler] in (handler width remaining outer_remaining) in
 lazymatch code with dropWithinLoop ?raw=>exact raw end.
Definition raw_meta width remaining outer_remaining : LoopAction unit := ltac:(raw_handler SchemaEvaluation.meta_handler width remaining outer_remaining).
Definition raw_literal width remaining outer_remaining : LoopAction unit := ltac:(raw_handler SchemaEvaluation.literal_handler width remaining outer_remaining).
Definition raw_abstract width remaining outer_remaining : LoopAction unit := ltac:(raw_handler SchemaEvaluation.abstract_handler width remaining outer_remaining).
Definition raw_binary width remaining outer_remaining : LoopAction unit := ltac:(raw_handler SchemaEvaluation.binary_handler width remaining outer_remaining).
Definition raw_all width remaining outer_remaining : LoopAction unit := ltac:(raw_handler SchemaEvaluation.all_handler width remaining outer_remaining).
Definition raw_axiom width remaining outer_remaining : LoopAction unit := ltac:(raw_handler SchemaEvaluation.axiom_handler width remaining outer_remaining).
Definition raw_output width remaining outer_remaining : LoopAction unit := ltac:(raw_handler SchemaEvaluation.output_handler width remaining outer_remaining).
Ltac fold_raw code raw call :=
 let family:=eval pattern raw in code in lazymatch family with ?family _=>
 let result:=eval cbv beta in (family call) in result end.
Definition compact_compute width remaining outer_remaining : LoopAction unit := ltac:(
 let code:=eval cbv beta iota zeta delta [SchemaEvaluation.compute_body] in (SchemaEvaluation.compute_body width remaining outer_remaining) in
 let raw:=eval unfold raw_meta in (raw_meta width remaining outer_remaining) in
 let code:=fold_raw code raw (raw_meta width remaining outer_remaining) in
 let raw:=eval unfold raw_literal in (raw_literal width remaining outer_remaining) in
 let code:=fold_raw code raw (raw_literal width remaining outer_remaining) in
 let raw:=eval unfold raw_abstract in (raw_abstract width remaining outer_remaining) in
 let code:=fold_raw code raw (raw_abstract width remaining outer_remaining) in
 let raw:=eval unfold raw_binary in (raw_binary width remaining outer_remaining) in
 let code:=fold_raw code raw (raw_binary width remaining outer_remaining) in
 let raw:=eval unfold raw_all in (raw_all width remaining outer_remaining) in
 let code:=fold_raw code raw (raw_all width remaining outer_remaining) in
 let raw:=eval unfold raw_axiom in (raw_axiom width remaining outer_remaining) in
 let code:=fold_raw code raw (raw_axiom width remaining outer_remaining) in
 let raw:=eval unfold raw_output in (raw_output width remaining outer_remaining) in
 let code:=fold_raw code raw (raw_output width remaining outer_remaining) in exact code).
Lemma actual_compute width remaining outer_remaining : SchemaEvaluation.compute_body width remaining outer_remaining=compact_compute width remaining outer_remaining.
Proof. reflexivity. Qed.
Ltac straight_code := repeat first [apply straight_lift|apply straight_bind|solve [cbn [straight];tauto]|intro|
 match goal with |- straight (if ?test then _ else _)=>destruct test end].
Lemma meta_straight width remaining outer_remaining : straight (raw_meta width remaining outer_remaining).
Proof. unfold raw_meta. straight_code. Qed.
Lemma literal_straight width remaining outer_remaining : straight (raw_literal width remaining outer_remaining).
Proof. unfold raw_literal. straight_code. Qed.
Lemma abstract_straight width remaining outer_remaining : straight (raw_abstract width remaining outer_remaining).
Proof. unfold raw_abstract. straight_code. Qed.
Lemma binary_straight width remaining outer_remaining : straight (raw_binary width remaining outer_remaining).
Proof. unfold raw_binary. straight_code. Qed.
Lemma all_straight width remaining outer_remaining : straight (raw_all width remaining outer_remaining).
Proof. unfold raw_all. straight_code. Qed.
Lemma axiom_straight width remaining outer_remaining : straight (raw_axiom width remaining outer_remaining).
Proof. unfold raw_axiom. straight_code. Qed.

Inductive branch := meta | literal | abstraction | binary | universal | axiom.
Definition applies which kind := match which with
| meta=>kind=0 | literal=>kind=1 \/ kind=2 \/ kind=11 | abstraction=>kind=3
| binary=>kind=4 \/ kind=5 \/ kind=6 \/ kind=9 | universal=>kind=7 \/ kind=10 | axiom=>kind=8 end.
Definition selected which width remaining outer_remaining := match which with
| meta=>raw_meta width remaining outer_remaining
| literal=>raw_literal width remaining outer_remaining
| abstraction=>raw_abstract width remaining outer_remaining
| binary=>raw_binary width remaining outer_remaining
| universal=>raw_all width remaining outer_remaining
| axiom=>raw_axiom width remaining outer_remaining end.
Lemma selected_straight which width remaining outer_remaining : straight (selected which width remaining outer_remaining).
Proof. destruct which;cbn [selected];auto using meta_straight,literal_straight,abstract_straight,binary_straight,all_straight,axiom_straight. Qed.
Local Opaque raw_meta raw_literal raw_abstract raw_binary raw_all raw_axiom raw_output.
Theorem generated_dispatch which (f middle:Frame) width remaining outer_remaining kind observations :
 nums f vardef_0__schemaInstance_kind=kind -> nums middle vardef_0__schemaInstance_kind=kind -> applies which kind ->
 execLocalObserved (dropWithinLoop (selected which width remaining outer_remaining)) (f,observations)=Some (KeepGoing,(middle,observations)) ->
 execLocalObserved (dropWithinLoop (SchemaEvaluation.compute_body width remaining outer_remaining)) (f,observations)=
 execLocalObserved (dropWithinLoop (raw_output width remaining outer_remaining)) (middle,observations).
Proof.
 intros Hkind Hmiddle Happly Hrun.
 rewrite actual_compute. unfold compact_compute.
 destruct which;cbn [selected applies] in *;
 repeat match goal with H:_ \/ _ |- _=>destruct H end;
 subst kind;
 repeat first [progress cbn [optionBind fst snd bind]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |NativePrimitives.primitive ltac:(fun frame name slot=>lia)
 |progress rewrite Hkind|progress rewrite Hmiddle
 |match goal with |- context [bool_decide ?P]=>first
    [progress rewrite (bool_decide_true P) by intuition congruence
    |progress rewrite (bool_decide_false P) by intuition congruence] end
 |match goal with |- context [execLocalObserved (dropWithinLoop (?code >>= ?tail)) (?current,observations)]=>
    let Hstraight:=fresh in assert (Hstraight:straight code) by
      (first [apply meta_straight|apply literal_straight|apply abstract_straight|apply binary_straight|apply all_straight|apply axiom_straight]);
    let Hstep:=fresh in assert (Hstep:execLocalObserved (dropWithinLoop (code >>= tail)) (current,observations)=
      execLocalObserved (dropWithinLoop (tail tt)) (middle,observations)) by
      (apply (straight_drop_tail code (tail tt) current observations middle observations Hstraight Hrun));
    rewrite Hstep;clear Hstep Hstraight end].
 all: reflexivity.
Qed.

End SchemaPair.
