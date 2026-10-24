From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  SchemaEvaluation SchemaEvaluationControl AxiomTaggedInvariant AxiomInvariant AxiomCommand
  AxiomStorage Representation FormulaTopology RenameMemoLengths.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationAxiom.
Import IndexExecution SipHashExecution ObservedLocal SchemaEvaluationControl.
Definition selected_id (s:Machine) stride d (needed:bool) raw :=
 if needed then SchemaEvaluation.value s (raw*stride+d)%nat else Z.of_nat raw.
Definition arguments_frame (f:SchemaEvaluation.Frame) ia ib ic :=
 setNum (setNum (setNum f vardef_0__schemaInstance_va ia) vardef_0__schemaInstance_vb ib) vardef_0__schemaInstance_vc ic.
Definition native_frame (f:SchemaEvaluation.Frame) stride d tag rawI rawJ rawK :=
 let start:=arguments_frame f (Z.of_nat rawI) (Z.of_nat rawJ) (Z.of_nat rawK) in
 let readyA:=if AxiomTaggedInvariant.needs_p tag then setNum start vardef_0__schemaInstance_va
   (selected_id (machine f) stride d true rawI) else start in
 let readyB:=if AxiomTaggedInvariant.needs_q tag then setNum readyA vardef_0__schemaInstance_vb
   (selected_id (machine f) stride d true rawJ) else readyA in
 if Nat.eqb tag 1 then setNum readyB vardef_0__schemaInstance_vc (selected_id (machine f) stride d true rawK) else readyB.
Definition readable (s:Machine) stride d needed raw :=
 needed=true -> Z.of_nat (raw*stride+d)<=maximum /\
 (raw*stride+d<length (memory s arraydef_0__schemaValues))%nat.
Local Opaque funcdef_0__axiom Imperative.update.
Theorem generated_helper (f:SchemaEvaluation.Frame) width remaining outer_remaining tag rawI rawJ rawK stride d final observations :
 (tag<=17)%nat -> nums f vardef_0__schemaInstance_a=Z.of_nat tag ->
 nums f vardef_0__schemaInstance_b=Z.of_nat rawI -> nums f vardef_0__schemaInstance_c=Z.of_nat rawJ ->
 nums f vardef_0__schemaInstance_d=Z.of_nat rawK -> nums f vardef_0__schemaInstance_width=Z.of_nat stride ->
 SchemaEvaluation.depth width remaining=Z.of_nat d ->
 readable (machine f) stride d (AxiomTaggedInvariant.needs_p tag) rawI ->
 readable (machine f) stride d (AxiomTaggedInvariant.needs_q tag) rawJ ->
 readable (machine f) stride d (Nat.eqb tag 1) rawK ->
 (13<length (memory final arraydef_0__meta))%nat -> meta_value final 13=1 ->
 execObserved (funcdef_0__axiom (fun _=>false) (AxiomCommand.arguments (Z.of_nat tag)
   (selected_id (machine f) stride d (AxiomTaggedInvariant.needs_p tag) rawI)
   (selected_id (machine f) stride d (AxiomTaggedInvariant.needs_q tag) rawJ)
   (selected_id (machine f) stride d (Nat.eqb tag 1) rawK))) (machine f,observations)=Some (tt,(final,observations)) ->
 execLocalObserved (SchemaEvaluation.axiom_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine (native_frame f stride d tag rawI rawJ rawK) final,observations)).
Proof.
 intros Htag Ha Hb Hc Hd Hstride Hdepth HreadA HreadB HreadC Hmeta Hsuccess Hrun.
 let rec cases count index := lazymatch count with O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 18%nat tag.
 19:lia.
 all: unfold native_frame.
 all: cbn [AxiomTaggedInvariant.needs_p AxiomTaggedInvariant.needs_q existsb Nat.eqb orb selected_id] in *.
 all: unfold readable in HreadA,HreadB,HreadC;try specialize (HreadA eq_refl);try specialize (HreadB eq_refl);try specialize (HreadC eq_refl).
 all: repeat match goal with H:_ /\ _ |- _=>destruct H end.
 all: try (assert (HmulA:coerceInt (Z.of_nat rawI*Z.of_nat stride) 64=Z.of_nat (rawI*stride)) by
   (rewrite <-Nat2Z.inj_mul;apply coerce_word;unfold word;lia)).
 all: try (assert (HmulB:coerceInt (Z.of_nat rawJ*Z.of_nat stride) 64=Z.of_nat (rawJ*stride)) by
   (rewrite <-Nat2Z.inj_mul;apply coerce_word;unfold word;lia)).
 all: try (assert (HmulC:coerceInt (Z.of_nat rawK*Z.of_nat stride) 64=Z.of_nat (rawK*stride)) by
   (rewrite <-Nat2Z.inj_mul;apply coerce_word;unfold word;lia)).
 all: try (assert (HaddA:coerceInt (Z.of_nat (rawI*stride)+(width-Z.of_nat remaining-1)) 64=Z.of_nat (rawI*stride+d)) by
   (change (coerceInt (Z.of_nat (rawI*stride)+SchemaEvaluation.depth width remaining) 64=Z.of_nat (rawI*stride+d));rewrite Hdepth,coerce_word by (unfold word;lia);lia)).
 all: try (assert (HaddB:coerceInt (Z.of_nat (rawJ*stride)+(width-Z.of_nat remaining-1)) 64=Z.of_nat (rawJ*stride+d)) by
   (change (coerceInt (Z.of_nat (rawJ*stride)+SchemaEvaluation.depth width remaining) 64=Z.of_nat (rawJ*stride+d));rewrite Hdepth,coerce_word by (unfold word;lia);lia)).
 all: try (assert (HaddC:coerceInt (Z.of_nat (rawK*stride)+(width-Z.of_nat remaining-1)) 64=Z.of_nat (rawK*stride+d)) by
   (change (coerceInt (Z.of_nat (rawK*stride)+SchemaEvaluation.depth width remaining) 64=Z.of_nat (rawK*stride+d));rewrite Hdepth,coerce_word by (unfold word;lia);lia)).
 all: destruct f as [s bs ns];cbn [machine nums] in *.
 all: unfold SchemaEvaluation.axiom_handler,arguments_frame.
 all: repeat first [progress cbn [optionBind fst snd bind]
 |progress rewrite drop_assoc|progress rewrite drop_lift|progress rewrite drop_lift_final
 |progress unfold addInt at 1|progress unfold multInt at 1
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];rewrite ?Nat2Z.id;first [exact Hmeta|assumption])
 |progress rewrite Ha|progress rewrite Hb|progress rewrite Hc|progress rewrite Hd|progress rewrite Hstride
 |progress rewrite HmulA|progress rewrite HmulB|progress rewrite HmulC
 |progress rewrite HaddA|progress rewrite HaddB|progress rewrite HaddC|progress rewrite Nat2Z.id
 |progress rewrite RenameMemoControl.updated_same
 |progress rewrite RenameMemoControl.updated_other by discriminate
 |progress replace (Z.to_nat 13) with 13%nat by reflexivity
 |progress rewrite Hsuccess
 |match goal with |- context [bool_decide ?P]=>first
   [progress rewrite (bool_decide_true P) by lia|progress rewrite (bool_decide_false P) by lia] end
 |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__axiom ?bi ?ni) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__axiom bi ni) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(final,observations))) by exact Hrun;rewrite Hsame;clear Hsame end
 |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
 ].
 all: reflexivity.
Qed.
End SchemaEvaluationAxiom.
