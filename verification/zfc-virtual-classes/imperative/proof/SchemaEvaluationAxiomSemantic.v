From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  SchemaEvaluation SchemaEvaluationControl AxiomTaggedInvariant AxiomInvariant AxiomCommand
  SchemaEvaluationAxiom AxiomStorage Representation FormulaTopology RenameMemoLengths.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationAxiomSemantic.
Import IndexExecution SipHashExecution ObservedLocal SchemaEvaluationControl SchemaEvaluationAxiom.
Theorem generated_semantic (f:SchemaEvaluation.Frame) width remaining outer_remaining tag rawI rawJ rawK stride d idA idB idC
 fs classes rho tp tq tr bound reserve observations :
 (tag<=17)%nat -> nums f vardef_0__schemaInstance_a=Z.of_nat tag ->
 nums f vardef_0__schemaInstance_b=Z.of_nat rawI -> nums f vardef_0__schemaInstance_c=Z.of_nat rawJ ->
 nums f vardef_0__schemaInstance_d=Z.of_nat rawK -> nums f vardef_0__schemaInstance_width=Z.of_nat stride ->
 SchemaEvaluation.depth width remaining=Z.of_nat d ->
 readable (machine f) stride d (AxiomTaggedInvariant.needs_p tag) rawI ->
 readable (machine f) stride d (AxiomTaggedInvariant.needs_q tag) rawJ ->
 readable (machine f) stride d (Nat.eqb tag 1) rawK ->
 selected_id (machine f) stride d (AxiomTaggedInvariant.needs_p tag) rawI=Z.of_nat idA ->
 selected_id (machine f) stride d (AxiomTaggedInvariant.needs_q tag) rawJ=Z.of_nat idB ->
 selected_id (machine f) stride d (Nat.eqb tag 1) rawK=Z.of_nat idC ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) -> meta_value (machine f) 8=0 ->
 nth_error fs 0=Some SetTheory.falsity -> word (Z.of_nat idA) -> word (Z.of_nat idB) -> word (Z.of_nat idC) ->
 AxiomTaggedInvariant.ready fs tag idA idB idC rawI rawJ rawK
   (Schemata.instantiate_formula rho d tp) (Schemata.instantiate_formula rho d tq) (Schemata.instantiate_formula rho d tr) ->
 AxiomTaggedInvariant.renaming_ready tag idA rawJ (Schemata.instantiate_formula rho d tp) bound ->
 Z.of_nat (length fs+AxiomTaggedInvariant.cost tag idA+reserve)<=9223372036854775807 ->
 exists final next,execLocalObserved (SchemaEvaluation.axiom_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine (native_frame f stride d tag rawI rawJ rawK) final,observations)) /\
 SchemaEvaluation.meaning next classes rho d (Protocol.PE (Schemata.template_ax (Schemata.template_axiom tag tp tq tr rawI rawJ rawK)))
   (meta_value final 0) /\
 NativeRepresentation.canonical_arena final next /\ FormulaTopology.ordered final (length next) /\
 (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ meta_value final 13=1 /\
 Z.of_nat (length next+reserve)<=9223372036854775807 /\
 (length next<=length fs+AxiomTaggedInvariant.cost tag idA)%nat /\
 AxiomStorage.logical_frame (machine f) final /\
 (forall watched,RenameMemoLengths.protected watched -> length (memory final watched)=length (memory (machine f) watched)).
Proof.
 intros Htag Ha Hb Hc Hd Hstride Hdepth HreadA HreadB HreadC HA HB HC Hmeta Hsip Harena Htop Herror Hfalse
   HwordA HwordB HwordC Hready Hrename Hbudget.
 destruct (AxiomTaggedInvariant.construct (machine f) fs tag idA idB idC rawI rawJ rawK
   (Schemata.instantiate_formula rho d tp) (Schemata.instantiate_formula rho d tq) (Schemata.instantiate_formula rho d tr)
   bound reserve observations Htag Hmeta Hsip Harena Htop Herror Hfalse HwordA HwordB HwordC Hready Hrename Hbudget)
 as (witness & Hwitness & final & next & index & Hrun & Hnext & Hindex & Hindexword & Hmeaning & Hderives & Hprefix & Hflag & Hsuccess & Hnexttop & Hroom & Hgrowth & Hframe & Hlengths).
 exists final,next. split.
 - eapply generated_helper;try eassumption.
   + rewrite Hlengths by (unfold RenameMemoLengths.protected;repeat split;discriminate). lia.
   + now rewrite HA,HB,HC.
 - split.
   + exists (SetTheory.axiom_formula witness). split.
     * cbn [Schemata.infer]. rewrite <-AxiomTaggedInvariant.literal_instantiated,Hwitness. reflexivity.
     * unfold SchemaEvaluation.formula_value. rewrite Hindex. split;[exact Hindexword|]. now rewrite Nat2Z.id.
   + exact (conj Hnext (conj Hnexttop (conj Hprefix (conj Hflag (conj Hsuccess (conj Hroom (conj Hgrowth (conj Hframe Hlengths)))))))).
Qed.
End SchemaEvaluationAxiomSemantic.
