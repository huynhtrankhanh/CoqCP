From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal SchemaEvaluation SchemaPair SchemaPairStep SchemaPairSemantic
 SchemaClass ClassStorage Representation FormulaTopology RenameMemoControl.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationAbstractSemantic.
Import IndexExecution SipHashExecution ObservedLocal SchemaPair SchemaPairStep SchemaPairSemantic.
Theorem generated_abstract (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar stride depth key childKey id fs classes rho p reserve observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (3,Z.of_nat a,b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key ->
 childKey=(a*stride+depth+1)%nat -> Z.of_nat childKey<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) childKey=Some id ->
 (8<length (memory (machine f) arraydef_0__meta))%nat -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> ClassStorage.represents (machine f) fs classes ->
 meta_value (machine f) 8=0 -> FormulaTopology.ordered (machine f) (length fs) ->
 SchemaEvaluation.formula_value fs id (Schemata.instantiate_formula rho (S depth) p) ->
 Z.of_nat (length classes+S reserve)<=maximum ->
 exists final,
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=Some (KeepGoing,(final,observations)) /\
 post f final fs (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)]) rho depth (Protocol.CE (Schemata.template_abstract p)) key /\
 NativeRepresentation.canonical_arena (machine final) fs /\
 ClassStorage.represents (machine final) fs (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)]) /\
 meta_value (machine final) 8=0 /\ FormulaTopology.ordered (machine final) (length fs) /\
 Z.of_nat (length (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)])+reserve)<=maximum.
Proof.
 intros Hnode Hraw Hstride Hdepth Hkey Hchildkey Hchildword Hchild Hmeta Hbound Harena Hclasses Herror Htop Hmeaning Hbudget.
 set (parsed:=descriptor_frame f (3,Z.of_nat a,b,c,rawd,ty,ar)).
 set (built:=SchemaClass.result (machine f) (length classes) (1,id)).
 set (middle:=setMachine parsed built).
 assert (Hdecode:ClassStorage.decode fs (1,id)=Some (Schemata.instantiate_class rho depth (Schemata.template_abstract p))).
 { cbn [ClassStorage.decode Schemata.instantiate_class]. now rewrite (proj2 Hmeaning). }
 destruct (SchemaClass.generated_refines (machine f) (fun _=>false) (SchemaClass.arguments 1 id) fs classes 1 id
   (Schemata.instantiate_class rho depth (Schemata.template_abstract p)) reserve observations Hmeta Hclasses eq_refl eq_refl Hdecode Hbudget)
 as [Hhelper [Hnext [Hindex Hroom]]].
 assert (Hrun:execLocalObserved (dropWithinLoop (selected abstraction width remaining outer_remaining)) (parsed,observations)=Some (KeepGoing,(middle,observations))).
 { change (execLocalObserved (SchemaEvaluation.abstract_handler width remaining outer_remaining) (parsed,observations)=Some (KeepGoing,(middle,observations))).
   apply (SchemaEvaluation.generated_abstract_helper parsed width remaining outer_remaining a stride depth childKey id built observations
     (descriptor_a _ _ _ _ _ _ _ _) ltac:(unfold parsed;now rewrite descriptor_width) Hdepth Hchildkey Hchildword Hchild Hhelper). }
 assert (Hresult:SchemaEvaluation.meaning fs (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)]) rho depth
   (Protocol.CE (Schemata.template_abstract p)) (meta_value (machine middle) 0)).
 { change (SchemaEvaluation.class_value (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)]) (meta_value built 0)
     (Schemata.instantiate_class rho depth (Schemata.template_abstract p))).
   unfold SchemaEvaluation.class_value.
   change (meta_value built 0=Z.of_nat (length classes)) in Hindex. rewrite Hindex. split;[unfold word;lia|].
   rewrite Nat2Z.id,nth_error_app2 by lia. now rewrite Nat.sub_diag. }
 destruct (finish abstraction f middle width remaining outer_remaining node 3 (Z.of_nat a) b c rawd ty ar key fs
   (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)]) rho depth (Protocol.CE (Schemata.template_abstract p)) observations
   Hnode Hraw ltac:(unfold middle;cbn [nums setMachine];apply descriptor_kind) eq_refl Hrun ltac:(lia)
   ltac:(unfold middle;cbn [nums setMachine];unfold parsed;now rewrite descriptor_key) Hbound Hresult) as [Hexec Hpost].
 exists (output middle key). split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. split.
 - apply written_arena. now apply SchemaClass.result_arena.
 - split;[exact (written_classes _ _ _ _ _ Hnext)|]. split.
   + rewrite written_meta. unfold built. now rewrite SchemaClass.result_meta_other by lia.
   + split;[apply written_topology;now apply SchemaClass.result_topology|exact Hroom].
Qed.
End SchemaEvaluationAbstractSemantic.
