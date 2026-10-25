From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import RenameStorage SchemaPairSemantic Index SipHash ObservedLocal SchemaEvaluation SchemaEvaluationControl SchemaPair SchemaPairStep
 SchemaShiftClass SchemaClass ArenaFrame SchemaEvaluationPreservation SchemaEvaluationMeta RenameMemoBounds RenameMemoIndexBounds RenameMemoTransition SchemaEvaluationBinaryMP SchemaEvaluationFrames SchemaEvaluationAxiom SchemaEvaluationAxiomSemantic AxiomTaggedInvariant AxiomStorage RenameMemoLengths Representation ClassStorage ClassLookup RenameMemoClassEqual RenameMemoClassMember RenameMemoResourceBounds ClassStorage FormulaTopology RenameMemoControl InternReserve FormulaEncoding FormulaCircuit Intern SemanticFrames HashTable.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationFamilyInvariant.
Import IndexExecution SipHashExecution ObservedLocal SchemaPair SchemaPairStep SchemaPairSemantic.
Theorem generated_equal (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar stride depth key ka kb ia ib fs classes rho ta tb reserve observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (4,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 ka=(a*stride+depth)%nat -> kb=(b*stride+depth)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some (Z.of_nat ia) ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some (Z.of_nat ib) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 nth_error fs 0=Some SetTheory.falsity -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error classes ia=Some (Schemata.instantiate_class rho depth ta) ->
 nth_error classes ib=Some (Schemata.instantiate_class rho depth tb) ->
 RenameMemoClassEqual.ready (machine f) fs ia ib (Schemata.instantiate_class rho depth ta) (Schemata.instantiate_class rho depth tb) ->
 Z.of_nat (length fs+RenameMemoClassEqual.work (machine f) ia ib
   (Schemata.instantiate_class rho depth ta) (Schemata.instantiate_class rho depth tb)+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 exists final next,execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\ post f final next classes rho depth (Protocol.FE (Schemata.template_equal ta tb)) key /\
 NativeRepresentation.canonical_arena (machine final) next /\ ClassStorage.represents (machine final) next classes /\
 FormulaTopology.ordered (machine final) (length next) /\ meta_value (machine final) 8=0 /\
 (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\
 ClassLookup.wellformed (machine final) /\ meta_value (machine final) 18=meta_value (machine f) 18.
Proof.
 intros Hnode Hraw Hstride Hdepth Hkey Hbound Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib Hready Hbudget.
 set (parsed:=descriptor_frame f (4,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar)).
 assert (Ha:nums parsed vardef_0__schemaInstance_a=Z.of_nat a) by apply descriptor_a.
 assert (Hb:nums parsed vardef_0__schemaInstance_b=Z.of_nat b).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 destruct (SchemaEvaluation.generated_binary_equal parsed width remaining outer_remaining a b stride depth ka kb ia ib fs classes rho ta tb reserve observations
   (descriptor_kind _ _ _ _ _ _ _ _) Ha Hb ltac:(unfold parsed;now rewrite descriptor_width) Hdepth Hka Hkb Hworda Hwordb Hlookupa Hlookupb
   Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib Hready Hbudget)
 as (built & next & Hrun & Hnext & Hmeaning & Hprefix & Hflag & Hframe & Hnextclasses & Hnextgood & Hroom & Hnexttop).
 set (middle:=setMachine (SchemaEvaluation.binary_frame parsed (Z.of_nat ia) (Z.of_nat ib)) built).
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations)) /\ post f (output middle key) next classes rho depth (Protocol.FE (Schemata.template_equal ta tb)) key).
 { eapply (finish binary);try eassumption.
   - unfold middle. exact (descriptor_kind f 4 (Z.of_nat a) (Z.of_nat b) c rawd ty ar).
   - unfold applies. intuition.
   - lia.
 }
 assert (Hwellformed:ClassLookup.wellformed built).
 { unfold ClassLookup.wellformed in *. rewrite (proj1 Hframe) by (unfold RenameStorage.Arrays.persistent_array;repeat split;discriminate). exact Hgood. }
 assert (Hvalid:meta_value built 18=meta_value (machine f) 18).
 { apply (proj1 (proj2 Hframe));unfold RenameStorage.Cells.protected;repeat split;discriminate. }
 exists (output middle key),next. destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. split;[now apply written_arena|]. split;[now apply written_classes|].
 split;[now apply written_topology|]. split;[now rewrite written_meta|]. split;[exact Hprefix|]. split;[exact Hroom|]. split.
 - unfold ClassLookup.wellformed. now rewrite written_other by discriminate.
 - now rewrite written_meta.
Qed.
Theorem generated_member (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar stride depth key ka kb ia ib fs classes rho ta tb reserve observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (5,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 ka=(a*stride+depth)%nat -> kb=(b*stride+depth)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some (Z.of_nat ia) ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some (Z.of_nat ib) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 nth_error fs 0=Some SetTheory.falsity -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error classes ia=Some (Schemata.instantiate_class rho depth ta) ->
 nth_error classes ib=Some (Schemata.instantiate_class rho depth tb) ->
 RenameMemoClassMember.ready (machine f) fs ia ib (Schemata.instantiate_class rho depth ta) (Schemata.instantiate_class rho depth tb) ->
 Z.of_nat (length fs+RenameMemoClassMember.work (machine f) ia ib
   (Schemata.instantiate_class rho depth ta) (Schemata.instantiate_class rho depth tb)+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 exists final next,execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\ post f final next classes rho depth (Protocol.FE (Schemata.template_member ta tb)) key /\
 NativeRepresentation.canonical_arena (machine final) next /\ ClassStorage.represents (machine final) next classes /\
 FormulaTopology.ordered (machine final) (length next) /\ meta_value (machine final) 8=0 /\
 (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\
 ClassLookup.wellformed (machine final) /\ meta_value (machine final) 18=meta_value (machine f) 18.
Proof.
 intros Hnode Hraw Hstride Hdepth Hkey Hbound Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib Hready Hbudget.
 set (parsed:=descriptor_frame f (5,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar)).
 assert (Ha:nums parsed vardef_0__schemaInstance_a=Z.of_nat a) by apply descriptor_a.
 assert (Hb:nums parsed vardef_0__schemaInstance_b=Z.of_nat b).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 destruct (SchemaEvaluation.generated_binary_member parsed width remaining outer_remaining a b stride depth ka kb ia ib fs classes rho ta tb reserve observations
   (descriptor_kind _ _ _ _ _ _ _ _) Ha Hb ltac:(unfold parsed;now rewrite descriptor_width) Hdepth Hka Hkb Hworda Hwordb Hlookupa Hlookupb
   Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib Hready Hbudget)
 as (built & next & Hrun & Hnext & Hmeaning & Hprefix & Hflag & Hframe & Hnextclasses & Hnextgood & Hroom & Hnexttop).
 set (middle:=setMachine (SchemaEvaluation.binary_frame parsed (Z.of_nat ia) (Z.of_nat ib)) built).
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations)) /\ post f (output middle key) next classes rho depth (Protocol.FE (Schemata.template_member ta tb)) key).
 { eapply (finish binary);try eassumption.
   - unfold middle. exact (descriptor_kind f 5 (Z.of_nat a) (Z.of_nat b) c rawd ty ar).
   - unfold applies. intuition.
   - lia.
 }
 assert (Hwellformed:ClassLookup.wellformed built).
 { unfold ClassLookup.wellformed in *. rewrite (proj1 Hframe) by (unfold RenameStorage.Arrays.persistent_array;repeat split;discriminate). exact Hgood. }
 assert (Hvalid:meta_value built 18=meta_value (machine f) 18).
 { apply (proj1 (proj2 Hframe));unfold RenameStorage.Cells.protected;repeat split;discriminate. }
 exists (output middle key),next. destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. split;[now apply written_arena|]. split;[now apply written_classes|].
 split;[now apply written_topology|]. split;[now rewrite written_meta|]. split;[exact Hprefix|]. split;[exact Hroom|]. split.
 - unfold ClassLookup.wellformed. now rewrite written_other by discriminate.
 - now rewrite written_meta.
Qed.
Theorem generated_imp (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar stride depth key ka kb va vb fs classes rho p q reserve observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (6,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 ka=(a*stride+depth)%nat -> kb=(b*stride+depth)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some va ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some vb ->
 (0<length (memory (machine f) arraydef_0__meta))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 meta_value (machine f) 8=0 -> ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 SchemaEvaluation.formula_value fs va (Schemata.instantiate_formula rho depth p) ->
 SchemaEvaluation.formula_value fs vb (Schemata.instantiate_formula rho depth q) ->
 Z.of_nat (length fs+S reserve)<=9223372036854775807 ->
 exists final next,execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\ post f final next classes rho depth (Protocol.FE (Schemata.template_imp p q)) key /\
 NativeRepresentation.canonical_arena (machine final) next /\ ClassStorage.represents (machine final) next classes /\
 FormulaTopology.ordered (machine final) (length next) /\ meta_value (machine final) 8=0 /\
 (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
 ClassLookup.wellformed (machine final) /\ meta_value (machine final) 18=meta_value (machine f) 18.
Proof.
 intros Hnode Hraw Hstride Hdepth Hkey Hbound Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Harena Htop Herror Hclasses Hgood [Hleft Hpleft] [Hright Hpright] Hbudget.
 set (parsed:=descriptor_frame f (6,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar)).
 assert (Ha:nums parsed vardef_0__schemaInstance_a=Z.of_nat a) by apply descriptor_a.
 assert (Hb:nums parsed vardef_0__schemaInstance_b=Z.of_nat b).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 assert (Hnormal:FormulaEncoding.normal (3,va,vb)) by (right;left;auto).
 assert (Hdecode:FormulaEncoding.decode fs (3,va,vb)=Some (SetTheory.implies (Schemata.instantiate_formula rho depth p) (Schemata.instantiate_formula rho depth q))).
 { cbn [FormulaEncoding.decode]. now rewrite Hpleft,Hpright. }
 destruct (InternReserve.generated_refines (machine f) (fun _=>false) (FormulaCircuit.arguments 3 va vb) fs _ reserve observations Harena Herror Hbudget Hnormal Hdecode)
 as (built & next & index & Hnative & Hframe & Hnext & Hflag & Hindex & Hindexword & Hresult & Hprefix & Hroom).
 assert (Hrun:execLocalObserved (SchemaEvaluation.binary_handler width remaining outer_remaining) (parsed,observations)=
   Some (KeepGoing,(setMachine (SchemaEvaluation.binary_frame parsed va vb) built,observations))).
 { eapply SchemaEvaluation.generated_binary_imp_helper;try eassumption;first [apply descriptor_kind|unfold parsed;now rewrite descriptor_width]. }
 set (middle:=setMachine (SchemaEvaluation.binary_frame parsed va vb) built).
 assert (Hmeaning:SchemaEvaluation.meaning next classes rho depth (Protocol.FE (Schemata.template_imp p q)) (meta_value (machine middle) 0)).
 { change (SchemaEvaluation.formula_value next (meta_value built 0) (SetTheory.implies (Schemata.instantiate_formula rho depth p) (Schemata.instantiate_formula rho depth q))).
   rewrite Hindex. split;[exact Hindexword|]. now rewrite Nat2Z.id. }
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations)) /\ post f (output middle key) next classes rho depth (Protocol.FE (Schemata.template_imp p q)) key).
 { eapply (finish binary);try eassumption.
   - unfold middle. exact (descriptor_kind f 6 (Z.of_nat a) (Z.of_nat b) c rawd ty ar).
   - unfold applies. intuition.
 }
 assert (Hnextclasses:ClassStorage.represents built next classes).
 { destruct Hprefix as [extra Hprefix]. rewrite Hprefix. destruct Hframe as [Harrays [Hcells Hio]].
   eapply SemanticFrames.classes_extend;[apply Hcells;lia|apply Harrays;discriminate|exact Hclasses]. }
 assert (Hnexttop:FormulaTopology.ordered built (length next)).
 { destruct (FormulaTopology.generated_intern_preserves (machine f) (fun _=>false) (FormulaCircuit.arguments 3 va vb) fs _ Harena Htop Herror ltac:(lia) Hdecode)
   as (other & Hplain & Hotherflag & Hothertop).
   pose proof (f_equal (fun run=>option_map (fun response=>(fst response,fst (snd response))) run) Hnative) as Herase.
   rewrite execObserved_erases in Herase. cbn [option_map fst snd] in Herase. rewrite Herase in Hplain. injection Hplain as <-.
   destruct Hnext as [[Hready [Hcount Hrest]] Hnextmeaning]. now rewrite Hcount,Nat2Z.id in Hothertop. }
 assert (Hwellformed:ClassLookup.wellformed built).
 { unfold ClassLookup.wellformed in *. rewrite (proj1 Hframe) by discriminate. exact Hgood. }
 assert (Hvalid:meta_value built 18=meta_value (machine f) 18).
 { apply (proj1 (proj2 Hframe));lia. }
 exists (output middle key),next. destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. split;[now apply written_arena|]. split;[now apply written_classes|].
 split;[now apply written_topology|]. split;[now rewrite written_meta|]. split;[exact Hprefix|]. split;[exact Hroom|]. split.
 - unfold ClassLookup.wellformed. now rewrite written_other by discriminate.
 - now rewrite written_meta.
Qed.
Theorem generated_axiom (f:SchemaEvaluation.Frame) width remaining outer_remaining node ty ar key tag rawI rawJ rawK stride d idA idB idC
 fs classes rho tp tq tr bound reserve observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (8,Z.of_nat tag,Z.of_nat rawI,Z.of_nat rawJ,Z.of_nat rawK,ty,ar) ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 (tag<=17)%nat -> nums f vardef_0__schemaInstance_width=Z.of_nat stride ->
 SchemaEvaluation.depth width remaining=Z.of_nat d ->
 SchemaEvaluationAxiom.readable (machine f) stride d (AxiomTaggedInvariant.needs_p tag) rawI ->
 SchemaEvaluationAxiom.readable (machine f) stride d (AxiomTaggedInvariant.needs_q tag) rawJ ->
 SchemaEvaluationAxiom.readable (machine f) stride d (Nat.eqb tag 1) rawK ->
 SchemaEvaluationAxiom.selected_id (machine f) stride d (AxiomTaggedInvariant.needs_p tag) rawI=Z.of_nat idA ->
 SchemaEvaluationAxiom.selected_id (machine f) stride d (AxiomTaggedInvariant.needs_q tag) rawJ=Z.of_nat idB ->
 SchemaEvaluationAxiom.selected_id (machine f) stride d (Nat.eqb tag 1) rawK=Z.of_nat idC ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) -> meta_value (machine f) 8=0 ->
 nth_error fs 0=Some SetTheory.falsity -> word (Z.of_nat idA) -> word (Z.of_nat idB) -> word (Z.of_nat idC) ->
 AxiomTaggedInvariant.ready fs tag idA idB idC rawI rawJ rawK
   (Schemata.instantiate_formula rho d tp) (Schemata.instantiate_formula rho d tq) (Schemata.instantiate_formula rho d tr) ->
 AxiomTaggedInvariant.renaming_ready tag idA rawJ (Schemata.instantiate_formula rho d tp) bound ->
 Z.of_nat (length fs+AxiomTaggedInvariant.cost tag idA+reserve)<=9223372036854775807 ->
 exists final next,execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\
 post f final next classes rho d (Protocol.PE (Schemata.template_ax (Schemata.template_axiom tag tp tq tr rawI rawJ rawK))) key /\
 NativeRepresentation.canonical_arena (machine final) next /\ FormulaTopology.ordered (machine final) (length next) /\
 ClassStorage.represents (machine final) next classes /\
 (exists extra,next=fs++extra) /\ meta_value (machine final) 8=0 /\ meta_value (machine final) 13=1 /\
 Z.of_nat (length next+reserve)<=9223372036854775807 /\ (length next<=length fs+AxiomTaggedInvariant.cost tag idA)%nat /\
 ClassLookup.wellformed (machine final) /\ meta_value (machine final) 18=meta_value (machine f) 18.
Proof.
 intros Hnode Hraw Hkey Hbound Hclasses Hgood Htag Hstride Hdepth HreadA HreadB HreadC HA HB HC Hmeta Hsip Harena Htop Herror Hfalse
   HwordA HwordB HwordC Hready Hrename Hbudget.
 set (parsed:=descriptor_frame f (8,Z.of_nat tag,Z.of_nat rawI,Z.of_nat rawJ,Z.of_nat rawK,ty,ar)).
 assert (Ha:nums parsed vardef_0__schemaInstance_a=Z.of_nat tag) by apply descriptor_a.
 assert (Hb:nums parsed vardef_0__schemaInstance_b=Z.of_nat rawI).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 assert (Hc:nums parsed vardef_0__schemaInstance_c=Z.of_nat rawJ).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 assert (Hd:nums parsed vardef_0__schemaInstance_d=Z.of_nat rawK).
 { unfold parsed. cbn [descriptor_frame nums setNum]. apply RenameMemoControl.updated_same. }
 destruct (SchemaEvaluationAxiomSemantic.generated_semantic parsed width remaining outer_remaining tag rawI rawJ rawK stride d idA idB idC
   fs classes rho tp tq tr bound reserve observations Htag Ha Hb Hc Hd ltac:(unfold parsed;now rewrite descriptor_width) Hdepth
   HreadA HreadB HreadC HA HB HC Hmeta Hsip Harena Htop Herror Hfalse HwordA HwordB HwordC Hready Hrename Hbudget)
 as (built & next & Hrun & Hmeaning & Hnext & Hnexttop & Hprefix & Hflag & Hsuccess & Hroom & Hgrowth & Hframe & Hlengths).
 set (middle:=setMachine (SchemaEvaluationAxiom.native_frame parsed stride d tag rawI rawJ rawK) built).
 assert (Hkind:nums middle vardef_0__schemaInstance_kind=8).
 { unfold middle,SchemaEvaluationAxiom.native_frame,SchemaEvaluationAxiom.arguments_frame.
   repeat match goal with |- context [if ?test then _ else _]=>destruct test end;exact (descriptor_kind f 8 (Z.of_nat tag) (Z.of_nat rawI) (Z.of_nat rawJ) (Z.of_nat rawK) ty ar). }
 assert (Hmiddlekey:nums middle vardef_0__schemaInstance_key=Z.of_nat key).
 { unfold middle,SchemaEvaluationAxiom.native_frame,SchemaEvaluationAxiom.arguments_frame.
   repeat match goal with |- context [if ?test then _ else _]=>destruct test end;exact Hkey. }
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations)) /\
   post f (output middle key) next classes rho d (Protocol.PE (Schemata.template_ax (Schemata.template_axiom tag tp tq tr rawI rawJ rawK))) key).
 { eapply (finish axiom);try eassumption;first [reflexivity|lia]. }
 assert (Hwellformed:ClassLookup.wellformed built).
 { unfold ClassLookup.wellformed in *. rewrite (proj1 Hframe) by (unfold RenameStorage.Arrays.persistent_array;repeat split;discriminate). exact Hgood. }
 assert (Hvalid:meta_value built 18=meta_value (machine f) 18).
 { apply (proj1 (proj2 Hframe));unfold RenameStorage.Cells.protected;repeat split;discriminate. }
 exists (output middle key),next. destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 assert (Hnextclasses:ClassStorage.represents built next classes).
 { destruct Hprefix as [extra Hprefix]. rewrite Hprefix. eapply AxiomStorage.classes_transport;[exact Hframe|exact Hclasses]. }
 unfold output,middle. cbn [machine setMachine]. split;[now apply written_arena|]. split;[now apply written_topology|].
 split;[now apply written_classes|]. split;[exact Hprefix|]. split;[now rewrite written_meta|]. split;[now rewrite written_meta|]. split;[exact Hroom|]. split;[exact Hgrowth|]. split.
 - unfold ClassLookup.wellformed. now rewrite written_other by discriminate.
 - now rewrite written_meta.
Qed.
Theorem generated_mp (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar stride depth key ka kb implication vb fs classes rho ci ca observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (9,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 ka=(a*stride+depth)%nat -> kb=(b*stride+depth)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some (Z.of_nat implication) ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some vb ->
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 meta_value (machine f) 8=0 -> ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 SchemaEvaluation.meaning fs classes rho depth (Protocol.PE ci) (Z.of_nat implication) ->
 SchemaEvaluation.meaning fs classes rho depth (Protocol.PE ca) vb ->
 exists final,execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\
 NativeRepresentation.canonical_arena (machine final) fs /\ ClassStorage.represents (machine final) fs classes /\
 FormulaTopology.ordered (machine final) (length fs) /\ meta_value (machine final) 8=0 /\
 (forall index,index<>key -> SchemaEvaluation.value (machine final) index=SchemaEvaluation.value (machine f) index) /\
 (forall watched,length (memory (machine final) watched)=length (memory (machine f) watched)) /\
 match Schemata.infer rho depth (Schemata.template_mp ci ca) with
 | Some result=>post f final fs classes rho depth (Protocol.PE (Schemata.template_mp ci ca)) key /\
    meta_value (machine final) 18=meta_value (machine f) 18
 | None=>meta_value (machine final) 18=0
 end /\ ClassLookup.wellformed (machine final).
Proof.
 intros Hnode Hraw Hstride Hdepth Hkey Hbound Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Harena Htop Herror Hclasses Hgood Hci Hca.
 set (parsed:=descriptor_frame f (9,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar)).
 assert (Ha:nums parsed vardef_0__schemaInstance_a=Z.of_nat a) by apply descriptor_a.
 assert (Hb:nums parsed vardef_0__schemaInstance_b=Z.of_nat b).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 destruct (SchemaEvaluationBinaryMP.generated_binary_mp parsed width remaining outer_remaining a b stride depth ka kb implication vb fs classes rho ci ca observations
   (descriptor_kind _ _ _ _ _ _ _ _) Ha Hb ltac:(unfold parsed;now rewrite descriptor_width) Hdepth Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Harena Hci Hca)
 as (raw & Hrun & Hmeaning).
 set (middle:=setMachine (SchemaEvaluation.binary_frame parsed (Z.of_nat implication) vb)
   (SchemaEvaluation.mp_result (machine f) raw vb)).
 assert (Hmarked:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations))).
 { unfold output. eapply (generated_marked binary);try eassumption.
   - unfold middle. exact (descriptor_kind f 9 (Z.of_nat a) (Z.of_nat b) c rawd ty ar).
   - unfold applies. intuition.
   - unfold middle. cbn [machine setMachine]. rewrite SchemaEvaluationBinaryMP.mp_lengths. lia.
   - unfold middle. cbn [machine setMachine]. now rewrite SchemaEvaluationBinaryMP.mp_arrays by discriminate.
 }
 assert (Hvalues:forall index,index<>key -> SchemaEvaluation.value (machine (output middle key)) index=SchemaEvaluation.value (machine f) index).
 { intros index Hindex. unfold output,middle. cbn [machine setMachine]. rewrite written_preserves by exact Hindex.
   unfold SchemaEvaluation.value. now rewrite SchemaEvaluationBinaryMP.mp_arrays by discriminate. }
 assert (Hlengths:forall watched,length (memory (machine (output middle key)) watched)=length (memory (machine f) watched)).
 { intro watched. unfold output,middle. cbn [machine setMachine]. rewrite written_all_lengths. apply SchemaEvaluationBinaryMP.mp_lengths. }
 exists (output middle key). split;[exact Hmarked|].
 split;[unfold output,middle;cbn [machine setMachine];apply written_arena;now apply SchemaEvaluationBinaryMP.mp_arena|].
 split;[unfold output,middle;cbn [machine setMachine];apply written_classes;now apply SchemaEvaluationBinaryMP.mp_classes|].
 split;[unfold output,middle;cbn [machine setMachine];apply written_topology;now apply SchemaEvaluationBinaryMP.mp_topology|].
 split;[unfold output,middle;cbn [machine setMachine];rewrite written_meta,SchemaEvaluationBinaryMP.mp_cell by discriminate;exact Herror|].
 split;[exact Hvalues|]. split;[exact Hlengths|].
 assert (Hnextgood:ClassLookup.wellformed (machine (output middle key))).
 { unfold output,middle,ClassLookup.wellformed. cbn [machine setMachine].
   rewrite written_other,SchemaEvaluationBinaryMP.mp_arrays by discriminate. exact Hgood. }
 split;[|exact Hnextgood].
 destruct (Schemata.infer rho depth (Schemata.template_mp ci ca)) as [result|] eqn:Hinfer.
 - destruct Hmeaning as [Hmeaning Hvalid]. split.
   + unfold post. split.
     * exists result. split;[exact Hinfer|]. unfold output,middle. cbn [machine setMachine]. rewrite written_same.
       -- exact Hmeaning.
       -- now rewrite SchemaEvaluationBinaryMP.mp_arrays by discriminate.
     * split;[exact Hvalues|]. intros watched Hprotected. apply Hlengths.
   + unfold output,middle. cbn [machine setMachine]. now rewrite written_meta.
 - unfold output,middle. cbn [machine setMachine]. now rewrite written_meta.
Qed.

End SchemaEvaluationFamilyInvariant.
