From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal SchemaEvaluation SchemaEvaluationDependencies SchemaEvaluationResources
 SchemaEvaluationInvariant SchemaPair SchemaPairStep SchemaPairSemantic SchemaEvaluationAbstractSemantic SchemaGraph SchemaRepresentation SchemaMetadata
 Representation ClassStorage ClassLookup FormulaTopology ArenaFrame RenameMemoControl RenameMemoLengths HashTable AxiomTaggedInvariant InternInvariant SchemaEvaluationMetaInvariant SchemaEvaluationFamilyInvariant SchemaEvaluationPreservation SchemaEvaluationCell RenameMemoBounds RenameMemoIndexBounds RenameMemoTransition RenameMemoClassEqual RenameMemoClassMember RenameMemoResourceBounds.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationBoundedCell.
Import IndexExecution SipHashExecution ObservedLocal SchemaEvaluationDependencies SchemaEvaluationCell.
Definition bound : Z := 9223372036854775807.
Definition shifted (native:Machine) fs classes rho depth a reserve :=
  SchemaEvaluationResources.argument native classes rho a /\
  (depth<>0%nat -> SchemaEvaluationResources.class_room classes /\
    (forall variable,rho a=VirtualClasses.set variable -> Z.of_nat variable+Z.of_nat depth<=maximum) /\
    (forall cls root p,nth_error (memory native arraydef_0__classes) cls=Some (1,Z.of_nat root) ->
      nth_error fs root=Some p ->
      exists bound,
        Z.of_nat (RenameMemoBounds.fuel root)<=maximum /\ RenameMemoIndexBounds.formula_bound bound p /\
        Z.of_nat bound+Z.of_nat depth<=maximum /\ Z.of_nat (S (RenameMemoTransition.height p))<=maximum /\
        Z.of_nat (length fs+S root*S root+reserve)<=9223372036854775807)).
Definition equal (native:Machine) fs classes reserve := forall ia ib ca cb,
  nth_error classes ia=Some ca -> nth_error classes ib=Some cb ->
  RenameMemoClassEqual.ready native fs ia ib ca cb /\
  Z.of_nat (length fs+RenameMemoClassEqual.work native ia ib ca cb+reserve)<=RenameMemoResourceBounds.doubling_limit.
Definition member (native:Machine) fs classes reserve := forall ia ib ca cb,
  nth_error classes ia=Some ca -> nth_error classes ib=Some cb ->
  RenameMemoClassMember.ready native fs ia ib ca cb /\
  Z.of_nat (length fs+RenameMemoClassMember.work native ia ib ca cb+reserve)<=RenameMemoResourceBounds.doubling_limit.
Definition axiom fs tag rawJ reserve := forall idA p,
  word (Z.of_nat idA) -> (AxiomTaggedInvariant.needs_p tag=true -> nth_error fs idA=Some p) ->
  exists bound,AxiomTaggedInvariant.renaming_ready tag idA rawJ p bound /\
    Z.of_nat (length fs+AxiomTaggedInvariant.cost tag idA+reserve)<=9223372036854775807.
(** Explicit sufficient mathematical resources for a single native cell. Only
    its instruction family requests a budget; no operational run is assumed. *)
Definition ready (native:Machine) fs classes rho depth (k a b c d:nat) reserve : Prop :=
  Z.of_nat (length fs+reserve)<=bound /\
  match k with
  | 0%nat=>shifted native fs classes rho depth a reserve
  | 3%nat=>SchemaEvaluationResources.class_room classes
  | 4%nat=>equal native fs classes reserve
  | 5%nat=>member native fs classes reserve
  | 6%nat | 7%nat | 10%nat=>Z.of_nat (length fs+S reserve)<=bound
  | 8%nat=>axiom fs a c reserve
  | _=>True end.

Definition core (f:SchemaEvaluation.Frame) width remaining outer_remaining fs classes rho depth expression key reserve observations :=
  exists final next_fs next_classes,
    execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
      Some (KeepGoing,(final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) next_fs /\ meta_value (machine final) 8=0 /\
    prefix fs next_fs /\ prefix classes next_classes /\
    ClassStorage.represents (machine final) next_fs next_classes /\
    FormulaTopology.ordered (machine final) (length next_fs) /\ ClassLookup.wellformed (machine final) /\
    (length next_classes<=S (length classes))%nat /\ word (Z.of_nat (length next_fs)) /\
    Z.of_nat (length next_fs+reserve)<=bound /\
    semantic_result f final next_fs next_classes rho depth expression key.
Lemma core_success (f final:SchemaEvaluation.Frame) width remaining outer_remaining fs classes next_fs next_classes rho depth expression key reserve observations :
  execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
    Some (KeepGoing,(final,observations)) ->
  NativeRepresentation.canonical_arena (machine final) next_fs -> meta_value (machine final) 8=0 ->
  prefix fs next_fs -> prefix classes next_classes ->
  ClassStorage.represents (machine final) next_fs next_classes ->
  FormulaTopology.ordered (machine final) (length next_fs) -> ClassLookup.wellformed (machine final) ->
  (length next_classes<=S (length classes))%nat ->
  SchemaPairSemantic.post f final next_fs next_classes rho depth expression key ->
  meta_value (machine final) 18=meta_value (machine f) 18 ->
  Z.of_nat (length next_fs+reserve)<=bound ->
  core f width remaining outer_remaining fs classes rho depth expression key reserve observations.
Proof.
  intros Hrun Harena Herror Hfs Hclasses Hclassrep Htop Hgood Hgrowth Hpost Hvalid Hreserve.
  exists final,next_fs,next_classes.
  split;[exact Hrun|]. split;[exact Harena|]. split;[exact Herror|].
  split;[exact Hfs|]. split;[exact Hclasses|]. split;[exact Hclassrep|].
  split;[exact Htop|]. split;[exact Hgood|]. split;[exact Hgrowth|].
  split;[exact (arena_count_word _ _ Harena)|]. split;[exact Hreserve|]. left. split;assumption.
Qed.
Theorem generated_view source (f:SchemaEvaluation.Frame) root fs classes expressions rho node depth kind a b c d expression
 width remaining outer_remaining reserve observations :
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 SchemaGraph.reachable source root node depth ->
 view fs classes expressions kind a b c d expression ->
 SchemaRepresentation.fields_fit kind a b c d expression ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode kind a b c d expression) ->
 nth_error (memory source arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode kind a b c d expression) ->
 SchemaEvaluationInvariant.completed source root expressions rho fs classes (machine f) (SchemaGraph.key root node depth) ->
 Z.of_nat (SchemaGraph.width root*SchemaGraph.width root)<=maximum ->
 (SchemaGraph.width root*SchemaGraph.width root<=length (memory (machine f) arraydef_0__schemaValues))%nat ->
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
 nums f vardef_0__schemaInstance_key=Z.of_nat (SchemaGraph.key root node depth) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error fs 0=Some SetTheory.falsity -> meta_value (machine f) 8=0 ->
 ready (machine f) fs classes rho depth kind a b c d reserve ->
 core f width remaining outer_remaining fs classes rho depth expression (SchemaGraph.key root node depth) reserve observations.
Proof.
 intros Hordered Hroot Hreachable Hview Hfit Hraw Hsource Hcompleted Hword Hallocated Hnode Hdepth Hstride Hkey
   Hmeta Hsip Harena Htop Hclasses Hwellformed Hfalse Herror [HinitialRoom Hready].
 pose proof (SchemaGraph.reachable_grid source root node depth Hordered Hroot Hreachable) as [Hnodegrid [Hdepthgrid Hkeygrid]].
 assert (Hbound:(SchemaGraph.key root node depth<length (memory (machine f) arraydef_0__schemaValues))%nat) by lia.
 destruct Hview as [aa bb cc dd Hsmall|aa bb cc dd cls Hliteral|aa bb cc dd p Hliteral|
   aa bb cc dd p Hchild|aa bb cc dd ca cb Hleft Hright|aa bb cc dd ca cb Hleft Hright|
   aa bb cc dd p q Hleft Hright|aa bb cc dd p Hchild|tag aa bb cc p q r Htag Hp Hq Hr|
   aa bb cc dd ci ca Hleft Hright|aa bb cc dd ci Hchild|aa bb cc dd p checked Hliteral].
 - cbn [ready] in Hready.
   destruct Hready as [[cls [Hargument [Hclsword Hcls]]] Hshift].
   destruct depth as [|depth'].
   + destruct (SchemaEvaluationMetaInvariant.generated_meta_zero f width remaining outer_remaining node aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ cls fs classes rho observations
       Hnode Hraw Hkey Hbound Hargument Hdepth ltac:(lia) Harena Htop Herror Hclasses Hwellformed Hcls Hclsword)
       as (final & Hrun & Hpost & Hnextclasses & Hnext & Hnexttop & Hflag & Hvalid & Hnextgood).
     eapply core_success;try eassumption;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
   + destruct (Hshift ltac:(lia)) as [Hclassroom [Hsetroom Habstractroom]].
     destruct (ClassLookup.lookup (machine f) fs classes cls (rho aa) Hclasses Hwellformed Hcls)
       as [_ [[variable [Hrho [Hvariable Hclass]]]|[body [p [Hrho [Hp Hclass]]]]]].
     * destruct (SchemaEvaluationMetaInvariant.generated_meta_set f width remaining outer_remaining node aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ cls variable (S depth') fs classes rho 0 observations
         Hnode Hraw Hkey Hbound Hargument Hdepth ltac:(lia) ltac:(lia) Harena Htop Hclasses Hwellformed Hclass Hrho (Hsetroom variable Hrho) Hclassroom)
         as (final & Hrun & Hpost & Hnextclasses & Hnext & Hnexttop & Hvalid & Hflag & Hroom & Hnextgood).
       rewrite Herror in Hflag. eapply core_success;try eassumption.
       -- apply prefix_refl.
       -- eexists;reflexivity.
       -- rewrite length_app;cbn;lia.
     * destruct (Habstractroom cls body p Hclass Hp) as (bound & Hfuel & Hindices & Hindicesroom & Hheight & Hbudget).
       destruct (SchemaEvaluationMetaInvariant.generated_meta_abstract f width remaining outer_remaining node aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ cls body p (S depth') bound fs classes rho reserve 0 observations
         Hnode Hraw Hkey Hbound Hargument Hdepth ltac:(lia) Hmeta Hsip Harena Htop Herror Hclasses Hwellformed Hclass Hp Hrho Hfalse
         Hfuel Hindices Hindicesroom Hheight Hbudget Hclassroom)
         as (final & next & Hrun & Hpost & Hnext & Hnextclasses & Hflag & Hprefix & Hnexttop & Hroom & Hclassroom' & Hnextgood & Hvalid).
       eapply core_success;try eassumption;first [eexists;reflexivity|rewrite length_app;cbn;lia|lia].

 - destruct (fields_words _ _ _ _ _ _ Hfit) as [Hkword [Haword [Hbword [Hcword Hdword]]]].
   assert (Hmeaning:SchemaEvaluation.meaning fs classes rho depth (Protocol.CE (Schemata.literal_class cls)) (Z.of_nat aa)).
   { change (word (Z.of_nat aa) /\ nth_error classes (Z.to_nat (Z.of_nat aa))=Some cls). rewrite Nat2Z.id. split;assumption. }
   destruct (generated_literal f width remaining outer_remaining node 1 (Z.of_nat aa) (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ fs classes rho depth _ observations
     Hnode Hraw ltac:(auto) ltac:(lia) Hkey Hbound Harena Hclasses Htop Hwellformed Herror Hmeaning)
     as (final & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid).
   eapply core_success;try eassumption;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
 - destruct (fields_words _ _ _ _ _ _ Hfit) as [Hkword [Haword [Hbword [Hcword Hdword]]]].
   assert (Hmeaning:SchemaEvaluation.meaning fs classes rho depth (Protocol.FE (Schemata.literal_formula p)) (Z.of_nat aa)).
   { change (word (Z.of_nat aa) /\ nth_error fs (Z.to_nat (Z.of_nat aa))=Some p). rewrite Nat2Z.id. split;assumption. }
   destruct (generated_literal f width remaining outer_remaining node 2 (Z.of_nat aa) (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ fs classes rho depth _ observations
     Hnode Hraw ltac:(auto) ltac:(lia) Hkey Hbound Harena Hclasses Htop Hwellformed Herror Hmeaning)
     as (final & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid).
   eapply core_success;try eassumption;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 1 (Protocol.FE p)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hchild Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_1_r in HreadA,HmeanA,HkeyA.
   destruct (SchemaEvaluationMetaInvariant.generated_abstraction f width remaining outer_remaining node aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa (S depth)) (Z.of_nat idA) fs classes rho p 0 observations
     Hnode Hraw Hstride Hdepth Hkey ltac:(unfold SchemaGraph.key;lia) HkeyA HreadA ltac:(lia) Hbound Harena Hclasses Hwellformed Herror Htop HmeanA Hready)
     as (final & Hrun & Hpost & Hnext & Hnextclasses & Hflag & Hnexttop & Hroom & Hnextgood & Hvalid).
   eapply core_success;try eassumption;first [apply prefix_refl|eexists;reflexivity|rewrite length_app;cbn;lia|lia].
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 0 (Protocol.CE ca)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hleft Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_0_r in HreadA,HmeanA,HkeyA.
   destruct (completed_value source (machine f) root expressions rho fs classes node depth _ bb 0 (Protocol.CE cb)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hright Hword Hallocated) as (idB & HwordB & HreadB & HmeanB & HkeyB).
   rewrite Nat.add_0_r in HreadB,HmeanB,HkeyB.
   change (word (Z.of_nat idA) /\ nth_error classes (Z.to_nat (Z.of_nat idA))=Some (Schemata.instantiate_class rho depth ca)) in HmeanA.
   change (word (Z.of_nat idB) /\ nth_error classes (Z.to_nat (Z.of_nat idB))=Some (Schemata.instantiate_class rho depth cb)) in HmeanB.
   rewrite Nat2Z.id in HmeanA,HmeanB. destruct HmeanA as [_ HclassA]. destruct HmeanB as [_ HclassB].
   destruct (Hready idA idB _ _ HclassA HclassB) as [Hrename Hbudget].
   destruct (SchemaEvaluationFamilyInvariant.generated_equal f width remaining outer_remaining node aa bb (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa depth) (SchemaGraph.key root bb depth) idA idB fs classes rho ca cb reserve observations
     Hnode Hraw Hstride Hdepth Hkey Hbound eq_refl eq_refl HkeyA HkeyB HreadA HreadB Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hwellformed
     HclassA HclassB Hrename Hbudget)
     as (final & next & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hflag & Hprefix & Hroom & Hnextgood & Hvalid).
   eapply core_success;try eassumption;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 0 (Protocol.CE ca)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hleft Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_0_r in HreadA,HmeanA,HkeyA.
   destruct (completed_value source (machine f) root expressions rho fs classes node depth _ bb 0 (Protocol.CE cb)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hright Hword Hallocated) as (idB & HwordB & HreadB & HmeanB & HkeyB).
   rewrite Nat.add_0_r in HreadB,HmeanB,HkeyB.
   change (word (Z.of_nat idA) /\ nth_error classes (Z.to_nat (Z.of_nat idA))=Some (Schemata.instantiate_class rho depth ca)) in HmeanA.
   change (word (Z.of_nat idB) /\ nth_error classes (Z.to_nat (Z.of_nat idB))=Some (Schemata.instantiate_class rho depth cb)) in HmeanB.
   rewrite Nat2Z.id in HmeanA,HmeanB. destruct HmeanA as [_ HclassA]. destruct HmeanB as [_ HclassB].
   destruct (Hready idA idB _ _ HclassA HclassB) as [Hrename Hbudget].
   destruct (SchemaEvaluationFamilyInvariant.generated_member f width remaining outer_remaining node aa bb (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa depth) (SchemaGraph.key root bb depth) idA idB fs classes rho ca cb reserve observations
     Hnode Hraw Hstride Hdepth Hkey Hbound eq_refl eq_refl HkeyA HkeyB HreadA HreadB Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hwellformed
     HclassA HclassB Hrename Hbudget)
     as (final & next & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hflag & Hprefix & Hroom & Hnextgood & Hvalid).
   eapply core_success;try eassumption;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 0 (Protocol.FE p)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hleft Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_0_r in HreadA,HmeanA,HkeyA.
   destruct (completed_value source (machine f) root expressions rho fs classes node depth _ bb 0 (Protocol.FE q)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hright Hword Hallocated) as (idB & HwordB & HreadB & HmeanB & HkeyB).
   rewrite Nat.add_0_r in HreadB,HmeanB,HkeyB.
   destruct (SchemaEvaluationFamilyInvariant.generated_imp f width remaining outer_remaining node aa bb (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa depth) (SchemaGraph.key root bb depth) (Z.of_nat idA) (Z.of_nat idB) fs classes rho p q reserve observations
     Hnode Hraw Hstride Hdepth Hkey Hbound eq_refl eq_refl HkeyA HkeyB HreadA HreadB ltac:(lia) Harena Htop Herror Hclasses Hwellformed HmeanA HmeanB
     Hready)
     as (final & next & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hflag & Hprefix & Hroom & Hnextgood & Hvalid).
   eapply core_success;try eassumption;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 1 (Protocol.FE p)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hchild Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_1_r in HreadA,HmeanA,HkeyA.
   destruct (SchemaEvaluationPreservation.generated_universal f width remaining outer_remaining node 7 aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa (S depth)) (Z.of_nat idA) fs classes rho (Schemata.instantiate_formula rho (S depth) p) (Protocol.FE (Schemata.template_all p)) reserve observations
     Hnode Hraw ltac:(auto) Hstride Hdepth Hkey ltac:(unfold SchemaGraph.key;lia) HkeyA HreadA ltac:(lia) Hbound Harena Htop Herror Hclasses Hwellformed HmeanA ltac:(intros;assumption)
     Hready)
     as (final & next & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid & Hprefix & Hroom).
   eapply core_success;try eassumption;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
 - destruct (fields_words _ _ _ _ _ _ Hfit) as [Hkword [Htagword [Haword [Hbword Hcword]]]].
   destruct (axiom_ready source (machine f) root expressions rho fs classes node depth tag aa bb cc p q r _
     Hordered Hroot Hreachable Hsource Hp Hq Hr Hcompleted Hword Hallocated Haword Hbword Hcword)
     as (idA & idB & idC & HreadA & HreadB & HreadC & HselectedA & HselectedB & HselectedC & HwordA & HwordB & HwordC & HtypedReady).
   assert (Hneeded:AxiomTaggedInvariant.needs_p tag=true -> nth_error fs idA=Some (Schemata.instantiate_formula rho depth p)).
   { intro Hneed. destruct HtypedReady as [HA _]. unfold AxiomTaggedInvariant.ready in HA.
     rewrite Hneed in HA. exact HA. }
   destruct (Hready idA (Schemata.instantiate_formula rho depth p) HwordA Hneeded) as [bound [Hrename Hbudget]].
   destruct (SchemaEvaluationFamilyInvariant.generated_axiom f width remaining outer_remaining node _ _ _ tag aa bb cc (SchemaGraph.width root) depth idA idB idC
     fs classes rho p q r bound reserve observations Hnode Hraw Hkey Hbound Hclasses Hwellformed Htag Hstride Hdepth
     HreadA HreadB HreadC HselectedA HselectedB HselectedC Hmeta Hsip Harena Htop Herror Hfalse HwordA HwordB HwordC HtypedReady Hrename Hbudget)
     as (final & next & Hrun & Hpost & Hnext & Hnexttop & Hnextclasses & Hprefix & Hflag & Hsuccess & Hroom & Hgrowth & Hnextgood & Hvalid).
   eapply core_success;try eassumption;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 0 (Protocol.PE ci)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];left;reflexivity)
     Hcompleted Hleft Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_0_r in HreadA,HmeanA,HkeyA.
   destruct (completed_value source (machine f) root expressions rho fs classes node depth _ bb 0 (Protocol.PE ca)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];right;left;reflexivity)
     Hcompleted Hright Hword Hallocated) as (idB & HwordB & HreadB & HmeanB & HkeyB).
   rewrite Nat.add_0_r in HreadB,HmeanB,HkeyB.
   destruct (SchemaEvaluationFamilyInvariant.generated_mp f width remaining outer_remaining node aa bb (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa depth) (SchemaGraph.key root bb depth) idA (Z.of_nat idB) fs classes rho ci ca observations
     Hnode Hraw Hstride Hdepth Hkey Hbound eq_refl eq_refl HkeyA HkeyB HreadA HreadB ltac:(lia) Harena Htop Herror Hclasses Hwellformed HmeanA HmeanB)
     as (final & Hrun & Hnext & Hnextclasses & Hnexttop & Hflag & Hvalues & Hlengths & Hsemantic & Hnextgood).
   destruct (Schemata.infer rho depth (Schemata.template_mp ci ca)) as [result|] eqn:Hinfer.
   + destruct Hsemantic as [Hpost Hvalid]. eapply core_success;try eassumption;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
   + exists final,fs,classes. split;[exact Hrun|]. split;[exact Hnext|]. split;[exact Hflag|].
     split;[apply prefix_refl|]. split;[apply prefix_refl|]. split;[exact Hnextclasses|].
     split;[exact Hnexttop|]. split;[exact Hnextgood|]. split;[lia|]. split;[exact (arena_count_word _ _ Hnext)|]. split;[exact HinitialRoom|].
     right. exists (Schemata.template_mp ci ca). repeat split;assumption.
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 1 (Protocol.PE ci)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];left;reflexivity)
     Hcompleted Hchild Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_1_r in HreadA,HmeanA,HkeyA.
   destruct HmeanA as [childResult [HchildInfer HchildMeaning]].
   destruct (SchemaEvaluationPreservation.generated_universal f width remaining outer_remaining node 10 aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa (S depth)) (Z.of_nat idA) fs classes rho childResult (Protocol.PE (Schemata.template_gen ci)) reserve observations
     Hnode Hraw ltac:(auto) Hstride Hdepth Hkey ltac:(unfold SchemaGraph.key;lia) HkeyA HreadA ltac:(lia) Hbound Harena Htop Herror Hclasses Hwellformed HchildMeaning
     ltac:(intros next value Hvalue;exists (SetTheory.all childResult);split;[cbn [Schemata.infer];rewrite HchildInfer;reflexivity|exact Hvalue])
     Hready)
     as (final & next & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid & Hprefix & Hroom).
   eapply core_success;try eassumption;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
 - destruct (fields_words _ _ _ _ _ _ Hfit) as [Hkword [Haword [Hbword [Hcword Hdword]]]].
   assert (Hmeaning:SchemaEvaluation.meaning fs classes rho depth (Protocol.PE (Schemata.saved_theorem p checked)) (Z.of_nat aa)).
   { exists p. split;[reflexivity|]. change (word (Z.of_nat aa) /\ nth_error fs (Z.to_nat (Z.of_nat aa))=Some p). rewrite Nat2Z.id. split;assumption. }
   destruct (generated_literal f width remaining outer_remaining node 11 (Z.of_nat aa) (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ fs classes rho depth _ observations
     Hnode Hraw ltac:(auto) ltac:(lia) Hkey Hbound Harena Hclasses Htop Hwellformed Herror Hmeaning)
     as (final & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid).
   eapply core_success;try eassumption;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
Qed.

(** A represented descriptor supplies its own typed view. The only additional
    premise selects explicit mathematical resources for whichever descriptor is
    stored; it never assumes an execution. *)
Theorem generated_represented source (f:SchemaEvaluation.Frame) logical root rho node depth expression
 width remaining outer_remaining reserve observations :
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 SchemaGraph.reachable source root node depth ->
 SchemaRepresentation.represents (machine f) logical ->
 memory (machine f) arraydef_0__schemaNodes=memory source arraydef_0__schemaNodes ->
 nth_error (Protocol.expressions logical) node=Some expression ->
 SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho (Protocol.formulas logical) (Protocol.classes logical)
   (machine f) (SchemaGraph.key root node depth) ->
 Z.of_nat (SchemaGraph.width root*SchemaGraph.width root)<=maximum ->
 (SchemaGraph.width root*SchemaGraph.width root<=length (memory (machine f) arraydef_0__schemaValues))%nat ->
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
 nums f vardef_0__schemaInstance_key=Z.of_nat (SchemaGraph.key root node depth) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) (Protocol.formulas logical) ->
 FormulaTopology.ordered (machine f) (length (Protocol.formulas logical)) ->
 ClassStorage.represents (machine f) (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed (machine f) ->
 nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity -> meta_value (machine f) 8=0 ->
 (forall k a b c d,
   nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode k a b c d expression) ->
   ready (machine f) (Protocol.formulas logical) (Protocol.classes logical) rho depth k a b c d reserve) ->
 core f width remaining outer_remaining (Protocol.formulas logical) (Protocol.classes logical) rho depth expression
   (SchemaGraph.key root node depth) reserve observations.
Proof.
 intros Hordered Hroot Hreachable Hrep Hnodes Hlookup Hcompleted Hword Hallocated Hnode Hdepth Hstride Hkey
   Hmeta Hsip Harena Htop Hclasses Hwellformed Hfalse Herror Hready.
 destruct (represented_view (machine f) logical node expression Hrep Hlookup)
   as (kind & a & b & c & d & Hraw & Hfit & Hview).
 eapply (generated_view source f root (Protocol.formulas logical) (Protocol.classes logical) (Protocol.expressions logical)
   rho node depth kind a b c d expression width remaining outer_remaining reserve observations);try eassumption.
 - now rewrite <-Hnodes.
 - exact (Hready kind a b c d Hraw).
Qed.
End SchemaEvaluationBoundedCell.
