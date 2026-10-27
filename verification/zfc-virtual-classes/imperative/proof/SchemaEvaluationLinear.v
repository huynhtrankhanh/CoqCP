From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal SchemaEvaluation SchemaEvaluationDependencies SchemaEvaluationResources
 SchemaEvaluationInvariant SchemaPair SchemaPairStep SchemaPairSemantic SchemaEvaluationAbstractSemantic SchemaGraph SchemaRepresentation SchemaMetadata
 SchemaEvaluationCell Representation ClassStorage ClassLookup FormulaTopology ArenaFrame RenameMemoControl RenameMemoLengths HashTable AxiomTaggedInvariant InternInvariant SchemaEvaluationMetaInvariant SchemaEvaluationFamilyInvariant SchemaEvaluationPreservation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationLinear.
Import IndexExecution SipHashExecution ObservedLocal SchemaEvaluationDependencies SchemaEvaluationCell.
Definition supported kind := kind=1%nat \/ kind=2%nat \/ kind=6%nat \/ kind=7%nat \/ kind=9%nat \/ kind=10%nat \/ kind=11%nat.
Definition bound : Z := 9223372036854775807.
Definition result (f:SchemaEvaluation.Frame) width remaining outer_remaining fs classes rho depth expression key reserve observations :=
 exists final next_fs next_classes,
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=Some (KeepGoing,(final,observations)) /\
 NativeRepresentation.canonical_arena (machine final) next_fs /\ meta_value (machine final) 8=0 /\
 prefix fs next_fs /\ prefix classes next_classes /\
 ClassStorage.represents (machine final) next_fs next_classes /\
 FormulaTopology.ordered (machine final) (length next_fs) /\ ClassLookup.wellformed (machine final) /\
 (length next_classes<=S (length classes))%nat /\ word (Z.of_nat (length next_fs)) /\
 Z.of_nat (length next_fs+reserve)<=bound /\
 semantic_result f final next_fs next_classes rho depth expression key.
Lemma success (f final:SchemaEvaluation.Frame) width remaining outer_remaining fs classes next_fs next_classes rho depth expression key reserve observations :
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=Some (KeepGoing,(final,observations)) ->
 NativeRepresentation.canonical_arena (machine final) next_fs -> meta_value (machine final) 8=0 ->
 prefix fs next_fs -> prefix classes next_classes ->
 ClassStorage.represents (machine final) next_fs next_classes -> FormulaTopology.ordered (machine final) (length next_fs) ->
 ClassLookup.wellformed (machine final) -> (length next_classes<=S (length classes))%nat ->
 SchemaPairSemantic.post f final next_fs next_classes rho depth expression key ->
 meta_value (machine final) 18=meta_value (machine f) 18 ->
 Z.of_nat (length next_fs+reserve)<=bound ->
 result f width remaining outer_remaining fs classes rho depth expression key reserve observations.
Proof.
 intros Hrun Harena Herror Hfs Hclasses Hclassrep Htop Hgood Hgrowth Hpost Hvalid Hroom.
 exists final,next_fs,next_classes.
 split;[exact Hrun|]. split;[exact Harena|]. split;[exact Herror|].
 split;[exact Hfs|]. split;[exact Hclasses|]. split;[exact Hclassrep|].
 split;[exact Htop|]. split;[exact Hgood|]. split;[exact Hgrowth|].
 split;[exact (arena_count_word _ _ Harena)|]. split;[exact Hroom|]. left. split;assumption.
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
 supported kind -> Z.of_nat (length fs+S reserve)<=bound ->
 result f width remaining outer_remaining fs classes rho depth expression (SchemaGraph.key root node depth) reserve observations.
Proof.
 intros Hordered Hroot Hreachable Hview Hfit Hraw Hsource Hcompleted Hword Hallocated Hnode Hdepth Hstride Hkey
   Hmeta Hsip Harena Htop Hclasses Hwellformed Hfalse Herror Hlinear Hbudget.
 pose proof (SchemaGraph.reachable_grid source root node depth Hordered Hroot Hreachable) as [Hnodegrid [Hdepthgrid Hkeygrid]].
 assert (Hbound:(SchemaGraph.key root node depth<length (memory (machine f) arraydef_0__schemaValues))%nat) by lia.
 destruct Hview as [aa bb cc dd Hsmall|aa bb cc dd cls Hliteral|aa bb cc dd p Hliteral|
   aa bb cc dd p Hchild|aa bb cc dd ca cb Hleft Hright|aa bb cc dd ca cb Hleft Hright|
   aa bb cc dd p q Hleft Hright|aa bb cc dd p Hchild|tag aa bb cc p q r Htag Hp Hq Hr|
   aa bb cc dd ci ca Hleft Hright|aa bb cc dd ci Hchild|aa bb cc dd p checked Hliteral].
 all: try (unfold supported in Hlinear;lia).
 - destruct (fields_words _ _ _ _ _ _ Hfit) as [Hkword [Haword [Hbword [Hcword Hdword]]]].
   assert (Hmeaning:SchemaEvaluation.meaning fs classes rho depth (Protocol.CE (Schemata.literal_class cls)) (Z.of_nat aa)).
   { change (word (Z.of_nat aa) /\ nth_error classes (Z.to_nat (Z.of_nat aa))=Some cls). rewrite Nat2Z.id. split;assumption. }
   destruct (generated_literal f width remaining outer_remaining node 1 (Z.of_nat aa) (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ fs classes rho depth _ observations
     Hnode Hraw ltac:(auto) ltac:(lia) Hkey Hbound Harena Hclasses Htop Hwellformed Herror Hmeaning)
     as (final & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid).
   eapply success;try eassumption;unfold bound in *;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
 - destruct (fields_words _ _ _ _ _ _ Hfit) as [Hkword [Haword [Hbword [Hcword Hdword]]]].
   assert (Hmeaning:SchemaEvaluation.meaning fs classes rho depth (Protocol.FE (Schemata.literal_formula p)) (Z.of_nat aa)).
   { change (word (Z.of_nat aa) /\ nth_error fs (Z.to_nat (Z.of_nat aa))=Some p). rewrite Nat2Z.id. split;assumption. }
   destruct (generated_literal f width remaining outer_remaining node 2 (Z.of_nat aa) (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ fs classes rho depth _ observations
     Hnode Hraw ltac:(auto) ltac:(lia) Hkey Hbound Harena Hclasses Htop Hwellformed Herror Hmeaning)
     as (final & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid).
   eapply success;try eassumption;unfold bound in *;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
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
     Hbudget)
     as (final & next & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hflag & Hprefix & Hroom & Hnextgood & Hvalid).
   eapply success;try eassumption;unfold bound in *;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 1 (Protocol.FE p)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hchild Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_1_r in HreadA,HmeanA,HkeyA.
   destruct (SchemaEvaluationPreservation.generated_universal f width remaining outer_remaining node 7 aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa (S depth)) (Z.of_nat idA) fs classes rho (Schemata.instantiate_formula rho (S depth) p) (Protocol.FE (Schemata.template_all p)) reserve observations
     Hnode Hraw ltac:(auto) Hstride Hdepth Hkey ltac:(unfold SchemaGraph.key;lia) HkeyA HreadA ltac:(lia) Hbound Harena Htop Herror Hclasses Hwellformed HmeanA ltac:(intros;assumption)
     Hbudget)
     as (final & next & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid & Hprefix & Hroom).
   eapply success;try eassumption;unfold bound in *;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
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
   + destruct Hsemantic as [Hpost Hvalid]. eapply success;try eassumption;unfold bound in *;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
   + exists final,fs,classes. split;[exact Hrun|]. split;[exact Hnext|]. split;[exact Hflag|].
     split;[apply prefix_refl|]. split;[apply prefix_refl|]. split;[exact Hnextclasses|].
     split;[exact Hnexttop|]. split;[exact Hnextgood|]. split;[lia|]. split;[exact (arena_count_word _ _ Hnext)|].
     split;[unfold bound in *;lia|]. right. exists (Schemata.template_mp ci ca). repeat split;assumption.
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 1 (Protocol.PE ci)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];left;reflexivity)
     Hcompleted Hchild Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_1_r in HreadA,HmeanA,HkeyA.
   destruct HmeanA as [childResult [HchildInfer HchildMeaning]].
   destruct (SchemaEvaluationPreservation.generated_universal f width remaining outer_remaining node 10 aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa (S depth)) (Z.of_nat idA) fs classes rho childResult (Protocol.PE (Schemata.template_gen ci)) reserve observations
     Hnode Hraw ltac:(auto) Hstride Hdepth Hkey ltac:(unfold SchemaGraph.key;lia) HkeyA HreadA ltac:(lia) Hbound Harena Htop Herror Hclasses Hwellformed HchildMeaning
     ltac:(intros next value Hvalue;exists (SetTheory.all childResult);split;[cbn [Schemata.infer];rewrite HchildInfer;reflexivity|exact Hvalue])
     Hbudget)
     as (final & next & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid & Hprefix & Hroom).
   eapply success;try eassumption;unfold bound in *;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
 - destruct (fields_words _ _ _ _ _ _ Hfit) as [Hkword [Haword [Hbword [Hcword Hdword]]]].
   assert (Hmeaning:SchemaEvaluation.meaning fs classes rho depth (Protocol.PE (Schemata.saved_theorem p checked)) (Z.of_nat aa)).
   { exists p. split;[reflexivity|]. change (word (Z.of_nat aa) /\ nth_error fs (Z.to_nat (Z.of_nat aa))=Some p). rewrite Nat2Z.id. split;assumption. }
   destruct (generated_literal f width remaining outer_remaining node 11 (Z.of_nat aa) (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ fs classes rho depth _ observations
     Hnode Hraw ltac:(auto) ltac:(lia) Hkey Hbound Harena Hclasses Htop Hwellformed Herror Hmeaning)
     as (final & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid).
   eapply success;try eassumption;unfold bound in *;first [apply prefix_refl|rewrite length_app;cbn;lia|lia].
Qed.
End SchemaEvaluationLinear.
