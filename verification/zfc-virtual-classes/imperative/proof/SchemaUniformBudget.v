From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash SchemaGraph SchemaMetadata SchemaRepresentation SchemaMarking SchemaNodeMeaning
 AxiomTaggedInvariant SchemaEvaluationBoundedCell SchemaEvaluationIndexCell SchemaEvaluationIndexBudget SchemaEvaluationIndexReady
 SchemaInstanceGeneralReady SchemaInstanceGeneralProtocol.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaUniformBudget.
Import IndexExecution SipHashExecution.
Definition formula_next capacity := (capacity+3*(capacity*capacity)+42)%nat.
Definition index_next expression_cap field_cap bound := (2*bound+expression_cap+3*field_cap+4)%nat.
Fixpoint formula_after initial count := match count with O=>initial|S count=>formula_next (formula_after initial count) end.
Fixpoint index_after expression_cap field_cap initial count := match count with
 | O=>initial|S count=>index_next expression_cap field_cap (index_after expression_cap field_cap initial count) end.
Definition slots expression_cap := (expression_cap*expression_cap)%nat.
Definition formula_ceiling expression_cap initial key := formula_after initial (Nat.min key (slots expression_cap)).
Definition index_ceiling expression_cap field_cap initial key := index_after expression_cap field_cap initial (Nat.min key (slots expression_cap)).
(** Only the fields that can introduce variable indices need this bound.
    The tag/parameter field a may contain a resolved saved-formula ID. *)
Definition encoded_fields (native:Machine) field_cap := forall node kind a b c d expression,
 nth_error (memory native arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode kind a b c d expression) ->
 (b<=field_cap /\ c<=field_cap /\ d<=field_cap)%nat.
Lemma cost_bound capacity kind tag depth :
 (SchemaEvaluationIndexBudget.cost capacity kind tag depth<=3*(capacity*capacity)+42)%nat.
Proof.
 let rec cases count index := lazymatch count with
   O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 12%nat kind.
 all: cbn [SchemaEvaluationIndexBudget.cost];try lia;try nia.
 - destruct (Nat.eqb depth 0);nia.
 - unfold SchemaEvaluationIndexBudget.axiom_cost.
   let rec cases count index := lazymatch count with
     O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 18%nat tag.
   all: destruct capacity as [|capacity];cbn [AxiomTaggedInvariant.cost Nat.sub];nia.
Qed.
Lemma index_step_bound kind bound depth b c d expression_cap field_cap :
 (depth<=expression_cap)%nat -> (b<=field_cap)%nat -> (c<=field_cap)%nat -> (d<=field_cap)%nat ->
 (SchemaEvaluationIndexCell.successor kind bound depth b c d<=index_next expression_cap field_cap bound)%nat.
Proof.
 intros Hdepth Hb Hc Hd. unfold index_next.
 let rec cases count index := lazymatch count with
   O=>idtac | S ?rest=>destruct index as [|index];[cbn [SchemaEvaluationIndexCell.successor];lia|cases rest index] end in cases 12%nat kind.
 cbn [SchemaEvaluationIndexCell.successor];lia.
Qed.
Lemma formula_mono initial first last : (first<=last)%nat -> (formula_after initial first<=formula_after initial last)%nat.
Proof. intro H. induction H as [|last H IH];[reflexivity|]. cbn [formula_after]. unfold formula_next;nia. Qed.
Lemma index_mono expression_cap field_cap initial first last : (first<=last)%nat ->
 (index_after expression_cap field_cap initial first<=index_after expression_cap field_cap initial last)%nat.
Proof. intro H. induction H as [|last H IH];[reflexivity|]. cbn [index_after]. unfold index_next;nia. Qed.
Lemma formula_ceiling_step expression_cap initial key :
 (formula_ceiling expression_cap initial key<=formula_ceiling expression_cap initial (S key))%nat.
Proof. apply formula_mono. apply Nat.min_le_compat_r;lia. Qed.
Lemma index_ceiling_step expression_cap field_cap initial key :
 (index_ceiling expression_cap field_cap initial key<=index_ceiling expression_cap field_cap initial (S key))%nat.
Proof. apply index_mono. apply Nat.min_le_compat_r;lia. Qed.
Lemma formula_ceiling_terminal expression_cap initial key :
 (formula_ceiling expression_cap initial key<=formula_after initial (slots expression_cap))%nat.
Proof. apply formula_mono. apply Nat.le_min_r. Qed.
Lemma index_ceiling_terminal expression_cap field_cap initial key :
 (index_ceiling expression_cap field_cap initial key<=index_after expression_cap field_cap initial (slots expression_cap))%nat.
Proof. apply index_mono. apply Nat.le_min_r. Qed.
Lemma formula_ceiling_word expression_cap initial :
 Z.of_nat (formula_after initial (slots expression_cap))<=SchemaEvaluationBoundedCell.bound ->
 forall key,Z.of_nat (formula_ceiling expression_cap initial key)<=SchemaEvaluationBoundedCell.bound.
Proof. intros H key. pose proof (formula_ceiling_terminal expression_cap initial key). lia. Qed.
Lemma index_ceiling_word expression_cap field_cap initial :
 Z.of_nat (index_after expression_cap field_cap initial (slots expression_cap))<=maximum ->
 forall key,Z.of_nat (index_ceiling expression_cap field_cap initial key)<=maximum.
Proof. intros H key. pose proof (index_ceiling_terminal expression_cap field_cap initial key). lia. Qed.
Theorem scalar native root expression_cap field_cap initialF initialB initialC class_base :
 SchemaGraph.ordered native -> (root<length (memory native arraydef_0__schemaNodes))%nat ->
 (SchemaGraph.width root<=expression_cap)%nat -> encoded_fields native field_cap -> (class_base<=initialC)%nat ->
 Z.of_nat (5*(formula_after initialF (slots expression_cap)*formula_after initialF (slots expression_cap))+1)<=maximum ->
 Z.of_nat (initialC+slots expression_cap+1)<=maximum ->
 SchemaEvaluationIndexReady.scalar (formula_ceiling expression_cap initialF)
   (index_ceiling expression_cap field_cap initialB) native root class_base.
Proof.
 intros Hordered Hroot Hwidth Hfields HclassBase Hfuel Hclasses node depth kind a b c d expression Hreachable Hraw.
 destruct (SchemaGraph.reachable_grid native root node depth Hordered Hroot Hreachable) as [Hnode [Hdepth Hkey]].
 destruct (Hfields node kind a b c d expression Hraw) as [Hb [Hc Hd]].
 set (key:=SchemaGraph.key root node depth) in *.
 assert (Hslot:(key<slots expression_cap)%nat) by (unfold slots;nia).
 assert (HdepthCap:(depth<=expression_cap)%nat) by lia.
 pose proof (formula_ceiling_terminal expression_cap initialF key) as Hterminal.
 unfold formula_ceiling,index_ceiling.
 rewrite (Nat.min_l key (slots expression_cap) ltac:(lia)),(Nat.min_l (S key) (slots expression_cap) ltac:(lia)).
 split.
 - cbn [formula_after]. unfold formula_next. pose proof (cost_bound (formula_after initialF key) kind a depth). lia.
 - split.
   + intro Hrenames. change (Z.of_nat (5*(formula_after initialF key*formula_after initialF key)+1)<=maximum).
     unfold formula_ceiling in Hterminal. rewrite (Nat.min_l key (slots expression_cap) ltac:(lia)) in Hterminal.
     apply Nat2Z.inj_le in Hterminal. repeat rewrite Nat2Z.inj_add in *. repeat rewrite Nat2Z.inj_mul in *. nia.
   + split.
     * intro Hneeds. repeat rewrite Nat2Z.inj_add in *. lia.
     * cbn [index_after]. exact (index_step_bound kind (index_after expression_cap field_cap initialB key) depth b c d
         expression_cap field_cap HdepthCap Hb Hc Hd).
Qed.
Theorem resources native logical root actual expression_cap field_cap initialF initialB initialC :
 SchemaGraph.ordered native -> (root<length (memory native arraydef_0__schemaNodes))%nat ->
 (SchemaGraph.width root<=expression_cap)%nat -> encoded_fields native field_cap ->
 (length (Protocol.formulas logical)<=initialF)%nat -> (length (Protocol.classes logical)<=initialC)%nat ->
 SchemaEvaluationIndexCell.bounded native (Protocol.formulas logical) (Protocol.classes logical) initialB ->
 Z.of_nat (formula_after initialF (slots expression_cap))<=SchemaEvaluationBoundedCell.bound ->
 Z.of_nat (index_after expression_cap field_cap initialB (slots expression_cap))<=maximum ->
 Z.of_nat (5*(formula_after initialF (slots expression_cap)*formula_after initialF (slots expression_cap))+1)<=maximum ->
 Z.of_nat (initialC+slots expression_cap+1)<=maximum ->
 SchemaInstanceGeneralReady.resources native logical root actual.
Proof.
 intros Hordered Hroot Hwidth Hfields Hformulas HclassCount Hbounded HF HB Hfuel HC.
 exists (formula_ceiling expression_cap initialF),(index_ceiling expression_cap field_cap initialB).
 split;[exact (formula_ceiling_word expression_cap initialF HF)|].
 split;[apply formula_ceiling_step|]. split;[exact (index_ceiling_word expression_cap field_cap initialB HB)|].
 split;[apply index_ceiling_step|]. split;[exact Hformulas|]. split;[exact Hbounded|].
 exact (scalar native root expression_cap field_cap initialF initialB initialC (length (Protocol.classes logical))
   Hordered Hroot Hwidth Hfields HclassCount Hfuel HC).
Qed.
Theorem protocol_resources native logical ids name expression_cap field_cap initialF initialB initialC :
 SchemaRepresentation.represents native logical ->
 (length (Protocol.expressions logical)<=expression_cap)%nat -> encoded_fields native field_cap ->
 (length (Protocol.formulas logical)<=initialF)%nat -> (length (Protocol.classes logical)<=initialC)%nat ->
 SchemaEvaluationIndexCell.bounded native (Protocol.formulas logical) (Protocol.classes logical) initialB ->
 Z.of_nat (length (Protocol.history logical))<maximum ->
 Z.of_nat (formula_after initialF (slots expression_cap))<=SchemaEvaluationBoundedCell.bound ->
 Z.of_nat (index_after expression_cap field_cap initialB (slots expression_cap))<=maximum ->
 Z.of_nat (5*(formula_after initialF (slots expression_cap)*formula_after initialF (slots expression_cap))+1)<=maximum ->
 Z.of_nat (initialC+slots expression_cap+1)<=maximum ->
 SchemaInstanceGeneralProtocol.resources native logical ids name.
Proof.
 intros Hschema Hexpressions Hfields HF0 HC0 Hbounded Hhistory HF HB Hfuel HC root cert actual Hlookup Hproof Harity Hactual.
 pose proof (SchemaNodeMeaning.proof_lookup logical root cert Hproof) as HrootLookup.
 assert (HlogicalRoot:(root<length (Protocol.expressions logical))%nat) by (apply nth_error_Some;congruence).
 assert (HnativeRoot:(root<length (memory native arraydef_0__schemaNodes))%nat).
 { rewrite (SchemaMetadata.represents_length native _ (SchemaRepresentation.metadata native logical Hschema)). exact HlogicalRoot. }
 assert (Hwidth:(SchemaGraph.width root<=expression_cap)%nat) by (unfold SchemaGraph.width;lia).
 split.
 - assert (Hsize:(SchemaMarking.size root<=slots expression_cap)%nat) by (unfold SchemaMarking.size,SchemaGraph.width,slots in *;nia).
   repeat rewrite Nat2Z.inj_add in HC. lia.
 - split;[exact Hhistory|]. exact (resources native logical root actual expression_cap field_cap initialF initialB initialC
     (SchemaGraph.represented_ordered native logical Hschema) HnativeRoot Hwidth Hfields HF0 HC0 Hbounded HF HB Hfuel HC).
Qed.
End SchemaUniformBudget.
