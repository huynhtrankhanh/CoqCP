From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Schemata VirtualClasses.
From NativeProof Require Import Index SipHash ObservedLocal AxiomCommand AxiomInvariant AxiomTaggedInvariant
 AxiomLogicalProtocol AxiomRenamingProtocol AxiomEqualityCircuits AxiomFixedCircuits AxiomRefl AxiomK
 AxiomEqualityRefinement AxiomSRefinement AxiomDNERefinement Intern InternReserve InternLengths FormulaEncoding
 Representation FormulaTopology ArenaFrame RenameMemoBounds RenameMemoIndexBounds RenameMemoTransition RenameMemoInput
 RenameMemoLengths AxiomStorage SchemaEvaluationIndexBounds SchemaEvaluationIndexCircuit
 SchemaEvaluationIndexCircuitTrace SchemaEvaluationIndexAxiomCircuits SchemaEvaluationIndexAxiomRenaming
 SchemaEvaluationIndexAxiomReplacement.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaEvaluationIndexAxiomTagged.
Import IndexExecution SipHashExecution ObservedLocal AxiomTaggedInvariant SchemaEvaluationIndexAxiomCircuits.
Definition constructed s bs ns observations fs wanted reserve allowance bound :=
  exists final next index, SchemaEvaluationIndexBounds.raw_arena final (length next) bound /\
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some wanted /\ SetTheory.derives wanted /\ (exists extra,next=fs++extra) /\
    meta_value final 8=0 /\ meta_value final 13=1 /\ FormulaTopology.ordered final (length next) /\
    Z.of_nat (length next+reserve)<=9223372036854775807 /\ (length next<=length fs+allowance)%nat /\
    AxiomStorage.logical_frame s final /\
    (forall watched,RenameMemoLengths.protected watched -> length (memory final watched)=length (memory s watched)).

Lemma strengthen s bs ns observations fs wanted reserve allowance bound final next :
 AxiomInvariant.constructed s bs ns observations fs wanted reserve allowance ->
 execObserved (funcdef_0__axiom bs ns) (s,observations)=Some(tt,(final,observations)) ->
 NativeRepresentation.canonical_arena final next ->
 SchemaEvaluationIndexBounds.raw_arena final (length next) bound ->
 constructed s bs ns observations fs wanted reserve allowance bound.
Proof.
 intros (actual & actualfs & index & Hactual & Hrest) Hrun Hnext Hraw.
 rewrite Hrun in Hactual. injection Hactual as Hsame. subst actual.
 assert (Hlength:length actualfs=length next).
 { rewrite <- (SchemaEvaluationIndexCircuitTrace.count_is_length final actualfs (proj1 Hrest)).
   exact (SchemaEvaluationIndexCircuitTrace.count_is_length final next Hnext). }
 exists final,actualfs,index. split;[rewrite Hlength;exact Hraw|exact (conj Hrun Hrest)].
Qed.
Definition ceiling bound rawI rawJ rawK := (bound+rawI+rawJ+rawK+4)%nat.
Module Reflexivity.
Import AxiomRefl.
Theorem generated_refines s bs ns fs variable reserve bound observations :
  NativeRepresentation.canonical_arena s fs -> meta_value s 8 = 0 ->
  (13 < length (memory s arraydef_0__meta))%nat -> word (Z.of_nat variable) ->
  Z.of_nat (length fs + S reserve) <= 9223372036854775807 ->
  ns vardef_0__axiom_tag = 5 -> ns vardef_0__axiom_p = Z.of_nat variable ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound -> (variable<=bound)%nat ->
  exists final next index, SchemaEvaluationIndexBounds.raw_arena final (length next) bound /\
    execObserved (funcdef_0__axiom bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (SetTheory.equal variable variable) /\
    SetTheory.derives (SetTheory.equal variable variable) /\
    (exists extra, next = fs ++ extra) /\ meta_value final 8 = 0 /\ meta_value final 13 = 1 /\
    logical_frame s final /\ Z.of_nat (length next + reserve) <= 9223372036854775807.
Proof.
  intros Harena Herror Hmeta Hvariable Hreserve Htag Hp HrawInitial HvariableBound.
  assert (Hstorage : ArenaFrame.storage s (cleared s)).
  { unfold cleared. apply ArenaFrame.storage_meta; lia. }
  assert (Hclear : NativeRepresentation.canonical_arena (cleared s) fs).
  { exact (ArenaFrame.storage_arena s (cleared s) fs Hstorage Harena). }
  assert (Hclearerror : meta_value (cleared s) 8 = 0).
  { unfold cleared. rewrite meta_store_other by discriminate. exact Herror. }
  assert (Hnormal : FormulaEncoding.normal (arguments (Z.of_nat variable) vardef_0__intern_tag,
    arguments (Z.of_nat variable) vardef_0__intern_a,arguments (Z.of_nat variable) vardef_0__intern_b)).
  { change (FormulaEncoding.normal (1,Z.of_nat variable,Z.of_nat variable)). right. left. auto. }
  assert (Hdecode : FormulaEncoding.decode fs (arguments (Z.of_nat variable) vardef_0__intern_tag,
    arguments (Z.of_nat variable) vardef_0__intern_a,arguments (Z.of_nat variable) vardef_0__intern_b) = Some (SetTheory.equal variable variable)).
  { change (Some (SetTheory.equal (Z.to_nat (Z.of_nat variable)) (Z.to_nat (Z.of_nat variable))) = Some (SetTheory.equal variable variable)). now rewrite Nat2Z.id. }
  destruct (InternReserve.generated_refines (cleared s) (fun _=>false) (arguments (Z.of_nat variable)) fs (SetTheory.equal variable variable) reserve observations
    Hclear Hclearerror Hreserve Hnormal Hdecode)
    as [built [next [index [Hrun [Hframe [Hnext [Hflag [Hindex [Hword [Hmeaning [Hextends Hremaining]]]]]]]]]]].
  destruct (InternLengths.observed_lengths (cleared s) (fun _=>false) (arguments (Z.of_nat variable)) observations built observations Hrun) as [Hlength Hsip].
  assert (Hbuilt : (13 < length (memory built arraydef_0__meta))%nat).
  { rewrite Hlength. unfold cleared. now rewrite store_meta_length. }
  assert (HrawBuilt:SchemaEvaluationIndexBounds.raw_arena built (length next) bound).
  { eapply SchemaEvaluationIndexBounds.observed_intern;[exact Hclear|exact Hclearerror| | | |exact Hrun|exact Hnext].
    - rewrite Nat2Z.inj_add in Hreserve. lia.
    - exact (storage_raw s (cleared s) (length fs) bound Hstorage HrawInitial).
    - change (RenameMemoInput.raw_bound bound (1,Z.of_nat variable,Z.of_nat variable)).
      unfold RenameMemoInput.raw_bound. intros _. rewrite Nat2Z.id. exact (conj HvariableBound HvariableBound). }
  exists (finished built),next,index. split;[exact (storage_raw built (finished built) (length next) bound (finished_storage built) HrawBuilt)|]. split.
  - eapply generated_helper; eassumption.
  - split; [exact (ArenaFrame.storage_arena built (finished built) next (finished_storage built) Hnext)|].
    split.
    + unfold finished. rewrite meta_store_other by discriminate. rewrite meta_store_same by lia. exact Hindex.
    + split; [exact Hword|]. split; [exact Hmeaning|]. split; [apply SetTheory.d_refl|]. split; [exact Hextends|].
      split.
      * unfold finished. rewrite !meta_store_other by discriminate. exact Hflag.
      * split.
        -- unfold finished. rewrite meta_store_same; [reflexivity|rewrite store_meta_length; exact Hbuilt].
        -- split; [now apply frame|exact Hremaining].
Qed.
End Reflexivity.
Theorem construct s fs tag idA idB idC rawI rawJ rawK p q r bound reserve observations :
 (tag<=17)%nat ->
 (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
 nth_error fs 0=Some SetTheory.falsity ->
 word (Z.of_nat idA) -> word (Z.of_nat idB) -> word (Z.of_nat idC) ->
 ready fs tag idA idB idC rawI rawJ rawK p q r -> renaming_ready tag idA rawJ p bound ->
 Z.of_nat (length fs+cost tag idA+reserve)<=9223372036854775807 ->
 SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
 exists witness,literal_axiom tag p q r rawI rawJ rawK=Some witness /\
 constructed s (fun _=>false)
   (AxiomCommand.arguments (Z.of_nat tag) (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC))
   observations fs (SetTheory.axiom_formula witness) reserve (cost tag idA) (ceiling bound rawI rawJ rawK).
Proof.
 intros Htag Hmeta Hsip Harena Hordered Herror Hfalse HAword HBword HCword Hready Hrename Hbudget HrawInitial.
 destruct (AxiomTaggedInvariant.construct s fs tag idA idB idC rawI rawJ rawK p q r bound reserve observations
   Htag Hmeta Hsip Harena Hordered Herror Hfalse HAword HBword HCword Hready Hrename Hbudget)
   as (witness & Hliteral & Hconstructed).
 exists witness. split;[exact Hliteral|].
 assert (HrawCeiling:SchemaEvaluationIndexBounds.raw_arena s (length fs) (ceiling bound rawI rawJ rawK)).
 { exact (SchemaEvaluationIndexBounds.raw_arena_mono s (length fs) bound (ceiling bound rawI rawJ rawK) ltac:(unfold ceiling;lia) HrawInitial). }
 let rec cases count index := lazymatch count with
   O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 18%nat tag.
 19: lia.
 all: destruct Hready as [HA [HB HC]];cbn [needs_p needs_q existsb Nat.eqb orb] in HA,HB,HC.
 - destruct (K.generated_refines s (fun _=>false) (AxiomCommand.arguments 0 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC))
 fs (Z.of_nat idA) (Z.of_nat idB) p q reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) eq_refl eq_refl eq_refl HAword HBword
 ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) Hbudget HrawCeiling)
 as (built & next & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - destruct (SRule.generated_refines s (fun _=>false) (AxiomCommand.arguments 1 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC))
 fs (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC) p q r reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) eq_refl eq_refl eq_refl eq_refl HAword HBword HCword
 ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) Hbudget HrawCeiling)
 as (built & next & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - destruct (DNE.generated_refines s (fun _=>false) (AxiomCommand.arguments 2 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC))
 fs (Z.of_nat idA) p reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) Hfalse HAword ltac:(now rewrite Nat2Z.id) Hbudget eq_refl eq_refl HrawCeiling)
 as (final & next & index & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - subst idB. destruct Hrename as [Hfuel [Hbound [Hindices Hheight]]].
 destruct (SchemaEvaluationIndexAxiomRenaming.Instantiation.generated_refines s (fun _=>false)
 (AxiomCommand.arguments 3 (Z.of_nat idA) (Z.of_nat rawJ) (Z.of_nat idC)) fs p idA rawJ bound reserve observations
 Hmeta Hsip Harena Hordered Herror HA Hfalse eq_refl eq_refl eq_refl Hfuel Hbound Hindices Hheight
 ltac:(cbn [cost] in Hbudget;lia) HrawInitial)
 as (final & next & index & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   eapply SchemaEvaluationIndexBounds.raw_arena_mono;[|exact Hraw]. unfold ceiling;lia.
 - destruct Hrename as [Hfuel [Hbound [Hindices Hheight]]].
 destruct (SchemaEvaluationIndexAxiomRenaming.Distribution.generated_refines s (fun _=>false)
 (AxiomCommand.arguments 4 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC)) fs p q idA idB bound reserve observations
 Hmeta Hsip Harena Hordered Herror HA HB Hfalse eq_refl eq_refl eq_refl Hfuel Hbound Hindices Hheight
 ltac:(cbn [cost] in Hbudget;lia) HrawInitial)
 as (built & next & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   eapply SchemaEvaluationIndexBounds.raw_arena_mono;[|exact Hraw]. unfold ceiling;lia.
 - subst idA.
 destruct (Reflexivity.generated_refines s (fun _=>false) (AxiomCommand.arguments 5 (Z.of_nat rawI) (Z.of_nat idB) (Z.of_nat idC))
 fs rawI reserve (ceiling bound rawI rawJ rawK) observations Harena Herror ltac:(lia) HAword
 ltac:(cbn [cost] in Hbudget;lia) eq_refl eq_refl HrawCeiling ltac:(unfold ceiling;lia))
 as (final & next & index & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - subst idA idB idC.
 destruct (Equality.generated_refines AxiomEqualityCircuits.member_left s (fun _=>false)
 (AxiomCommand.arguments 6 (Z.of_nat rawI) (Z.of_nat rawJ) (Z.of_nat rawK)) fs rawI rawJ rawK reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) eq_refl eq_refl eq_refl eq_refl HAword HBword HCword Hbudget HrawCeiling
 ltac:(unfold AxiomEqualityCircuits.plan,AxiomEqualityCircuits.left_op,AxiomEqualityCircuits.right_op;repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];unfold ceiling;lia))
 as (built & next & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - subst idA idB idC.
 destruct (Equality.generated_refines AxiomEqualityCircuits.member_right s (fun _=>false)
 (AxiomCommand.arguments 7 (Z.of_nat rawI) (Z.of_nat rawJ) (Z.of_nat rawK)) fs rawI rawJ rawK reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) eq_refl eq_refl eq_refl eq_refl HAword HBword HCword Hbudget HrawCeiling
 ltac:(unfold AxiomEqualityCircuits.plan,AxiomEqualityCircuits.left_op,AxiomEqualityCircuits.right_op;repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];unfold ceiling;lia))
 as (built & next & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - subst idA idB idC.
 destruct (Equality.generated_refines AxiomEqualityCircuits.equal_trans s (fun _=>false)
 (AxiomCommand.arguments 8 (Z.of_nat rawI) (Z.of_nat rawJ) (Z.of_nat rawK)) fs rawI rawJ rawK reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) eq_refl eq_refl eq_refl eq_refl HAword HBword HCword Hbudget HrawCeiling
 ltac:(unfold AxiomEqualityCircuits.plan,AxiomEqualityCircuits.left_op,AxiomEqualityCircuits.right_op;repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];unfold ceiling;lia))
 as (built & next & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - destruct (Fixed.generated_refines AxiomFixedCircuits.extensionality s (fun _=>false)
 (AxiomCommand.arguments 9 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC)) fs reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) Hfalse Hbudget eq_refl HrawCeiling
 ltac:(cbn [AxiomFixedCircuits.plan];repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];unfold ceiling;lia))
 as (final & next & index & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - destruct (Fixed.generated_refines AxiomFixedCircuits.foundation s (fun _=>false)
 (AxiomCommand.arguments 10 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC)) fs reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) Hfalse Hbudget eq_refl HrawCeiling
 ltac:(cbn [AxiomFixedCircuits.plan];repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];unfold ceiling;lia))
 as (final & next & index & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - destruct (Fixed.generated_refines AxiomFixedCircuits.pairing s (fun _=>false)
 (AxiomCommand.arguments 11 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC)) fs reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) Hfalse Hbudget eq_refl HrawCeiling
 ltac:(cbn [AxiomFixedCircuits.plan];repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];unfold ceiling;lia))
 as (final & next & index & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - destruct (Fixed.generated_refines AxiomFixedCircuits.union s (fun _=>false)
 (AxiomCommand.arguments 12 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC)) fs reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) Hfalse Hbudget eq_refl HrawCeiling
 ltac:(cbn [AxiomFixedCircuits.plan];repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];unfold ceiling;lia))
 as (final & next & index & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - destruct (Fixed.generated_refines AxiomFixedCircuits.power s (fun _=>false)
 (AxiomCommand.arguments 13 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC)) fs reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) Hfalse Hbudget eq_refl HrawCeiling
 ltac:(cbn [AxiomFixedCircuits.plan];repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];unfold ceiling;lia))
 as (final & next & index & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - destruct (Fixed.generated_refines AxiomFixedCircuits.infinity s (fun _=>false)
 (AxiomCommand.arguments 14 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC)) fs reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) Hfalse Hbudget eq_refl HrawCeiling
 ltac:(cbn [AxiomFixedCircuits.plan];repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];unfold ceiling;lia))
 as (final & next & index & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
 - destruct Hrename as [Hfuel [Hbound [Hindices Hheight]]].
 destruct (SchemaEvaluationIndexAxiomRenaming.Separation.generated_refines s (fun _=>false)
 (AxiomCommand.arguments 15 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC)) fs p idA bound reserve observations
 Hmeta Hsip Harena Hordered Herror HA Hfalse eq_refl eq_refl Hfuel Hbound Hindices Hheight
 ltac:(cbn [cost] in Hbudget;lia) HrawInitial)
 as (built & next & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   eapply SchemaEvaluationIndexBounds.raw_arena_mono;[|exact Hraw]. unfold ceiling;lia.
 - destruct Hrename as [Hfuel [Hbound [Hindices Hheight]]].
 destruct (SchemaEvaluationIndexAxiomReplacement.generated_refines s (fun _=>false)
 (AxiomCommand.arguments 16 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC)) fs p idA bound reserve observations
 Hmeta Hsip Harena Hordered Herror HA Hfalse eq_refl eq_refl Hfuel Hbound Hindices Hheight
 ltac:(cbn [cost] in Hbudget;lia) HrawInitial)
 as (built & next & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   eapply SchemaEvaluationIndexBounds.raw_arena_mono;[|exact Hraw]. unfold ceiling;lia.
 - destruct (Fixed.generated_refines AxiomFixedCircuits.choice s (fun _=>false)
 (AxiomCommand.arguments 17 (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC)) fs reserve (ceiling bound rawI rawJ rawK) observations
 Harena Hordered Herror ltac:(lia) Hfalse Hbudget eq_refl HrawCeiling
 ltac:(cbn [AxiomFixedCircuits.plan];repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];unfold ceiling;lia))
 as (final & next & index & Hraw & Hrun & Hnext & Hrest).
   eapply strengthen;[exact Hconstructed|exact Hrun|exact Hnext|].
   exact Hraw.
Qed.
End SchemaEvaluationIndexAxiomTagged.
