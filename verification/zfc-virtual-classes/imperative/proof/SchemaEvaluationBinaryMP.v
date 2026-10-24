From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  SchemaEvaluation SchemaMarking SchemaRepresentation FormulaEncoding Representation ClassStorage SchemaClass
  FormulaCircuit InternReserve HashTable FormulaTopology RenameMemoClassEqual RenameMemoClassMember
  ClassLookup RenameMemoResourceBounds RenameStorage SchemaShiftClass.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationBinaryMP.
Import IndexExecution SipHashExecution ObservedLocal SchemaEvaluation.
Theorem generated_binary_mp_raw (f:Frame) width remaining outer_remaining a b stride d ka kb va vb node tag left right observations :
 nums f vardef_0__schemaInstance_kind=9 ->
 nums f vardef_0__schemaInstance_a=Z.of_nat a -> nums f vardef_0__schemaInstance_b=Z.of_nat b ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 ka=(a*stride+d)%nat -> kb=(b*stride+d)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some va ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some vb ->
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 (node<length (memory (machine f) arraydef_0__formulas))%nat ->
 HashTableInvariant.tuple_at (machine f) node=(tag,left,right) -> va=Z.of_nat node ->
 execLocalObserved (binary_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine (binary_frame f va vb) (mp_result (machine f) (tag,left,right) vb),observations)).
Proof.
 intros Hkind Ha Hb Hstride Hd Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Hnode Hraw Hva.
 unfold HashTableInvariant.tuple_at in Hraw.
 assert (Hbounda:(ka<length (memory (machine f) arraydef_0__schemaValues))%nat)
   by (apply nth_error_Some;congruence).
 assert (Hboundb:(kb<length (memory (machine f) arraydef_0__schemaValues))%nat)
   by (apply nth_error_Some;congruence).
 pose proof (List.nth_error_nth _ _ 0 Hlookupa) as Hntha.
 pose proof (List.nth_error_nth _ _ 0 Hlookupb) as Hnthb.
 assert (Hmula:coerceInt (Z.of_nat a*Z.of_nat stride) 64=Z.of_nat (a*stride)).
 { rewrite <-Nat2Z.inj_mul. apply coerce_word. unfold word;lia. }
 assert (Hmulb:coerceInt (Z.of_nat b*Z.of_nat stride) 64=Z.of_nat (b*stride)).
 { rewrite <-Nat2Z.inj_mul. apply coerce_word. unfold word;lia. }
 assert (Hadda:coerceInt (Z.of_nat (a*stride)+(width-Z.of_nat remaining-1)) 64=Z.of_nat ka).
 { change (coerceInt (Z.of_nat (a*stride)+depth width remaining) 64=Z.of_nat ka).
   rewrite Hd,coerce_word by (unfold word;lia). lia. }
 assert (Haddb:coerceInt (Z.of_nat (b*stride)+(width-Z.of_nat remaining-1)) 64=Z.of_nat kb).
 { change (coerceInt (Z.of_nat (b*stride)+depth width remaining) 64=Z.of_nat kb).
   rewrite Hd,coerce_word by (unfold word;lia). lia. }
 destruct (Z.eq_dec tag 3) as [->|Htag];destruct (Z.eq_dec left vb) as [->|Hleft].
 all: destruct f as [s bs ns];cbn [machine nums] in *.
 all: unfold binary_handler,binary_frame,mp_result;cbn [fst snd].
 all: repeat first [progress cbn [optionBind fst snd bind]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |progress unfold addInt at 1|progress unfold multInt at 1
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];rewrite ?Nat2Z.id;
     first [exact Hbounda|exact Hboundb|exact Hnode|lia])
 |progress rewrite Ha|progress rewrite Hb|progress rewrite Hstride|progress rewrite Hmula|progress rewrite Hmulb
 |progress rewrite Hadda|progress rewrite Haddb|progress rewrite Nat2Z.id|progress rewrite Hraw
 |match goal with |- context [List.nth ?i ?xs ?zero]=>
    let expression:=constr:(List.nth i xs zero) in let Hsame:=fresh in first
    [assert (Hsame:expression=va) by exact Hntha|assert (Hsame:expression=vb) by exact Hnthb|assert (Hsame:expression=(tag,left,right)) by exact Hraw];rewrite Hsame;clear Hsame end
 |progress rewrite RenameMemoControl.updated_same
 |progress rewrite RenameMemoControl.updated_other by discriminate
 |progress rewrite Hkind|progress rewrite Hva
 |match goal with |- context [bool_decide ?P]=>first
    [progress rewrite (bool_decide_true P) by (cbn [fst snd];intuition congruence)|progress rewrite (bool_decide_false P) by (cbn [fst snd];intuition congruence)] end
 |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
 ]. all: reflexivity.
Qed.
End SchemaEvaluationBinaryMP.
