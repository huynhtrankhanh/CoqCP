From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  SchemaEvaluation SchemaMarking SchemaRepresentation FormulaEncoding Representation ClassStorage SchemaClass
  FormulaCircuit InternReserve HashTable FormulaTopology RenameMemoClassEqual RenameMemoClassMember
  ClassLookup RenameMemoResourceBounds RenameStorage SchemaShiftClass ArenaFrame.
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
Lemma mp_arrays s raw antecedent name : name<>arraydef_0__meta ->
 memory (mp_result s raw antecedent) name=memory s name.
Proof. intro Hname. unfold mp_result. destruct (bool_decide _);now apply store_meta_other. Qed.
Lemma mp_lengths s raw antecedent name :
 length (memory (mp_result s raw antecedent) name)=length (memory s name).
Proof.
 unfold mp_result. destruct (bool_decide _);destruct (decide (name=arraydef_0__meta)) as [->|Hname];
 first [apply store_meta_length|now rewrite store_meta_other].
Qed.
Lemma mp_cell s raw antecedent cell : cell<>0%nat -> cell<>18%nat ->
 meta_value (mp_result s raw antecedent) cell=meta_value s cell.
Proof. intros Hzero Hvalid. unfold mp_result. destruct (bool_decide _);apply meta_store_other;assumption. Qed.
Lemma mp_arena s raw antecedent fs : NativeRepresentation.canonical_arena s fs ->
 NativeRepresentation.canonical_arena (mp_result s raw antecedent) fs.
Proof.
 intro Harena. unfold mp_result. destruct (bool_decide _).
 all: apply (ArenaFrame.storage_arena s);[apply ArenaFrame.storage_meta;lia|exact Harena].
Qed.
Lemma mp_classes s raw antecedent fs classes : ClassStorage.represents s fs classes ->
 ClassStorage.represents (mp_result s raw antecedent) fs classes.
Proof. unfold ClassStorage.represents. rewrite mp_cell,mp_arrays by discriminate. tauto. Qed.
Lemma mp_topology s raw antecedent count : FormulaTopology.ordered s count ->
 FormulaTopology.ordered (mp_result s raw antecedent) count.
Proof.
 intro Htop. apply (FormulaTopology.same s);[exact Htop|].
 intros parent Hparent. unfold HashTableInvariant.tuple_at. now rewrite mp_arrays by discriminate.
Qed.
Theorem generated_binary_mp (f:Frame) width remaining outer_remaining a b stride d ka kb node vb fs classes rho ci ca observations :
 nums f vardef_0__schemaInstance_kind=9 ->
 nums f vardef_0__schemaInstance_a=Z.of_nat a -> nums f vardef_0__schemaInstance_b=Z.of_nat b ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 ka=(a*stride+d)%nat -> kb=(b*stride+d)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some (Z.of_nat node) ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some vb ->
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs ->
 meaning fs classes rho d (Protocol.PE ci) (Z.of_nat node) ->
 meaning fs classes rho d (Protocol.PE ca) vb ->
 exists raw,
 execLocalObserved (binary_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine (binary_frame f (Z.of_nat node) vb) (mp_result (machine f) raw vb),observations)) /\
 match Schemata.infer rho d (Schemata.template_mp ci ca) with
 | Some result=>formula_value fs (meta_value (mp_result (machine f) raw vb) 0) result /\
    meta_value (mp_result (machine f) raw vb) 18=meta_value (machine f) 18
 | None=>meta_value (mp_result (machine f) raw vb) 18=0
 end.
Proof.
 intros Hkind Ha Hb Hstride Hd Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Harena
   [p [Hci [Hid Hp]]] [q [Hca Hq]].
 rewrite Nat2Z.id in Hp.
 pose proof Harena as [Htable [Hrep [Hunique Hnormal]]].
 assert (Hlogicalbound:(node<length fs)%nat) by (apply nth_error_Some;congruence).
 assert (Hnativebound:(node<length (memory (machine f) arraydef_0__formulas))%nat).
 { destruct Htable as [[_ [_ [_ [_ [Hcapacity _]]]]] _]. lia. }
 pose proof (NativeRepresentation.represented_lookup (machine f) fs node p Hrep Hp) as Hdecode.
 pose proof (Hnormal node Hlogicalbound) as Hrawnormal.
 destruct (HashTableInvariant.tuple_at (machine f) node) as [[tag left] right] eqn:Hraw.
 exists (tag,left,right). split.
 - eapply generated_binary_mp_raw;try eassumption;reflexivity.
 - cbn [Schemata.infer]. rewrite Hci,Hca.
   eapply mp_semantic;eassumption.
Qed.
End SchemaEvaluationBinaryMP.
