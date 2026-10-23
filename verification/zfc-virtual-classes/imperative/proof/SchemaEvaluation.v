From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  SchemaMarking SchemaRepresentation FormulaEncoding Representation ClassStorage SchemaClass
  FormulaCircuit InternReserve HashTable FormulaTopology RenameMemoClassEqual RenameMemoClassMember
  ClassLookup RenameMemoResourceBounds RenameStorage SchemaShiftClass.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluation.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := SchemaMarking.Frame.
Definition LocalAction := SchemaMarking.LocalAction.
Definition LoopAction R := Action (WithinLoop arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) withinLoopReturnValue R.
Definition outer_body width remaining : LocalAction LoopOutcome := ltac:(
 let code:=eval unfold SchemaMarking.evaluation in SchemaMarking.evaluation in
 lazymatch code with bind ?first _=>lazymatch first with bind _ ?next=>
 let code:=eval cbn beta in (next width) in lazymatch code with loop _ ?body=>exact (body remaining) end end end).
Definition inner_body width remaining outer_remaining : LocalAction LoopOutcome := ltac:(
 let code:=eval cbv beta iota zeta delta [outer_body] in (outer_body width outer_remaining) in
 lazymatch code with dropWithinLoop ?code=>
 let code:=SchemaMarking.drop_statements 1%nat code in
 lazymatch code with bind (liftToWithinLoop (bind _ ?next)) _=>
 let code:=eval cbn beta in (next width) in
 lazymatch code with loop _ ?body=>exact (body remaining) end end end).
Definition marked_body width remaining outer_remaining : LoopAction unit := ltac:(
 let code:=eval cbv beta iota zeta delta [inner_body outer_body] in (inner_body width remaining outer_remaining) in
 multimatch code with context [bind (liftToWithinLoop ?condition) ?branch]=>
 lazymatch condition with context [retrieve _ _ _ arraydef_0__schemaMarks _]=>
 exact (branch true) end end).
Definition compute_body width remaining outer_remaining : LoopAction unit := ltac:(
 let code:=eval cbv beta iota zeta delta [marked_body inner_body outer_body] in (marked_body width remaining outer_remaining) in
 let code:=SchemaMarking.drop_statements 5%nat code in exact code).
Ltac select_statement width remaining outer_remaining position :=
 let code:=eval cbv beta iota zeta delta [compute_body marked_body inner_body outer_body] in (compute_body width remaining outer_remaining) in
 let code:=SchemaMarking.drop_statements position code in lazymatch code with bind ?first _=>first end.
Ltac selected_handler width remaining outer_remaining position :=
 let code:=select_statement width remaining outer_remaining position in
 lazymatch code with bind _ ?branch=>exact (dropWithinLoop (branch true)) end.
Definition meta_handler width remaining outer_remaining : LocalAction LoopOutcome := ltac:(selected_handler width remaining outer_remaining 0%nat).
Definition literal_handler width remaining outer_remaining : LocalAction LoopOutcome := ltac:(selected_handler width remaining outer_remaining 1%nat).
Definition abstract_handler width remaining outer_remaining : LocalAction LoopOutcome := ltac:(selected_handler width remaining outer_remaining 2%nat).
Definition binary_handler width remaining outer_remaining : LocalAction LoopOutcome := ltac:(selected_handler width remaining outer_remaining 3%nat).
Definition all_handler width remaining outer_remaining : LocalAction LoopOutcome := ltac:(selected_handler width remaining outer_remaining 4%nat).
Definition axiom_handler width remaining outer_remaining : LocalAction LoopOutcome := ltac:(selected_handler width remaining outer_remaining 5%nat).
Definition output_handler width remaining outer_remaining : LocalAction LoopOutcome := ltac:(
 let code:=select_statement width remaining outer_remaining 6%nat in exact (dropWithinLoop code)).

Definition binary_branches width remaining outer_remaining : LoopAction unit := ltac:(
 let code:=select_statement width remaining outer_remaining 3%nat in
 lazymatch code with bind _ ?branch=>
 let code:=eval cbn beta iota in (branch true) in
 let code:=SchemaMarking.drop_statements 2%nat code in exact code end).
Ltac binary_selected width remaining outer_remaining position :=
 let code:=eval cbv beta iota zeta delta [binary_branches] in (binary_branches width remaining outer_remaining) in
 let code:=SchemaMarking.drop_statements position code in
 lazymatch code with bind ?first _=>lazymatch first with bind _ ?branch=>exact (dropWithinLoop (branch true)) end end.
Definition equal_handler width remaining outer_remaining : LocalAction LoopOutcome := ltac:(binary_selected width remaining outer_remaining 0%nat).
Definition member_handler width remaining outer_remaining : LocalAction LoopOutcome := ltac:(binary_selected width remaining outer_remaining 1%nat).
Definition imp_handler width remaining outer_remaining : LocalAction LoopOutcome := ltac:(binary_selected width remaining outer_remaining 2%nat).
Definition mp_handler width remaining outer_remaining : LocalAction LoopOutcome := ltac:(binary_selected width remaining outer_remaining 3%nat).
Definition binary_frame (f:Frame) va vb := setNum (setNum f vardef_0__schemaInstance_va va) vardef_0__schemaInstance_vb vb.
Definition depth width remaining := width-Z.of_nat remaining-1.
Definition value (s:Machine) key := List.nth key (memory s arraydef_0__schemaValues) 0.
Definition formula_value (fs:list SetTheory.formula) id p := word id /\ nth_error fs (Z.to_nat id)=Some p.
Definition class_value (classes:list VirtualClasses.class) id cls := word id /\ nth_error classes (Z.to_nat id)=Some cls.
Definition meaning fs classes rho depth expression id := match expression with
| Protocol.CE c => class_value classes id (Schemata.instantiate_class rho depth c)
| Protocol.FE p => formula_value fs id (Schemata.instantiate_formula rho depth p)
| Protocol.PE p => exists result, Schemata.infer rho depth p=Some result /\ formula_value fs id result
end.
Local Opaque Imperative.update funcdef_0__intern funcdef_0__schemaClass funcdef_0__classEqual funcdef_0__classMember.
Theorem generated_literal (f:Frame) width remaining outer_remaining observations :
 (0<length (memory (machine f) arraydef_0__meta))%nat ->
 execLocalObserved (literal_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f (store_meta (machine f) 0 (nums f vardef_0__schemaInstance_a)),observations)).
Proof.
 intro Hmeta. unfold literal_handler.
 repeat first [progress cbn [optionBind fst snd]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine];lia)
 |progress cbn [dropWithinLoop Action_rect bind]]. reflexivity.
Qed.
Lemma literal_class_semantic fs classes rho depth id cls : class_value classes id cls ->
 meaning fs classes rho depth (Protocol.CE (Schemata.literal_class cls)) id.
Proof. exact (fun H=>H). Qed.
Lemma literal_formula_semantic fs classes rho depth id p : formula_value fs id p ->
 meaning fs classes rho depth (Protocol.FE (Schemata.literal_formula p)) id.
Proof. exact (fun H=>H). Qed.
Lemma saved_semantic fs classes rho depth id p checked : formula_value fs id p ->
 meaning fs classes rho depth (Protocol.PE (Schemata.saved_theorem p checked)) id.
Proof. intro H. exists p. split;[reflexivity|exact H]. Qed.

Theorem generated_all_helper (f:Frame) width remaining outer_remaining a stride d key id final observations :
 nums f vardef_0__schemaInstance_a=Z.of_nat a ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 key=(a*stride+d+1)%nat -> Z.of_nat key<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) key=Some id ->
 execObserved (funcdef_0__intern (fun _=>false) (FormulaCircuit.arguments 4 id 0))
   (machine f,observations)=Some (tt,(final,observations)) ->
 execLocalObserved (all_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)).
Proof.
 intros Ha Hstride Hd Hkey Hword Hlookup Hrun.
 assert (Hbound:(key<length (memory (machine f) arraydef_0__schemaValues))%nat)
   by (apply nth_error_Some;congruence).
 pose proof (List.nth_error_nth _ _ 0 Hlookup) as Hnth.
 assert (Hmul:coerceInt (Z.of_nat a*Z.of_nat stride) 64=Z.of_nat (a*stride)).
 { rewrite <-Nat2Z.inj_mul. apply coerce_word. unfold word;lia. }
 assert (Hadd:coerceInt (Z.of_nat (a*stride)+(width-Z.of_nat remaining-1)) 64=Z.of_nat (a*stride+d)).
 { change (coerceInt (Z.of_nat (a*stride)+depth width remaining) 64=Z.of_nat (a*stride+d)).
   rewrite Hd,<-Nat2Z.inj_add. apply coerce_word. unfold word;lia. }
 assert (Hnext:coerceInt (Z.of_nat (a*stride+d)+1) 64=Z.of_nat key).
 { rewrite coerce_word by (unfold word;lia). lia. }
 unfold all_handler.
 repeat first [progress cbn [optionBind fst snd]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |progress unfold addInt at 1|progress unfold multInt at 1
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine];rewrite ?Nat2Z.id;exact Hbound)
 |progress rewrite Ha|progress rewrite Hstride|progress rewrite Hmul|progress rewrite Hadd|progress rewrite Hnext
 |progress rewrite Nat2Z.id
 |match goal with |- context [List.nth ?i ?xs ?zero]=>
    let expression:=constr:(List.nth i xs zero) in
    let Hsame:=fresh in assert (Hsame:expression=id) by exact Hnth;rewrite Hsame;clear Hsame end
 |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(final,observations))) by exact Hrun;rewrite Hsame;clear Hsame end
 |progress cbn [dropWithinLoop Action_rect bind]]. reflexivity.
Qed.
Theorem generated_abstract_helper (f:Frame) width remaining outer_remaining a stride d key id final observations :
 nums f vardef_0__schemaInstance_a=Z.of_nat a ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 key=(a*stride+d+1)%nat -> Z.of_nat key<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) key=Some id ->
 execObserved (funcdef_0__schemaClass (fun _=>false) (SchemaClass.arguments 1 id))
   (machine f,observations)=Some (tt,(final,observations)) ->
 execLocalObserved (abstract_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)).
Proof.
 intros Ha Hstride Hd Hkey Hword Hlookup Hrun.
 assert (Hbound:(key<length (memory (machine f) arraydef_0__schemaValues))%nat)
   by (apply nth_error_Some;congruence).
 pose proof (List.nth_error_nth _ _ 0 Hlookup) as Hnth.
 assert (Hmul:coerceInt (Z.of_nat a*Z.of_nat stride) 64=Z.of_nat (a*stride)).
 { rewrite <-Nat2Z.inj_mul. apply coerce_word. unfold word;lia. }
 assert (Hadd:coerceInt (Z.of_nat (a*stride)+(width-Z.of_nat remaining-1)) 64=Z.of_nat (a*stride+d)).
 { change (coerceInt (Z.of_nat (a*stride)+depth width remaining) 64=Z.of_nat (a*stride+d)).
   rewrite Hd,<-Nat2Z.inj_add. apply coerce_word. unfold word;lia. }
 assert (Hnext:coerceInt (Z.of_nat (a*stride+d)+1) 64=Z.of_nat key).
 { rewrite coerce_word by (unfold word;lia). lia. }
 unfold abstract_handler.
 repeat first [progress cbn [optionBind fst snd]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |progress unfold addInt at 1|progress unfold multInt at 1
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine];rewrite ?Nat2Z.id;exact Hbound)
 |progress rewrite Ha|progress rewrite Hstride|progress rewrite Hmul|progress rewrite Hadd|progress rewrite Hnext
 |progress rewrite Nat2Z.id
 |match goal with |- context [List.nth ?i ?xs ?zero]=>
    let expression:=constr:(List.nth i xs zero) in
    let Hsame:=fresh in assert (Hsame:expression=id) by exact Hnth;rewrite Hsame;clear Hsame end
 |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__schemaClass ?bi ?ni) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__schemaClass bi ni) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(final,observations))) by exact Hrun;rewrite Hsame;clear Hsame end
 |progress cbn [dropWithinLoop Action_rect bind]]. reflexivity.
Qed.

Theorem generated_all_formula (f:Frame) width remaining outer_remaining a stride d key id fs classes rho p reserve observations :
 nums f vardef_0__schemaInstance_a=Z.of_nat a ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 key=(a*stride+d+1)%nat -> Z.of_nat key<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) key=Some id ->
 NativeRepresentation.canonical_arena (machine f) fs -> meta_value (machine f) 8=0 ->
 formula_value fs id (Schemata.instantiate_formula rho (S d) p) ->
 Z.of_nat (length fs+S reserve)<=9223372036854775807 ->
 exists final next, execLocalObserved (all_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)) /\
 NativeRepresentation.canonical_arena final next /\ meta_value final 8=0 /\
 meaning next classes rho d (Protocol.FE (Schemata.template_all p)) (meta_value final 0) /\
 (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807.
Proof.
 intros Ha Hstride Hd Hkey Hword Hlookup Harena Herror [Hid Hmeaning] Hbudget.
 assert (Hnormal:FormulaEncoding.normal (4,id,0)) by (right;right;auto).
 assert (Hdecode:FormulaEncoding.decode fs (4,id,0)=Some (SetTheory.all (Schemata.instantiate_formula rho (S d) p))).
 { cbn [FormulaEncoding.decode]. now rewrite Hmeaning. }
 destruct (InternReserve.generated_refines (machine f) (fun _=>false) (FormulaCircuit.arguments 4 id 0) fs
   (SetTheory.all (Schemata.instantiate_formula rho (S d) p)) reserve observations Harena Herror Hbudget Hnormal Hdecode)
 as [final [next [index [Hrun [Hframe [Hnext [Hflag [Hindex [Hindexword [Hresult [Hprefix Hroom]]]]]]]]]]].
 exists final,next. split.
 - eapply generated_all_helper; eassumption.
 - split;[exact Hnext|]. split;[exact Hflag|]. split.
   + change (formula_value next (meta_value final 0) (SetTheory.all (Schemata.instantiate_formula rho (S d) p))).
     rewrite Hindex. split;[exact Hindexword|]. now rewrite Nat2Z.id.
   + split;assumption.
Qed.
Theorem generated_abstract (f:Frame) width remaining outer_remaining a stride d key id fs classes rho p reserve observations :
 nums f vardef_0__schemaInstance_a=Z.of_nat a ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 key=(a*stride+d+1)%nat -> Z.of_nat key<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) key=Some id ->
 (8<length (memory (machine f) arraydef_0__meta))%nat -> ClassStorage.represents (machine f) fs classes ->
 formula_value fs id (Schemata.instantiate_formula rho (S d) p) ->
 Z.of_nat (length classes+S reserve)<=maximum ->
 exists final, execLocalObserved (abstract_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)) /\
 ClassStorage.represents final fs (classes++[Schemata.instantiate_class rho d (Schemata.template_abstract p)]) /\
 meaning fs (classes++[Schemata.instantiate_class rho d (Schemata.template_abstract p)]) rho d
 (Protocol.CE (Schemata.template_abstract p)) (meta_value final 0) /\
 Z.of_nat (length (classes++[Schemata.instantiate_class rho d (Schemata.template_abstract p)])+reserve)<=maximum.
Proof.
 intros Ha Hstride Hd Hkey Hword Hlookup Hmeta Hclasses [Hid Hmeaning] Hbudget.
 assert (Hdecode:ClassStorage.decode fs (1,id)=Some (Schemata.instantiate_class rho d (Schemata.template_abstract p))).
 { cbn [ClassStorage.decode Schemata.instantiate_class]. now rewrite Hmeaning. }
 destruct (SchemaClass.generated_refines (machine f) (fun _=>false) (SchemaClass.arguments 1 id) fs classes 1 id
   (Schemata.instantiate_class rho d (Schemata.template_abstract p)) reserve observations Hmeta Hclasses eq_refl eq_refl Hdecode Hbudget)
 as [Hrun [Hnext [Hindex Hroom]]].
 exists (SchemaClass.result (machine f) (length classes) (1,id)). split.
 - eapply generated_abstract_helper; eassumption.
 - split;[exact Hnext|]. split;[|exact Hroom].
   change (class_value (classes++[Schemata.instantiate_class rho d (Schemata.template_abstract p)])
    (meta_value (SchemaClass.result (machine f) (length classes) (1,id)) 0)
    (Schemata.instantiate_class rho d (Schemata.template_abstract p))).
   unfold class_value.
   match goal with |- context [meta_value ?state 0]=>
     let Hsame:=fresh in assert (Hsame:meta_value state 0=Z.of_nat (length classes)) by exact Hindex;
     rewrite Hsame;clear Hsame end.
   split;[unfold word;lia|]. rewrite Nat2Z.id,nth_error_app2 by lia. now rewrite Nat.sub_diag.
Qed.

Theorem generated_imp_helper (f:Frame) width remaining outer_remaining final observations :
 execObserved (funcdef_0__intern (fun _=>false) (FormulaCircuit.arguments 3
   (nums f vardef_0__schemaInstance_va) (nums f vardef_0__schemaInstance_vb)))
   (machine f,observations)=Some (tt,(final,observations)) ->
 execLocalObserved (imp_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)).
Proof.
 intro Hrun. unfold imp_handler.
 repeat first [progress cbn [optionBind fst snd]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |NativePrimitives.primitive ltac:(fun frame name slot=>lia)
 |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(final,observations))) by exact Hrun;rewrite Hsame;clear Hsame end
 |progress cbn [dropWithinLoop Action_rect bind]]. reflexivity.
Qed.
Theorem generated_imp (f:Frame) width remaining outer_remaining fs classes rho d p q reserve observations :
 NativeRepresentation.canonical_arena (machine f) fs -> meta_value (machine f) 8=0 ->
 formula_value fs (nums f vardef_0__schemaInstance_va) (Schemata.instantiate_formula rho d p) ->
 formula_value fs (nums f vardef_0__schemaInstance_vb) (Schemata.instantiate_formula rho d q) ->
 Z.of_nat (length fs+S reserve)<=9223372036854775807 ->
 exists final next, execLocalObserved (imp_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)) /\
 NativeRepresentation.canonical_arena final next /\ meta_value final 8=0 /\
 meaning next classes rho d (Protocol.FE (Schemata.template_imp p q)) (meta_value final 0) /\
 (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807.
Proof.
 intros Harena Herror [Hleft Hpleft] [Hright Hpright] Hbudget.
 assert (Hnormal:FormulaEncoding.normal (3,nums f vardef_0__schemaInstance_va,nums f vardef_0__schemaInstance_vb)) by (right;left;auto).
 assert (Hdecode:FormulaEncoding.decode fs (3,nums f vardef_0__schemaInstance_va,nums f vardef_0__schemaInstance_vb)=
   Some (SetTheory.implies (Schemata.instantiate_formula rho d p) (Schemata.instantiate_formula rho d q))).
 { cbn [FormulaEncoding.decode]. now rewrite Hpleft,Hpright. }
 destruct (InternReserve.generated_refines (machine f) (fun _=>false)
   (FormulaCircuit.arguments 3 (nums f vardef_0__schemaInstance_va) (nums f vardef_0__schemaInstance_vb)) fs
   (SetTheory.implies (Schemata.instantiate_formula rho d p) (Schemata.instantiate_formula rho d q)) reserve observations
   Harena Herror Hbudget Hnormal Hdecode)
 as [final [next [index [Hrun [Hframe [Hnext [Hflag [Hindex [Hindexword [Hresult [Hprefix Hroom]]]]]]]]]]].
 exists final,next. split;[apply generated_imp_helper;exact Hrun|].
 split;[exact Hnext|]. split;[exact Hflag|]. split.
 - change (formula_value next (meta_value final 0)
   (SetTheory.implies (Schemata.instantiate_formula rho d p) (Schemata.instantiate_formula rho d q))).
   rewrite Hindex. split;[exact Hindexword|]. now rewrite Nat2Z.id.
 - split;assumption.
Qed.

Definition mp_result s (raw:Z*Z*Z) antecedent :=
 if bool_decide (fst (fst raw)=3 /\ snd (fst raw)=antecedent)
 then store_meta s 0 (snd raw) else store_meta s 18 0.
Theorem generated_mp_raw (f:Frame) width remaining outer_remaining node tag left right antecedent observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 (node<length (memory (machine f) arraydef_0__formulas))%nat ->
 HashTableInvariant.tuple_at (machine f) node=(tag,left,right) ->
 nums f vardef_0__schemaInstance_va=Z.of_nat node -> nums f vardef_0__schemaInstance_vb=antecedent ->
 execLocalObserved (mp_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f (mp_result (machine f) (tag,left,right) antecedent),observations)).
Proof.
 intros Hmeta Hnode Hraw Hva Hvb. unfold HashTableInvariant.tuple_at in Hraw.
 destruct (Z.eq_dec tag 3) as [->|Htag];destruct (Z.eq_dec left antecedent) as [->|Hleft];
 unfold mp_handler,mp_result;cbn [fst snd];
 repeat first [progress cbn [optionBind fst snd]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine];rewrite ?Nat2Z.id;
     first [exact Hnode|lia])
 |progress rewrite Hva|progress rewrite Hvb|progress rewrite Nat2Z.id
 |match goal with |- context [List.nth ?i ?xs ?zero]=>
    let expression:=constr:(List.nth i xs zero) in
    let Hsame:=fresh in assert (Hsame:expression=(tag,left,right)) by exact Hraw;rewrite Hsame;clear Hsame end
 |progress rewrite Hraw
 |match goal with |- context [bool_decide ?P]=>first
    [progress rewrite (bool_decide_true P) by (cbn [fst snd];tauto)
    |progress rewrite (bool_decide_false P) by (cbn [fst snd];intuition congruence)] end
 |progress cbn [dropWithinLoop Action_rect bind]].
 all: reflexivity.
Qed.
Lemma mp_decode fs raw antecedent p q : FormulaEncoding.unique fs -> FormulaEncoding.normal raw ->
 FormulaEncoding.decode fs raw=Some p -> formula_value fs antecedent q ->
 (match p with SetTheory.implies a b =>
    if SetTheory.formula_eqb a q then Some b else None | _=>None end)=
 if bool_decide (fst (fst raw)=3 /\ snd (fst raw)=antecedent)
 then nth_error fs (Z.to_nat (snd raw)) else None.
Proof.
 intros Hunique Hnormal Hdecode [Hword Hq].
 destruct raw as [[tag left] right]. cbn [fst snd].
 destruct (Z.eq_dec tag 3) as [->|Htag].
 - unfold FormulaEncoding.decode in Hdecode.
   repeat match goal with H:context[Z.eq_dec ?x ?y] |- _=>destruct (Z.eq_dec x y);try lia end.
   destruct (nth_error fs (Z.to_nat left)) as [a|] eqn:Ha;[|discriminate].
   destruct (nth_error fs (Z.to_nat right)) as [b|] eqn:Hb;[|discriminate].
   injection Hdecode as <-. cbn.
   assert (Hleftword:word left).
   { unfold FormulaEncoding.normal in Hnormal. destruct Hnormal as [[Hbad _]|[[Htag [Hl Hr]]|[Hbad _]]];try lia;exact Hl. }
   pose proof (FormulaEncoding.formula_id_equality fs left antecedent a q Hunique Hleftword Hword Ha Hq) as Hequal.
   unfold SetTheory.formula_eqb. destruct (SetTheory.formula_eq_dec a q) as [Heq|Hneq].
   + rewrite bool_decide_true by intuition. reflexivity.
   + rewrite bool_decide_false by intuition. reflexivity.
 - rewrite bool_decide_false by tauto.
   unfold FormulaEncoding.normal in Hnormal.
   destruct Hnormal as [[-> [-> ->]]|[[Htags [Hl Hr]]|[-> [Hl ->]]]].
   + cbn [FormulaEncoding.decode] in Hdecode. now injection Hdecode as <-.
   + destruct Htags as [->|[->|Hbad]];[| |contradiction];cbn [FormulaEncoding.decode] in Hdecode;
       injection Hdecode as <-;reflexivity.
   + cbn [FormulaEncoding.decode] in Hdecode. destruct (nth_error fs (Z.to_nat left));[|discriminate].
     injection Hdecode as <-. reflexivity.
Qed.

Lemma mp_semantic s fs raw antecedent p q :
 (18<length (memory s arraydef_0__meta))%nat ->
 FormulaEncoding.unique fs -> FormulaEncoding.normal raw -> FormulaEncoding.decode fs raw=Some p ->
 formula_value fs antecedent q ->
 match (match p with SetTheory.implies a b =>
   if SetTheory.formula_eqb a q then Some b else None | _=>None end) with
 | Some result=>formula_value fs (meta_value (mp_result s raw antecedent) 0) result /\
    meta_value (mp_result s raw antecedent) 18=meta_value s 18
 | None=>meta_value (mp_result s raw antecedent) 18=0
 end.
Proof.
 intros Hmeta Hunique Hnormal Hdecode Hq.
 pose proof (mp_decode fs raw antecedent p q Hunique Hnormal Hdecode Hq) as Hinfer.
 rewrite Hinfer. unfold mp_result.
 destruct (bool_decide (fst (fst raw)=3 /\ snd (fst raw)=antecedent)) eqn:Haccept.
 - apply bool_decide_eq_true in Haccept. destruct raw as [[tag left] right]. cbn [fst snd] in Haccept|-*.
   destruct Haccept as [-> ->].
   assert (Hrightword:word right).
   { unfold FormulaEncoding.normal in Hnormal. destruct Hnormal as [[Hbad _]|[[Htags [Hl Hr]]|[Hbad _]]];try lia;exact Hr. }
   cbn [FormulaEncoding.decode] in Hdecode.
   destruct (nth_error fs (Z.to_nat antecedent)) as [a|];[|discriminate].
   destruct (nth_error fs (Z.to_nat right)) as [b|] eqn:Hb;[|discriminate].
   split;[unfold formula_value;rewrite meta_store_same by lia;auto|]. apply meta_store_other;lia.
 - apply meta_store_same;lia.
Qed.
Theorem generated_mp (f:Frame) width remaining outer_remaining node fs classes rho d ci ca observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 (node<length (memory (machine f) arraydef_0__formulas))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs ->
 nums f vardef_0__schemaInstance_va=Z.of_nat node ->
 meaning fs classes rho d (Protocol.PE ci) (Z.of_nat node) ->
 meaning fs classes rho d (Protocol.PE ca) (nums f vardef_0__schemaInstance_vb) ->
 exists final,execLocalObserved (mp_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)) /\
 match Schemata.infer rho d (Schemata.template_mp ci ca) with
 | Some result=>formula_value fs (meta_value final 0) result /\ meta_value final 18=meta_value (machine f) 18
 | None=>meta_value final 18=0
 end.
Proof.
 intros Hmeta Hnode [Htable [Hrep [Hunique Hnormal]]] Hva [p [Hci [Hid Hp]]] [q [Hca Hq]].
 rewrite Nat2Z.id in Hp.
 pose proof (NativeRepresentation.represented_lookup (machine f) fs node p Hrep Hp) as Hdecode.
 assert (Hlogicalbound:(node<length fs)%nat) by (apply nth_error_Some;congruence).
 pose proof (Hnormal node Hlogicalbound) as Hrawnormal.
 destruct (HashTableInvariant.tuple_at (machine f) node) as [[tag left] right] eqn:Hraw.
 exists (mp_result (machine f) (tag,left,right) (nums f vardef_0__schemaInstance_vb)). split.
 - eapply generated_mp_raw;try eassumption;reflexivity.
 - cbn [Schemata.infer]. rewrite Hci,Hca.
   eapply mp_semantic;eassumption.
Qed.

Theorem generated_binary_imp_helper (f:Frame) width remaining outer_remaining a b stride d ka kb va vb final observations :
 nums f vardef_0__schemaInstance_kind=6 ->
 nums f vardef_0__schemaInstance_a=Z.of_nat a -> nums f vardef_0__schemaInstance_b=Z.of_nat b ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 ka=(a*stride+d)%nat -> kb=(b*stride+d)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some va ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some vb ->
 execObserved (funcdef_0__intern (fun _=>false) (FormulaCircuit.arguments 3 va vb))
   (machine f,observations)=Some (tt,(final,observations)) ->
 execLocalObserved (binary_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine (binary_frame f va vb) final,observations)).
Proof.
 intros Hkind Ha Hb Hstride Hd Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hrun.
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
 destruct f as [s bs ns]. cbn [machine nums] in *.
 unfold binary_handler,binary_frame.
 repeat first [progress cbn [optionBind fst snd bind]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |progress unfold addInt at 1|progress unfold multInt at 1
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];rewrite ?Nat2Z.id;
     first [exact Hbounda|exact Hboundb])
 |progress rewrite Ha|progress rewrite Hb|progress rewrite Hstride|progress rewrite Hmula|progress rewrite Hmulb
 |progress rewrite Hadda|progress rewrite Haddb|progress rewrite Nat2Z.id
 |match goal with |- context [List.nth ?i ?xs ?zero]=>
    let expression:=constr:(List.nth i xs zero) in let Hsame:=fresh in first
    [assert (Hsame:expression=va) by exact Hntha|assert (Hsame:expression=vb) by exact Hnthb];rewrite Hsame;clear Hsame end
 |progress rewrite RenameMemoControl.updated_same
 |progress rewrite RenameMemoControl.updated_other by discriminate
 |progress rewrite Hkind
 |match goal with |- context [bool_decide ?P]=>first
    [progress rewrite (bool_decide_true P) by reflexivity|progress rewrite (bool_decide_false P) by congruence] end
 |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(final,observations))) by exact Hrun;rewrite Hsame;clear Hsame end
 |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
 ]. reflexivity.
Qed.
Theorem generated_binary_equal_helper (f:Frame) width remaining outer_remaining a b stride d ka kb va vb final observations :
 nums f vardef_0__schemaInstance_kind=4 ->
 nums f vardef_0__schemaInstance_a=Z.of_nat a -> nums f vardef_0__schemaInstance_b=Z.of_nat b ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 ka=(a*stride+d)%nat -> kb=(b*stride+d)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some va ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some vb ->
 execObserved (funcdef_0__classEqual (fun _=>false) (update (update (fun _=>0) vardef_0__classEqual_a va) vardef_0__classEqual_b vb))
   (machine f,observations)=Some (tt,(final,observations)) ->
 execLocalObserved (binary_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine (binary_frame f va vb) final,observations)).
Proof.
 intros Hkind Ha Hb Hstride Hd Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hrun.
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
 destruct f as [s bs ns]. cbn [machine nums] in *.
 unfold binary_handler,binary_frame.
 repeat first [progress cbn [optionBind fst snd bind]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |progress unfold addInt at 1|progress unfold multInt at 1
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];rewrite ?Nat2Z.id;
     first [exact Hbounda|exact Hboundb])
 |progress rewrite Ha|progress rewrite Hb|progress rewrite Hstride|progress rewrite Hmula|progress rewrite Hmulb
 |progress rewrite Hadda|progress rewrite Haddb|progress rewrite Nat2Z.id
 |match goal with |- context [List.nth ?i ?xs ?zero]=>
    let expression:=constr:(List.nth i xs zero) in let Hsame:=fresh in first
    [assert (Hsame:expression=va) by exact Hntha|assert (Hsame:expression=vb) by exact Hnthb];rewrite Hsame;clear Hsame end
 |progress rewrite RenameMemoControl.updated_same
 |progress rewrite RenameMemoControl.updated_other by discriminate
 |progress rewrite Hkind
 |match goal with |- context [bool_decide ?P]=>first
    [progress rewrite (bool_decide_true P) by reflexivity|progress rewrite (bool_decide_false P) by congruence] end
 |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__classEqual ?bi ?ni) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__classEqual bi ni) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(final,observations))) by exact Hrun;rewrite Hsame;clear Hsame end
 |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
 ]. reflexivity.
Qed.
Theorem generated_binary_member_helper (f:Frame) width remaining outer_remaining a b stride d ka kb va vb final observations :
 nums f vardef_0__schemaInstance_kind=5 ->
 nums f vardef_0__schemaInstance_a=Z.of_nat a -> nums f vardef_0__schemaInstance_b=Z.of_nat b ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 ka=(a*stride+d)%nat -> kb=(b*stride+d)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some va ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some vb ->
 execObserved (funcdef_0__classMember (fun _=>false) (update (update (fun _=>0) vardef_0__classMember_a va) vardef_0__classMember_b vb))
   (machine f,observations)=Some (tt,(final,observations)) ->
 execLocalObserved (binary_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine (binary_frame f va vb) final,observations)).
Proof.
 intros Hkind Ha Hb Hstride Hd Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hrun.
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
 destruct f as [s bs ns]. cbn [machine nums] in *.
 unfold binary_handler,binary_frame.
 repeat first [progress cbn [optionBind fst snd bind]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |progress unfold addInt at 1|progress unfold multInt at 1
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];rewrite ?Nat2Z.id;
     first [exact Hbounda|exact Hboundb])
 |progress rewrite Ha|progress rewrite Hb|progress rewrite Hstride|progress rewrite Hmula|progress rewrite Hmulb
 |progress rewrite Hadda|progress rewrite Haddb|progress rewrite Nat2Z.id
 |match goal with |- context [List.nth ?i ?xs ?zero]=>
    let expression:=constr:(List.nth i xs zero) in let Hsame:=fresh in first
    [assert (Hsame:expression=va) by exact Hntha|assert (Hsame:expression=vb) by exact Hnthb];rewrite Hsame;clear Hsame end
 |progress rewrite RenameMemoControl.updated_same
 |progress rewrite RenameMemoControl.updated_other by discriminate
 |progress rewrite Hkind
 |match goal with |- context [bool_decide ?P]=>first
    [progress rewrite (bool_decide_true P) by reflexivity|progress rewrite (bool_decide_false P) by congruence] end
 |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__classMember ?bi ?ni) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__classMember bi ni) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(final,observations))) by exact Hrun;rewrite Hsame;clear Hsame end
 |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
 ]. reflexivity.
Qed.

Theorem generated_gen (f:Frame) width remaining outer_remaining a stride d key id fs classes rho ci reserve observations :
 nums f vardef_0__schemaInstance_a=Z.of_nat a ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 key=(a*stride+d+1)%nat -> Z.of_nat key<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) key=Some id ->
 NativeRepresentation.canonical_arena (machine f) fs -> meta_value (machine f) 8=0 ->
 meaning fs classes rho (S d) (Protocol.PE ci) id ->
 Z.of_nat (length fs+S reserve)<=9223372036854775807 ->
 exists final next, execLocalObserved (all_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)) /\
 NativeRepresentation.canonical_arena final next /\ meta_value final 8=0 /\
 meaning next classes rho d (Protocol.PE (Schemata.template_gen ci)) (meta_value final 0) /\
 (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807.
Proof.
 intros Ha Hstride Hd Hkey Hword Hlookup Harena Herror [p [Hci Hp]] Hbudget.
 destruct (generated_all_formula f width remaining outer_remaining a stride d key id fs classes rho
   (Schemata.literal_formula p) reserve observations Ha Hstride Hd Hkey Hword Hlookup Harena Herror Hp Hbudget)
 as [final [next [Hrun [Hnext [Hflag [Hmeaning [Hprefix Hroom]]]]]]].
 exists final,next. split;[exact Hrun|]. split;[exact Hnext|]. split;[exact Hflag|]. split.
 - exists (SetTheory.all p). split;[cbn [Schemata.infer];now rewrite Hci|exact Hmeaning].
 - split;assumption.
Qed.

Theorem generated_binary_equal (f:Frame) width remaining outer_remaining a b stride d ka kb ia ib fs classes rho ta tb reserve observations :
 nums f vardef_0__schemaInstance_kind=4 ->
 nums f vardef_0__schemaInstance_a=Z.of_nat a -> nums f vardef_0__schemaInstance_b=Z.of_nat b ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 ka=(a*stride+d)%nat -> kb=(b*stride+d)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some (Z.of_nat ia) ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some (Z.of_nat ib) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 nth_error fs 0=Some SetTheory.falsity -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error classes ia=Some (Schemata.instantiate_class rho d ta) ->
 nth_error classes ib=Some (Schemata.instantiate_class rho d tb) ->
 RenameMemoClassEqual.ready (machine f) fs ia ib (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb) ->
 Z.of_nat (length fs+RenameMemoClassEqual.work (machine f) ia ib
   (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb)+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 exists final next,execLocalObserved (binary_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine (binary_frame f (Z.of_nat ia) (Z.of_nat ib)) final,observations)) /\
 NativeRepresentation.canonical_arena final next /\
 meaning next classes rho d (Protocol.FE (Schemata.template_equal ta tb)) (meta_value final 0) /\
 (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ RenameStorage.logical_frame (machine f) final /\
 ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\
 Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\ FormulaTopology.ordered final (length next).
Proof.
 intros Hkind Ha Hb Hstride Hd Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib Hready Hbudget.
 destruct (RenameMemoClassEqual.generated_refines (machine f) (fun _=>false)
   (update (update (fun _=>0) vardef_0__classEqual_a (Z.of_nat ia)) vardef_0__classEqual_b (Z.of_nat ib))
   fs classes ia ib (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb) reserve observations
   Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib ltac:(rewrite RenameMemoControl.updated_other by discriminate;apply RenameMemoControl.updated_same) ltac:(apply RenameMemoControl.updated_same) Hready Hbudget)
 as [final [next [index [Hrun [Hnext [Hindex [Hindexword [Hmeaning [Hprefix [Hflag [Hframe [Hnextclasses [Hnextgood [Hroom [Hnexttop Hgrowth]]]]]]]]]]]]]]].
 exists final,next. split.
 - eapply generated_binary_equal_helper;eassumption.
 - split;[exact Hnext|]. split.
   + change (formula_value next (meta_value final 0)
       (VirtualClasses.erase (VirtualClasses.class_equal (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb)))).
     rewrite Hindex. split;[exact Hindexword|]. now rewrite Nat2Z.id.
   + exact (conj Hprefix (conj Hflag (conj Hframe (conj Hnextclasses (conj Hnextgood (conj Hroom Hnexttop)))))).
Qed.

Theorem generated_binary_member (f:Frame) width remaining outer_remaining a b stride d ka kb ia ib fs classes rho ta tb reserve observations :
 nums f vardef_0__schemaInstance_kind=5 ->
 nums f vardef_0__schemaInstance_a=Z.of_nat a -> nums f vardef_0__schemaInstance_b=Z.of_nat b ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 ka=(a*stride+d)%nat -> kb=(b*stride+d)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some (Z.of_nat ia) ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some (Z.of_nat ib) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 nth_error fs 0=Some SetTheory.falsity -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error classes ia=Some (Schemata.instantiate_class rho d ta) ->
 nth_error classes ib=Some (Schemata.instantiate_class rho d tb) ->
 RenameMemoClassMember.ready (machine f) fs ia ib (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb) ->
 Z.of_nat (length fs+RenameMemoClassMember.work (machine f) ia ib
   (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb)+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 exists final next,execLocalObserved (binary_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine (binary_frame f (Z.of_nat ia) (Z.of_nat ib)) final,observations)) /\
 NativeRepresentation.canonical_arena final next /\
 meaning next classes rho d (Protocol.FE (Schemata.template_member ta tb)) (meta_value final 0) /\
 (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ RenameStorage.logical_frame (machine f) final /\
 ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\
 Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\ FormulaTopology.ordered final (length next).
Proof.
 intros Hkind Ha Hb Hstride Hd Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib Hready Hbudget.
 destruct (RenameMemoClassMember.generated_refines (machine f) (fun _=>false)
   (update (update (fun _=>0) vardef_0__classMember_a (Z.of_nat ia)) vardef_0__classMember_b (Z.of_nat ib))
   fs classes ia ib (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb) reserve observations
   Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib ltac:(rewrite RenameMemoControl.updated_other by discriminate;apply RenameMemoControl.updated_same) ltac:(apply RenameMemoControl.updated_same) Hready Hbudget)
 as [final [next [index [Hrun [Hnext [Hindex [Hindexword [Hmeaning [Hprefix [Hflag [Hframe [Hnextclasses [Hnextgood [Hroom [Hnexttop Hgrowth]]]]]]]]]]]]]]].
 exists final,next. split.
 - eapply generated_binary_member_helper;eassumption.
 - split;[exact Hnext|]. split.
   + change (formula_value next (meta_value final 0)
       (VirtualClasses.erase (VirtualClasses.class_member (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb)))).
     rewrite Hindex. split;[exact Hindexword|]. now rewrite Nat2Z.id.
   + exact (conj Hprefix (conj Hflag (conj Hframe (conj Hnextclasses (conj Hnextgood (conj Hroom Hnexttop)))))).
Qed.
End SchemaEvaluation.
