From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  SchemaEvaluation SchemaShiftClass SchemaClass ClassStorage ClassLookup RenameMemoCallers
  Representation FormulaTopology RenameMemoBounds RenameMemoIndexBounds RenameMemoTransition.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationMeta.
Import IndexExecution SipHashExecution ObservedLocal.
Definition arguments cls depth : varsfuncdef_0__schemaShiftClass->Z :=
 update (update (fun _=>0) vardef_0__schemaShiftClass_cls cls) vardef_0__schemaShiftClass_depth depth.
Local Opaque funcdef_0__schemaShiftClass Imperative.update.
Theorem generated_helper (f:SchemaEvaluation.Frame) width remaining outer_remaining a (id:Z) final observations :
 nums f vardef_0__schemaInstance_a=Z.of_nat a ->
 nth_error (memory (machine f) arraydef_0__schemaArguments) a=Some id ->
 execObserved (funcdef_0__schemaShiftClass (fun _=>false) (arguments id (SchemaEvaluation.depth width remaining)))
   (machine f,observations)=Some (tt,(final,observations)) ->
 execLocalObserved (SchemaEvaluation.meta_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)).
Proof.
 intros Ha Hlookup Hrun.
 assert (Hbound:(a<length (memory (machine f) arraydef_0__schemaArguments))%nat) by (apply nth_error_Some;congruence).
 pose proof (List.nth_error_nth _ _ 0 Hlookup) as Hnth.
 unfold SchemaEvaluation.meta_handler.
 repeat first [progress cbn [optionBind fst snd bind]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine];rewrite ?Nat2Z.id;exact Hbound)
 |progress rewrite Ha|progress rewrite Nat2Z.id
 |match goal with |- context [List.nth ?i ?xs ?zero]=>
   let expression:=constr:(List.nth i xs zero) in let Hsame:=fresh in assert (Hsame:expression=id) by exact Hnth;rewrite Hsame;clear Hsame end
 |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__schemaShiftClass ?bi ?ni) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__schemaShiftClass bi ni) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(final,observations))) by exact Hrun;rewrite Hsame;clear Hsame end
 |progress cbn [dropWithinLoop Action_rect]]. reflexivity.
Qed.
Lemma rename_identity p : SetTheory.rename (fun i=>i) p=p.
Proof.
 induction p as [|i j|i j|p IHp q IHq|p IHp];cbn [SetTheory.rename];try reflexivity;try congruence.
 transitivity (SetTheory.all (SetTheory.rename (fun i=>i) p));[|now rewrite IHp].
 f_equal. apply RenameMemoCallers.rename_extensional. intros [|i];reflexivity.
Qed.
Lemma shifted_zero_core p : Schemata.shifted_class 0 (VirtualClasses.abstract (VirtualClasses.core p))=
 VirtualClasses.abstract (VirtualClasses.core p).
Proof.
 cbn [Schemata.shifted_class VirtualClasses.erase]. f_equal. f_equal.
 transitivity (SetTheory.rename (fun i=>i) p);[|apply rename_identity].
 apply RenameMemoCallers.rename_extensional. intros [|i];reflexivity.
Qed.
Theorem generated_zero (f:SchemaEvaluation.Frame) width remaining outer_remaining a cls fs classes rho observations :
 nums f vardef_0__schemaInstance_a=Z.of_nat a ->
 nth_error (memory (machine f) arraydef_0__schemaArguments) a=Some (Z.of_nat cls) ->
 SchemaEvaluation.depth width remaining=0 ->
 (8<length (memory (machine f) arraydef_0__meta))%nat ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error classes cls=Some (rho a) -> word (Z.of_nat cls) ->
 exists final,execLocalObserved (SchemaEvaluation.meta_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)) /\ ClassStorage.represents final fs classes /\
 SchemaEvaluation.meaning fs classes rho 0 (Protocol.CE (Schemata.metavariable a)) (meta_value final 0).
Proof.
 intros Ha Hlookup Hd Hmeta Hclasses Hgood Hcls Hword.
 assert (Hrun:execObserved (funcdef_0__schemaShiftClass (fun _=>false) (arguments (Z.of_nat cls) (SchemaEvaluation.depth width remaining)))
   (machine f,observations)=Some (tt,(SchemaShiftClass.started (machine f) cls,observations))).
 { apply SchemaShiftClass.generated_zero with (cls:=cls);try assumption.
   - unfold arguments. rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same.
 }
 exists (SchemaShiftClass.started (machine f) cls). split;[eapply generated_helper;eassumption|].
 split;[now apply SchemaShiftClass.started_classes|].
 change (SchemaEvaluation.class_value classes (meta_value (SchemaShiftClass.started (machine f) cls) 0) (Schemata.shifted_class 0 (rho a))).
 unfold SchemaShiftClass.started. rewrite meta_store_same by lia. split;[exact Hword|]. rewrite Nat2Z.id.
 destruct (proj2 (ClassLookup.lookup (machine f) fs classes cls (rho a) Hclasses Hgood Hcls)) as
   [[variable [Hrho [Hvariable Hraw]]]|[root [p [Hrho [Hp Hraw]]]]].
 - rewrite Hrho in *. cbn [Schemata.shifted_class]. exact Hcls.
 - rewrite Hrho in *. rewrite shifted_zero_core. exact Hcls.
Qed.
Theorem generated_set (f:SchemaEvaluation.Frame) width remaining outer_remaining a cls variable d fs classes rho reserve observations :
 nums f vardef_0__schemaInstance_a=Z.of_nat a ->
 nth_error (memory (machine f) arraydef_0__schemaArguments) a=Some (Z.of_nat cls) ->
 SchemaEvaluation.depth width remaining=Z.of_nat d -> (0<d)%nat ->
 (8<length (memory (machine f) arraydef_0__meta))%nat -> ClassStorage.represents (machine f) fs classes ->
 nth_error (memory (machine f) arraydef_0__classes) cls=Some (0,Z.of_nat variable) -> rho a=VirtualClasses.set variable ->
 Z.of_nat variable+Z.of_nat d<=maximum -> Z.of_nat (length classes+S reserve)<=maximum ->
 exists final,execLocalObserved (SchemaEvaluation.meta_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)) /\
 ClassStorage.represents final fs (classes++[Schemata.instantiate_class rho d (Schemata.metavariable a)]) /\
 SchemaEvaluation.meaning fs (classes++[Schemata.instantiate_class rho d (Schemata.metavariable a)]) rho d
   (Protocol.CE (Schemata.metavariable a)) (meta_value final 0) /\
 meta_value final 8=meta_value (machine f) 8 /\
 Z.of_nat (length (classes++[Schemata.instantiate_class rho d (Schemata.metavariable a)])+reserve)<=maximum.
Proof.
 intros Ha Hlookup Hd Hpositive Hmeta Hclasses Hraw Hrho Hsum Hbudget.
 pose proof (SchemaShiftClass.generated_set_refines (machine f) (fun _=>false)
   (arguments (Z.of_nat cls) (SchemaEvaluation.depth width remaining)) fs classes cls variable d reserve observations
   Hmeta Hclasses Hraw ltac:(unfold arguments;rewrite RenameMemoControl.updated_other by discriminate;apply RenameMemoControl.updated_same)
   ltac:(unfold arguments;rewrite RenameMemoControl.updated_same;exact Hd) Hpositive Hsum Hbudget) as Hstep.
 cbn zeta in Hstep. destruct Hstep as [Hrun [Hnext [Hindex [Hflag [Hroom Hio]]]]].
 set (final:=SchemaClass.result (SchemaShiftClass.started (machine f) cls) (length classes) (0,Z.of_nat (variable+d))).
 exists final. split;[eapply generated_helper;eassumption|].
 assert (Hmeaning:Schemata.instantiate_class rho d (Schemata.metavariable a)=Schemata.shifted_class d (VirtualClasses.set variable)).
 { cbn [Schemata.instantiate_class]. now rewrite Hrho. }
 rewrite Hmeaning. split;[exact Hnext|]. split;[|split;assumption].
 unfold SchemaEvaluation.meaning,SchemaEvaluation.class_value. rewrite Hmeaning.
 change (word (meta_value final 0) /\ nth_error (classes++[Schemata.shifted_class d (VirtualClasses.set variable)]) (Z.to_nat (meta_value final 0))=
   Some (Schemata.shifted_class d (VirtualClasses.set variable))).
 change (meta_value final 0=Z.of_nat (length classes)) in Hindex. rewrite Hindex.
 split;[unfold word;lia|]. rewrite Nat2Z.id,nth_error_app2 by lia. now rewrite Nat.sub_diag.
Qed.

Theorem generated_abstract (f:SchemaEvaluation.Frame) width remaining outer_remaining a cls root p d bound fs classes rho formula_reserve class_reserve observations :
 nums f vardef_0__schemaInstance_a=Z.of_nat a ->
 nth_error (memory (machine f) arraydef_0__schemaArguments) a=Some (Z.of_nat cls) ->
 SchemaEvaluation.depth width remaining=Z.of_nat d -> (0<d)%nat ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes ->
 nth_error (memory (machine f) arraydef_0__classes) cls=Some (1,Z.of_nat root) -> nth_error fs root=Some p ->
 rho a=VirtualClasses.abstract (VirtualClasses.core p) -> nth_error fs 0=Some SetTheory.falsity ->
 Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> RenameMemoIndexBounds.formula_bound bound p ->
 Z.of_nat bound+Z.of_nat d<=maximum -> Z.of_nat (S (RenameMemoTransition.height p))<=maximum ->
 Z.of_nat (length fs+S root*S root+formula_reserve)<=9223372036854775807 ->
 Z.of_nat (length classes+S class_reserve)<=maximum ->
 exists final next,execLocalObserved (SchemaEvaluation.meta_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)) /\ NativeRepresentation.canonical_arena final next /\
 ClassStorage.represents final next (classes++[Schemata.instantiate_class rho d (Schemata.metavariable a)]) /\
 SchemaEvaluation.meaning next (classes++[Schemata.instantiate_class rho d (Schemata.metavariable a)]) rho d
   (Protocol.CE (Schemata.metavariable a)) (meta_value final 0) /\ meta_value final 8=0 /\
 (exists extra,next=fs++extra) /\ FormulaTopology.ordered final (length next) /\
 Z.of_nat (length next+formula_reserve)<=9223372036854775807 /\
 Z.of_nat (length (classes++[Schemata.instantiate_class rho d (Schemata.metavariable a)])+class_reserve)<=maximum.
Proof.
 intros Ha Hlookup Hd Hpositive Hmeta Hsip Harena Htop Herror Hclasses Hraw Hp Hrho Hfalse Hfuel Hbound Hindices Hheight Hbudget Hclassbudget.
 destruct (SchemaShiftClass.generated_abstract_refines (machine f) (fun _=>false)
   (arguments (Z.of_nat cls) (SchemaEvaluation.depth width remaining)) fs classes cls root p d bound class_reserve observations
   Hmeta Hsip Harena Htop Herror Hclasses Hraw Hp Hfalse
   ltac:(unfold arguments;rewrite RenameMemoControl.updated_other by discriminate;apply RenameMemoControl.updated_same)
   ltac:(unfold arguments;rewrite RenameMemoControl.updated_same;exact Hd) Hpositive Hfuel Hbound Hindices Hheight ltac:(lia) Hclassbudget)
 as [final [next [Hrun [Hnext [Hnextclasses [Hindex [Hflag [Hprefix [Hnexttop [Hgrowth [Hclassroom Hio]]]]]]]]]]].
 exists final,next. split;[eapply generated_helper;eassumption|]. split;[exact Hnext|].
 assert (Hmeaning:Schemata.instantiate_class rho d (Schemata.metavariable a)=Schemata.shifted_class d (VirtualClasses.abstract (VirtualClasses.core p))).
 { cbn [Schemata.instantiate_class]. now rewrite Hrho. }
 rewrite Hmeaning. split;[exact Hnextclasses|]. split.
 - unfold SchemaEvaluation.meaning,SchemaEvaluation.class_value. rewrite Hmeaning,Hindex. split;[unfold word;lia|].
   rewrite Nat2Z.id,nth_error_app2 by lia. now rewrite Nat.sub_diag.
 - split;[exact Hflag|]. split;[exact Hprefix|]. split;[exact Hnexttop|]. split;[lia|exact Hclassroom].
Qed.
End SchemaEvaluationMeta.
