From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
 SchemaEvaluation SchemaEvaluationControl SchemaPair SchemaPairStep SchemaEvaluationFrames
 MetaCellFrame RenameStorage AxiomStorage InternLengths SchemaPairSemantic FormulaEncoding FormulaCircuit InternReserve Intern SemanticFrames Representation ClassStorage ClassLookup FormulaTopology.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationPreservation.
Import IndexExecution SipHashExecution ObservedLocal.
Definition LocalAction R := SchemaEvaluation.LocalAction R.
Definition LoopAction R := SchemaEvaluation.LoopAction R.
Definition Frame := SchemaEvaluation.Frame.
Section Numbers.
Context (watched:varsfuncdef_0__schemaInstance).
Definition number_safe (effect:WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) :=
 match effect with NumberLocalSet _ _ _ name _=>name<>watched|_=>True end.
Fixpoint number_ro {R} (code:LocalAction R) : Prop := match code with
 |Done _ _ _ _=>True|Dispatch _ _ _ effect cont=>number_safe effect /\ forall response,number_ro (cont response) end.
Definition within_number_safe (effect:WithinLoop arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) :=
 match effect with DoWithLocalVariables _ _ _ effect=>number_safe effect|_=>True end.
Fixpoint within_number_ro {R} (code:LoopAction R) : Prop := match code with
 |Done _ _ _ _=>True|Dispatch _ _ _ effect cont=>within_number_safe effect /\ forall response,within_number_ro (cont response) end.
Lemma number_bind {A B} (code:LocalAction A) (next:A->LocalAction B) :
 number_ro code -> (forall value,number_ro (next value)) -> number_ro (code>>=next).
Proof. induction code as [value|effect cont IH];[intros _ H;apply H|]. intros [Hsafe Hcode] Hnext. split;[exact Hsafe|]. intro;apply IH;auto. Qed.
Lemma within_number_bind {A B} (code:LoopAction A) (next:A->LoopAction B) :
 within_number_ro code -> (forall value,within_number_ro (next value)) -> within_number_ro (code>>=next).
Proof. induction code as [value|effect cont IH];[intros _ H;apply H|]. intros [Hsafe Hcode] Hnext. split;[exact Hsafe|]. intro;apply IH;auto. Qed.
Lemma number_lift {R} (code:Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue R) :
 number_ro (liftToWithLocalVariables code).
Proof. induction code;cbn [liftToWithLocalVariables Action_rect number_ro number_safe];auto. Qed.
Lemma within_number_lift {R} (code:LocalAction R) : number_ro code -> within_number_ro (liftToWithinLoop code).
Proof. induction code;cbn [liftToWithinLoop Action_rect within_number_ro within_number_safe];[tauto|]. intros [Hsafe Hcode]. split;[exact Hsafe|]. intro;auto. Qed.
Lemma number_drop (code:LoopAction unit) : within_number_ro code -> number_ro (dropWithinLoop code).
Proof.
 induction code as [value|effect cont IH];[exact (fun _=>I)|]. intros [Hsafe Hcode].
 destruct effect as [effect| |];cbn [dropWithinLoop Action_rect number_ro];try exact I.
 split;[exact Hsafe|]. intro response. apply IH. apply Hcode.
Qed.
Lemma number_step effect (f:Frame) observations value final after :
 number_safe effect -> localStepObserved effect (f,observations)=Some (value,(final,after)) -> nums final watched=nums f watched.
Proof.
 intros Hsafe Hrun. destruct effect as [effect|name|name value'|name|name value'];unfold localStepObserved in Hrun;cbn [fst snd] in Hrun.
 - destruct (observedStep effect (machine f,observations)) as [[response [middle trace]]|];[|discriminate].
   cbn [optionBind fst snd] in Hrun. injection Hrun as _ <- <-. reflexivity.
 - injection Hrun as _ <- <-. reflexivity.
 - injection Hrun as _ <- <-. reflexivity.
 - injection Hrun as _ <- <-. reflexivity.
 - injection Hrun as _ <- <-. cbn [nums setNum]. apply RenameMemoControl.updated_other. now cbn [number_safe] in Hsafe.
Qed.
Lemma number_preserves {R} (code:LocalAction R) (f:Frame) observations value final after :
 number_ro code -> execLocalObserved code (f,observations)=Some (value,(final,after)) -> nums final watched=nums f watched.
Proof.
 induction code as [result|effect cont IH] in f,observations|-*.
 - intros _ Hrun. injection Hrun as _ <- <-. reflexivity.
 - intros [Hsafe Hcode] Hrun. cbn [execLocalObserved] in Hrun.
   destruct (localStepObserved effect (f,observations)) as [[response [middle trace]]|] eqn:Hstep;[|discriminate].
   cbn [optionBind fst snd] in Hrun. rewrite (IH response middle trace (Hcode response) Hrun).
   eapply number_step;eassumption.
Qed.
End Numbers.
Ltac number_frames := first
 [lazymatch goal with |- number_ro _ (Done _ _ _ _)=>exact I end
 |lazymatch goal with |- within_number_ro _ (Done _ _ _ _)=>exact I end
 |lazymatch goal with |- number_ro _ (bind _ _)=>apply number_bind;[number_frames|intro;number_frames] end
 |lazymatch goal with |- within_number_ro _ (bind _ _)=>apply within_number_bind;[number_frames|intro;number_frames] end
 |apply number_lift|apply within_number_lift;number_frames|apply number_drop;number_frames
 |lazymatch goal with |- number_ro _ (if ?test then _ else _)=>destruct test;number_frames end
 |lazymatch goal with |- within_number_ro _ (if ?test then _ else _)=>destruct test;number_frames end
 |lazymatch goal with |- number_ro _ (Dispatch _ _ _ _ _)=>split;[cbn [number_safe];intuition congruence|intro;number_frames] end
 |lazymatch goal with |- within_number_ro _ (Dispatch _ _ _ _ _)=>split;[cbn [within_number_safe number_safe];intuition congruence|intro;number_frames] end
 |progress cbv beta iota zeta delta [numberLocalGet numberLocalSet booleanLocalGet booleanLocalSet retrieve store grow trap readChar writeChar flush shortCircuitAnd shortCircuitOr addInt subInt multInt];number_frames].
Definition protected_number watched :=
 watched<>vardef_0__schemaInstance_kind /\ watched<>vardef_0__schemaInstance_a /\ watched<>vardef_0__schemaInstance_b /\
 watched<>vardef_0__schemaInstance_c /\ watched<>vardef_0__schemaInstance_d /\ watched<>vardef_0__schemaInstance_va /\
 watched<>vardef_0__schemaInstance_vb /\ watched<>vardef_0__schemaInstance_vc.
Theorem marked_number_ro watched width remaining outer_remaining : protected_number watched ->
 number_ro watched (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)).
Proof. unfold protected_number. intros H. unfold SchemaEvaluation.marked_body. number_frames. Qed.
Theorem marked_numbers watched width remaining outer_remaining f observations outcome final after : protected_number watched ->
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=Some (outcome,(final,after)) ->
 nums final watched=nums f watched.
Proof. intros Hprotected Hrun. eapply number_preserves;[apply marked_number_ro;exact Hprotected|exact Hrun]. Qed.
Theorem local_cell {R} cell (code:LocalAction R) f observations value final after :
 MetaCellFrame.local_ro cell code -> execLocalObserved code (f,observations)=Some (value,(final,after)) ->
 meta_value (machine final) cell=meta_value (machine f) cell.
Proof.
 intros Hro Hrun. destruct f as [s bs ns].
 set (discard:=code>>=fun _=>Done _ _ _ tt).
 assert (Hdiscard:MetaCellFrame.local_ro cell discard).
 { apply MetaCellFrame.local_bind;[exact Hro|]. intro;exact I. }
 assert (Hexec:execObserved (eliminateLocalVariables bs ns discard) (s,observations)=Some (tt,(machine final,after))).
 { rewrite eliminate_correct. unfold discard. rewrite local_bind,Hrun. reflexivity. }
 exact (MetaCellFrame.observed_preserves cell _ s observations tt (machine final) after
   (MetaCellFrame.eliminate_ro cell discard bs ns Hdiscard) Hexec).
Qed.
Theorem schemaClass_cells cell : cell<>0%nat -> cell<>2%nat -> cell<>8%nat -> forall bs ns,
 MetaCellFrame.array_ro cell (funcdef_0__schemaClass bs ns).
Proof. intros Hzero Hclasses Herror bs ns. unfold funcdef_0__schemaClass. apply MetaCellFrame.eliminate_ro. unfold funcdef_0__schemaClass_body. MetaCellFrame.ro. Qed.
Local Opaque funcdef_0__schemaClass funcdef_0__rename funcdef_0__intern funcdef_0__predicate funcdef_0__axiom.
Theorem schemaShift_cells cell : RenameStorage.Cells.protected cell -> cell<>2%nat -> forall bs ns,
 MetaCellFrame.array_ro cell (funcdef_0__schemaShiftClass bs ns).
Proof.
 intros Hprotected Hclasses bs ns.
 pose proof (schemaClass_cells cell (proj1 Hprotected) Hclasses (proj1 (proj2 (proj2 Hprotected)))) as Hschema.
 pose proof (RenameStorage.Cells.rename_ro cell Hprotected) as Hrename.
 unfold RenameStorage.Cells.protected in Hprotected.
 unfold funcdef_0__schemaShiftClass. apply MetaCellFrame.eliminate_ro. unfold funcdef_0__schemaShiftClass_body. MetaCellFrame.ro.
Qed.
Local Opaque funcdef_0__schemaShiftClass.
Theorem selected_cells which cell width remaining outer_remaining :
 which<>SchemaPair.binary -> RenameStorage.Cells.protected cell -> cell<>2%nat -> cell<>13%nat -> (which=SchemaPair.axiom -> cell<>18%nat) ->
 MetaCellFrame.local_ro cell (dropWithinLoop (SchemaPair.selected which width remaining outer_remaining)).
Proof.
 intros Hbinary Hprotected Hclasses Hflag Haxiomflag.
 pose proof (schemaClass_cells cell (proj1 Hprotected) Hclasses (proj1 (proj2 (proj2 Hprotected)))) as Hschema.
 pose proof (schemaShift_cells cell Hprotected Hclasses) as Hshift.
 pose proof (RenameStorage.Cells.intern_ro cell Hprotected) as Hintern.
 pose proof (AxiomStorage.cells_ro cell Hprotected Hflag) as Haxiom.
 unfold RenameStorage.Cells.protected in Hprotected.
 destruct which;try contradiction;try (specialize (Haxiomflag eq_refl));cbn [SchemaPair.selected];
 unfold SchemaPair.raw_meta,SchemaPair.raw_literal,SchemaPair.raw_abstract,SchemaPair.raw_all,SchemaPair.raw_axiom;
 MetaCellFrame.ro.
Qed.
Theorem selected_cell which cell width remaining outer_remaining f observations outcome final after :
 which<>SchemaPair.binary -> RenameStorage.Cells.protected cell -> cell<>2%nat -> cell<>13%nat -> (which=SchemaPair.axiom -> cell<>18%nat) ->
 execLocalObserved (dropWithinLoop (SchemaPair.selected which width remaining outer_remaining)) (f,observations)=Some (outcome,(final,after)) ->
 meta_value (machine final) cell=meta_value (machine f) cell.
Proof. intros Hbinary Hprotected Hclasses Hflag Haxiomflag Hrun. exact (local_cell cell _ f observations outcome final after (selected_cells which cell width remaining outer_remaining Hbinary Hprotected Hclasses Hflag Haxiomflag) Hrun). Qed.
Theorem classEqual_cells cell : RenameStorage.Cells.protected cell -> forall bs ns,
 MetaCellFrame.array_ro cell (funcdef_0__classEqual bs ns).
Proof.
 intros Hprotected bs ns. pose proof (RenameStorage.Cells.predicate_ro cell Hprotected) as Hpredicate.
 pose proof (RenameStorage.Cells.intern_ro cell Hprotected) as Hintern.
 unfold RenameStorage.Cells.protected in Hprotected.
 unfold funcdef_0__classEqual. apply MetaCellFrame.eliminate_ro. unfold funcdef_0__classEqual_body. MetaCellFrame.ro.
Qed.
Theorem classMember_cells cell : RenameStorage.Cells.protected cell -> forall bs ns,
 MetaCellFrame.array_ro cell (funcdef_0__classMember bs ns).
Proof.
 intros Hprotected bs ns. pose proof (RenameStorage.Cells.predicate_ro cell Hprotected) as Hpredicate.
 pose proof (RenameStorage.Cells.rename_ro cell Hprotected) as Hrename.
 pose proof (RenameStorage.Cells.intern_ro cell Hprotected) as Hintern.
 unfold RenameStorage.Cells.protected in Hprotected.
 unfold funcdef_0__classMember. apply MetaCellFrame.eliminate_ro. unfold funcdef_0__classMember_body. MetaCellFrame.ro.
Qed.
Local Opaque funcdef_0__classEqual funcdef_0__classMember.
Theorem marked_cells cell width remaining outer_remaining :
 RenameStorage.Cells.protected cell -> cell<>2%nat -> cell<>13%nat -> cell<>18%nat ->
 MetaCellFrame.local_ro cell (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)).
Proof.
 intros Hprotected Hclasses Hflag Hvalid.
 pose proof (schemaClass_cells cell (proj1 Hprotected) Hclasses (proj1 (proj2 (proj2 Hprotected)))) as Hschema.
 pose proof (schemaShift_cells cell Hprotected Hclasses) as Hshift.
 pose proof (RenameStorage.Cells.intern_ro cell Hprotected) as Hintern.
 pose proof (AxiomStorage.cells_ro cell Hprotected Hflag) as Haxiom.
 pose proof (classEqual_cells cell Hprotected) as Hequal.
 pose proof (classMember_cells cell Hprotected) as Hmember.
 unfold RenameStorage.Cells.protected in Hprotected. unfold SchemaEvaluation.marked_body. MetaCellFrame.ro.
Qed.
Theorem marked_cell cell width remaining outer_remaining f observations outcome final after :
 RenameStorage.Cells.protected cell -> cell<>2%nat -> cell<>13%nat -> cell<>18%nat ->
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=Some (outcome,(final,after)) ->
 meta_value (machine final) cell=meta_value (machine f) cell.
Proof. intros Hprotected Hclasses Hflag Hvalid Hrun. exact (local_cell cell _ f observations outcome final after (marked_cells cell width remaining outer_remaining Hprotected Hclasses Hflag Hvalid) Hrun). Qed.
Theorem generated_universal (f:Frame) width remaining outer_remaining node kind a b c rawd ty ar stride depth key childKey id
 fs classes rho p expression reserve observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (kind,Z.of_nat a,b,c,rawd,ty,ar) ->
 (kind=7 \/ kind=10) ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key ->
 childKey=(a*stride+depth+1)%nat -> Z.of_nat childKey<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) childKey=Some id ->
 (0<length (memory (machine f) arraydef_0__meta))%nat -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 SchemaEvaluation.formula_value fs id p ->
 (forall next value,SchemaEvaluation.formula_value next value (SetTheory.all p) ->
   SchemaEvaluation.meaning next classes rho depth expression value) ->
 Z.of_nat (length fs+S reserve)<=9223372036854775807 ->
 exists final next,execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\ SchemaPairSemantic.post f final next classes rho depth expression key /\
 NativeRepresentation.canonical_arena (machine final) next /\ ClassStorage.represents (machine final) next classes /\
 FormulaTopology.ordered (machine final) (length next) /\ ClassLookup.wellformed (machine final) /\
 meta_value (machine final) 8=0 /\ meta_value (machine final) 18=meta_value (machine f) 18 /\
 (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807.
Proof.
 intros Hnode Hraw Hkind Hstride Hdepth Hkey Hchildkey Hchildword Hchild Hmeta Hbound Harena Htop Herror Hclasses Hgood [Hid Hp] Htarget Hbudget.
 set (parsed:=SchemaPairStep.descriptor_frame f (kind,Z.of_nat a,b,c,rawd,ty,ar)).
 assert (Hnormal:FormulaEncoding.normal (4,id,0)) by (right;right;auto).
 assert (Hdecode:FormulaEncoding.decode fs (4,id,0)=Some (SetTheory.all p)).
 { cbn [FormulaEncoding.decode]. now rewrite Hp. }
 destruct (InternReserve.generated_refines (machine f) (fun _=>false) (FormulaCircuit.arguments 4 id 0) fs _ reserve observations
   Harena Herror Hbudget Hnormal Hdecode)
 as (built & next & index & Hnative & Hframe & Hnext & Hflag & Hindex & Hindexword & Hresult & Hprefix & Hroom).
 assert (Hrun:execLocalObserved (SchemaEvaluation.all_handler width remaining outer_remaining) (parsed,observations)=
   Some (KeepGoing,(setMachine parsed built,observations))).
 { eapply SchemaEvaluation.generated_all_helper;try eassumption.
   - apply SchemaPairSemantic.descriptor_a. }
 set (middle:=setMachine parsed built).
 assert (Hmeaning:SchemaEvaluation.meaning next classes rho depth expression (meta_value built 0)).
 { apply Htarget. unfold SchemaEvaluation.formula_value. rewrite Hindex. split;[exact Hindexword|]. now rewrite Nat2Z.id. }
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(SchemaPairSemantic.output middle key,observations)) /\
   SchemaPairSemantic.post f (SchemaPairSemantic.output middle key) next classes rho depth expression key).
 { eapply (SchemaPairSemantic.finish SchemaPair.universal);try eassumption.
   - unfold middle. exact (SchemaPairStep.descriptor_kind f kind (Z.of_nat a) b c rawd ty ar).
 }
 assert (Hnextclasses:ClassStorage.represents built next classes).
 { destruct Hprefix as [extra Hprefix]. rewrite Hprefix. destruct Hframe as [Harrays [Hcells Hio]].
   eapply SemanticFrames.classes_extend;[apply Hcells;lia|apply Harrays;discriminate|exact Hclasses]. }
 assert (Hnexttop:FormulaTopology.ordered built (length next)).
 { destruct (FormulaTopology.generated_intern_preserves (machine f) (fun _=>false) (FormulaCircuit.arguments 4 id 0) fs _
     Harena Htop Herror ltac:(lia) Hdecode) as (other & Hplain & Hotherflag & Hothertop).
   pose proof (f_equal (fun run=>option_map (fun response=>(fst response,fst (snd response))) run) Hnative) as Herase.
   rewrite execObserved_erases in Herase. cbn [option_map fst snd] in Herase. rewrite Herase in Hplain. injection Hplain as <-.
   destruct Hnext as [[Hready [Hcount Hrest]] Hnextmeaning]. now rewrite Hcount,Nat2Z.id in Hothertop. }
 assert (Hnextgood:ClassLookup.wellformed built).
 { unfold ClassLookup.wellformed in *. rewrite (proj1 Hframe) by discriminate. exact Hgood. }
 assert (Hvalid:meta_value built 18=meta_value (machine f) 18) by (apply (proj1 (proj2 Hframe));lia).
 exists (SchemaPairSemantic.output middle key),next. destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 unfold SchemaPairSemantic.output,middle. cbn [machine setMachine]. split;[now apply SchemaPairStep.written_arena|].
 split;[now apply SchemaPairStep.written_classes|]. split;[now apply SchemaPairStep.written_topology|].
 split;[unfold ClassLookup.wellformed;now rewrite SchemaPairStep.written_other by discriminate|].
 split;[now rewrite SchemaPairStep.written_meta|]. split;[now rewrite SchemaPairStep.written_meta|]. split;assumption.
Qed.
End SchemaEvaluationPreservation.
