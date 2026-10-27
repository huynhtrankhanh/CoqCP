From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal RenameMemoControl MetaCellFrame ArrayLengthFrame NativePrimitives
 NativeStateFrames NativeCommandFrames NativeCommandLengths CommandInput CommandQuit CommandDispatch CommandChain CommandStructure
 PrintingFrame RenameStorage SchemaEvaluationPreservation SchemaInstanceStorage AxiomStorage TokenByte.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeCommandStop.
Import IndexExecution SipHashExecution ObservedLocal CommandQuitExecution.
Module Counts.
Import MetaCellFrame.
Definition registry_cell cell := cell=9%nat.
Lemma rename_protected cell : registry_cell cell -> RenameStorage.Cells.protected cell.
Proof. unfold registry_cell,RenameStorage.Cells.protected;intros Hcell;repeat split;lia. Qed.
Lemma print_ro cell {R} (code : Action (WithArrays arrayIndex0 (arrayType _ environment0)) withArraysReturnValue R) :
  array_ro cell (PrintingFrame.translate_print code).
Proof.
  induction code as [value|effect cont IH]; [constructor|].
  destruct effect as [effect|array slot|array slot value|array size zero].
  - cbn [PrintingFrame.translate_print translateArrays withArraysReturnValueDoBasicEffectArrayType array_ro].
    split; [destruct effect; constructor|]. intro response. apply IH.
  - destruct array. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split; [constructor|]. intro response. apply IH.
  - destruct array. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split; [constructor|]. intro response. apply IH.
  - destruct array. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split; [discriminate|]. intro response. apply IH.
Qed.
#[local] Hint Resolve print_ro : cell_frames.
Theorem intern_ro cell (Hcell:registry_cell cell) bs ns :
 MetaCellFrame.array_ro cell (funcdef_0__intern bs ns).
Proof. exact (RenameStorage.Cells.intern_ro cell (rename_protected cell Hcell) bs ns). Qed.
Local Opaque funcdef_0__intern.
Theorem tokenByte_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__tokenByte bs ns).
Proof.
  unfold registry_cell in Hcell.
  unfold funcdef_0__tokenByte. apply eliminate_ro. unfold funcdef_0__tokenByte_body. ro.
Qed.
Local Opaque funcdef_0__tokenByte.
Theorem readToken_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__readToken bs ns).
Proof.
  unfold registry_cell in Hcell.
  pose proof (tokenByte_ro cell Hcell) as Hdep0.
  unfold funcdef_0__readToken. apply eliminate_ro. unfold funcdef_0__readToken_body. ro.
Qed.
Local Opaque funcdef_0__readToken.
Theorem readNat_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__readNat bs ns).
Proof.
  unfold registry_cell in Hcell.
  pose proof (readToken_ro cell Hcell) as Hdep0.
  unfold funcdef_0__readNat. apply eliminate_ro. unfold funcdef_0__readNat_body. ro.
Qed.
Local Opaque funcdef_0__readNat.
Theorem lookup_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__lookup bs ns).
Proof.
  unfold registry_cell in Hcell.
  unfold funcdef_0__lookup. apply eliminate_ro. unfold funcdef_0__lookup_body. ro.
Qed.
Local Opaque funcdef_0__lookup.
Theorem ok_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__ok bs ns).
Proof.
  unfold registry_cell in Hcell.
  unfold funcdef_0__ok. apply eliminate_ro. unfold funcdef_0__ok_body.
  apply local_bind.
  - apply string_ro. intro ch. ro.
  - intros [].
    change (local_ro cell
      ((numberLocalGet _ _ _ vardef_0__ok_value >>= fun value =>
        liftToWithLocalVariables (PrintingFrame.translate_print (funcdef_0_PrintInt64_unsigned
          (fun _ => false) (update (fun _ => 0%Z) vardef_0_PrintInt64_unsigned_num value))))
      >>= fun _ => writeChar _ _ _ (coerceInt 10 8) >>= fun _ =>
        flush _ _ _ >>= fun _ => Done _ _ _ tt)).
    apply local_bind.
    + apply local_bind; [ro|intro value; apply local_lift; apply print_ro; tauto].
    + intros []. ro.
Qed.
Local Opaque funcdef_0__ok.
Theorem no_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__no bs ns).
Proof.
  unfold registry_cell in Hcell.
  unfold funcdef_0__no. apply eliminate_ro. unfold funcdef_0__no_body. ro.
Qed.
Local Opaque funcdef_0__no.
Theorem appendTheorem_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__appendTheorem bs ns).
Proof.
  unfold registry_cell in Hcell.
  pose proof (ok_ro cell Hcell) as H_ok.
  unfold funcdef_0__appendTheorem. apply eliminate_ro. unfold funcdef_0__appendTheorem_body. ro.
Qed.
Local Opaque funcdef_0__appendTheorem.
Theorem modusPonens_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__modusPonens bs ns).
Proof.
  unfold registry_cell in Hcell.
  pose proof (appendTheorem_ro cell Hcell) as H_appendTheorem.
  pose proof (no_ro cell Hcell) as H_no.
  unfold funcdef_0__modusPonens. apply eliminate_ro. unfold funcdef_0__modusPonens_body. ro.
Qed.
Local Opaque funcdef_0__modusPonens.
Theorem generalize_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__generalize bs ns).
Proof.
  unfold registry_cell in Hcell.
  pose proof (intern_ro cell Hcell) as H_intern.
  pose proof (appendTheorem_ro cell Hcell) as H_appendTheorem.
  unfold funcdef_0__generalize. apply eliminate_ro. unfold funcdef_0__generalize_body. ro.
Qed.
Local Opaque funcdef_0__generalize.
Theorem setness_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__setness bs ns).
Proof.
  unfold registry_cell in Hcell.
  pose proof (RenameStorage.Cells.predicate_ro cell (rename_protected cell Hcell)) as Hdep0.
  pose proof (intern_ro cell Hcell) as Hdep1.
  unfold funcdef_0__setness. apply eliminate_ro. unfold funcdef_0__setness_body. ro.
Qed.
Local Opaque funcdef_0__setness.
Theorem schemaCheck_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__schemaCheck bs ns).
Proof.
  unfold registry_cell in Hcell.
  unfold funcdef_0__schemaCheck. apply eliminate_ro. unfold funcdef_0__schemaCheck_body. ro.
Qed.
Local Opaque funcdef_0__schemaCheck.
Theorem bindName_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__bindName bs ns).
Proof.
 pose proof (lookup_ro cell Hcell) as Hlookup. pose proof (ok_ro cell Hcell) as Hok. pose proof (no_ro cell Hcell) as Hno.
 unfold registry_cell in Hcell. unfold funcdef_0__bindName. apply eliminate_ro. unfold funcdef_0__bindName_body. ro.
Qed.
Local Opaque funcdef_0__bindName.
Theorem schemaNode_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__schemaNode bs ns).
Proof.
 pose proof (schemaCheck_ro cell Hcell) as Hcheck. pose proof (ok_ro cell Hcell) as Hok. pose proof (no_ro cell Hcell) as Hno.
 unfold registry_cell in Hcell. unfold funcdef_0__schemaNode. apply eliminate_ro. unfold funcdef_0__schemaNode_body. ro.
Qed.
End Counts.
Local Opaque funcdef_0__ok funcdef_0__no funcdef_0__intern funcdef_0__readNat funcdef_0__readToken funcdef_0__lookup
 funcdef_0__appendTheorem funcdef_0__modusPonens funcdef_0__generalize funcdef_0__classEqual funcdef_0__classMember
 funcdef_0__axiom funcdef_0__bindName funcdef_0__setness funcdef_0__schemaInstance funcdef_0__schemaCheck funcdef_0__schemaNode.
Theorem handler_ro opcode : (1<=opcode<=26)%nat ->
 MetaCellFrame.local_ro 9 (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)).
Proof.
 intro Hbound. assert (Hcell:Counts.registry_cell 9%nat) by reflexivity.
 pose proof (Counts.readNat_ro 9%nat Hcell) as HreadNat.
 pose proof (Counts.readToken_ro 9%nat Hcell) as HreadToken.
 pose proof (Counts.lookup_ro 9%nat Hcell) as Hlookup.
 pose proof (Counts.ok_ro 9%nat Hcell) as Hok.
 pose proof (Counts.no_ro 9%nat Hcell) as Hno.
 pose proof (Counts.intern_ro 9%nat Hcell) as Hintern.
 pose proof (Counts.appendTheorem_ro 9%nat Hcell) as HappendTheorem.
 pose proof (Counts.modusPonens_ro 9%nat Hcell) as HmodusPonens.
 pose proof (Counts.generalize_ro 9%nat Hcell) as Hgeneralize.
 pose proof (SchemaEvaluationPreservation.classEqual_cells 9%nat (Counts.rename_protected 9%nat Hcell)) as HclassEqual.
 pose proof (SchemaEvaluationPreservation.classMember_cells 9%nat (Counts.rename_protected 9%nat Hcell)) as HclassMember.
 pose proof (AxiomStorage.cells_ro 9%nat (Counts.rename_protected 9%nat Hcell) ltac:(lia)) as Haxiom.
 pose proof (Counts.setness_ro 9%nat Hcell) as Hsetness.
 pose proof (SchemaInstanceStorage.cells 9%nat ltac:(unfold SchemaInstanceStorage.protected_cell;split;[exact (Counts.rename_protected 9%nat Hcell)|repeat split;lia])) as HschemaInstance.
 pose proof (Counts.schemaCheck_ro 9%nat Hcell) as HschemaCheck.
 pose proof (Counts.bindName_ro 9%nat Hcell) as HbindName.
 pose proof (Counts.schemaNode_ro 9%nat Hcell) as HschemaNode.
 let rec cases count tag := lazymatch count with
 | O=>idtac
 | S ?rest=>let next:=fresh "opcode" in destruct tag as [|next];[idtac|cases rest next]
 end in cases 27%nat opcode.
 all:try lia.
 all:match goal with |-context[Z.of_nat ?tag]=>let value:=eval compute in (Z.of_nat tag) in change (Z.of_nat tag) with value end.
 all:unfold CommandChain.handler_for;cbn beta iota.
 all:unfold CommandStructure.handler_1,CommandStructure.handler_2,CommandStructure.handler_3,CommandStructure.handler_4,CommandStructure.handler_5,CommandStructure.handler_6,CommandStructure.handler_7,CommandStructure.handler_8,CommandStructure.handler_9,CommandStructure.handler_10,CommandStructure.handler_11,CommandStructure.handler_12,CommandStructure.handler_13,CommandStructure.handler_14,CommandStructure.handler_15,CommandStructure.handler_16,CommandStructure.handler_17,CommandStructure.handler_18,CommandStructure.handler_19,CommandStructure.handler_20,CommandStructure.handler_21,CommandStructure.handler_22,CommandStructure.handler_23,CommandStructure.handler_24,CommandStructure.handler_25,CommandStructure.handler_26.
 all:MetaCellFrame.ro.
Qed.
Lemma postlude_length (f final:Frame) observations after :
 execLocalObserved NativeCommandFrames.postlude (f,observations)=Some(tt,(final,after)) ->
 length (memory (machine final) arraydef_0__meta)=length (memory (machine f) arraydef_0__meta).
Proof.
 intro Hrun. destruct f as [s bs ns].
 apply (ArrayLengthFrame.observed_preserves arraydef_0__meta (eliminateLocalVariables bs ns NativeCommandFrames.postlude)
   s observations tt (machine final) after).
 - apply ArrayLengthFrame.eliminate_ro. unfold NativeCommandFrames.postlude. ArrayLengthFrame.ro.
 - etransitivity;[exact (ObservedLocal.eliminate_correct NativeCommandFrames.postlude bs ns s observations)|].
   exact (f_equal (fun result=>optionBind result
     (fun response=>Some(fst response,(machine (fst (snd response)),snd (snd response))))) Hrun).
Qed.
Lemma postlude_zero (f:Frame) observations :
 (8<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
 execLocalObserved NativeCommandFrames.postlude (f,observations)=Some(tt,(f,observations)).
Proof.
 intros Hmeta Herror. unfold NativeCommandFrames.postlude.
 repeat first [progress cbn [optionBind fst snd]
  |NativePrimitives.primitive ltac:(fun frame name slot=>first[exact Hmeta|cbn [machine setMachine];lia])
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |progress rewrite Herror
  |match goal with |-context[bool_decide ?P]=>first
    [progress rewrite (bool_decide_true P) by congruence|progress rewrite (bool_decide_false P) by congruence] end].
 reflexivity.
Qed.
Theorem generated native bs ns readstate opcode observations final trace :
 (1<=opcode<=26)%nat ->
 execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (native,observations)=Some(tt,(readstate,observations)) ->
 (17<length (memory readstate arraydef_0__meta))%nat ->
 meta_value readstate 11=Z.of_nat opcode -> meta_value readstate 14=1 -> meta_value readstate 8=0 ->
 meta_value readstate 9=meta_value native 9 ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 (8<length (memory final arraydef_0__meta))%nat -> meta_value final 8=0 ->
 meta_value final 9=meta_value native 9.
Proof.
 intros Hrange Hreader Hmeta Hnumber Hvalid Herror HparsedStop Hrun HfinalMeta HfinalError.
 unfold funcdef_0__command in Hrun.
 rewrite ObservedLocal.eliminate_correct,CommandQuitExecution.actual_body,CommandDispatch.actual_body in Hrun.
 pose proof (f_equal (fun result=>optionBind result
   (fun response=>Some(fst response,(machine (fst (snd response)),snd (snd response)))))
   (NativeCommandFrames.positive_projection funcdef_0__readNat (CommandChain.source_chain funcdef_0__readNat)
   {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode) observations
   Hreader Hmeta Hnumber Hvalid Herror ltac:(lia))) as Hprojection.
 assert (Hreduced:optionBind (NativeCommandFrames.post_sequence (CommandChain.source_chain funcdef_0__readNat)
   (CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode)) observations)
   (fun response=>Some(fst response,(machine (fst (snd response)),snd (snd response))))=Some(tt,(final,trace))).
 { exact (eq_trans (eq_sym Hprojection) Hrun). }
 clear Hrun. rename Hreduced into Hrun. unfold NativeCommandFrames.post_sequence in Hrun.
 lazymatch type of Hrun with optionBind (optionBind ?actual ?post) ?projection=_=>
  remember actual as chainResult eqn:Hchain in Hrun end.
 destruct chainResult as [[[] [middle middleTrace]]|];cbn [optionBind fst snd] in Hrun;[|discriminate].
 symmetry in Hchain.
 lazymatch type of Hrun with optionBind ?actual ?projection=_=>
  remember actual as postResult eqn:Hpost in Hrun end.
 destruct postResult as [[[] [finished finalTrace]]|];cbn [optionBind fst snd] in Hrun;[|discriminate].
 symmetry in Hpost. injection Hrun as Hfinal Htrace. subst final trace.
 set (parsed:=CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode)).
 assert (Hhandler:execLocalObserved (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode))
   (parsed,observations)=Some(tt,(middle,middleTrace))).
 { refine (NativeCommandFrames.chain_inverse opcode parsed middle observations middleTrace Hrange _ Herror _ Hchain).
   - unfold parsed,CommandDispatch.opcode_frame. cbn [nums setNum]. apply RenameMemoControl.updated_same.
   - change (8<length (memory readstate arraydef_0__meta))%nat;lia. }
 pose proof (postlude_length middle finished middleTrace finalTrace Hpost) as Hlength.
 pose proof (NativeStateFrames.local_cell 8 NativeCommandFrames.postlude middle finished middleTrace finalTrace
   (NativeCommandFrames.postlude_cell 8 ltac:(lia)) Hpost) as HerrorSame.
 assert (HmiddleMeta:(8<length (memory (machine middle) arraydef_0__meta))%nat) by (rewrite <-Hlength;exact HfinalMeta).
 assert (HmiddleError:meta_value (machine middle) 8=0) by exact (eq_trans (eq_sym HerrorSame) HfinalError).
 pose proof (postlude_zero middle middleTrace HmiddleMeta HmiddleError) as Hzero.
 pose proof (eq_trans (eq_sym Hzero) Hpost) as Hsame.
 injection Hsame as Hmiddle Htrace. subst finished finalTrace.
 exact (eq_trans (NativeStateFrames.local_cell 9 _ parsed middle observations middleTrace (handler_ro opcode Hrange) Hhandler) HparsedStop).
Qed.
Theorem canonical opcode ch chars native bs ns separator payload observations final trace :
 (1<=opcode<=26)%nat -> decimalBytes opcode=ch::chars ->
 (17<length (memory native arraydef_0__meta))%nat -> (1024<=length (memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> TokenByteExecution.separator separator ->
 stdin native=chars++separator::payload ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 meta_value final 8=0 -> meta_value final 9=meta_value native 9.
Proof.
 intros Hrange Hencoding Hmeta Htoken Hpending Herror Hseparator Hinput Hrun HfinalError.
 assert (Hword:Z.of_nat opcode<=maximum) by (unfold maximum;lia).
 assert (HfinalMeta:(8<length (memory final arraydef_0__meta))%nat).
 { rewrite (NativeCommandLengths.generated arraydef_0__meta native bs ns final observations trace NativeCommandLengths.meta_protected Hrun);lia. }
 exact (generated native bs ns (CommandInput.parsed native ch chars payload) opcode observations final trace Hrange
   (CommandInput.generated_pending native (fun _=>false) (fun _=>0) opcode ch chars separator payload observations
      Hmeta Htoken Hpending Herror Hword Hencoding Hseparator Hinput)
   ltac:(now rewrite CommandInput.parsed_meta_length)
   (CommandInput.parsed_number native opcode ch chars payload Hmeta Hword Hencoding)
   (CommandInput.parsed_valid native ch chars payload Hmeta)
   ltac:(rewrite CommandInput.parsed_meta_other by lia;exact Herror)
   ltac:(apply CommandInput.parsed_meta_other;lia) Hrun HfinalMeta HfinalError).
Qed.
End NativeCommandStop.
