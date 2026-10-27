From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash EffectFrame MetaCellFrame PrintingFrame ImmutableStorage ImmutableHandlers
 NativeBasicDispatcher NativeCommandFrames NativeStateFrames NativeProtocolLift NativeState CommandQuit CommandStructure CommandChain CommandDispatch
 ObservedLocal RenameMemoControl RenameStorage CommandInput TokenByte FormulaTopology ClassLookup HashTable
 NativeSimpleCommands FormulaEncoding Representation ArenaFrame FormulaProjection Intern InternBounded Observation ReplyOK ReadOne ReadTwo.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeBasicCountInvariant.
Import IndexExecution SipHashExecution ObservedLocal MetaCellFrame.
Lemma print_ro {R} (code : Action (WithArrays arrayIndex0 (arrayType _ environment0)) withArraysReturnValue R) :
  array_ro 1%nat (PrintingFrame.translate_print code).
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
Theorem tokenByte_ro bs ns : array_ro 1%nat (funcdef_0__tokenByte bs ns).
Proof.
  unfold funcdef_0__tokenByte. apply eliminate_ro. unfold funcdef_0__tokenByte_body. ro.
Qed.
Local Opaque funcdef_0__tokenByte.
Theorem readToken_ro bs ns : array_ro 1%nat (funcdef_0__readToken bs ns).
Proof.
  pose proof (tokenByte_ro) as Hdep0.
  unfold funcdef_0__readToken. apply eliminate_ro. unfold funcdef_0__readToken_body. ro.
Qed.
Local Opaque funcdef_0__readToken.
Theorem readNat_ro bs ns : array_ro 1%nat (funcdef_0__readNat bs ns).
Proof.
  pose proof (readToken_ro) as Hdep0.
  unfold funcdef_0__readNat. apply eliminate_ro. unfold funcdef_0__readNat_body. ro.
Qed.
Local Opaque funcdef_0__readNat.
Theorem lookup_ro bs ns : array_ro 1%nat (funcdef_0__lookup bs ns).
Proof.
  unfold funcdef_0__lookup. apply eliminate_ro. unfold funcdef_0__lookup_body. ro.
Qed.
Local Opaque funcdef_0__lookup.
Theorem ok_ro bs ns : array_ro 1%nat (funcdef_0__ok bs ns).
Proof.
  unfold funcdef_0__ok. apply eliminate_ro. unfold funcdef_0__ok_body.
  apply local_bind.
  - apply string_ro. intro ch. ro.
  - intros [].
    change (local_ro 1%nat
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
Theorem no_ro bs ns : array_ro 1%nat (funcdef_0__no bs ns).
Proof.
  unfold funcdef_0__no. apply eliminate_ro. unfold funcdef_0__no_body. ro.
Qed.
Local Opaque funcdef_0__no.
Theorem appendTheorem_ro bs ns : array_ro 1%nat (funcdef_0__appendTheorem bs ns).
Proof.
  pose proof (ok_ro) as H_ok.
  unfold funcdef_0__appendTheorem. apply eliminate_ro. unfold funcdef_0__appendTheorem_body. ro.
Qed.
Local Opaque funcdef_0__appendTheorem.
Theorem modusPonens_ro bs ns : array_ro 1%nat (funcdef_0__modusPonens bs ns).
Proof.
  pose proof (appendTheorem_ro) as H_appendTheorem.
  pose proof (no_ro) as H_no.
  unfold funcdef_0__modusPonens. apply eliminate_ro. unfold funcdef_0__modusPonens_body. ro.
Qed.
Local Opaque funcdef_0__modusPonens.
Theorem bindName_ro bs ns : array_ro 1%nat (funcdef_0__bindName bs ns).
Proof.
  pose proof lookup_ro as Hlookup. pose proof ok_ro as Hok. pose proof no_ro as Hno.
  unfold funcdef_0__bindName. apply eliminate_ro. unfold funcdef_0__bindName_body. ro.
Qed.
Local Opaque funcdef_0__bindName.
Definition unchanged opcode := opcode<>1%nat /\ opcode<>2%nat /\ opcode<>3%nat /\ opcode<>4%nat /\ opcode<>13%nat.
Local Opaque funcdef_0__intern funcdef_0__generalize.
Theorem handler_ro opcode : unchanged opcode -> NativeBasicDispatcher.supported opcode ->
 local_ro 1%nat (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)).
Proof.
 intros Hallowed Hsupported. pose proof (NativeBasicDispatcher.supported_bound opcode Hsupported) as Hbound.
 unfold NativeBasicDispatcher.supported,NativeBasicDispatcher.two,NativeBasicDispatcher.one,NativeBasicDispatcher.zero,
 NativeBasicDispatcher.named,NativeBasicDispatcher.query in Hsupported.
 unfold unchanged in Hallowed.
 let rec cases count tag := lazymatch count with O=>idtac|S ?rest=>let next:=fresh "opcode" in destruct tag as [|next];[idtac|cases rest next] end in cases 27%nat opcode.
 all:try (exfalso;intuition lia).
 all:match goal with |-context[Z.of_nat ?tag]=>let value:=eval compute in (Z.of_nat tag) in change (Z.of_nat tag) with value end.
 all:unfold CommandChain.handler_for;cbn beta iota.
 all:unfold CommandStructure.handler_5,CommandStructure.handler_6,CommandStructure.handler_9,CommandStructure.handler_10,CommandStructure.handler_12,CommandStructure.handler_15,CommandStructure.handler_16,CommandStructure.handler_17,CommandStructure.handler_18,CommandStructure.handler_19,CommandStructure.handler_20,CommandStructure.handler_21,CommandStructure.handler_23,CommandStructure.handler_25,CommandStructure.handler_26.
 all:pose proof readNat_ro as Hnat;pose proof readToken_ro as Htoken;pose proof lookup_ro as Hlookup;
 pose proof ok_ro as Hok;pose proof no_ro as Hno;pose proof appendTheorem_ro as Happend;
 pose proof modusPonens_ro as Hmp;pose proof bindName_ro as Hbind.
 all:ro.
Qed.
Theorem generated_count native bs ns readstate opcode observations final trace :
 (1<=opcode<=26)%nat -> unchanged opcode -> NativeBasicDispatcher.supported opcode ->
 execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (native,observations)=Some(tt,(readstate,observations)) ->
 (17<length (memory readstate arraydef_0__meta))%nat ->
 meta_value readstate 11=Z.of_nat opcode -> meta_value readstate 14=1 -> meta_value readstate 8=0 ->
 meta_value readstate 1=meta_value native 1 ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 meta_value final 1=meta_value native 1.
Proof.
 intros Hrange Hallowed Hsupported Hreader Hmeta Hnumber Hvalid Herror Hparsed Hrun.
 unfold funcdef_0__command in Hrun.
 rewrite ObservedLocal.eliminate_correct,CommandQuitExecution.actual_body,CommandDispatch.actual_body in Hrun.
 change (optionBind (execLocalObserved (CommandDispatch.with_chain funcdef_0__readNat (CommandChain.source_chain funcdef_0__readNat))
  ({|machine:=native;bools:=bs;nums:=ns|},observations))
  (fun response=>Some(fst response,(machine (fst (snd response)),snd (snd response))))=Some(tt,(final,trace))) in Hrun.
 pose proof (f_equal (fun result=>optionBind result
   (fun response=>Some(fst response,(machine (fst (snd response)),snd (snd response)))))
   (NativeCommandFrames.positive_projection funcdef_0__readNat (CommandChain.source_chain funcdef_0__readNat)
   {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode) observations
   Hreader Hmeta Hnumber Hvalid Herror ltac:(lia))) as Hprojection.
 assert (Hreduced:optionBind (NativeCommandFrames.post_sequence (CommandChain.source_chain funcdef_0__readNat)
   (CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode)) observations)
   (fun response=>Some(fst response,(machine (fst (snd response)),snd (snd response))))=Some(tt,(final,trace))).
 { exact (eq_trans (eq_sym Hprojection) Hrun). }
 clear Hrun. rename Hreduced into Hrun.
 unfold NativeCommandFrames.post_sequence in Hrun.
 lazymatch type of Hrun with optionBind (optionBind ?actual ?post) ?projection=_=>
  remember actual as chainResult eqn:Hchain in Hrun end.
 destruct chainResult as [[[] [middle middleTrace]]|];cbn [optionBind fst snd] in Hrun;[|discriminate].
 symmetry in Hchain.
 lazymatch type of Hrun with optionBind ?actual ?projection=_=>
  remember actual as postResult eqn:Hpost in Hrun end.
 destruct postResult as [[[] [finished finalTrace]]|];cbn [optionBind fst snd] in Hrun;[|discriminate].
 symmetry in Hpost.
 injection Hrun as Hfinal Htrace. subst final trace.
 transitivity (meta_value readstate 1);[|exact Hparsed].
 transitivity (meta_value (machine middle) 1).
 - eapply NativeStateFrames.local_cell;[apply NativeCommandFrames.postlude_cell;lia|exact Hpost].
 -
 assert (Hhandler:execLocalObserved (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode))
   (CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode),observations)=Some(tt,(middle,middleTrace))).
 { refine (NativeCommandFrames.chain_inverse opcode
     (CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode))
     middle observations middleTrace Hrange _ Herror _ Hchain).
   - unfold CommandDispatch.opcode_frame. cbn [nums setNum]. apply RenameMemoControl.updated_same.
   - change (8<length (memory readstate arraydef_0__meta))%nat;lia. }
 exact (NativeStateFrames.local_cell 1 _ _ middle observations middleTrace (handler_ro opcode Hallowed Hsupported) Hhandler).
Qed.
Theorem canonical_count opcode ch chars native bs ns separator payload observations final trace :
 unchanged opcode -> NativeBasicDispatcher.supported opcode ->
 decimalBytes opcode=ch::chars ->
 (17<length (memory native arraydef_0__meta))%nat -> (1024<=length (memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> TokenByteExecution.separator separator ->
 stdin native=chars++separator::payload ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 meta_value final 1=meta_value native 1.
Proof.
 intros Hallowed Hsupported Hencoding Hmeta Htoken Hpending Herror Hseparator Hinput Hrun.
 pose proof (NativeBasicDispatcher.supported_bound opcode Hsupported) as Hbound.
 assert (Hword:Z.of_nat opcode<=maximum) by (unfold maximum;lia).
 eapply generated_count with (readstate:=CommandInput.parsed native ch chars payload) (opcode:=opcode);try eassumption.
 - exact (CommandInput.generated_pending native (fun _=>false) (fun _=>0) opcode ch chars separator payload observations
     Hmeta Htoken Hpending Herror Hword Hencoding Hseparator Hinput).
 - rewrite CommandInput.parsed_meta_length;exact Hmeta.
 - exact (CommandInput.parsed_number native opcode ch chars payload Hmeta Hword Hencoding).
 - apply CommandInput.parsed_valid;exact Hmeta.
 - rewrite CommandInput.parsed_meta_other by lia. exact Herror.
 - apply CommandInput.parsed_meta_other;lia.
Qed.
End NativeBasicCountInvariant.
