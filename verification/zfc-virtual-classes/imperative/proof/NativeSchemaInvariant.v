From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash EffectFrame PrintingFrame ImmutableStorage ImmutableHandlers
 NativeBasicDispatcher NativeCommandFrames NativeStateFrames NativeProtocolLift NativeState CommandQuit CommandStructure CommandChain CommandDispatch
 ObservedLocal RenameMemoControl RenameStorage CommandInput TokenByte FormulaTopology ClassLookup HashTable
 NativeSimpleCommands FormulaEncoding Representation ArenaFrame FormulaProjection Intern InternBounded Observation ReplyOK ReadOne ReadTwo.
From NativeProof Require Import NativeBasicInvariant NativeSchemaBoundary SchemaNodeTotal.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSchemaInvariant.
Import IndexExecution SipHashExecution ObservedLocal EffectFrame.
Lemma schemaCheck_ro bs ns : array_ro arraydef_0__classes (funcdef_0__schemaCheck bs ns).
Proof. unfold funcdef_0__schemaCheck. apply eliminate_ro. unfold funcdef_0__schemaCheck_body. ro. Qed.
Local Opaque funcdef_0__schemaCheck.
Lemma schemaNode_ro bs ns : array_ro arraydef_0__classes (funcdef_0__schemaNode bs ns).
Proof.
 pose proof schemaCheck_ro as Hcheck.
 pose proof (NativeBasicInvariant.Arrays.ok_ro arraydef_0__classes ltac:(repeat split;discriminate)) as Hok.
 pose proof (NativeBasicInvariant.Arrays.no_ro arraydef_0__classes ltac:(repeat split;discriminate)) as Hno.
 unfold funcdef_0__schemaNode. apply eliminate_ro. unfold funcdef_0__schemaNode_body. ro.
Qed.
Local Opaque funcdef_0__schemaNode funcdef_0__readNat.
Module Arrays.
Definition kind watched := watched=arraydef_0__classes.
Definition unchanged opcode (watched:arrayIndex1) := opcode=22%nat.
Definition supported opcode := opcode=22%nat.
Lemma handler_ro watched opcode : kind watched -> unchanged opcode watched -> supported opcode ->
 local_ro watched (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)).
Proof.
 intros -> -> _. change (Z.of_nat 22) with 22. unfold CommandChain.handler_for. cbn beta iota.
 pose proof schemaNode_ro as Hnode.
 pose proof (NativeBasicInvariant.Arrays.no_ro arraydef_0__classes ltac:(repeat split;discriminate)) as Hno.
 pose proof (NativeBasicInvariant.Arrays.readNat_ro arraydef_0__classes ltac:(repeat split;discriminate)) as Hread.
 unfold CommandStructure.handler_22. ro.
Qed.
End Arrays.
Theorem generated_array watched native bs ns readstate opcode observations final trace :
 (1<=opcode<=26)%nat -> Arrays.kind watched -> Arrays.unchanged opcode watched -> Arrays.supported opcode ->
 execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (native,observations)=Some(tt,(readstate,observations)) ->
 (17<length (memory readstate arraydef_0__meta))%nat ->
 meta_value readstate 11=Z.of_nat opcode -> meta_value readstate 14=1 -> meta_value readstate 8=0 ->
 memory readstate watched=memory native watched ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 memory final watched=memory native watched.
Proof.
 intros Hrange Hkind Hallowed Hsupported Hreader Hmeta Hnumber Hvalid Herror Hparsed Hrun.
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
 transitivity (memory readstate watched);[|exact Hparsed].
 transitivity (memory (machine middle) watched).
 - eapply ImmutableHandlers.local_observed_preserves;[apply NativeCommandFrames.postlude_array;unfold Arrays.kind in Hkind;intuition congruence|exact Hpost].
 -
 assert (Hhandler:execLocalObserved (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode))
   (CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode),observations)=Some(tt,(middle,middleTrace))).
 { refine (NativeCommandFrames.chain_inverse opcode
     (CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode))
     middle observations middleTrace Hrange _ Herror _ Hchain).
   - unfold CommandDispatch.opcode_frame. cbn [nums setNum]. apply RenameMemoControl.updated_same.
   - change (8<length (memory readstate arraydef_0__meta))%nat;lia. }
 exact (ImmutableHandlers.local_observed_preserves watched _ _ middle observations middleTrace (Arrays.handler_ro watched opcode Hkind Hallowed Hsupported) Hhandler).
Qed.
Theorem canonical_array watched opcode ch chars native bs ns separator payload observations final trace :
 Arrays.kind watched -> Arrays.unchanged opcode watched -> Arrays.supported opcode ->
 decimalBytes opcode=ch::chars ->
 (17<length (memory native arraydef_0__meta))%nat -> (1024<=length (memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> TokenByteExecution.separator separator ->
 stdin native=chars++separator::payload ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 memory final watched=memory native watched.
Proof.
 intros Hkind Hallowed Hsupported Hencoding Hmeta Htoken Hpending Herror Hseparator Hinput Hrun.
 assert (Hbound:(1<=opcode<=26)%nat) by (unfold Arrays.supported in Hsupported;lia).
 assert (Hword:Z.of_nat opcode<=maximum) by (unfold maximum;lia).
 eapply generated_array with (readstate:=CommandInput.parsed native ch chars payload) (opcode:=opcode);try eassumption.
 - exact (CommandInput.generated_pending native (fun _=>false) (fun _=>0) opcode ch chars separator payload observations
     Hmeta Htoken Hpending Herror Hword Hencoding Hseparator Hinput).
 - rewrite CommandInput.parsed_meta_length;exact Hmeta.
 - exact (CommandInput.parsed_number native opcode ch chars payload Hmeta Hword Hencoding).
 - apply CommandInput.parsed_valid;exact Hmeta.
 - rewrite CommandInput.parsed_meta_other by lia. exact Herror.
 - apply CommandInput.parsed_other;unfold Arrays.kind in Hkind;intuition congruence.
Qed.
Theorem generated_total s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations :
 decimalBytes 22=ch::chars -> Guarantees.safe logical ->
 (19<length (memory s arraydef_0__meta))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 ->
 Z.of_nat kind<=maximum -> Z.of_nat a<=maximum -> Z.of_nat b<=maximum ->
 Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
 Z.of_nat (length (Protocol.expressions logical))<maximum -> NativeState.represents s logical -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) ->
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
 TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 -> TokenByteExecution.separator sep5 ->
 stdin s=chars++sep0::decimalBytes kind++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::decimalBytes d++sep5::tail ->
 exists final reply next, NativeSchemaBoundary.complete s logical bs ns kind a b c d tail observations final reply next /\
 ClassLookup.wellformed final /\ FormulaTopology.ordered final (length (Protocol.formulas next)) /\
 Protocol.formulas next=Protocol.formulas logical /\ Protocol.classes next=Protocol.classes logical /\
 (length (Protocol.formulas next)<=length (Protocol.formulas logical))%nat.
Proof.
 intros Hencoding Hsafe Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hcapacity Hstate Hgood Htop
   Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput.
 destruct (NativeSchemaBoundary.generated_total s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
   Hencoding Hsafe Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hcapacity Hstate
   Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput) as (final & reply & next & Hcomplete).
 pose proof Hcomplete as [Hchecked [Hfinalstate [Hio [Hunchanged Houtcome]]]].
 destruct Hchecked as (Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hschemas & Hlengths & Hclear & Hnexttop & Hnextsafe).
 assert (Harray:memory final arraydef_0__classes=memory s arraydef_0__classes).
 { exact (canonical_array arraydef_0__classes 22 ch chars s bs ns sep0
     (decimalBytes kind++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::decimalBytes d++sep5::tail)
     observations final _ eq_refl eq_refl eq_refl Hencoding ltac:(lia) Htoken Hpending Herror Hsep0 Hinput Hrun). }
 exists final,reply,next. split;[exact Hcomplete|]. split.
 - exact (ClassLookup.transport s final Harray Hgood).
 - split;[exact (Hnexttop Htop)|]. unfold NativeSchemaBoundary.unchanged in Hunchanged.
   destruct Hunchanged as (Hformulas & HclassesSame & Hrest). split;[exact Hformulas|]. split;[exact HclassesSame|]. rewrite Hformulas;lia.
Qed.
End NativeSchemaInvariant.
