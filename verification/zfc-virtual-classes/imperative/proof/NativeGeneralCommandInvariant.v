From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Guarantees.
From NativeProof Require Import Index SipHash DecimalInput TokenByte NativeState NativeBasicDispatcher NativeCommandBoundary
 NativeClassBinaryBoundary RenameMemoClassEqual RenameMemoClassMember RenameMemoResourceBounds FormulaTopology ClassLookup
 NativeAxiomTotal NativeClassCertifyBoundary ClassCertifyTotal NativeSchemaBoundary SchemaNodeTotal
 NativeSchemaInstanceBoundary SchemaInstanceCommand LogicalNames LogicalHistory.
From NativeProof Require Import NativeFullDispatcher NativeGeneralDispatcher AxiomStorage NativeBasicInvariant NativeBasicCommandInvariant NativeBasicSession NativeAxiomInvariant NativeSchemaInvariant NativeSchemaGeneralInvariant NativeNameCompact NativeCommandLengths LogicalRegistryBounds LogicalStorageMonotone NativeStateFrames ImmutableHandlers ImmutableStorage CommandChain CommandStructure CommandDispatch CommandQuit NativeCommandFrames ObservedLocal RenameMemoControl CommandInput EffectFrame SchemaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeGeneralCommandInvariant.
Import IndexExecution SipHashExecution NativeFullDispatcher.
Definition checked native logical request bs ns tail observations := exists final reply next,
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical request reply next /\ NativeState.represents final next /\
 NativeCommandBoundary.io native final reply tail /\ Guarantees.safe next /\
 FormulaTopology.ordered final(length(Protocol.formulas next)) /\ ClassLookup.wellformed final.
Lemma finish native logical request bs ns tail observations final reply next :
 Guarantees.safe logical ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) ->
 Protocol.step logical request reply next -> NativeState.represents final next ->
 NativeCommandBoundary.io native final reply tail ->
 FormulaTopology.ordered final(length(Protocol.formulas next)) -> ClassLookup.wellformed final ->
 checked native logical request bs ns tail observations.
Proof.
 intros Hsafe Hrun Hstep Hstate Hio Htop Hgood. exists final,reply,next.
 split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hstate|]. split;[exact Hio|].
 split;[exact(Guarantees.step_safe _ _ _ _ Hstep Hsafe)|]. split;assumption.
Qed.
Theorem graph_generated native logical request bs ns tail observations :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 (31<length (memory native arraydef_0__meta))%nat -> (0<length (memory native arraydef_0__sipState))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat -> (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first (Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical ->
 FormulaTopology.ordered native (length (Protocol.formulas logical)) ->
 nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity -> ClassLookup.wellformed native ->
 NoDup (map fst (Protocol.bindings logical)) -> NativeGeneralDispatcher.resources native logical request ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 checked native logical request bs ns tail observations.
Proof.
 intros Hshape Hbound Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hresources Hinput.
 destruct Hresources as [Hbasic Hschema Hspecific].
 destruct (supported_dec (Protocol.opcode request)) as [Hsupported|Hnot].
 - destruct (NativeBasicCommandInvariant.generated_canonical native logical request bs ns tail observations Hshape Hsupported
     ltac:(lia) Htoken Hprint Hpending Herror Hstate Hsafe Hbasic Htop Hfalse Hgood Hunique Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hio & HsafeNext & HhistoryNext & HnamesNext & Hpost).
   destruct Hpost as (HnextTop & HnextFalse & HnextGood & Hrest). eapply finish;eassumption.
 - pose proof (NativeBasicDispatcher.safe_history logical Hsafe) as HhistoryValid.
   pose proof (NativeBasicDispatcher.safe_names logical Hsafe) as HnamesValid.
   destruct Hbasic as [HformulaRoom HclassRoom HhistoryRoom HbindingRoom HnameRoom].
   destruct (shape_extra request Hshape Hbound Hnot) as [a b|a b|tag a b c|tid name|kind a b c d|ids name].
   all: cbn [NativeGeneralDispatcher.specific_resources NativeFullDispatcher.specific_resources Protocol.opcode Protocol.arguments Protocol.object_name] in Hspecific.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|a' values Ha Hvalues];subst a' values.
     inversion Hvalues as [|b' values Hb Hnil];subst b' values.
     change (meta_value native 15=56) in Hpending. rewrite (binary_rest 7 a b tail ltac:(tauto)) in Hinput.
     destruct (NativeClassBinaryBoundary.Equal.generated_total_protocol 55 [] native logical bs ns a b 32 32 10 tail observations
       eq_refl Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hspecific Ha Hb Hstate Hgood ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hpost & Hsafe').
     destruct Hpost as (Hio & HnextTop & HnextGood & Hrest). eapply finish;eassumption.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|a' values Ha Hvalues];subst a' values.
     inversion Hvalues as [|b' values Hb Hnil];subst b' values.
     change (meta_value native 15=57) in Hpending. rewrite (binary_rest 8 a b tail ltac:(tauto)) in Hinput.
     destruct (NativeClassBinaryBoundary.Member.generated_total_protocol 56 [] native logical bs ns a b 32 32 10 tail observations
       eq_refl Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hspecific Ha Hb Hstate Hgood ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hpost & Hsafe').
     destruct Hpost as (Hio & HnextTop & HnextGood & Hrest). eapply finish;eassumption.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|tag' values Htag Hrest];subst tag' values.
     inversion Hrest as [|a' values Ha Hrest2];subst a' values.
     inversion Hrest2 as [|b' values Hb Hrest3];subst b' values.
     inversion Hrest3 as [|c' values Hc Hnil];subst c' values.
     change (meta_value native 15=50) in Hpending. rewrite axiom_rest in Hinput.
     destruct (NativeAxiomInvariant.generated_total native logical bs ns 49 [49] tag a b c 32 32 32 32 10 tail observations
       eq_refl Hmeta Hsip Htoken Hprint Hpending Herror HhistoryRoom Htag Ha Hb Hc Hstate Htop Hfalse Hgood Hspecific
       ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hio & Hsafe' & HnextTop & HnextGood & Hprefix & Hgrowth).
     eapply finish;eassumption.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hfields.
     destruct Hfields as [Hlen Hname]. inversion Hwords as [|tid' values Htid Hnil];subst tid' values.
     change (meta_value native 15=50) in Hpending. rewrite certify_rest in Hinput.
     destruct (NativeClassCertifyBoundary.generated_total native logical bs ns name tid 32 32 10 tail 0 observations
       Hmeta Hsip Htoken Hprint Hpending Herror Hname Htid Hstate Htop Hfalse Hgood Hunique HnamesValid HhistoryValid Hspecific
       ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hcomplete).
     destruct Hcomplete as (Hrun & Hstep & Hnext & Hio & Hmachine & Hrest).
     destruct Hmachine as (Hlength & Hclear & HnextTop & HnextGood). eapply finish;eassumption.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|kind' values Hkind Hrest];subst kind' values.
     inversion Hrest as [|a' values Ha Hrest2];subst a' values.
     inversion Hrest2 as [|b' values Hb Hrest3];subst b' values.
     inversion Hrest3 as [|c' values Hc Hrest4];subst c' values.
     inversion Hrest4 as [|d' values Hd Hnil];subst d' values.
     change (meta_value native 15=51) in Hpending. rewrite node_rest in Hinput.
     destruct (NativeSchemaInvariant.generated_total native logical bs ns 50 [50] kind a b c d 32 32 32 32 32 10 tail observations
       eq_refl Hsafe ltac:(lia) Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hschema Hstate Hgood Htop
       ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hcomplete & HnextGood & HnextTop & HsameFs & HsameCs & Hgrowth).
     destruct Hcomplete as (Hchecked & Hnext & Hio & Hremaining).
     destruct Hchecked as (Hrun & Hstep & Hrest'). eapply finish;eassumption.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hfields.
     destruct Hfields as [Hname Hlength].
     change (meta_value native 15=51) in Hpending. rewrite instance_rest in Hinput.
     destruct (NativeSchemaGeneralInvariant.generated_canonical native bs ns logical ids name tail observations
       Hmeta Htoken Hsip Hprint Hpending Herror Hname Hwords Hlength Hinput Hstate Hgood Htop Hfalse Hsafe Hspecific)
     as (final & reply & next & Hrun & Hstep & Hnext & Hclear & Hsafe' & Hio & HnextGood & HnextTop & Hprefix & Hclassprefix & Hword).
     eapply finish;eassumption.
Qed.
Import ObservedLocal EffectFrame.
Theorem selected_array watched native bs ns readstate opcode observations final trace :
 (1<=opcode<=26)%nat -> watched<>arraydef_0__meta -> watched<>arraydef_0__token ->
 local_ro watched (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)) ->
 execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (native,observations)=Some(tt,(readstate,observations)) ->
 (17<length (memory readstate arraydef_0__meta))%nat ->
 meta_value readstate 11=Z.of_nat opcode -> meta_value readstate 14=1 -> meta_value readstate 8=0 ->
 memory readstate watched=memory native watched ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 memory final watched=memory native watched.
Proof.
 intros Hrange HwatchedMeta HwatchedToken HhandlerRO Hreader Hmeta Hnumber Hvalid Herror Hparsed Hrun.
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
 - eapply ImmutableHandlers.local_observed_preserves;[apply NativeCommandFrames.postlude_array;tauto|exact Hpost].
 -
 assert (Hhandler:execLocalObserved (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode))
   (CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode),observations)=Some(tt,(middle,middleTrace))).
 { refine (NativeCommandFrames.chain_inverse opcode
     (CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode))
     middle observations middleTrace Hrange _ Herror _ Hchain).
   - unfold CommandDispatch.opcode_frame. cbn [nums setNum]. apply RenameMemoControl.updated_same.
   - change (8<length (memory readstate arraydef_0__meta))%nat;lia. }
 exact (ImmutableHandlers.local_observed_preserves watched _ _ middle observations middleTrace HhandlerRO Hhandler).
Qed.
Theorem canonical_array watched opcode ch chars native bs ns separator payload observations final trace :
 (1<=opcode<=26)%nat -> watched<>arraydef_0__meta -> watched<>arraydef_0__token ->
 local_ro watched (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)) ->
 decimalBytes opcode=ch::chars ->
 (17<length (memory native arraydef_0__meta))%nat -> (1024<=length (memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> TokenByteExecution.separator separator ->
 stdin native=chars++separator::payload ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 memory final watched=memory native watched.
Proof.
 intros Hrange HwatchedMeta HwatchedToken HhandlerRO Hencoding Hmeta Htoken Hpending Herror Hseparator Hinput Hrun.
 assert (Hword:Z.of_nat opcode<=maximum) by (unfold maximum;lia).
 eapply selected_array with (readstate:=CommandInput.parsed native ch chars payload) (opcode:=opcode);try eassumption.
 - exact (CommandInput.generated_pending native (fun _=>false) (fun _=>0) opcode ch chars separator payload observations
     Hmeta Htoken Hpending Herror Hword Hencoding Hseparator Hinput).
 - rewrite CommandInput.parsed_meta_length;exact Hmeta.
 - exact (CommandInput.parsed_number native opcode ch chars payload Hmeta Hword Hencoding).
 - apply CommandInput.parsed_valid;exact Hmeta.
 - rewrite CommandInput.parsed_meta_other by lia. exact Herror.
 - apply CommandInput.parsed_other;assumption.
Qed.
Module Names.
Local Opaque funcdef_0__ok funcdef_0__no funcdef_0__intern funcdef_0__readNat funcdef_0__readToken funcdef_0__lookup
 funcdef_0__appendTheorem funcdef_0__modusPonens funcdef_0__generalize funcdef_0__classEqual funcdef_0__classMember
 funcdef_0__axiom funcdef_0__bindName funcdef_0__setness funcdef_0__schemaInstance funcdef_0__schemaCheck.
Lemma schemaNode bs ns : array_ro arraydef_0__names (funcdef_0__schemaNode bs ns).
Proof.
 pose proof (ImmutableStorage.schemaCheck_ro arraydef_0__names ImmutableStorage.name_array_persistent) as Hcheck.
 pose proof (ImmutableStorage.ok_ro arraydef_0__names ImmutableStorage.name_array_persistent) as Hok.
 pose proof (ImmutableStorage.no_ro arraydef_0__names ImmutableStorage.name_array_persistent) as Hno.
 unfold funcdef_0__schemaNode. apply eliminate_ro. unfold funcdef_0__schemaNode_body. ro.
Qed.
Local Opaque funcdef_0__schemaNode.
Theorem handler_ro opcode : (opcode<=26)%nat -> opcode<>9%nat -> opcode<>20%nat -> opcode<>23%nat ->
 EffectFrame.local_ro arraydef_0__names (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)).
Proof.
 intros Hbound H9 H20 H23.
 pose proof (ImmutableStorage.readNat_ro arraydef_0__names ImmutableStorage.name_array_persistent) as HreadNat.
 pose proof (ImmutableStorage.readToken_ro arraydef_0__names ImmutableStorage.name_array_persistent) as HreadToken.
 pose proof (ImmutableStorage.lookup_ro arraydef_0__names ImmutableStorage.name_array_persistent) as Hlookup.
 pose proof (ImmutableStorage.ok_ro arraydef_0__names ImmutableStorage.name_array_persistent) as Hok.
 pose proof (ImmutableStorage.no_ro arraydef_0__names ImmutableStorage.name_array_persistent) as Hno.
 pose proof (ImmutableStorage.intern_ro arraydef_0__names ImmutableStorage.name_array_persistent) as Hintern.
 pose proof (ImmutableStorage.appendTheorem_ro arraydef_0__names ImmutableStorage.name_array_persistent) as HappendTheorem.
 pose proof (ImmutableStorage.modusPonens_ro arraydef_0__names ImmutableStorage.name_array_persistent) as HmodusPonens.
 pose proof (ImmutableStorage.generalize_ro arraydef_0__names ImmutableStorage.name_array_persistent) as Hgeneralize.
 pose proof (ImmutableStorage.classEqual_ro arraydef_0__names ImmutableStorage.name_array_persistent) as HclassEqual.
 pose proof (ImmutableStorage.classMember_ro arraydef_0__names ImmutableStorage.name_array_persistent) as HclassMember.
 pose proof (ImmutableStorage.axiom_ro arraydef_0__names ImmutableStorage.name_array_persistent) as Haxiom.
 pose proof (ImmutableStorage.setness_ro arraydef_0__names ImmutableStorage.name_array_persistent) as Hsetness.
 pose proof (ImmutableStorage.schemaInstance_ro arraydef_0__names ImmutableStorage.name_array_persistent) as HschemaInstance.
 pose proof (ImmutableStorage.schemaCheck_ro arraydef_0__names ImmutableStorage.name_array_persistent) as HschemaCheck.
 pose proof schemaNode as Hnode.
 let rec cases count tag := lazymatch count with
 | O=>idtac
 | S ?rest=>let next:=fresh "opcode" in destruct tag as [|next];[idtac|cases rest next]
 end in cases 27%nat opcode.
 all: try lia.
 all: match goal with |- context [Z.of_nat ?tag]=>
  let value:=eval compute in (Z.of_nat tag) in change (Z.of_nat tag) with value end.
 all: unfold CommandChain.handler_for;cbn beta iota.
 all: unfold CommandStructure.handler_1, CommandStructure.handler_2, CommandStructure.handler_3, CommandStructure.handler_4, CommandStructure.handler_5, CommandStructure.handler_6, CommandStructure.handler_7, CommandStructure.handler_8, CommandStructure.handler_9, CommandStructure.handler_10, CommandStructure.handler_11, CommandStructure.handler_12, CommandStructure.handler_13, CommandStructure.handler_14, CommandStructure.handler_15, CommandStructure.handler_16, CommandStructure.handler_17, CommandStructure.handler_18, CommandStructure.handler_19, CommandStructure.handler_20, CommandStructure.handler_21, CommandStructure.handler_22, CommandStructure.handler_23, CommandStructure.handler_24, CommandStructure.handler_25, CommandStructure.handler_26.
 all: EffectFrame.ro.
Qed.
End Names.
Lemma request_parts request : Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 exists chars sep payload,
 decimalBytes (Protocol.opcode request)=NativeBasicDispatcher.first (Protocol.opcode request)::chars /\
 TokenByteExecution.separator sep /\ NativeBasicDispatcher.rest request=chars++sep::payload.
Proof.
 intros Hshape Hbound. destruct (NativeFullDispatcher.supported_dec (Protocol.opcode request)) as [Hsupported|Hnot].
 - exact (NativeBasicCommandInvariant.request_parts request Hshape Hsupported).
 - destruct (NativeFullDispatcher.shape_extra request Hshape Hbound Hnot) as [a b|a b|tag a b c|tid name|kind a b c d|ids name].
   + exists [],32,(decimalBytes a++32::decimalBytes b++[10]). split;[reflexivity|]. split;[unfold TokenByteExecution.separator;tauto|].
     pose proof (NativeFullDispatcher.binary_rest 7 a b [] ltac:(tauto)) as Hrest. now rewrite app_nil_r in Hrest.
   + exists [],32,(decimalBytes a++32::decimalBytes b++[10]). split;[reflexivity|]. split;[unfold TokenByteExecution.separator;tauto|].
     pose proof (NativeFullDispatcher.binary_rest 8 a b [] ltac:(tauto)) as Hrest. now rewrite app_nil_r in Hrest.
   + exists [49],32,(decimalBytes tag++32::decimalBytes a++32::decimalBytes b++32::decimalBytes c++[10]). split;[reflexivity|]. split;[unfold TokenByteExecution.separator;tauto|].
     pose proof (NativeFullDispatcher.axiom_rest tag a b c []) as Hrest. now rewrite app_nil_r in Hrest.
   + exists [52],32,(name++32::decimalBytes tid++[10]). split;[reflexivity|]. split;[unfold TokenByteExecution.separator;tauto|].
     pose proof (NativeFullDispatcher.certify_rest tid name []) as Hrest. now rewrite app_nil_r in Hrest.
   + exists [50],32,(decimalBytes kind++32::decimalBytes a++32::decimalBytes b++32::decimalBytes c++32::decimalBytes d++[10]). split;[reflexivity|]. split;[unfold TokenByteExecution.separator;tauto|].
     pose proof (NativeFullDispatcher.node_rest kind a b c d []) as Hrest. now rewrite app_nil_r in Hrest.
   + exists [52],32,(SchemaInstanceCommand.payload ids name []). split;[reflexivity|]. split;[unfold TokenByteExecution.separator;tauto|].
     pose proof (NativeFullDispatcher.instance_rest ids name []) as Hrest. now rewrite app_nil_r in Hrest.
Qed.
Local Opaque funcdef_0__axiom funcdef_0__readNat funcdef_0__appendTheorem funcdef_0__no.
Lemma axiom_handler_ro : local_ro arraydef_0__classes (CommandChain.handler_for funcdef_0__readNat 11).
Proof.
 pose proof (AxiomStorage.arrays_ro arraydef_0__classes ltac:(repeat split;discriminate)) as Haxiom.
 pose proof (NativeBasicInvariant.Arrays.readNat_ro arraydef_0__classes ltac:(repeat split;discriminate)) as Hread.
 pose proof (NativeBasicInvariant.Arrays.appendTheorem_ro arraydef_0__classes ltac:(repeat split;discriminate) ltac:(discriminate)) as Happend.
 pose proof (NativeBasicInvariant.Arrays.no_ro arraydef_0__classes ltac:(repeat split;discriminate)) as Hno.
 unfold CommandChain.handler_for. cbn beta iota. unfold CommandStructure.handler_11. ro.
Qed.
Lemma axiom_class_count native logical request bs ns tail observations final trace next :
 Protocol.shape request -> Protocol.opcode request=11%nat ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> NativeState.represents final next ->
 length(Protocol.classes next)=length(Protocol.classes logical).
Proof.
 intros Hshape Hopcode Hmeta Htoken Hpending Herror Hinput Hrun Hstate Hnext.
 destruct(request_parts request Hshape ltac:(rewrite Hopcode;lia)) as (chars & sep & payload & Hencoding & Hsep & Hparts).
 rewrite Hparts,<-app_assoc in Hinput. change(stdin native=chars++sep::(payload++tail)) in Hinput.
 assert(Hraw:memory final arraydef_0__classes=memory native arraydef_0__classes).
 { eapply canonical_array with (opcode:=Protocol.opcode request);try eassumption;try discriminate.
   - rewrite Hopcode;lia.
   - rewrite Hopcode. change (Z.of_nat 11) with 11. exact axiom_handler_ro. }
 rewrite <-(NativeBasicCommandInvariant.class_count _ _ Hstate),<-(NativeBasicCommandInvariant.class_count _ _ Hnext),Hraw. reflexivity.
Qed.
Lemma compact_step native logical request bs ns tail observations final trace reply next :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical -> NativeBasicDispatcher.resources native logical request ->
 NativeNameCompact.compact native logical -> stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 Protocol.step logical request reply next -> NativeState.represents final next -> NativeNameCompact.compact final next.
Proof.
 intros Hshape Hbound Hmeta Htoken Hprint Hpending Herror Hstate Hsafe Hresources Hcompact Hinput Hrun Hstep Hnext.
 destruct(NativeFullDispatcher.supported_dec (Protocol.opcode request)) as [Hsupported|Hnot].
 - destruct Hresources as [HformulaRoom HclassRoom HhistoryRoom HbindingRoom HnameRoom].
   exact(NativeBasicSession.compact_step native logical request bs ns tail observations final trace reply next
     Hshape Hsupported Hmeta Htoken Hprint Hpending Herror HbindingRoom HnameRoom Hstate
     (NativeBasicDispatcher.safe_history logical Hsafe) Hcompact Hinput Hrun Hstep Hnext).
 - assert (H9:Protocol.opcode request<>9%nat /\ Protocol.opcode request<>20%nat /\ Protocol.opcode request<>23%nat).
   { unfold NativeBasicDispatcher.supported,NativeBasicDispatcher.named in Hnot;intuition. }
   destruct H9 as [H9 [H20 H23]].
   destruct(request_parts request Hshape Hbound) as (chars & sep & payload & Hencoding & Hsep & Hparts).
   rewrite Hparts,<-app_assoc in Hinput. change(stdin native=chars++sep::(payload++tail)) in Hinput.
   assert(Hraw:memory final arraydef_0__names=memory native arraydef_0__names).
   { exact(canonical_array arraydef_0__names (Protocol.opcode request) _ chars native bs ns sep (payload++tail) observations final trace
       Hbound ltac:(discriminate) ltac:(discriminate) (Names.handler_ro (Protocol.opcode request) ltac:(lia) H9 H20 H23)
       Hencoding Hmeta Htoken Hpending Herror Hsep Hinput Hrun). }
   unfold NativeNameCompact.compact,NativeNameCompact.compact_bindings in *.
   rewrite Hraw. change(length(memory native arraydef_0__names)=NativeNameCompact.bytes next).
   rewrite(NativeNameCompact.step_bytes_unchanged logical request reply next H9 H20 H23 Hstep). exact Hcompact.
Qed.
Definition post (native:Machine) logical (final:Machine) next :=
 Guarantees.safe next /\ FormulaTopology.ordered final(length(Protocol.formulas next)) /\
 ClassLookup.wellformed final /\ NativeNameCompact.compact final next /\
 LogicalRegistryBounds.unique next /\ nth_error(Protocol.formulas next)0=Some SetTheory.falsity /\
 length(memory final arraydef_0__meta)=length(memory native arraydef_0__meta) /\
 length(memory final arraydef_0__sipState)=length(memory native arraydef_0__sipState) /\
 (31<length(memory final arraydef_0__meta))%nat /\ (0<length(memory final arraydef_0__sipState))%nat /\
 LogicalStorageMonotone.extends logical next /\ LogicalRegistryBounds.counts logical next 1.
Theorem preserves native logical request bs ns tail observations final trace reply next :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat -> (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> LogicalRegistryBounds.unique logical -> NativeNameCompact.compact native logical ->
 NativeGeneralDispatcher.resources native logical request -> stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 Protocol.step logical request reply next -> NativeState.represents final next -> post native logical final next.
Proof.
 intros Hshape Hbound Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hcompact Hresources Hinput Hrun Hstep Hnext.
 destruct(graph_generated native logical request bs ns tail observations Hshape Hbound Hmeta Hsip Htoken Hprint Hpending Herror
   Hstate Hsafe Htop Hfalse Hgood Hunique Hresources Hinput)
   as(model & modelReply & after & HmodelRun & HmodelStep & HmodelState & HmodelIo & HmodelSafe & HmodelTop & HmodelGood).
 assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
 pose proof(NativeBasicCommandInvariant.formula_count _ _ HmodelState) as HmodelCount.
 pose proof(NativeBasicCommandInvariant.formula_count _ _ Hnext) as HnextCount.
 assert(Hcount:length(Protocol.formulas next)=length(Protocol.formulas after)) by lia.
 pose proof(NativeCommandLengths.generated arraydef_0__meta native bs ns final observations trace NativeCommandLengths.meta_protected Hrun) as HmetaLength.
 pose proof(NativeCommandLengths.generated arraydef_0__sipState native bs ns final observations trace NativeCommandLengths.sipState_protected Hrun) as HsipLength.
 unfold post. split;[exact(Guarantees.step_safe _ _ _ _ Hstep Hsafe)|]. split;[now rewrite Hcount|].
 split;[exact HmodelGood|]. split.
 - exact(compact_step native logical request bs ns tail observations final trace reply next Hshape Hbound ltac:(lia) Htoken Hprint
     Hpending Herror Hstate Hsafe (NativeGeneralDispatcher.basic_resources _ _ _ Hresources) Hcompact Hinput Hrun Hstep Hnext).
 - split;[exact(LogicalRegistryBounds.step_unique _ _ _ _ Hstep Hunique)|]. split.
   + exact(LogicalStorageMonotone.formula_lookup logical next 0 SetTheory.falsity (LogicalStorageMonotone.step _ _ _ _ Hstep) Hfalse).
   + split;[exact HmetaLength|]. split;[exact HsipLength|]. split;[now rewrite HmetaLength|]. split;[now rewrite HsipLength|].
     split;[exact(LogicalStorageMonotone.step _ _ _ _ Hstep)|exact(LogicalRegistryBounds.step_counts _ _ _ _ Hstep)].
Qed.
Theorem generated_canonical native logical request bs ns tail observations :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat -> (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> LogicalRegistryBounds.unique logical -> NativeNameCompact.compact native logical ->
 NativeGeneralDispatcher.resources native logical request -> stdin native=NativeBasicDispatcher.rest request++tail ->
 exists final reply next,
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical request reply next /\ NativeState.represents final next /\
 NativeCommandBoundary.io native final reply tail /\ post native logical final next.
Proof.
 intros Hshape Hbound Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hcompact Hresources Hinput.
 destruct(graph_generated native logical request bs ns tail observations Hshape Hbound Hmeta Hsip Htoken Hprint Hpending Herror
   Hstate Hsafe Htop Hfalse Hgood Hunique Hresources Hinput)
   as(final & reply & next & Hrun & Hstep & Hnext & Hio & HsafeNext & HtopNext & HgoodNext).
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hnext|]. split;[exact Hio|].
 exact(preserves native logical request bs ns tail observations final _ reply next Hshape Hbound Hmeta Hsip Htoken Hprint Hpending Herror
   Hstate Hsafe Htop Hfalse Hgood Hunique Hcompact Hresources Hinput Hrun Hstep Hnext).
Qed.
End NativeGeneralCommandInvariant.
