From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal RenameMemoControl NativeState NativeStateFrames
 NativeCommandFrames NativeProtocolLift CommandInput CommandQuit CommandDispatch CommandChain CommandSchemaFrame
 ImmutableHandlers SchemaProtocolFrame TokenByte Representation ClassStorage HistoryRefinement NameRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSchemaLift.
Import IndexExecution SipHashExecution ObservedLocal CommandQuitExecution.
(** Naming and certification may change bindings, but they cannot change the
    immutable schema graph. Its semantic interpretation survives arena growth. *)
Theorem generated_frame native bs ns readstate opcode observations final trace :
 (1<=opcode<=26)%nat -> opcode<>22%nat ->
 execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (native,observations)=Some(tt,(readstate,observations)) ->
 (17<length (memory readstate arraydef_0__meta))%nat ->
 meta_value readstate 11=Z.of_nat opcode -> meta_value readstate 14=1 -> meta_value readstate 8=0 ->
 meta_value readstate 16=meta_value native 16 -> memory readstate arraydef_0__schemaNodes=memory native arraydef_0__schemaNodes ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 meta_value final 16=meta_value native 16 /\ memory final arraydef_0__schemaNodes=memory native arraydef_0__schemaNodes.
Proof.
 intros Hrange HnotNode Hreader Hmeta Hnumber Hvalid Herror HparsedCount HparsedNodes Hrun.
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
 pose proof (NativeCommandFrames.postlude_registries middle finished middleTrace finalTrace Hpost) as HpostFrame.
 split.
 - exact (eq_trans (NativeStateFrames.schema_count _ _ HpostFrame)
     (eq_trans (CommandSchemaFrame.local_count _ parsed middle observations middleTrace
       (CommandSchemaFrame.count_ro opcode ltac:(lia) HnotNode) Hhandler) HparsedCount)).
 - exact (eq_trans (NativeStateFrames.schemas _ _ HpostFrame)
     (eq_trans (ImmutableHandlers.local_observed_preserves arraydef_0__schemaNodes _ parsed middle observations middleTrace
       (CommandSchemaFrame.nodes_ro opcode ltac:(lia) HnotNode) Hhandler) HparsedNodes)).
Qed.
Theorem canonical opcode ch chars native bs ns separator payload observations final trace logical request reply next :
 (1<=opcode<=26)%nat -> opcode<>22%nat -> Protocol.opcode request=opcode -> decimalBytes opcode=ch::chars ->
 (17<length (memory native arraydef_0__meta))%nat -> (1024<=length (memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> TokenByteExecution.separator separator ->
 stdin native=chars++separator::payload ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> Protocol.step logical request reply next ->
 NativeRepresentation.canonical_arena final (Protocol.formulas next) ->
 ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) -> HistoryRefinement.represents final next ->
 NameRepresentation.represents final (Protocol.bindings next) -> NativeState.represents final next.
Proof.
 intros Hrange HnotNode Hopcode Hencoding Hmeta Htoken Hpending Herror Hseparator Hinput Hrun Hstate Hstep Harena Hclasses Hhistory Hnames.
 assert (Hword:Z.of_nat opcode<=maximum) by (unfold maximum;lia).
 destruct (generated_frame native bs ns (CommandInput.parsed native ch chars payload) opcode observations final trace
   Hrange HnotNode
   (CommandInput.generated_pending native (fun _=>false) (fun _=>0) opcode ch chars separator payload observations
     Hmeta Htoken Hpending Herror Hword Hencoding Hseparator Hinput)
   ltac:(now rewrite CommandInput.parsed_meta_length)
   (CommandInput.parsed_number native opcode ch chars payload Hmeta Hword Hencoding)
   (CommandInput.parsed_valid native ch chars payload Hmeta)
   ltac:(rewrite CommandInput.parsed_meta_other by lia;exact Herror)
   ltac:(apply CommandInput.parsed_meta_other;lia) ltac:(apply CommandInput.parsed_other;discriminate) Hrun)
 as [Hcount Hnodes].
 constructor;try assumption.
 eapply SchemaProtocolFrame.preserves;[exact (NativeState.schema_representation _ _ Hstate)|exact Hstep|
   now rewrite Hopcode|exact Hcount|exact Hnodes].
Qed.
End NativeSchemaLift.
