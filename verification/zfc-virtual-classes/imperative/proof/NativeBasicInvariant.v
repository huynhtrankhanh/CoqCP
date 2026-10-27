From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash EffectFrame PrintingFrame ImmutableStorage ImmutableHandlers
 NativeBasicDispatcher NativeCommandFrames NativeStateFrames NativeProtocolLift NativeState CommandQuit CommandStructure CommandChain CommandDispatch
 ObservedLocal RenameMemoControl RenameStorage CommandInput TokenByte FormulaTopology ClassLookup HashTable
 NativeSimpleCommands FormulaEncoding Representation ArenaFrame FormulaProjection Intern InternBounded Observation ReplyOK ReadOne ReadTwo.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeBasicInvariant.
Import IndexExecution SipHashExecution ObservedLocal.
Module Arrays.
Import EffectFrame.
Definition scratch watched := arraydef_0__meta<>watched /\ arraydef_0__token<>watched /\ arraydef_0__printBuffer<>watched.
Theorem tokenByte_ro watched (Hprotected : scratch watched) bs ns : array_ro watched (funcdef_0__tokenByte bs ns).
Proof. unfold scratch in Hprotected.
  unfold funcdef_0__tokenByte. apply eliminate_ro. unfold funcdef_0__tokenByte_body. ro.
Qed.
Local Opaque funcdef_0__tokenByte.
Theorem readToken_ro watched (Hprotected : scratch watched) bs ns : array_ro watched (funcdef_0__readToken bs ns).
Proof. unfold scratch in Hprotected.
  pose proof (tokenByte_ro watched Hprotected) as Hdep0.
  unfold funcdef_0__readToken. apply eliminate_ro. unfold funcdef_0__readToken_body. ro.
Qed.
Local Opaque funcdef_0__readToken.
Theorem readNat_ro watched (Hprotected : scratch watched) bs ns : array_ro watched (funcdef_0__readNat bs ns).
Proof. unfold scratch in Hprotected.
  pose proof (readToken_ro watched Hprotected) as Hdep0.
  unfold funcdef_0__readNat. apply eliminate_ro. unfold funcdef_0__readNat_body. ro.
Qed.
Local Opaque funcdef_0__readNat.
Theorem lookup_ro watched (Hprotected : scratch watched) bs ns : array_ro watched (funcdef_0__lookup bs ns).
Proof. unfold scratch in Hprotected.
  unfold funcdef_0__lookup. apply eliminate_ro. unfold funcdef_0__lookup_body. ro.
Qed.
Local Opaque funcdef_0__lookup.
Theorem ok_ro watched (Hprotected : scratch watched) bs ns : array_ro watched (funcdef_0__ok bs ns).
Proof. unfold scratch in Hprotected.
  unfold funcdef_0__ok. apply eliminate_ro. unfold funcdef_0__ok_body.
  apply local_bind.
  - apply string_ro. intro ch. ro.
  - intros [].
    change (local_ro watched
      ((numberLocalGet _ _ _ vardef_0__ok_value >>= fun value =>
        liftToWithLocalVariables (PrintingFrame.translate_print (funcdef_0_PrintInt64_unsigned
          (fun _ => false) (update (fun _ => 0%Z) vardef_0_PrintInt64_unsigned_num value))))
      >>= fun _ => writeChar _ _ _ (coerceInt 10 8) >>= fun _ =>
        flush _ _ _ >>= fun _ => Done _ _ _ tt)).
    apply local_bind.
    + apply local_bind; [ro|intro value; apply local_lift; apply ImmutableStorage.print_ro; tauto].
    + intros []. ro.
Qed.
Local Opaque funcdef_0__ok.
Theorem no_ro watched (Hprotected : scratch watched) bs ns : array_ro watched (funcdef_0__no bs ns).
Proof. unfold scratch in Hprotected.
  unfold funcdef_0__no. apply eliminate_ro. unfold funcdef_0__no_body. ro.
Qed.
Local Opaque funcdef_0__no.
Theorem appendTheorem_ro watched (Hprotected : scratch watched) (Htheorems:arraydef_0__theorems<>watched) bs ns : array_ro watched (funcdef_0__appendTheorem bs ns).
Proof. unfold scratch in Hprotected.
  pose proof (ok_ro watched Hprotected) as H_ok.
  unfold funcdef_0__appendTheorem. apply eliminate_ro. unfold funcdef_0__appendTheorem_body. ro.
Qed.
Local Opaque funcdef_0__appendTheorem.
Theorem modusPonens_ro watched (Hprotected : scratch watched) (Htheorems:arraydef_0__theorems<>watched) bs ns : array_ro watched (funcdef_0__modusPonens bs ns).
Proof. unfold scratch in Hprotected.
  pose proof (appendTheorem_ro watched Hprotected Htheorems) as H_appendTheorem.
  pose proof (no_ro watched Hprotected) as H_no.
  unfold funcdef_0__modusPonens. apply eliminate_ro. unfold funcdef_0__modusPonens_body. ro.
Qed.
Local Opaque funcdef_0__modusPonens.
Lemma bindName_ro watched (Hprotected:scratch watched) (Hnames:arraydef_0__names<>watched) (Hbindings:arraydef_0__bindings<>watched) bs ns :
 array_ro watched (funcdef_0__bindName bs ns).
Proof.
 pose proof (ok_ro watched Hprotected) as Hok. pose proof (no_ro watched Hprotected) as Hno.
 pose proof (lookup_ro watched Hprotected) as Hlookup.
 unfold scratch in Hprotected. unfold funcdef_0__bindName. apply eliminate_ro. unfold funcdef_0__bindName_body. ro.
Qed.
Local Opaque funcdef_0__bindName funcdef_0__intern.
Lemma generalize_ro watched (Hprotected:scratch watched) (Hpersistent:RenameStorage.Arrays.persistent_array watched)
 (Htheorems:arraydef_0__theorems<>watched) bs ns : array_ro watched (funcdef_0__generalize bs ns).
Proof.
 pose proof (RenameStorage.Arrays.intern_ro watched Hpersistent) as Hintern.
 pose proof (appendTheorem_ro watched Hprotected Htheorems) as Happend.
 unfold scratch in Hprotected. unfold funcdef_0__generalize. apply eliminate_ro. unfold funcdef_0__generalize_body. ro.
Qed.
Local Opaque funcdef_0__generalize funcdef_0__appendTheorem funcdef_0__modusPonens.
Definition kind watched := watched=arraydef_0__formulas \/ watched=arraydef_0__classes \/ watched=arraydef_0__names.
Definition unchanged opcode watched :=
 (watched=arraydef_0__formulas -> opcode<>1%nat /\ opcode<>2%nat /\ opcode<>3%nat /\ opcode<>4%nat /\ opcode<>13%nat) /\
 (watched=arraydef_0__classes -> opcode<>5%nat /\ opcode<>6%nat) /\
 (watched=arraydef_0__names -> opcode<>9%nat /\ opcode<>20%nat /\ opcode<>23%nat).
Theorem handler_ro watched opcode : kind watched -> unchanged opcode watched -> NativeBasicDispatcher.supported opcode ->
 local_ro watched (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)).
Proof.
 intros Hkind Hallowed Hsupported.
 pose proof (NativeBasicDispatcher.supported_bound opcode Hsupported) as Hbound.
 unfold NativeBasicDispatcher.supported,NativeBasicDispatcher.two,NativeBasicDispatcher.one,NativeBasicDispatcher.zero,
 NativeBasicDispatcher.named,NativeBasicDispatcher.query in Hsupported.
 unfold kind in Hkind. destruct Hkind as [->|[->| ->]].
 all: let rec cases count tag := lazymatch count with
 |O=>idtac|S ?rest=>let next:=fresh "opcode" in destruct tag as [|next];[idtac|cases rest next] end in cases 27%nat opcode.
 all:try lia.
 all:try (exfalso;unfold unchanged in Hallowed;intuition congruence).
 all:match goal with |-context[Z.of_nat ?tag]=>let value:=eval compute in (Z.of_nat tag) in change (Z.of_nat tag) with value end.
 all:unfold CommandChain.handler_for;cbn beta iota.
 all:unfold CommandStructure.handler_1,CommandStructure.handler_2,CommandStructure.handler_3,CommandStructure.handler_4,CommandStructure.handler_5,CommandStructure.handler_6,CommandStructure.handler_9,CommandStructure.handler_10,CommandStructure.handler_12,CommandStructure.handler_13,CommandStructure.handler_15,CommandStructure.handler_16,CommandStructure.handler_17,CommandStructure.handler_18,CommandStructure.handler_19,CommandStructure.handler_20,CommandStructure.handler_21,CommandStructure.handler_23,CommandStructure.handler_25,CommandStructure.handler_26.
 all:match goal with |-local_ro ?watched _ =>
  let Hscratch:=fresh "Hscratch" in assert(Hscratch:scratch watched) by (repeat split;discriminate);
  pose proof (readNat_ro watched Hscratch) as HreadNat;
  pose proof (readToken_ro watched Hscratch) as HreadToken;
  pose proof (lookup_ro watched Hscratch) as Hlookup;
  pose proof (ok_ro watched Hscratch) as Hok;
  pose proof (no_ro watched Hscratch) as Hno;
  pose proof (appendTheorem_ro watched Hscratch ltac:(discriminate)) as Happend;
  pose proof (modusPonens_ro watched Hscratch ltac:(discriminate)) as Hmp;
  try (pose proof (RenameStorage.Arrays.intern_ro watched ltac:(repeat split;discriminate)) as Hintern);
  try (pose proof (generalize_ro watched Hscratch ltac:(repeat split;discriminate) ltac:(discriminate)) as Hgen);
  try (pose proof (bindName_ro watched Hscratch ltac:(discriminate) ltac:(discriminate)) as Hbind)
 end.
 all:ro.
Qed.
End Arrays.
Theorem generated_array watched native bs ns readstate opcode observations final trace :
 (1<=opcode<=26)%nat -> Arrays.kind watched -> Arrays.unchanged opcode watched -> NativeBasicDispatcher.supported opcode ->
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
 Arrays.kind watched -> Arrays.unchanged opcode watched -> NativeBasicDispatcher.supported opcode ->
 decimalBytes opcode=ch::chars ->
 (17<length (memory native arraydef_0__meta))%nat -> (1024<=length (memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> TokenByteExecution.separator separator ->
 stdin native=chars++separator::payload ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 memory final watched=memory native watched.
Proof.
 intros Hkind Hallowed Hsupported Hencoding Hmeta Htoken Hpending Herror Hseparator Hinput Hrun.
 pose proof (NativeBasicDispatcher.supported_bound opcode Hsupported) as Hbound.
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
End NativeBasicInvariant.
