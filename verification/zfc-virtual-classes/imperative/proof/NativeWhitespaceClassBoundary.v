From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash NativeState NativeClassCommands NativeHistoryCommands NativeSimpleCommands
 ClassSetInput ClassAbstractInput ClassSetRefinement ClassAbstractRefinement ClassStorage ReadOne CommandInput CommandArgs DecimalInput ReadNat ReadToken
 ReplyOK ReplyNO UndoInput UndoPositive ResetInput CommandReset TokenByte Representation HistoryRefinement.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From NativeProof Require Import NativeWhitespaceClassCommands NativeWhitespaceClassSetInput NativeWhitespaceClassAbstractInput.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceClassBoundary.
Import IndexExecution SipHashExecution.
Definition io before after reply tail :=
 stdin after=tail /\ stdout after=stdout before++Protocol.reply_bytes reply /\
 (1024<=length (memory after arraydef_0__token))%nat /\
 (20<=length (memory after arraydef_0__printBuffer))%nat /\
 meta_value after 8=0 /\ meta_value after 9=meta_value before 9.
Definition boundary before logical after reply next tail := io before after reply tail /\
 Protocol.formulas next=Protocol.formulas logical /\
 (length (Protocol.classes next)<=S (length (Protocol.classes logical)))%nat /\
 (length (Protocol.history next)<=length (Protocol.history logical))%nat.
Lemma argument_token native ch chars value sep tail :
 length (memory (ReadOne.argument_state native ch chars value sep tail) arraydef_0__token)=length (memory native arraydef_0__token).
Proof. apply NativeSimpleCommands.read_one_token_length. Qed.
Lemma allocated_io native parsed count entry tail :
 stdin parsed=tail -> stdout parsed=stdout native ->
 (1024<=length (memory parsed arraydef_0__token))%nat ->
 (20<=length (memory parsed arraydef_0__printBuffer))%nat ->
 meta_value parsed 8=0 -> meta_value parsed 9=meta_value native 9 ->
 io native (ClassStorage.result parsed count entry) (Protocol.OK count) tail.
Proof.
 intros Hin Hout Htoken Hprint Herror Hstop. unfold io. split.
 - unfold ClassStorage.result. change (stdin (ReplyOKExecution.reply_state (ClassStorage.written parsed count entry) count)=tail).
   rewrite ReplyOKExecution.reply_input. exact Hin.
 - split.
   + unfold ClassStorage.result. change (stdout (ReplyOKExecution.reply_state (ClassStorage.written parsed count entry) count)=stdout native++Protocol.reply_bytes (Protocol.OK count)).
     rewrite ReplyOKExecution.reply_output. change (stdout parsed++Protocol.reply_bytes (Protocol.OK count)=stdout native++Protocol.reply_bytes (Protocol.OK count)). now rewrite Hout.
   + split.
     * rewrite ClassStorage.result_other by discriminate. exact Htoken.
     * split.
       -- unfold ClassStorage.result. rewrite store_meta_other by discriminate.
          rewrite ReplyOKExecution.reply_buffer_length,ClassStorage.written_other by discriminate. exact Hprint.
       -- split;rewrite ClassStorage.result_meta_other by lia;assumption.
Qed.
Lemma parsed_facts native ch chars value sep tail :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat -> meta_value native 8=0 ->
 stdin (ReadOne.argument_state native ch chars value sep tail)=tail /\
 stdout (ReadOne.argument_state native ch chars value sep tail)=stdout native /\
 (1024<=length (memory (ReadOne.argument_state native ch chars value sep tail) arraydef_0__token))%nat /\
 (20<=length (memory (ReadOne.argument_state native ch chars value sep tail) arraydef_0__printBuffer))%nat /\
 meta_value (ReadOne.argument_state native ch chars value sep tail) 8=0 /\
 meta_value (ReadOne.argument_state native ch chars value sep tail) 9=meta_value native 9.
Proof.
 intros Hmeta Htoken Hprint Herror. split;[reflexivity|]. split.
 - unfold ReadOne.argument_state,ReadOne.opcode_state,DecimalInput.encoded_result,ReadNatExecution.token_number.
   change (stdout (ReadTokenExecution.read_result (CommandInput.parsed native ch chars (decimalBytes value++sep::tail)) (decimalBytes value) tail)=stdout native).
   rewrite ReadTokenExecution.result_output. apply CommandInput.parsed_output.
 - split.
   + rewrite argument_token. exact Htoken.
   + split.
     * rewrite ReadOne.argument_other by discriminate. exact Hprint.
     * split;rewrite ReadOne.argument_meta_other by (try exact Hmeta;lia);assumption || reflexivity.
Qed.
Lemma set_io native count value sep tail :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat -> meta_value native 8=0 ->
 io native (ClassSetInput.result native count value sep tail) (Protocol.OK count) tail.
Proof.
 intros Hmeta Htoken Hprint Herror.
 destruct (parsed_facts native 53 [] value sep tail Hmeta Htoken Hprint Herror) as (Hin & Hout & Ht & Hp & He & Hs).
 unfold ClassSetInput.result. eapply allocated_io;[exact Hin|exact Hout|exact Ht|exact Hp|exact He|exact Hs].
Qed.
Lemma abstract_io native count value sep tail :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat -> meta_value native 8=0 ->
 io native (ClassAbstractInput.result native count value sep tail) (Protocol.OK count) tail.
Proof.
 intros Hmeta Htoken Hprint Herror.
 destruct (parsed_facts native 54 [] value sep tail Hmeta Htoken Hprint Herror) as (Hin & Hout & Ht & Hp & He & Hs).
 unfold ClassAbstractInput.result. eapply allocated_io;[exact Hin|exact Hout|exact Ht|exact Hp|exact He|exact Hs].
Qed.
Lemma abstract_rejected_io native value sep tail :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat -> meta_value native 8=0 ->
 io native (ClassAbstractInput.rejected native value sep tail) Protocol.NO tail.
Proof.
 intros Hmeta Htoken Hprint Herror.
 destruct (parsed_facts native 54 [] value sep tail Hmeta Htoken Hprint Herror) as (Hin & Hout & Ht & Hp & He & Hs).
 unfold io,ClassAbstractInput.rejected. split;[exact Hin|]. split.
 - change (stdout (ClassAbstractInput.argument_state native value sep tail)++Protocol.reply_bytes Protocol.NO=stdout native++Protocol.reply_bytes Protocol.NO). exact (f_equal (fun bytes=>bytes++Protocol.reply_bytes Protocol.NO) Hout).
 - split;[exact Ht|]. split;[exact Hp|]. split;assumption.
Qed.


Theorem generated_set native logical bs ns value first spaces last tail observations :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=54 -> meta_value native 8=0 ->
 Z.of_nat (length (Protocol.classes logical))<maximum -> Z.of_nat value<=maximum ->
 NativeState.represents native logical ->
 TokenByteExecution.separator first -> TokenByteExecution.separator last -> Forall TokenByteExecution.separator spaces ->
 stdin native=first::spaces++decimalBytes value++last::tail ->
 exists final,
 execObserved (funcdef_0__command bs ns) (native,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes (Protocol.OK (length (Protocol.classes logical)));unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 5 [value] []) (Protocol.OK (length (Protocol.classes logical)))
   (ClassSetRefinement.logical_after logical value) /\
 NativeState.represents final (ClassSetRefinement.logical_after logical value) /\
 boundary native logical final (Protocol.OK (length (Protocol.classes logical))) (ClassSetRefinement.logical_after logical value) tail.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hstate Hfirst Hlast Hspaces Hinput.
 destruct (NativeWhitespaceClassCommands.generated_set native logical bs ns value first spaces last tail observations
  Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hstate Hfirst Hlast Hspaces Hinput) as (final & Hrun & Hstep & Hfinal).
 pose proof (NativeWhitespaceClassSetInput.generated_pending native bs ns (length (Protocol.classes logical)) value first spaces last tail observations
  Hmeta Htoken Hprint Hpending Herror (proj1 (NativeState.class_representation _ _ Hstate)) Hroom Hvalue Hfirst Hlast Hspaces Hinput) as Hexpected.
 assert (Hsame:final=ClassSetInput.result native (length (Protocol.classes logical)) value last tail) by congruence.
 subst final. eexists. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hfinal|].
 unfold boundary. split;[now apply set_io|]. split;[reflexivity|]. split;[|reflexivity].
 cbn [ClassSetRefinement.logical_after Protocol.classes]. rewrite length_app;cbn;lia.
Qed.
Theorem generated_abstract native logical bs ns value p first spaces last tail observations :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=55 -> meta_value native 8=0 ->
 Z.of_nat (length (Protocol.classes logical))<maximum -> Z.of_nat value<=maximum ->
 Protocol.formula_at logical value=Some p -> NativeState.represents native logical ->
 TokenByteExecution.separator first -> TokenByteExecution.separator last -> Forall TokenByteExecution.separator spaces ->
 stdin native=first::spaces++decimalBytes value++last::tail ->
 exists final,
 execObserved (funcdef_0__command bs ns) (native,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes (Protocol.OK (length (Protocol.classes logical)));unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 6 [value] []) (Protocol.OK (length (Protocol.classes logical)))
   (ClassAbstractRefinement.logical_after logical p) /\
 NativeState.represents final (ClassAbstractRefinement.logical_after logical p) /\
 boundary native logical final (Protocol.OK (length (Protocol.classes logical))) (ClassAbstractRefinement.logical_after logical p) tail.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hlookup Hstate Hfirst Hlast Hspaces Hinput.
 destruct (NativeWhitespaceClassCommands.generated_abstract native logical bs ns value p first spaces last tail observations
  Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hlookup Hstate Hfirst Hlast Hspaces Hinput) as (final & Hrun & Hstep & Hfinal).
 pose proof (NativeState.formula_representation _ _ Hstate) as Harena.
 assert (Hreference:Z.of_nat value<meta_value native 1).
 { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
   change (meta_value native 1=Z.of_nat (length (Protocol.formulas logical))) in Hcount.
   assert (Hi:(value<length (Protocol.formulas logical))%nat) by (apply nth_error_Some;unfold Protocol.formula_at in Hlookup;congruence).
   rewrite Hcount;lia. }
 pose proof (NativeWhitespaceClassAbstractInput.generated_pending native bs ns (length (Protocol.classes logical)) value first spaces last tail observations
  Hmeta Htoken Hprint Hpending Herror (proj1 (NativeState.class_representation _ _ Hstate)) Hroom Hvalue Hreference Hfirst Hlast Hspaces Hinput) as Hexpected.
 assert (Hsame:final=ClassAbstractInput.result native (length (Protocol.classes logical)) value last tail) by congruence.
 subst final. eexists. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hfinal|].
 unfold boundary. split;[now apply abstract_io|]. split;[reflexivity|]. split;[|reflexivity].
 cbn [ClassAbstractRefinement.logical_after Protocol.classes]. rewrite length_app;cbn;lia.
Qed.
Theorem generated_abstract_rejected native logical bs ns value first spaces last tail observations :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=55 -> meta_value native 8=0 -> Z.of_nat value<=maximum ->
 Protocol.formula_at logical value=None -> NativeState.represents native logical ->
 TokenByteExecution.separator first -> TokenByteExecution.separator last -> Forall TokenByteExecution.separator spaces ->
 stdin native=first::spaces++decimalBytes value++last::tail ->
 exists final,
 execObserved (funcdef_0__command bs ns) (native,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes Protocol.NO;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 6 [value] []) Protocol.NO logical /\ NativeState.represents final logical /\ boundary native logical final Protocol.NO logical tail.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hvalue Hlookup Hstate Hfirst Hlast Hspaces Hinput.
 destruct (NativeWhitespaceClassCommands.generated_abstract_rejected native logical bs ns value first spaces last tail observations
  Hmeta Htoken Hprint Hpending Herror Hvalue Hlookup Hstate Hfirst Hlast Hspaces Hinput) as (final & Hrun & Hstep & Hfinal).
 pose proof (NativeState.formula_representation _ _ Hstate) as Harena.
 assert (Hreference:meta_value native 1<=Z.of_nat value).
 { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
   change (meta_value native 1=Z.of_nat (length (Protocol.formulas logical))) in Hcount.
   pose proof Hlookup as Hi. unfold Protocol.formula_at in Hi. apply nth_error_None in Hi. rewrite Hcount;lia. }
 pose proof (NativeWhitespaceClassAbstractInput.generated_rejected native bs ns value first spaces last tail observations
  Hmeta Htoken Hprint Hpending Herror Hvalue Hreference Hfirst Hlast Hspaces Hinput) as Hexpected.
 assert (Hsame:final=ClassAbstractInput.rejected native value last tail) by congruence.
 subst final. eexists. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hfinal|].
 unfold boundary. split;[now apply abstract_rejected_io|]. repeat split;lia.
Qed.
Theorem generated_abstract_total native logical bs ns value first spaces last tail observations :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=55 -> meta_value native 8=0 ->
 Z.of_nat (length (Protocol.classes logical))<maximum -> Z.of_nat value<=maximum ->
 NativeState.represents native logical ->
 TokenByteExecution.separator first -> TokenByteExecution.separator last -> Forall TokenByteExecution.separator spaces ->
 stdin native=first::spaces++decimalBytes value++last::tail ->
 exists final reply next,
 execObserved (funcdef_0__command bs ns) (native,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 6 [value] []) reply next /\ NativeState.represents final next /\ boundary native logical final reply next tail.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hstate Hfirst Hlast Hspaces Hinput.
 destruct (Protocol.formula_at logical value) as [p|] eqn:Hlookup.
 - destruct (generated_abstract native logical bs ns value p first spaces last tail observations
    Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hlookup Hstate Hfirst Hlast Hspaces Hinput) as [final Hresult].
   exists final,(Protocol.OK (length (Protocol.classes logical))),(ClassAbstractRefinement.logical_after logical p). exact Hresult.
 - destruct (generated_abstract_rejected native logical bs ns value first spaces last tail observations
    Hmeta Htoken Hprint Hpending Herror Hvalue Hlookup Hstate Hfirst Hlast Hspaces Hinput) as [final Hresult].
   exists final,Protocol.NO,logical. exact Hresult.
Qed.

End NativeWhitespaceClassBoundary.
