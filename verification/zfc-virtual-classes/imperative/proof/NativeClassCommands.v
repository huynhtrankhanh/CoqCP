From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadOne ClassStorage ClassSetInput
 ClassSetRefinement ClassAbstractInput ClassAbstractRefinement Representation HistoryRefinement
 NativeState NativeStateFrames SemanticFrames ReplyNO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeClassCommands.
Import IndexExecution SipHashExecution.
Lemma allocated native count entry :
 NativeStateFrames.registries native (ClassStorage.result native count entry).
Proof.
 constructor;first [apply ClassStorage.result_meta_other;lia|
 apply ClassStorage.result_other;discriminate].
Qed.
Lemma set_frame native count value sep tail :
 (17<length (memory native arraydef_0__meta))%nat ->
 NativeStateFrames.registries native (ClassSetInput.result native count value sep tail).
Proof.
 intro Hmeta. unfold ClassSetInput.result. eapply NativeStateFrames.trans;[|apply allocated].
 constructor;first [apply ClassSetInput.argument_meta_other;try exact Hmeta;lia|
 apply ClassSetInput.argument_other;discriminate].
Qed.
Lemma abstract_frame native count value sep tail :
 (17<length (memory native arraydef_0__meta))%nat ->
 NativeStateFrames.registries native (ClassAbstractInput.result native count value sep tail).
Proof.
 intro Hmeta. unfold ClassAbstractInput.result,ClassAbstractInput.argument_state.
 eapply NativeStateFrames.trans;[exact (NativeStateFrames.read_one native 54 [] value sep tail Hmeta)|apply allocated].
Qed.
Lemma rejected_frame native value sep tail :
 (17<length (memory native arraydef_0__meta))%nat ->
 NativeStateFrames.registries native (ClassAbstractInput.rejected native value sep tail).
Proof.
 intro Hmeta. unfold ClassAbstractInput.rejected,ClassAbstractInput.argument_state.
 eapply NativeStateFrames.trans;[exact (NativeStateFrames.read_one native 54 [] value sep tail Hmeta)|apply NativeStateFrames.reply_no].
Qed.
Theorem generated_set native logical bs ns value first last tail observations :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=54 -> meta_value native 8=0 ->
 Z.of_nat (length (Protocol.classes logical))<maximum -> Z.of_nat value<=maximum ->
 NativeState.represents native logical ->
 TokenByteExecution.separator first -> TokenByteExecution.separator last ->
 stdin native=first::decimalBytes value++last::tail ->
 exists final,
 execObserved (funcdef_0__command bs ns) (native,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes (Protocol.OK (length (Protocol.classes logical)));unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 5 [value] []) (Protocol.OK (length (Protocol.classes logical)))
   (ClassSetRefinement.logical_after logical value) /\
 NativeState.represents final (ClassSetRefinement.logical_after logical value).
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hstate Hfirst Hlast Hinput.
 destruct Hstate as [Harena Hclasses Hhistory Hnames Hschemas].
 pose proof (SemanticFrames.arena_NoDup native _ Harena) as Hunique.
 set (final:=ClassSetInput.result native (length (Protocol.classes logical)) value last tail).
 assert (Hstep:Protocol.step logical (Protocol.Req 5 [value] []) (Protocol.OK (length (Protocol.classes logical)))
   (ClassSetRefinement.logical_after logical value)) by (now apply ClassSetRefinement.logical_step).
 exists final. split.
 - exact (ClassSetInput.generated_pending native bs ns (length (Protocol.classes logical)) value first last tail observations
    Hmeta Htoken Hprint Hpending Herror (proj1 Hclasses) Hroom Hvalue Hfirst Hlast Hinput).
 - split;[exact Hstep|]. eapply NativeStateFrames.finish with (native:=native) (before:=logical).
   + constructor;assumption.
   + apply set_frame;exact Hmeta.
   + exact Hstep.
   + discriminate.
   + reflexivity.
   + now apply ClassSetInput.result_arena.
   + now apply ClassSetInput.result_represents.
   + now apply ClassSetRefinement.result_history.
Qed.
Theorem generated_abstract native logical bs ns value p first last tail observations :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=55 -> meta_value native 8=0 ->
 Z.of_nat (length (Protocol.classes logical))<maximum -> Z.of_nat value<=maximum ->
 Protocol.formula_at logical value=Some p -> NativeState.represents native logical ->
 TokenByteExecution.separator first -> TokenByteExecution.separator last ->
 stdin native=first::decimalBytes value++last::tail ->
 exists final,
 execObserved (funcdef_0__command bs ns) (native,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes (Protocol.OK (length (Protocol.classes logical)));unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 6 [value] []) (Protocol.OK (length (Protocol.classes logical)))
   (ClassAbstractRefinement.logical_after logical p) /\
 NativeState.represents final (ClassAbstractRefinement.logical_after logical p).
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hlookup Hstate Hfirst Hlast Hinput.
 destruct Hstate as [Harena Hclasses Hhistory Hnames Hschemas].
 pose proof (SemanticFrames.arena_NoDup native _ Harena) as Hunique.
 assert (Hreference:Z.of_nat value<meta_value native 1).
 { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
   change (meta_value native 1=Z.of_nat (length (Protocol.formulas logical))) in Hcount.
   assert (Hi:(value<length (Protocol.formulas logical))%nat) by (apply nth_error_Some;unfold Protocol.formula_at in Hlookup;congruence).
   rewrite Hcount;lia. }
 set (final:=ClassAbstractInput.result native (length (Protocol.classes logical)) value last tail).
 assert (Hstep:Protocol.step logical (Protocol.Req 6 [value] []) (Protocol.OK (length (Protocol.classes logical)))
   (ClassAbstractRefinement.logical_after logical p)) by (now apply ClassAbstractRefinement.logical_step).
 exists final. split.
 - exact (ClassAbstractInput.generated_pending native bs ns (length (Protocol.classes logical)) value first last tail observations
    Hmeta Htoken Hprint Hpending Herror (proj1 Hclasses) Hroom Hvalue Hreference Hfirst Hlast Hinput).
 - split;[exact Hstep|]. eapply NativeStateFrames.finish with (native:=native) (before:=logical).
   + constructor;assumption.
   + apply abstract_frame;exact Hmeta.
   + exact Hstep.
   + discriminate.
   + reflexivity.
   + now apply ClassAbstractInput.result_arena.
   + now apply ClassAbstractInput.result_represents.
   + now apply ClassAbstractRefinement.result_history.
Qed.
Theorem generated_abstract_rejected native logical bs ns value first last tail observations :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=55 -> meta_value native 8=0 -> Z.of_nat value<=maximum ->
 Protocol.formula_at logical value=None -> NativeState.represents native logical ->
 TokenByteExecution.separator first -> TokenByteExecution.separator last ->
 stdin native=first::decimalBytes value++last::tail ->
 exists final,
 execObserved (funcdef_0__command bs ns) (native,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes Protocol.NO;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 6 [value] []) Protocol.NO logical /\ NativeState.represents final logical.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hvalue Hlookup Hstate Hfirst Hlast Hinput.
 destruct Hstate as [Harena Hclasses Hhistory Hnames Hschemas].
 pose proof (SemanticFrames.arena_NoDup native _ Harena) as Hunique.
 assert (Hreference:meta_value native 1<=Z.of_nat value).
 { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
   change (meta_value native 1=Z.of_nat (length (Protocol.formulas logical))) in Hcount.
   pose proof Hlookup as Hi. unfold Protocol.formula_at in Hi. apply nth_error_None in Hi. rewrite Hcount;lia. }
 set (final:=ClassAbstractInput.rejected native value last tail).
 assert (Hstep:Protocol.step logical (Protocol.Req 6 [value] []) Protocol.NO logical)
   by (now apply ClassAbstractRefinement.logical_rejected).
 exists final. split.
 - exact (ClassAbstractInput.generated_rejected native bs ns value first last tail observations
    Hmeta Htoken Hprint Hpending Herror Hvalue Hreference Hfirst Hlast Hinput).
 - split;[exact Hstep|]. eapply NativeStateFrames.finish with (native:=native) (before:=logical).
   + constructor;assumption.
   + apply rejected_frame;exact Hmeta.
   + exact Hstep.
   + discriminate.
   + reflexivity.
   + now apply ClassAbstractInput.rejected_arena.
   + now apply ClassAbstractInput.rejected_represents.
   + now apply ClassAbstractRefinement.rejected_history.
Qed.
Theorem generated_abstract_total native logical bs ns value first last tail observations :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=55 -> meta_value native 8=0 ->
 Z.of_nat (length (Protocol.classes logical))<maximum -> Z.of_nat value<=maximum ->
 NativeState.represents native logical ->
 TokenByteExecution.separator first -> TokenByteExecution.separator last ->
 stdin native=first::decimalBytes value++last::tail ->
 exists final reply next,
 execObserved (funcdef_0__command bs ns) (native,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 6 [value] []) reply next /\ NativeState.represents final next.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hstate Hfirst Hlast Hinput.
 destruct (Protocol.formula_at logical value) as [p|] eqn:Hlookup.
 - destruct (generated_abstract native logical bs ns value p first last tail observations
    Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hlookup Hstate Hfirst Hlast Hinput) as [final Hresult].
   exists final,(Protocol.OK (length (Protocol.classes logical))),(ClassAbstractRefinement.logical_after logical p). exact Hresult.
 - destruct (generated_abstract_rejected native logical bs ns value first last tail observations
    Hmeta Htoken Hprint Hpending Herror Hvalue Hlookup Hstate Hfirst Hlast Hinput) as [final Hresult].
   exists final,Protocol.NO,logical. exact Hresult.
Qed.
End NativeClassCommands.
