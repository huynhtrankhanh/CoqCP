From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte ReadFour AxiomCommand AxiomRefl AxiomStorage
  ArenaFrame Representation ClassStorage HistoryRefinement HistoryStorage SemanticFrames NativeState NativeStateFrames NativeSimpleCommands AxiomReflProtocol ReplyOK DecimalInput.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeAxiomCommands.
Import IndexExecution SipHashExecution.
Definition before_append := AxiomReflProtocol.before_append.
Definition logical_after := AxiomReflProtocol.logical_after.
Theorem generated_reflexivity s logical bs ns ch chars variable b c sep0 sep1 sep2 sep3 sep4 tail observations :
  decimalBytes 11=ch::chars ->
  (17<length (memory s arraydef_0__meta))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
  (20<=length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
  Z.of_nat (length (Protocol.formulas logical)+1)<=9223372036854775807 ->
  Z.of_nat (length (Protocol.history logical))<maximum ->
  Z.of_nat variable<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum ->
  NativeState.represents s logical ->
  TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
  stdin s=chars++sep0::decimalBytes 5++sep1::decimalBytes variable++sep2::decimalBytes b++sep3::decimalBytes c++sep4::tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)));unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 11 [5;variable;b;c]%nat []) (Protocol.OK (length (Protocol.history logical))) (logical_after logical fs index) /\
    nth_error fs index=Some (SetTheory.equal variable variable) /\ SetTheory.derives (SetTheory.equal variable variable) /\
    NativeState.represents final (logical_after logical fs index) /\
    stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical))) /\
    (1024<=length (memory final arraydef_0__token))%nat /\ (20<=length (memory final arraydef_0__printBuffer))%nat /\
    meta_value final 8=0 /\ meta_value final 9=meta_value s 9 /\
    (Guarantees.safe logical -> Guarantees.safe (logical_after logical fs index)).
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbudget Hhistorybound Hvariable Hb Hc
    Hnative Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hin.
  destruct Hnative as [Harena Hclasses Hhistory Hnames Hschemas].
  assert (Hcode:Z.of_nat 11<=maximum) by (unfold maximum;lia).
  assert (Htag:Z.of_nat 5<=maximum) by (unfold maximum;lia).
  destruct (ReadFour.generated_reads s 11 ch chars 5 variable b c sep0 sep1 sep2 sep3 sep4 tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Htag Hvariable Hb Hc Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hin)
    as (Hopcode & Hfirst & Hsecond & Hthird & Hfourth & Hargbuffer & Hinput & Houtput).
  set (arg:=ReadFour.fourth_state s ch chars 5 sep1 variable sep2 b sep3 c sep4 tail).
  pose proof Hfourth as [_ [Hargmeta [_ [_ Hargerror]]]].
  change (17<length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (meta_value arg 8=0) in Hargerror.
  change (20<=length (memory arg arraydef_0__printBuffer))%nat in Hargbuffer.
  assert (Harg_arena:NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { eapply ArenaFrame.storage_arena;[apply ReadFour.fourth_storage;exact Hmeta|exact Harena]. }
  pose proof (AxiomReflProtocol.argument_history s logical ch chars 5 sep1 variable sep2 b sep3 c sep4 tail Hmeta Hhistory) as Harg_history.
  pose proof (AxiomReflProtocol.argument_classes s (Protocol.formulas logical) (Protocol.classes logical) ch chars 5 sep1 variable sep2 b sep3 c sep4 tail Hmeta Hclasses) as Harg_classes.
  assert (Hvariableword:word (Z.of_nat variable)) by (unfold word;lia).
  assert (Hreserve:Z.of_nat (length (Protocol.formulas logical)+S 0)<=9223372036854775807) by exact Hbudget.
  destruct (AxiomRefl.generated_refines arg (fun _=>false)
    (AxiomCommand.arguments 5 (Z.of_nat variable) (Z.of_nat b) (Z.of_nat c)) (Protocol.formulas logical) variable 0 observations
    Harg_arena Hargerror ltac:(lia) Hvariableword Hreserve eq_refl eq_refl)
    as (built & fs & index & Hhelper & Hnext & Hindex & Hword & Hformula & Hderives & Hprefix & Hflag & Hsuccess & Hframe & Hremaining).
  pose proof (AxiomStorage.generated_frame _ _ _ _ _ _ Hhelper) as Hstorage.
  pose proof (AxiomStorage.history_transport arg built logical Hstorage Harg_history) as Hbuilt_history.
  pose proof Hframe as [Harrays [Hcells [Hinput_helper Houtput_helper]]].
  assert (Hpostmeta:(17<length (memory built arraydef_0__meta))%nat) by (pose proof (proj1 (proj1 Hnext)) as [Hcapacity Hrest];lia).
  assert (Hpostbuffer:(20<=length (memory built arraydef_0__printBuffer))%nat) by
    (rewrite Harrays by discriminate;exact Hargbuffer).
  pose proof (AxiomCommand.generated_command s bs ns _ _ _ _ arg built 5 (Z.of_nat variable) (Z.of_nat b) (Z.of_nat c)
    (length (Protocol.history logical)) index true observations Hopcode Hfirst Hsecond Hthird Hfourth Hhelper
    Hpostmeta Hsuccess Hflag Hindex (proj1 Hbuilt_history) Hhistorybound Hpostbuffer) as Hrun.
  change (stdin arg=tail) in Hinput. change (stdout arg=stdout s) in Houtput.
  rewrite Hinput_helper,Houtput_helper,Hinput,Houtput in Hrun.
  assert (Hunique:NoDup fs) by (eapply SemanticFrames.arena_NoDup;exact Hnext).
  assert (Hstep:Protocol.step logical (Protocol.Req 11 [5;variable;b;c]%nat []) (Protocol.OK (length (Protocol.history logical))) (logical_after logical fs index)).
  { eapply Protocol.step_accept with (t:=logical_after logical fs index).
    - unfold logical_after,before_append. cbn [Protocol.with_history Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
      eapply (Protocol.accept_proof logical (Protocol.Req 11 [5;variable;b;c]%nat []) (SetTheory.equal variable variable) fs (Protocol.classes logical) index).
      + apply Protocol.req_axiom. reflexivity.
      + split;[exact Hprefix|]. split;[exact Hunique|]. split;[exact Hformula|]. exists [];now rewrite app_nil_r.
    - apply HistoryRefinement.retained_refl. exact Hunique. }
  set (final:=HistoryStorage.result built (length (Protocol.history logical)) (Z.of_nat index)).
  assert (HfinalArena:NativeRepresentation.canonical_arena final fs) by (now apply HistoryStorage.result_arena).
  assert (HfinalClasses:ClassStorage.represents final fs (Protocol.classes logical)).
  { apply HistoryStorage.result_classes. destruct Hprefix as [extra ->]. eapply AxiomStorage.classes_transport;eassumption. }
  assert (HfinalHistory:HistoryRefinement.represents final (logical_after logical fs index)).
  { apply (HistoryStorage.append_represents built (before_append logical fs) index ltac:(lia) Hbuilt_history). }
  assert (Hregistries:NativeStateFrames.registries s final).
  { eapply NativeStateFrames.trans with (middle:=arg).
    - constructor;first [apply ReadFour.fourth_meta_other;try exact Hmeta;lia|apply ReadFour.fourth_other;discriminate].
    - eapply NativeStateFrames.trans with (middle:=built).
      + constructor;first [apply Hcells;lia|apply Harrays;discriminate].
      + constructor;first [apply HistoryStorage.result_meta_other;lia|apply HistoryStorage.result_other;discriminate]. }
  assert (HfinalState:NativeState.represents final (logical_after logical fs index)).
  { eapply NativeStateFrames.finish with (native:=s) (before:=logical).
    - constructor;assumption.
    - exact Hregistries.
    - exact Hstep.
    - discriminate.
    - reflexivity.
    - exact HfinalArena.
    - exact HfinalClasses.
    - exact HfinalHistory. }
  assert (HfinalInput:stdin final=tail).
  { unfold final,HistoryStorage.result. change (stdin (ReplyOKExecution.reply_state (HistoryStorage.written built (length (Protocol.history logical)) (Z.of_nat index)) (length (Protocol.history logical)))=tail).
    rewrite ReplyOKExecution.reply_input. change (stdin built=tail). congruence. }
  assert (HfinalOutput:stdout final=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)))).
  { unfold final,HistoryStorage.result. change (stdout (ReplyOKExecution.reply_state (HistoryStorage.written built (length (Protocol.history logical)) (Z.of_nat index)) (length (Protocol.history logical)))=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)))).
    rewrite ReplyOKExecution.reply_output. change (stdout built++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)))=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)))). congruence. }
  assert (HfinalToken:(1024<=length (memory final arraydef_0__token))%nat).
  { unfold final. rewrite HistoryStorage.result_other by discriminate. rewrite Harrays by discriminate.
    unfold arg,ReadFour.fourth_state,ReadFour.third_state,ReadFour.second_state.
    rewrite !DecimalInput.encoded_token_length,NativeSimpleCommands.read_two_token_length. exact Htoken. }
  assert (HfinalPrint:(20<=length (memory final arraydef_0__printBuffer))%nat).
  { unfold final,HistoryStorage.result. rewrite store_meta_other by discriminate.
    rewrite ReplyOKExecution.reply_buffer_length,HistoryStorage.written_other by discriminate. exact Hpostbuffer. }
  assert (HfinalError:meta_value final 8=0).
  { unfold final. rewrite HistoryStorage.result_meta_other by lia. exact Hflag. }
  assert (HfinalStop:meta_value final 9=meta_value s 9).
  { unfold final. rewrite HistoryStorage.result_meta_other by lia. rewrite Hcells by lia.
    unfold arg. apply ReadFour.fourth_meta_other;try exact Hmeta;lia. }
  exists final,index,fs. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hformula|]. split;[exact Hderives|].
  split;[exact HfinalState|]. split;[exact HfinalInput|]. split;[exact HfinalOutput|]. split;[exact HfinalToken|].
  split;[exact HfinalPrint|]. split;[exact HfinalError|]. split;[exact HfinalStop|].
  intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End NativeAxiomCommands.
