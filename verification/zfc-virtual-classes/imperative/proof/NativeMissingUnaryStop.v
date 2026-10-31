From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken CommandInput CommandLoop Dialogue NativeState NativeSession NativeDialogueComposition NativeGeneralPrefixStop NativeReadTokenLeadingMissing NativeMalformedUnaryCommand NativeMissingUnaryArgument.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeMissingUnaryStop.
Import IndexExecution SipHashExecution ReadTokenExecution.
Theorem missing separator spaces :
 TokenByteExecution.separator separator -> Forall TokenByteExecution.separator spaces ->
 NativeGeneralPrefixStop.stop_spec (52::separator::spaces) [].
Proof.
 intros Hsep Hspaces native logical observations Hboundary Hinput.
 pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary)) as Hmeta.
 pose proof(NativeDialogueComposition.token _ _ Hboundary) as Htoken.
 pose proof(NativeDialogueComposition.error _ _ Hboundary) as Herror.
 set(pending:=CommandLoopExecution.pending_state(withInput native(separator::spaces))52).
 assert(Hpmeta:(17<length(memory pending arraydef_0__meta))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. cbn [memory withInput]. lia. }
 assert(Hptoken:(1024<=length(memory pending arraydef_0__token))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
 assert(Hpvalue:meta_value pending 15=53).
 { unfold pending,CommandLoopExecution.pending_state. replace 53 with (52+1) by lia. apply meta_store_same. cbn [memory withInput]. lia. }
 assert(Hperror:meta_value pending 8=0).
 { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
 set(op:=CommandInput.parsed pending 52 [] spaces).
 set(arg:=NativeMissingUnaryArgument.argument op).
 set(final:=NativeMalformedUnaryCommand.final arg).
 assert(Hcommand:execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}]))).
 { unfold final,arg,op. change(execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,
   (NativeMalformedUnaryCommand.final(NativeMissingUnaryArgument.argument(CommandInput.parsed pending 52 [] spaces)),
    observations++[{|flushedOutput:=stdout pending++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}]))).
   exact(NativeMissingUnaryArgument.generated pending (fun _=>false)(fun _=>0) separator spaces observations Hpmeta Hptoken Hpvalue Hperror Hsep Hspaces eq_refl). }
 assert(Hfinalmeta:(9<length(memory final arraydef_0__meta))%nat).
 { unfold final,NativeMalformedUnaryCommand.final,NativeMalformedUnaryCommand.failed,arg,NativeMissingUnaryArgument.argument,NativeReadTokenLeadingMissing.result.
   repeat first [rewrite store_meta_length | progress cbn [memory withOutput withInput]]. change(9<length(memory(reset op)arraydef_0__meta))%nat.
   rewrite reset_length. unfold op. rewrite CommandInput.parsed_meta_length. lia. }
 assert(Hstop:meta_value final 9=1).
 { unfold final,NativeMalformedUnaryCommand.final. apply meta_store_same. cbn [memory withOutput].
   unfold NativeMalformedUnaryCommand.failed,arg,NativeMissingUnaryArgument.argument,NativeReadTokenLeadingMissing.result.
   repeat first [rewrite store_meta_length | progress cbn [memory withOutput withInput]]. change(9<length(memory(reset op)arraydef_0__meta))%nat.
   rewrite reset_length. unfold op. rewrite CommandInput.parsed_meta_length. lia. }
 exists final. split.
 - eapply DialogueExecution.stop with (ch:=52) (tail:=separator::spaces);[lia|exact Hinput|lia|exact Hcommand|exact Hfinalmeta|]. rewrite Hstop;discriminate.
 - split.
   + unfold final,NativeMalformedUnaryCommand.final,NativeMalformedUnaryCommand.failed,arg,NativeMissingUnaryArgument.argument,NativeReadTokenLeadingMissing.result.
     change(stdout op++Protocol.reply_bytes Protocol.ERR=stdout native++Protocol.reply_bytes Protocol.ERR).
     unfold op. rewrite CommandInput.parsed_output. reflexivity.
   + split;[reflexivity|exact Hstop].
Qed.
End NativeMissingUnaryStop.
