From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat NativeGeneralPrefixStop NativeSpacedUnaryErrorStop NativeInvalidUnaryArgument NativeOverlongUnaryArgument NativeMissingUnaryArgument NativeMalformedUnaryCommand NativeReadTokenLeadingMissing ReadToken CommandInput.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeAnyWhitespaceUnaryErrorStop.
Import IndexExecution SipHashExecution ReadNatExecution.
Theorem invalid leading separator chars spaces sep tail (ended:bool) prefix bad suffix :
 Forall TokenByteExecution.separator leading -> TokenByteExecution.separator separator -> (0<length chars<=1024)%nat ->
 Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars -> Forall TokenByteExecution.separator spaces ->
 TokenByteExecution.separator sep -> (if ended then tail=[] else True) ->
 prefix++bad::suffix=chars -> Forall(fun c=>48<=c<=57)prefix -> number_from 0 prefix<=maximum ->
 ((bad<48 \/ 57<bad) \/ (48<=bad<=57 /\ maximum<10*(number_from 0 prefix)+(bad-48))) ->
 NativeGeneralPrefixStop.stop_spec (leading++52::separator::(if ended then spaces++chars else spaces++chars++sep::tail)) tail.
Proof.
 intros Hleading Hseparator Hlength Hbytes Hspaces Hsep Hended Hencoding Hdigits Hbound Hbad.
 apply NativeSpacedUnaryErrorStop.any_spaces;try assumption.
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 assert(Hinput':if ended then stdin s=separator::spaces++chars /\ tail=[] else stdin s=separator::spaces++chars++sep::tail).
 { destruct ended;cbn in *;tauto. }
 exact(NativeInvalidUnaryArgument.generated s (fun _=>false)(fun _=>0) separator chars spaces sep tail ended prefix bad suffix observations
 Hmeta Htoken Hpending Herror Hseparator Hlength Hbytes Hspaces Hsep Hinput' Hencoding Hdigits Hbound Hbad).
Qed.
Theorem overlong leading separator chars spaces extra tail :
 Forall TokenByteExecution.separator leading -> TokenByteExecution.separator separator -> length chars=1024%nat ->
 Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars -> Forall TokenByteExecution.separator spaces ->
 0<=extra<256 -> ~TokenByteExecution.separator extra ->
 NativeGeneralPrefixStop.stop_spec (leading++52::separator::spaces++chars++extra::tail) tail.
Proof.
 intros Hleading Hseparator Hlength Hbytes Hspaces Hextra Hbad.
 apply NativeSpacedUnaryErrorStop.any_spaces;try assumption.
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 exact(NativeOverlongUnaryArgument.generated s (fun _=>false)(fun _=>0) separator chars spaces extra tail observations
 Hmeta Htoken Hpending Herror Hseparator Hlength Hbytes Hspaces Hextra Hbad Hinput).
Qed.
Theorem missing leading separator spaces :
 Forall TokenByteExecution.separator leading -> TokenByteExecution.separator separator -> Forall TokenByteExecution.separator spaces ->
 NativeGeneralPrefixStop.stop_spec (leading++52::separator::spaces) [].
Proof.
 intros Hleading Hseparator Hspaces.
 apply NativeSpacedUnaryErrorStop.any_spaces;try assumption.
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 set(op:=CommandInput.parsed s 52 [] spaces).
 set(arg:=NativeMissingUnaryArgument.argument op).
 set(final:=NativeMalformedUnaryCommand.final arg).
 assert(Hrun:execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(s,observations)=Some(tt,
 (final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}]))).
 { unfold final,arg,op. exact(NativeMissingUnaryArgument.generated s (fun _=>false)(fun _=>0) separator spaces observations Hmeta Htoken Hpending Herror Hseparator Hspaces Hinput). }
 assert(Hfinalmeta:(9<length(memory final arraydef_0__meta))%nat).
 { unfold final,NativeMalformedUnaryCommand.final,NativeMalformedUnaryCommand.failed,arg,NativeMissingUnaryArgument.argument,NativeReadTokenLeadingMissing.result.
   repeat first [rewrite store_meta_length | progress cbn [memory withOutput withInput]]. change(9<length(memory(ReadTokenExecution.reset op)arraydef_0__meta))%nat.
   rewrite ReadTokenExecution.reset_length. unfold op. rewrite CommandInput.parsed_meta_length. lia. }
 assert(Hstop:meta_value final 9=1).
 { unfold final,NativeMalformedUnaryCommand.final. apply meta_store_same.
   unfold NativeMalformedUnaryCommand.failed,arg,NativeMissingUnaryArgument.argument,NativeReadTokenLeadingMissing.result.
   repeat first [rewrite store_meta_length | progress cbn [memory withOutput withInput]]. change(9<length(memory(ReadTokenExecution.reset op)arraydef_0__meta))%nat.
   rewrite ReadTokenExecution.reset_length. unfold op. rewrite CommandInput.parsed_meta_length. lia. }
 exists final. split;[exact Hrun|]. split;[reflexivity|]. split.
 - unfold final,NativeMalformedUnaryCommand.final,NativeMalformedUnaryCommand.failed,arg,NativeMissingUnaryArgument.argument,NativeReadTokenLeadingMissing.result.
   change(stdout op++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR).
   unfold op. rewrite CommandInput.parsed_output. reflexivity.
 - now split.
Qed.
End NativeAnyWhitespaceUnaryErrorStop.
