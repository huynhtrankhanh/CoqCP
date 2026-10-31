From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat CommandLoop Dialogue NativeState NativeSession NativeDialogueComposition NativeGeneralPrefixStop NativeInvalidUnaryArgument.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeInvalidUnaryStop.
Import IndexExecution SipHashExecution ReadNatExecution.
Theorem invalid separator chars spaces sep tail (ended:bool) prefix bad suffix :
 TokenByteExecution.separator separator -> (0<length chars<=1024)%nat ->
 Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars -> Forall TokenByteExecution.separator spaces ->
 TokenByteExecution.separator sep -> (if ended then tail=[] else True) ->
 prefix++bad::suffix=chars -> Forall(fun c=>48<=c<=57)prefix -> number_from 0 prefix<=maximum ->
 ((bad<48 \/ 57<bad) \/ (48<=bad<=57 /\ maximum<10*(number_from 0 prefix)+(bad-48))) ->
 NativeGeneralPrefixStop.stop_spec (52::separator::(if ended then spaces++chars else spaces++chars++sep::tail)) tail.
Proof.
 intros Hseparator Hlength Hbytes Hspaces Hsep Hended Hencoding Hdigits Hbound Hbad native logical observations Hboundary Hinput.
 pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary)) as Hmeta.
 pose proof(NativeDialogueComposition.token _ _ Hboundary) as Htoken.
 pose proof(NativeDialogueComposition.error _ _ Hboundary) as Herror.
 set(rest:=if ended then spaces++chars else spaces++chars++sep::tail).
 set(pending:=CommandLoopExecution.pending_state(withInput native(separator::rest))52).
 assert(Hpmeta:(17<length(memory pending arraydef_0__meta))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. cbn [memory withInput]. lia. }
 assert(Hptoken:(1024<=length(memory pending arraydef_0__token))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
 assert(Hpvalue:meta_value pending 15=53).
 { unfold pending,CommandLoopExecution.pending_state. replace 53 with (52+1) by lia. apply meta_store_same. cbn [memory withInput]. lia. }
 assert(Hperror:meta_value pending 8=0).
 { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
 assert(Hpin:if ended then stdin pending=separator::spaces++chars /\ tail=[] else stdin pending=separator::spaces++chars++sep::tail).
 { unfold pending,CommandLoopExecution.pending_state,rest. destruct ended;cbn in *;tauto. }
 destruct(NativeInvalidUnaryArgument.generated pending (fun _=>false)(fun _=>0) separator chars spaces sep tail ended prefix bad suffix observations
   Hpmeta Hptoken Hpvalue Hperror Hseparator Hlength Hbytes Hspaces Hsep Hpin Hencoding Hdigits Hbound Hbad)
 as(final & Hcommand & Hin & Hout & Hstop & Hfinalmeta).
 exists final. split.
 - eapply DialogueExecution.stop with (ch:=52) (tail:=separator::rest);[lia|exact Hinput|lia| |exact Hfinalmeta|].
   + change(execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,
      (final,observations++[{|flushedOutput:=stdout pending++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}]))). exact Hcommand.
   + rewrite Hstop;discriminate.
 - split;[change(stdout final=stdout pending++Protocol.reply_bytes Protocol.ERR);exact Hout|]. now split.
Qed.
End NativeInvalidUnaryStop.
