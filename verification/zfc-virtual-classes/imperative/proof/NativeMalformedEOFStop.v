From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat TokenFrame CommandLoop Dialogue SeedBootstrap NativeStartupCompact NativePendingTokenEOF NativePendingBadNumberEOF NativeMalformedCommand NativeMalformedOpcodeEOF NativeDialogueComposition NativeSession NativeGeneralPrefixStop.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeMalformedEOFStop.
Import IndexExecution SipHashExecution.
Theorem malformed ch chars prefix bad suffix :
 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 (S(length chars)<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 prefix++bad::suffix=ch::chars ->
 Forall(fun x=>48<=x<=57)prefix -> ReadNatExecution.number_from 0 prefix<=maximum -> NativeMalformedOpcodeEOF.malformed prefix bad ->
 NativeGeneralPrefixStop.stop_spec (ch::chars) [].
Proof.
 intros Hch Hnosep Hlength Hbytes Hencoding Hdigits Hbound Hbad native logical observations Hboundary Hinput.
 pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary)) as Hmeta.
 pose proof(NativeDialogueComposition.token _ _ Hboundary) as Htoken.
 pose proof(NativeDialogueComposition.error _ _ Hboundary) as Herror.
 set(pending:=CommandLoopExecution.pending_state(withInput native chars)ch).
 assert(Hpendingmeta:(17<length(memory pending arraydef_0__meta))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. change(17<length(memory native arraydef_0__meta))%nat. lia. }
 assert(Hpendingtoken:(1024<=length(memory pending arraydef_0__token))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
 assert(Hpendingvalue:meta_value pending 15=ch+1).
 { unfold pending,CommandLoopExecution.pending_state. apply meta_store_same. change(15<length(memory native arraydef_0__meta))%nat;lia. }
 assert(Hpendingerror:meta_value pending 8=0).
 { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
 set(parsed:=NativePendingBadNumberEOF.parsed pending ch chars prefix).
 set(final:=NativeMalformedCommand.final parsed).
 assert(Hcommand:execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}]))).
 { unfold final,parsed. change(execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(NativeMalformedCommand.final(NativePendingBadNumberEOF.parsed pending ch chars prefix),
 observations++[{|flushedOutput:=stdout pending++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}]))).
   exact(NativeMalformedOpcodeEOF.generated_pending pending (fun _=>false)(fun _=>0) ch chars prefix bad suffix observations Hpendingmeta Hpendingtoken Hpendingvalue Hpendingerror Hch Hnosep Hlength Hbytes eq_refl Hencoding Hdigits Hbound Hbad). }
 assert(Hfinalmeta:(9<length(memory final arraydef_0__meta))%nat).
 { unfold final,NativeMalformedCommand.final,NativeMalformedCommand.failed,parsed,NativePendingBadNumberEOF.parsed.
   rewrite store_meta_length. change(9<length(memory(store_meta(store_meta(store_meta(NativePendingBadNumberEOF.tokenstate pending ch chars)14 0%Z)11 (ReadNatExecution.number_from 0 prefix))8 1%Z)arraydef_0__meta))%nat.
   rewrite !store_meta_length,NativePendingBadNumberEOF.token_meta_length. lia. }
 assert(Hfinalstop:meta_value final 9=1).
 { unfold final,NativeMalformedCommand.final. apply meta_store_same.
   unfold final,NativeMalformedCommand.final in Hfinalmeta. rewrite store_meta_length in Hfinalmeta. exact Hfinalmeta. }
 assert(Hrun:DialogueExecution.run native observations final (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}])).
 { eapply DialogueExecution.stop with (ch:=ch) (tail:=chars);[exact Hch|exact Hinput|lia|exact Hcommand|exact Hfinalmeta|]. rewrite Hfinalstop. discriminate. }
 exists final. split;[exact Hrun|]. split.
 - unfold final,NativeMalformedCommand.final,NativeMalformedCommand.failed,parsed,NativePendingBadNumberEOF.parsed.
   change(stdout(NativePendingBadNumberEOF.tokenstate pending ch chars)++Protocol.reply_bytes Protocol.ERR=stdout native++Protocol.reply_bytes Protocol.ERR).
   unfold NativePendingBadNumberEOF.tokenstate,NativePendingTokenEOF.eof_result.
   change(stdout(ReadTokenExecution.put_many(ReadTokenExecution.started pending ch)1 chars)++Protocol.reply_bytes Protocol.ERR=stdout native++Protocol.reply_bytes Protocol.ERR).
   rewrite ReadTokenExecution.put_many_output. reflexivity.
 - split;[reflexivity|exact Hfinalstop].
Qed.
End NativeMalformedEOFStop.
