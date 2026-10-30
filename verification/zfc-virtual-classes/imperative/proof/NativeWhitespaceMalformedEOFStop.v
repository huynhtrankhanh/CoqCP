From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat TokenFrame CommandLoop Dialogue SeedBootstrap NativeStartupCompact NativePendingBadNumber NativeMalformedCommand NativeMalformedOpcode NativeDialogueComposition NativeSession NativeGeneralPrefixStop NativePendingSeparatorMalformedEOF NativePendingSeparatorEOF NativeTooLongSeed ReadTokenPendingLeading.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeWhitespaceMalformedEOFStop.
Import IndexExecution SipHashExecution.
Theorem malformed ch spaces chars prefix bad suffix :
 0<=ch<256 -> TokenByteExecution.separator ch -> Forall TokenByteExecution.separator spaces ->
 (0<length chars<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 prefix++bad::suffix=chars ->
 Forall(fun x=>48<=x<=57)prefix -> ReadNatExecution.number_from 0 prefix<=maximum -> NativeMalformedOpcode.malformed prefix bad ->
 NativeGeneralPrefixStop.stop_spec (ch::spaces++chars) [].
Proof.
 intros Hch Hsep0 Hspaces Hlength Hbytes Hencoding Hdigits Hbound Hbad native logical observations Hboundary Hinput.
 pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary)) as Hmeta.
 pose proof(NativeDialogueComposition.token _ _ Hboundary) as Htoken.
 pose proof(NativeDialogueComposition.error _ _ Hboundary) as Herror.
 set(pending:=CommandLoopExecution.pending_state(withInput native (spaces++chars))ch).
 assert(Hpendingmeta:(17<length(memory pending arraydef_0__meta))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. change(17<length(memory native arraydef_0__meta))%nat. lia. }
 assert(Hpendingtoken:(1024<=length(memory pending arraydef_0__token))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
 assert(Hpendingvalue:meta_value pending 15=ch+1).
 { unfold pending,CommandLoopExecution.pending_state. apply meta_store_same. change(15<length(memory native arraydef_0__meta))%nat;lia. }
 assert(Hpendingerror:meta_value pending 8=0).
 { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
 set(parsed:=NativePendingSeparatorMalformedEOF.parsed pending chars prefix).
 set(final:=NativeMalformedCommand.final parsed).
 assert(Hcommand:execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}]))).
 { unfold final,parsed. change(execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(NativeMalformedCommand.final(NativePendingSeparatorMalformedEOF.parsed pending chars prefix),
 observations++[{|flushedOutput:=stdout pending++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}]))).
   exact(NativePendingSeparatorMalformedEOF.generated pending (fun _=>false)(fun _=>0) ch chars spaces prefix bad suffix observations Hpendingmeta Hpendingtoken Hpendingvalue Hpendingerror Hch Hsep0 Hlength Hbytes Hspaces eq_refl Hencoding Hdigits Hbound Hbad). }
 assert(Hfinalmeta:(9<length(memory final arraydef_0__meta))%nat).
 { unfold final,NativeMalformedCommand.final,NativeMalformedCommand.failed,parsed,NativePendingSeparatorMalformedEOF.parsed.
   rewrite store_meta_length. change(9<length(memory(store_meta(store_meta(store_meta(NativePendingSeparatorEOF.eof_result pending chars)14 0%Z)11 (ReadNatExecution.number_from 0 prefix))8 1%Z)arraydef_0__meta))%nat.
   rewrite !store_meta_length. unfold NativePendingSeparatorEOF.eof_result. rewrite !store_meta_length.
   change(9<length(memory(ReadTokenExecution.put_many(ReadTokenPendingLeading.pending_base pending)0 chars)arraydef_0__meta))%nat.
   rewrite ReadTokenExecution.put_many_meta_length,ReadTokenPendingLeading.pending_base_length. lia. }
 assert(Hfinalstop:meta_value final 9=1).
 { unfold final,NativeMalformedCommand.final. apply meta_store_same.
   unfold final,NativeMalformedCommand.final in Hfinalmeta. rewrite store_meta_length in Hfinalmeta. exact Hfinalmeta. }
 assert(Hrun:DialogueExecution.run native observations final (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}])).
 { eapply DialogueExecution.stop with (ch:=ch) (tail:=spaces++chars);[exact Hch|exact Hinput|lia|exact Hcommand|exact Hfinalmeta|]. rewrite Hfinalstop. discriminate. }
 exists final. split;[exact Hrun|]. split.
 - unfold final,NativeMalformedCommand.final,NativeMalformedCommand.failed,parsed,NativePendingSeparatorMalformedEOF.parsed.
   change(stdout(NativePendingSeparatorEOF.eof_result pending chars)++Protocol.reply_bytes Protocol.ERR=stdout native++Protocol.reply_bytes Protocol.ERR).
   unfold NativePendingSeparatorEOF.eof_result.
   change(stdout(ReadTokenExecution.put_many(ReadTokenPendingLeading.pending_base pending)0 chars)++Protocol.reply_bytes Protocol.ERR=stdout native++Protocol.reply_bytes Protocol.ERR).
   rewrite NativeTooLongSeed.put_many_output. reflexivity.
 - split;[reflexivity|exact Hfinalstop].
Qed.
End NativeWhitespaceMalformedEOFStop.
