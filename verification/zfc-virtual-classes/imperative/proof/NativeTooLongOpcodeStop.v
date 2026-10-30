From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat TokenFrame CommandLoop Dialogue SeedBootstrap NativeStartupCompact NativePendingBadNumber NativeMalformedCommand NativeMalformedOpcode NativeDialogueComposition NativeSession NativeGeneralPrefixStop NativePendingTooLong NativeTooLongOpcode NativeInvalidCommand NativeTooLongSeed ReadTokenPendingLeading.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeTooLongOpcodeStop.
Import IndexExecution SipHashExecution.
Theorem too_long ch chars extra tail :
 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 length chars=1023%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 0<=extra<256 -> ~TokenByteExecution.separator extra ->
 NativeGeneralPrefixStop.stop_spec (ch::chars++extra::tail) tail.
Proof.
 intros Hch Hnosep Hlength Hbytes Hextra Hbad native logical observations Hboundary Hinput.
 pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary)) as Hmeta.
 pose proof(NativeDialogueComposition.token _ _ Hboundary) as Htoken.
 pose proof(NativeDialogueComposition.error _ _ Hboundary) as Herror.
 set(pending:=CommandLoopExecution.pending_state(withInput native (chars++extra::tail))ch).
 assert(Hpendingmeta:(17<length(memory pending arraydef_0__meta))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. change(17<length(memory native arraydef_0__meta))%nat. lia. }
 assert(Hpendingtoken:(1024<=length(memory pending arraydef_0__token))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
 assert(Hpendingvalue:meta_value pending 15=ch+1).
 { unfold pending,CommandLoopExecution.pending_state. apply meta_store_same. change(15<length(memory native arraydef_0__meta))%nat;lia. }
 assert(Hpendingerror:meta_value pending 8=0).
 { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
 set(parsed:=NativeTooLongOpcode.readstate pending ch chars tail).
 set(final:=NativeInvalidCommand.final parsed).
 assert(Hcommand:execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}]))).
 { unfold final,parsed. change(execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(NativeInvalidCommand.final(NativeTooLongOpcode.readstate pending ch chars tail),
 observations++[{|flushedOutput:=stdout pending++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}]))).
   exact(NativeTooLongOpcode.generated_pending pending (fun _=>false)(fun _=>0) ch chars extra tail observations Hpendingmeta Hpendingtoken Hpendingvalue Hpendingerror Hch Hnosep Hlength Hbytes Hextra Hbad eq_refl). }
 assert(Hfinalmeta:(9<length(memory final arraydef_0__meta))%nat).
 { unfold final,NativeInvalidCommand.final,NativeInvalidCommand.failed,parsed,NativeTooLongOpcode.readstate.
   rewrite store_meta_length. change(9<length(memory(store_meta(store_meta(NativePendingTooLong.result pending ch chars tail)11 0%Z)8 1%Z)arraydef_0__meta))%nat.
   rewrite !store_meta_length. unfold NativePendingTooLong.result.
   change(9<length(memory(store_meta(ReadTokenExecution.put_many(ReadTokenExecution.started pending ch)1 chars)8 1%Z)arraydef_0__meta))%nat.
   rewrite store_meta_length,ReadTokenExecution.put_many_meta_length,ReadTokenExecution.started_length. lia. }
 assert(Hfinalstop:meta_value final 9=1).
 { unfold final,NativeInvalidCommand.final. apply meta_store_same.
   unfold final,NativeInvalidCommand.final in Hfinalmeta. rewrite store_meta_length in Hfinalmeta. exact Hfinalmeta. }
 assert(Hrun:DialogueExecution.run native observations final (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])).
 { eapply DialogueExecution.stop with (ch:=ch) (tail:=chars++extra::tail);[exact Hch|exact Hinput|lia|exact Hcommand|exact Hfinalmeta|]. rewrite Hfinalstop. discriminate. }
 exists final. split;[exact Hrun|]. split.
 - unfold final,NativeInvalidCommand.final,NativeInvalidCommand.failed,parsed,NativeTooLongOpcode.readstate,NativePendingTooLong.result.
   change(stdout(ReadTokenExecution.put_many(ReadTokenExecution.started pending ch)1 chars)++Protocol.reply_bytes Protocol.ERR=stdout native++Protocol.reply_bytes Protocol.ERR).
   rewrite NativeTooLongSeed.put_many_output. reflexivity.
 - split;[reflexivity|exact Hfinalstop].
Qed.
End NativeTooLongOpcodeStop.
