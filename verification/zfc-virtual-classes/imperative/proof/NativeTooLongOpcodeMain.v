From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken CommandLoop Dialogue SeedBootstrap NativeStartupCompact NativeTooLongSeed NativePendingTooLong NativeInvalidCommand NativeTooLongOpcode.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeTooLongOpcodeMain.
Import IndexExecution SipHashExecution.
Theorem actual_first_opcode key0 key1 ch chars extra tail bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 length chars=1023%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 0<=extra<256 -> ~TokenByteExecution.separator extra ->
 exists final, execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(ch::chars++extra::tail)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++ch::chars++extra::tail|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=ch::chars++extra::tail|};
  {|flushedOutput:=Protocol.handshake_output++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail /\ meta_value final 9=1.
Proof.
 intros Hkey0 Hkey1 Hch Hnosep Hlength Hbytes Hextra Hbad.
 destruct(NativeStartupCompact.main_to_commands key0 key1 (ch::chars++extra::tail) bs ns Hkey0 Hkey1)
 as(ready & Hstate & Htop & Hmeta32 & Hsip & Hzero & Herror & Hmeta & Htoken & Hprint & Hstop & Hhistory & Hinput & Houtput & Hmain & Hempty).
 set(pending:=CommandLoopExecution.pending_state(withInput ready (chars++extra::tail))ch).
 assert(Hpendingmeta:(17<length(memory pending arraydef_0__meta))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. change(17<length(memory ready arraydef_0__meta))%nat. lia. }
 assert(Hpendingtoken:(1024<=length(memory pending arraydef_0__token))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
 assert(Hpendingvalue:meta_value pending 15=ch+1).
 { unfold pending,CommandLoopExecution.pending_state. apply meta_store_same. change(15<length(memory ready arraydef_0__meta))%nat;lia. }
 assert(Hpendingerror:meta_value pending 8=0).
 { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
 set(parsed:=NativeTooLongOpcode.readstate pending ch chars tail).
 set(final:=NativeInvalidCommand.final parsed).
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++ch::chars++extra::tail|};
                    {|flushedOutput:=Protocol.handshake_output;unreadInput:=ch::chars++extra::tail|}]).
 assert(Hcommand:execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout ready++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}]))).
 { unfold final,parsed. change(execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(NativeInvalidCommand.final(NativeTooLongOpcode.readstate pending ch chars tail),
 observations++[{|flushedOutput:=stdout pending++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}]))).
   exact(NativeTooLongOpcode.generated_pending pending (fun _=>false)(fun _=>0) ch chars extra tail observations Hpendingmeta Hpendingtoken Hpendingvalue Hpendingerror Hch Hnosep Hlength Hbytes Hextra Hbad eq_refl). }
 assert(Hfinalmeta:(9<length(memory final arraydef_0__meta))%nat).
 { unfold final,NativeInvalidCommand.final,NativeInvalidCommand.failed,parsed,NativeTooLongOpcode.readstate,NativePendingTooLong.result.
   rewrite store_meta_length.
   change(9<length(memory(store_meta(store_meta(store_meta(ReadTokenExecution.put_many(ReadTokenExecution.started pending ch)1 chars)8 1%Z)11 0%Z)8 1%Z)arraydef_0__meta))%nat.
   rewrite !store_meta_length,ReadTokenExecution.put_many_meta_length,ReadTokenExecution.started_length. lia. }
 assert(Hfinalstop:meta_value final 9=1).
 { unfold final,NativeInvalidCommand.final. apply meta_store_same.
   change(9<length(memory final arraydef_0__meta))%nat in Hfinalmeta.
   unfold final,NativeInvalidCommand.final in Hfinalmeta. rewrite store_meta_length in Hfinalmeta. exact Hfinalmeta. }
 assert(Hrun:DialogueExecution.run ready observations final (observations++[{|flushedOutput:=stdout ready++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])).
 { eapply DialogueExecution.stop with (ch:=ch) (tail:=chars++extra::tail);[exact Hch|exact Hinput|lia|exact Hcommand|exact Hfinalmeta|]. rewrite Hfinalstop. discriminate. }
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 exists final. split.
 - rewrite Hmain. unfold observations in Hcommands. rewrite Houtput in Hcommands. exact Hcommands.
 - split.
   + unfold final,NativeInvalidCommand.final,NativeInvalidCommand.failed,parsed,NativeTooLongOpcode.readstate,NativePendingTooLong.result.
     change(stdout(ReadTokenExecution.put_many(ReadTokenExecution.started pending ch)1 chars)++Protocol.reply_bytes Protocol.ERR=Protocol.handshake_output++Protocol.reply_bytes Protocol.ERR).
     rewrite NativeTooLongSeed.put_many_output. change(stdout ready++Protocol.reply_bytes Protocol.ERR=Protocol.handshake_output++Protocol.reply_bytes Protocol.ERR). now rewrite Houtput.
   + split;[reflexivity|exact Hfinalstop].
Qed.
End NativeTooLongOpcodeMain.
