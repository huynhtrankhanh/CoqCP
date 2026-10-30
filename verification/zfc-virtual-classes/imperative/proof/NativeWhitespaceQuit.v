From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat NativeState NativeSession NativeDialogueComposition NativeCommandWhitespace NativePointwiseState
 MachinePointwise CommandLoop CommandQuit QuitInput QuitLoop.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceQuit.
Import IndexExecution SipHashExecution.
Theorem generated native logical ch prefix tail observations :
 NativeDialogueComposition.boundary native logical -> 0<=ch<256 -> TokenByteExecution.separator ch ->
 Forall TokenByteExecution.separator prefix ->
 exists after,
 execObserved(funcdef_0__command (fun _=>false)(fun _=>0))
  (CommandLoopExecution.pending_state(withInput native(prefix++[48;10]++tail))ch,observations)=
 Some(tt,(after,observations++[{|flushedOutput:=stdout native++CommandQuitExecution.bye_bytes;unreadInput:=tail|}])) /\
 NativeState.represents after logical /\ stdin after=tail /\ stdout after=stdout native++CommandQuitExecution.bye_bytes /\
 meta_value after 9=1 /\ meta_value after 8=0 /\ (9<length(memory after arraydef_0__meta))%nat.
Proof.
 intros Hboundary Hch Hsep Hprefix.
 destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning].
 pose proof(NativeSession.represented_meta native logical Hstate) as Hmeta.
 set(pending:=CommandLoopExecution.pending_state(withInput native(10::tail))48).
 assert(HpendingMeta:(17<length(memory pending arraydef_0__meta))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. cbn [memory withInput]. lia. }
 assert(HpendingToken:(1024<=length(memory pending arraydef_0__token))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
 assert(Hpending:meta_value pending 15=49).
 { unfold pending,CommandLoopExecution.pending_state. apply meta_store_same. cbn [memory withInput]. lia. }
 assert(HpendingError:meta_value pending 8=0).
 { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
 pose proof(QuitInputExecution.generated_quit_pending pending (fun _=>false)(fun _=>0) 10 tail observations
  HpendingMeta HpendingToken Hpending HpendingError ltac:(unfold TokenByteExecution.separator;tauto) eq_refl) as Hrun.
 change(execObserved(funcdef_0__command (fun _=>false)(fun _=>0))
   (NativeCommandWhitespace.canonical native 48 [] 10 tail,observations)=
   Some(tt,(QuitLoopExecution.loop_result native tail, observations++[{|flushedOutput:=stdout native++CommandQuitExecution.bye_bytes;unreadInput:=tail|}]))) in Hrun.
 destruct(NativeCommandWhitespace.generated native (fun _=>false)(fun _=>0) ch prefix 48 [] 10 tail observations _ _
   ltac:(lia) Htoken Herror Hch Hsep Hprefix ltac:(cbn;lia) ltac:(repeat constructor;lia)
   ltac:(cbn [ReadNatExecution.number_from];unfold maximum;lia) ltac:(unfold TokenByteExecution.separator;tauto) Hrun)
 as(after & Hactual & Hsame).
 exists after. split;[exact Hactual|].
 split;[apply (NativePointwiseState.represents _ _ _ Hsame);now apply NativeSession.quit_state|].
 pose proof Hsame as Hsame'. destruct Hsame as [Hin [Hout Hmemory]]. split;[rewrite <-Hin;apply QuitLoopExecution.loop_input|].
 split;[rewrite <-Hout;apply QuitLoopExecution.loop_output|].
 split;[unfold meta_value;rewrite <-Hmemory;apply QuitLoopExecution.loop_stop;lia|].
 split;[rewrite (NativePointwiseState.meta _ _ 8 Hsame'),QuitLoopExecution.loop_error;exact Herror|].
 rewrite <-Hmemory,QuitLoopExecution.callback_meta_length. cbn [memory withInput]. lia.
Qed.
End NativeWhitespaceQuit.
