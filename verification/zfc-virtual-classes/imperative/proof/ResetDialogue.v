From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash Representation SeedBootstrap StartupContinuation ResetLoop.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ResetDialogue.
Import IndexExecution SipHashExecution.
Theorem generated_seed_reset key0 key1 bs ns :
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  exists final,
    execObserved (funcdef_0__main bs ns)
      (SeedBootstrapExecution.initial key0 key1 [49;55;10] [],[]) = Some (tt,(final,
        [{|flushedOutput := Protocol.seed_prompt; unreadInput := Protocol.seed_bytes key0 key1 ++ [49;55;10]|};
         {|flushedOutput := Protocol.handshake_output; unreadInput := [49;55;10]|};
         {|flushedOutput := Protocol.handshake_output ++ Protocol.reply_bytes (Protocol.OK 0); unreadInput := []|}])) /\
    NativeRepresentation.canonical_arena final [SetTheory.falsity] /\
    meta_value final 3 = 0 /\ meta_value final 8 = 0 /\ meta_value final 9 = 0 /\
    stdin final = [] /\ stdout final = Protocol.handshake_output ++ Protocol.reply_bytes (Protocol.OK 0).
Proof.
  intros Hkey0 Hkey1.
  destruct (StartupContinuation.main_to_commands_framed key0 key1 [49;55;10] bs ns Hkey0 Hkey1)
    as [ready [Harena [Hzero [Herror [Hmeta [Htoken [Hprint [Hstop [Hhistory [Hin [Hout Hmain]]]]]]]]]]].
  assert (Hcapacity : (17 < length (memory ready arraydef_0__meta))%nat).
  { eapply Nat.le_lt_trans with (m := 28%nat); [lia|exact Hmeta]. }
  pose proof (ResetLoopExecution.generated_loop_reset ready bs ns
    [{|flushedOutput := Protocol.seed_prompt; unreadInput := Protocol.seed_bytes key0 key1 ++ [49;55;10]|};
     {|flushedOutput := Protocol.handshake_output; unreadInput := [49;55;10]|}]
    Hcapacity Htoken Hprint Herror Hstop Hin) as Hloop.
  rewrite Hout in Hloop.
  exists (ResetLoopExecution.result ready). split; [exact (eq_trans Hmain Hloop)|].
  split; [now apply ResetLoopExecution.result_arena|].
  split; [now apply ResetLoopExecution.result_history_zero|].
  split; [rewrite ResetLoopExecution.result_meta_other by lia; exact Herror|].
  split; [rewrite ResetLoopExecution.result_meta_other by lia; exact Hstop|].
  split; [apply ResetLoopExecution.result_input|]. rewrite ResetLoopExecution.result_output, Hout. reflexivity.
Qed.
End ResetDialogue.
