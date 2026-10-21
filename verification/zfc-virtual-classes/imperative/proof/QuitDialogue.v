From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From Trusted Require Import SetTheory Protocol.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash Representation ArenaFrame CommandQuit QuitLoop SeedBootstrap StartupContinuation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module QuitDialogue.
Import IndexExecution SipHashExecution.
Theorem generated_seed_quit key0 key1 tail bs ns :
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  exists final, execObserved (funcdef_0__main bs ns)
      (SeedBootstrapExecution.initial key0 key1 (48 :: 10 :: tail) [],[]) = Some (tt,(final,
        [{|flushedOutput := Protocol.seed_prompt; unreadInput := Protocol.seed_bytes key0 key1 ++ 48 :: 10 :: tail|};
         {|flushedOutput := Protocol.handshake_output; unreadInput := 48 :: 10 :: tail|};
         {|flushedOutput := Protocol.handshake_output ++ CommandQuitExecution.bye_bytes; unreadInput := tail|}])) /\
    NativeRepresentation.canonical_arena final [SetTheory.falsity] /\
    meta_value final 9 = 1 /\ meta_value final 8 = 0 /\ stdin final = tail /\
    stdout final = Protocol.handshake_output ++ CommandQuitExecution.bye_bytes.
Proof.
  intros Hkey0 Hkey1.
  destruct (StartupContinuation.main_to_commands key0 key1 (48 :: 10 :: tail) bs ns Hkey0 Hkey1)
    as [ready [Harena [Hzero [Herror [Hmeta [Htoken [Hinput [Houtput Hprefix]]]]]]]].
  exists (QuitLoopExecution.loop_result ready tail). split.
  - rewrite Hprefix.
    pose proof (QuitLoopExecution.generated_loop_quit ready bs ns tail
      [{|flushedOutput := Protocol.seed_prompt; unreadInput := Protocol.seed_bytes key0 key1 ++ 48 :: 10 :: tail|};
       {|flushedOutput := Protocol.handshake_output; unreadInput := 48 :: 10 :: tail|}]
      ltac:(lia) Htoken Herror Hinput) as Hloop.
    unfold IndexExecution.Machine in Hloop |- *. rewrite Hloop.
    now rewrite Houtput.
  - split.
    + apply (ArenaFrame.storage_arena ready); [apply QuitLoopExecution.loop_storage|exact Harena].
    + split; [apply QuitLoopExecution.loop_stop; lia|]. split.
      * now rewrite QuitLoopExecution.loop_error.
      * split; [apply QuitLoopExecution.loop_input|]. now rewrite QuitLoopExecution.loop_output, Houtput.
Qed.
End QuitDialogue.
