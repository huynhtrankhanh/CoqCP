From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From Trusted Require Import SetTheory Protocol.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash Intern InternInvariant Rebuild Representation Bootstrap Observation SeedInput SeedBootstrap Startup.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module StartupContinuation.
Import IndexExecution SipHashExecution SeedInputExecution.
Theorem main_to_commands_framed key0 key1 tail bs ns :
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  exists ready,
    NativeRepresentation.canonical_arena ready [SetTheory.falsity] /\
    meta_value ready 0 = 0 /\ meta_value ready 8 = 0 /\
    (28 < length (memory ready arraydef_0__meta))%nat /\
    (1024 <= length (memory ready arraydef_0__token))%nat /\
    (20 <= length (memory ready arraydef_0__printBuffer))%nat /\ meta_value ready 9 = 0 /\ meta_value ready 3 = 0 /\
    stdin ready = tail /\ stdout ready = Protocol.handshake_output /\
    execObserved (funcdef_0__main bs ns) (SeedBootstrapExecution.initial key0 key1 tail [],[]) =
      execObserved (eliminateLocalVariables bs ns StartupExecution.commands_body)
        (ready,[{|flushedOutput := Protocol.seed_prompt; unreadInput := Protocol.seed_bytes key0 key1 ++ tail|};
                {|flushedOutput := Protocol.handshake_output; unreadInput := tail|}]).
Proof.
  intros Hkey0 Hkey1.
  set (s := SeedBootstrapExecution.initial key0 key1 tail []).
  set (before := seed_result (SeedBootstrapExecution.initial key0 key1 tail Protocol.seed_prompt) key0 key1 tail).
  set (observations := [{|flushedOutput := Protocol.seed_prompt; unreadInput := Protocol.seed_bytes key0 key1 ++ tail|}]).
  assert (Hm : (27 < length (memory s arraydef_0__meta))%nat) by (change (27 < 32)%nat; lia).
  assert (Ht : (1024 <= length (memory s arraydef_0__token))%nat) by (change (1024 <= 1024)%nat; lia).
  assert (Hp : meta_value s 15 = 0) by reflexivity.
  assert (He : meta_value s 8 = 0) by reflexivity.
  assert (Hin : stdin s = Protocol.seed_bytes key0 key1 ++ tail) by reflexivity.
  pose proof (generated_main_seed_prefix s bs ns key0 key1 tail [] Hm Ht Hp He Hkey0 Hkey1 Hin) as Hprefix.
  change (execObserved (funcdef_0__main bs ns) (s,[]) =
    execObserved (eliminateLocalVariables bs ns finish_body) (before,observations)) in Hprefix.
  assert (Hbmeta : (27 < length (memory before arraydef_0__meta))%nat).
  { unfold before. rewrite seed_meta_length. change (27 < 32)%nat. lia. }
  assert (Hberror : meta_value before 8 = 0).
  { unfold before. rewrite seed_meta_other by (try apply SeedBootstrapExecution.initial_meta; lia). reflexivity. }
  destruct (BootstrapExecution.generated_bootstrap_false_framed
    (SeedBootstrapExecution.prepared key0 key1 tail Protocol.seed_prompt)
    (fun _ => false) SeedBootstrapExecution.bootstrap_arguments ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
    (SeedBootstrapExecution.parsed_empty_arena key0 key1 tail Protocol.seed_prompt)
    (SeedBootstrapExecution.prepared_no_error key0 key1 tail Protocol.seed_prompt))
    as [boot [Hplain [[Harrays [Hmetadata [Hinput Houtput]]] [Harena [Hzero Herror]]]]].
  assert (Hinput' : stdin boot = tail) by (rewrite Hinput; reflexivity).
  assert (Houtput' : stdout boot = Protocol.seed_prompt).
  { rewrite Houtput. unfold SeedBootstrapExecution.prepared. change
      (stdout (seed_result (SeedBootstrapExecution.initial key0 key1 tail Protocol.seed_prompt) key0 key1 tail) = Protocol.seed_prompt).
    rewrite seed_output. reflexivity. }
  assert (Hboot : execObserved (funcdef_0__intern (fun _ => false) SeedBootstrapExecution.bootstrap_arguments)
    (store_meta before 20 1024,observations) = Some (tt,(boot,observations))).
  { apply observed_plain; [apply InternalObservation.intern_nf|exact Hplain]. }
  assert (Hcapacity : (1024 <= length (memory boot arraydef_0__token))%nat).
  { rewrite (Harrays arraydef_0__token ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
    unfold SeedBootstrapExecution.prepared. rewrite store_meta_other by discriminate.
    rewrite seed_token_length. change (1024 <= 1024)%nat. lia. }
  assert (Hprint : (20 <= length (memory boot arraydef_0__printBuffer))%nat).
  { rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
    rewrite SeedBootstrapExecution.prepared_other by discriminate. change (20 <= 20)%nat. lia. }
  assert (Hstop : meta_value boot 9 = 0).
  { rewrite (Hmetadata 9%nat ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold SeedBootstrapExecution.prepared. rewrite meta_store_other by lia.
    rewrite seed_meta_other by (try apply SeedBootstrapExecution.initial_meta; lia). reflexivity. }
  assert (Hhistory : meta_value boot 3 = 0).
  { rewrite (Hmetadata 3%nat ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold SeedBootstrapExecution.prepared. rewrite meta_store_other by lia.
    rewrite seed_meta_other by (try apply SeedBootstrapExecution.initial_meta; lia). reflexivity. }
  pose proof (proj1 (proj1 (proj1 Harena))) as Hmetalength.
  rewrite StartupExecution.actual_finish, StartupExecution.finish_zero in Hprefix by (try exact Hberror; lia).
  rewrite StartupExecution.success_factorization, StartupExecution.generated_prepare_intern in Hprefix by lia.
  rewrite Hboot in Hprefix. cbn [optionBind fst snd] in Hprefix.
  rewrite StartupExecution.generated_ready_observed in Hprefix. cbn [optionBind fst snd] in Hprefix.
  set (ready := withOutput boot (stdout boot ++ Protocol.ready_reply)). fold ready in Hprefix.
  rewrite Houtput', Hinput' in Hprefix.
  exists ready. split; [now apply StartupExecution.arena_output|]. split; [exact Hzero|]. split; [exact Herror|].
  split; [exact Hmetalength|]. split; [exact Hcapacity|]. split; [exact Hprint|]. split; [exact Hstop|]. split; [exact Hhistory|]. split; [exact Hinput'|]. split.
  - change (stdout boot ++ Protocol.ready_reply = Protocol.handshake_output). now rewrite Houtput'.
  - exact Hprefix.
Qed.
Theorem main_to_commands key0 key1 tail bs ns :
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  exists ready,
    NativeRepresentation.canonical_arena ready [SetTheory.falsity] /\
    meta_value ready 0 = 0 /\ meta_value ready 8 = 0 /\
    (28 < length (memory ready arraydef_0__meta))%nat /\
    (1024 <= length (memory ready arraydef_0__token))%nat /\
    stdin ready = tail /\ stdout ready = Protocol.handshake_output /\
    execObserved (funcdef_0__main bs ns) (SeedBootstrapExecution.initial key0 key1 tail [],[]) =
      execObserved (eliminateLocalVariables bs ns StartupExecution.commands_body)
        (ready,[{|flushedOutput := Protocol.seed_prompt; unreadInput := Protocol.seed_bytes key0 key1 ++ tail|};
                {|flushedOutput := Protocol.handshake_output; unreadInput := tail|}]).
Proof.
  intros Hkey0 Hkey1.
  destruct (main_to_commands_framed key0 key1 tail bs ns Hkey0 Hkey1)
    as [ready [Harena [Hzero [Herror [Hmeta [Htoken [Hprint [Hstop [Hhistory [Hin [Hout Hmain]]]]]]]]]]].
  exists ready. exact (conj Harena (conj Hzero (conj Herror (conj Hmeta (conj Htoken (conj Hin (conj Hout Hmain))))))).
Qed.
End StartupContinuation.
