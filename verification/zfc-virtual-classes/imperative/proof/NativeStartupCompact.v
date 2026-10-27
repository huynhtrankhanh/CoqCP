From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From Trusted Require Import SetTheory Protocol.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash Intern InternInvariant Rebuild Representation Bootstrap Observation SeedInput SeedBootstrap Startup NativeState FormulaTopology InternLengths NativeStartup.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module NativeStartupCompact.
Import IndexExecution SipHashExecution SeedInputExecution NativeStartup.
Theorem main_to_commands key0 key1 tail bs ns :
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  exists ready,
    NativeState.represents ready Protocol.initial /\
    FormulaTopology.ordered ready 1 /\
    length (memory ready arraydef_0__meta)=32%nat /\ length (memory ready arraydef_0__sipState)=1%nat /\
    meta_value ready 0 = 0 /\ meta_value ready 8 = 0 /\
    (28 < length (memory ready arraydef_0__meta))%nat /\
    (1024 <= length (memory ready arraydef_0__token))%nat /\
    (20 <= length (memory ready arraydef_0__printBuffer))%nat /\ meta_value ready 9 = 0 /\ meta_value ready 3 = 0 /\
    stdin ready = tail /\ stdout ready = Protocol.handshake_output /\
    execObserved (funcdef_0__main bs ns) (SeedBootstrapExecution.initial key0 key1 tail [],[]) =
      execObserved (eliminateLocalVariables bs ns StartupExecution.commands_body)
        (ready,[{|flushedOutput := Protocol.seed_prompt; unreadInput := Protocol.seed_bytes key0 key1 ++ tail|};
                {|flushedOutput := Protocol.handshake_output; unreadInput := tail|}]) /\ NativeState.empty_registries ready.
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
  assert (HbootEmpty:NativeState.empty_registries boot).
  { apply (frame_empty (SeedBootstrapExecution.prepared key0 key1 tail Protocol.seed_prompt) boot);
      [repeat split;assumption|apply prepared_empty]. }
  assert (Hstate:NativeState.represents boot Protocol.initial) by (now apply NativeState.initial).
  destruct (FormulaTopology.generated_intern_preserves
    (SeedBootstrapExecution.prepared key0 key1 tail Protocol.seed_prompt)
    (fun _=>false) SeedBootstrapExecution.bootstrap_arguments [] SetTheory.falsity
    (SeedBootstrapExecution.parsed_empty_arena key0 key1 tail Protocol.seed_prompt)
    (FormulaTopology.empty _) (SeedBootstrapExecution.prepared_no_error key0 key1 tail Protocol.seed_prompt)
    ltac:(cbn;lia) ltac:(reflexivity)) as (same & Hsame & HsameFlag & Hordered).
  rewrite Hplain in Hsame. injection Hsame as <-.
  assert (Hcount:meta_value boot 1=1) by exact (proj1 (proj2 (proj1 Harena))).
  rewrite Hcount in Hordered.
  destruct (InternLengths.observed_lengths (store_meta before 20 1024) (fun _=>false)
    SeedBootstrapExecution.bootstrap_arguments observations boot observations Hboot) as [HmetaExact HsipExact].
  assert (Hmeta32:length (memory boot arraydef_0__meta)=32%nat).
  { rewrite HmetaExact,store_meta_length. unfold before. rewrite seed_meta_length. reflexivity. }
  assert (Hsip1:length (memory boot arraydef_0__sipState)=1%nat).
  { rewrite HsipExact,store_meta_other by discriminate. unfold before. rewrite seed_other by discriminate. reflexivity. }
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
  exists ready. split;[now apply NativeState.output|]. split;[|].
  { apply (FormulaTopology.same boot);[exact Hordered|]. intros parent Hparent. reflexivity. }
  split;[exact Hmeta32|]. split;[exact Hsip1|]. split;[exact Hzero|]. split;[exact Herror|].
  split; [exact Hmetalength|]. split; [exact Hcapacity|]. split; [exact Hprint|]. split; [exact Hstop|]. split; [exact Hhistory|]. split; [exact Hinput'|]. split.
  - change (stdout boot ++ Protocol.ready_reply = Protocol.handshake_output). now rewrite Houtput'.
  - split;[exact Hprefix|]. destruct HbootEmpty. constructor;assumption.
Qed.
End NativeStartupCompact.
