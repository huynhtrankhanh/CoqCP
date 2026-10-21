From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From Trusted Require Import SetTheory Protocol.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash HashTable Rehash Intern InternInvariant Representation Bootstrap Observation SeedInput SeedBootstrap.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module StartupExecution.
Import IndexExecution SipHashExecution SeedInputExecution.
Ltac finish_cases code use :=
  lazymatch code with bind (bind _ ?branch) _ =>
    let error := eval cbn beta iota in (branch true) in
    let success := eval cbn beta iota in (branch false) in use error success
  end.
Definition error_body : LocalAction unit := ltac:(
  let code := eval unfold finish_body in finish_body in finish_cases code ltac:(fun error success => exact error)).
Definition success_body : LocalAction unit := ltac:(
  let code := eval unfold finish_body in finish_body in finish_cases code ltac:(fun error success => exact success)).
Definition finish_with (error success : LocalAction unit) : LocalAction unit := ltac:(
  let code := eval unfold finish_body in finish_body in
  finish_cases code ltac:(fun e s =>
    let generalized := eval pattern e,s in code in
    lazymatch generalized with ?family _ _ => exact (family error success) end)).
Lemma actual_finish : finish_body = finish_with error_body success_body.
Proof. reflexivity. Qed.
Lemma finish_zero error success s bs ns observations :
  (8 < length (memory s arraydef_0__meta))%nat -> meta_value s 8 = 0 ->
  execObserved (eliminateLocalVariables bs ns (finish_with error success)) (s,observations) =
    execObserved (eliminateLocalVariables bs ns success) (s,observations).
Proof.
  intros Hmeta Hflag. unfold finish_with.
  cbn [bind eliminateLocalVariables Action_rect retrieve execObserved observedStep step optionBind fst snd].
  unfold observedStep at 1. cbn [step optionBind fst snd].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z).
  replace (Z.to_nat 8) with 8%nat by reflexivity.
  cbn [optionBind fst snd].
  change (execObserved (eliminateLocalVariables bs ns
    ((if bool_decide (meta_value s 8 <> 0) then error else success) >>= fun _ => Done _ _ _ tt))
      (s,observations) = execObserved (eliminateLocalVariables bs ns success) (s,observations)).
  rewrite Hflag, bool_decide_false by congruence.
  rewrite observed_local_bind. cbn [execObserved eliminateLocalVariables].
  destruct (execObserved (eliminateLocalVariables bs ns success) (s,observations)) as [[[] after]|]; reflexivity.
Qed.
Lemma observed_lift (code : Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit) bs ns state :
  execObserved (eliminateLocalVariables (variableIndex := varsfuncdef_0__main) bs ns (liftToWithLocalVariables code)) state = execObserved code state.
Proof.
  induction code as [value|effect cont IH] in state |- *; [reflexivity|].
  cbn [liftToWithLocalVariables eliminateLocalVariables Action_rect execObserved].
  destruct (observedStep effect state) as [[value after]|]; cbn [optionBind fst snd]; [apply IH|reflexivity].
Qed.

Ltac success_parts code use :=
  lazymatch code with bind ?prepare ?next =>
    let code := eval cbn beta in (next tt) in
    lazymatch code with bind ?intern ?next =>
      let code := eval cbn beta in (next tt) in
      lazymatch code with bind ?ready ?next =>
        let code := eval cbn beta in (next tt) in
        lazymatch code with bind ?flush_part ?next =>
          let commands := eval cbn beta in (next tt) in use prepare intern ready flush_part commands
        end
      end
    end
  end.
Definition prepare_intern_body : LocalAction unit := ltac:(
  let code := eval unfold success_body in success_body in
  success_parts code ltac:(fun prepare intern ready flush_part commands => exact (prepare >>= fun _ => intern))).
Definition ready_body : LocalAction unit := ltac:(
  let code := eval unfold success_body in success_body in
  success_parts code ltac:(fun prepare intern ready flush_part commands => exact (ready >>= fun _ => flush_part))).
Definition commands_body : LocalAction unit := ltac:(
  let code := eval unfold success_body in success_body in
  success_parts code ltac:(fun prepare intern ready flush_part commands => exact commands)).
Lemma success_factorization s bs ns observations :
  execObserved (eliminateLocalVariables bs ns success_body) (s,observations) =
  optionBind (execObserved (eliminateLocalVariables bs ns prepare_intern_body) (s,observations)) (fun first =>
    optionBind (execObserved (eliminateLocalVariables bs ns ready_body) (snd first))
      (fun second => execObserved (eliminateLocalVariables bs ns commands_body) (snd second))).
Proof. unfold success_body, prepare_intern_body, ready_body, commands_body. apply observed_sequence_factorization. Qed.
Lemma observed_store s bs ns slot value observations :
  (Z.to_nat slot < length (memory s arraydef_0__meta))%nat ->
  execObserved (eliminateLocalVariables (variableIndex := varsfuncdef_0__main) bs ns
    (store _ _ _ arraydef_0__meta slot value)) (s,observations) =
    Some (tt,(store_meta s (Z.to_nat slot) value,observations)).
Proof.
  intro Hmeta. cbn [store eliminateLocalVariables Action_rect execObserved].
  unfold observedStep. cbn [step optionBind fst snd]. case_decide; [reflexivity|lia].
Qed.
Theorem generated_prepare_intern s bs ns observations :
  (20 < length (memory s arraydef_0__meta))%nat ->
  execObserved (eliminateLocalVariables bs ns prepare_intern_body) (s,observations) =
  execObserved (funcdef_0__intern (fun _ => false) SeedBootstrapExecution.bootstrap_arguments)
    (store_meta s 20 1024,observations).
Proof.
  intro Hmeta. unfold prepare_intern_body. change
    (execObserved (eliminateLocalVariables bs ns
      (store _ _ _ arraydef_0__meta 20 1024 >>= fun _ =>
       liftToWithLocalVariables (funcdef_0__intern (fun _ => false) SeedBootstrapExecution.bootstrap_arguments))) (s,observations) =
      execObserved (funcdef_0__intern (fun _ => false) SeedBootstrapExecution.bootstrap_arguments) (store_meta s 20 1024,observations)).
  rewrite observed_local_bind, observed_store by exact Hmeta. cbn [optionBind fst snd]. apply observed_lift.
Qed.
Theorem generated_ready_observed s bs ns observations :
  execObserved (eliminateLocalVariables bs ns ready_body) (s,observations) =
    Some (tt,(withOutput s (stdout s ++ Protocol.ready_reply),
      observations ++ [{| flushedOutput := stdout s ++ Protocol.ready_reply; unreadInput := stdin s |}])).
Proof.
  unfold ready_body.
  cbv beta iota zeta delta [loopString dropWithinLoop liftToWithinLoop liftToWithLocalVariables Action_rect
    bind writeChar flush eliminateLocalVariables execObserved observedStep step optionBind fst snd
    withOutput stdout stdin Protocol.ready_reply].
  repeat rewrite <- List.app_assoc. reflexivity.
Qed.

Lemma observed_tape_eof (body : Z -> LocalAction LoopOutcome) s bs ns observations : stdin s = [] ->
  execObserved (eliminateLocalVariables bs ns (tapeEnd body)) (s,observations) = Some (tt,(s,observations)).
Proof.
  destruct s as [values input output]. cbn [stdin]. intro Hin. subst input.
  cbn [tapeEnd loop readChar bind eliminateLocalVariables Action_rect execObserved observedStep step optionBind fst snd].
  reflexivity.
Qed.
Theorem generated_commands_eof s bs ns observations : stdin s = [] ->
  execObserved (eliminateLocalVariables bs ns commands_body) (s,observations) = Some (tt,(s,observations)).
Proof.
  intro Hin. unfold commands_body. rewrite observed_local_bind, observed_tape_eof by exact Hin.
  reflexivity.
Qed.


Lemma arena_output s meaning output : NativeRepresentation.canonical_arena s meaning ->
  NativeRepresentation.canonical_arena (withOutput s output) meaning.
Proof.
  intros [[Hready [Hcount [Hword [Hlength [Hload [Hindexed Hunique]]]]]] [Hrep [Hsem Hnormal]]].
  split.
  - split; [exact Hready|]. split; [exact Hcount|]. split; [exact Hword|].
    split; [exact Hlength|]. split; [exact Hload|]. split.
    + change (HashTableInvariant.indexed (withOutput s output) (length meaning) (RehashExecution.keyed_bucket s)).
      apply (RehashExecution.indexed_preserved s); try reflexivity. exact Hindexed.
    + exact Hunique.
  - split; [exact Hrep|]. split; assumption.
Qed.
Theorem generated_seed_only key0 key1 bs ns :
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  exists final, execObserved (funcdef_0__main bs ns)
      (SeedBootstrapExecution.initial key0 key1 [] [],[]) = Some (tt,(final,
        [{|flushedOutput := Protocol.seed_prompt; unreadInput := Protocol.seed_bytes key0 key1|};
         {|flushedOutput := Protocol.handshake_output; unreadInput := []|}])) /\
    NativeRepresentation.canonical_arena final [SetTheory.falsity] /\
    meta_value final 0 = 0 /\ meta_value final 8 = 0 /\ stdin final = [] /\
    stdout final = Protocol.handshake_output.
Proof.
  intros Hkey0 Hkey1.
  set (s := SeedBootstrapExecution.initial key0 key1 [] []).
  set (before := seed_result (SeedBootstrapExecution.initial key0 key1 [] Protocol.seed_prompt) key0 key1 []).
  set (observations := [{|flushedOutput := Protocol.seed_prompt; unreadInput := Protocol.seed_bytes key0 key1|}]).
  assert (Hm : (27 < length (memory s arraydef_0__meta))%nat) by (change (27 < 32)%nat; lia).
  assert (Ht : (1024 <= length (memory s arraydef_0__token))%nat) by (change (1024 <= 1024)%nat; lia).
  assert (Hp : meta_value s 15 = 0) by reflexivity.
  assert (He : meta_value s 8 = 0) by reflexivity.
  assert (Hin : stdin s = Protocol.seed_bytes key0 key1 ++ []) by reflexivity.
  pose proof (generated_main_seed_prefix s bs ns key0 key1 [] [] Hm Ht Hp He Hkey0 Hkey1 Hin) as Hprefix.
  change (execObserved (funcdef_0__main bs ns) (s,[]) =
    execObserved (eliminateLocalVariables bs ns finish_body) (before,
      [{|flushedOutput := Protocol.seed_prompt; unreadInput := Protocol.seed_bytes key0 key1 ++ []|}])) in Hprefix.
  rewrite List.app_nil_r in Hprefix. fold observations in Hprefix.
  assert (Hbmeta : (27 < length (memory before arraydef_0__meta))%nat).
  { unfold before. rewrite seed_meta_length. change (27 < 32)%nat. lia. }
  assert (Hberror : meta_value before 8 = 0).
  { unfold before. rewrite seed_meta_other by (try apply SeedBootstrapExecution.initial_meta; lia). reflexivity. }
  destruct (SeedBootstrapExecution.generated_parsed_bootstrap_observed key0 key1 [] Protocol.seed_prompt observations)
    as [boot [Hboot [Harena [Hzero [Herror [Hinput Houtput]]]]]].
  rewrite actual_finish, finish_zero in Hprefix by (try exact Hberror; lia).
  rewrite success_factorization, generated_prepare_intern in Hprefix by lia.
  change (execObserved (funcdef_0__intern (fun _ => false) SeedBootstrapExecution.bootstrap_arguments)
    (store_meta before 20 1024,observations) = Some (tt,(boot,observations))) in Hboot.
  rewrite Hboot in Hprefix. cbn [optionBind fst snd] in Hprefix.
  rewrite generated_ready_observed in Hprefix. cbn [optionBind fst snd] in Hprefix.
  rewrite generated_commands_eof in Hprefix by exact Hinput.
  exists (withOutput boot (stdout boot ++ Protocol.ready_reply)). split.
  - rewrite Hprefix. rewrite Houtput, Hinput. reflexivity.
  - split; [now apply arena_output|]. split; [exact Hzero|]. split; [exact Herror|]. split; [exact Hinput|].
    change (stdout boot ++ Protocol.ready_reply = Protocol.handshake_output). now rewrite Houtput.
Qed.
End StartupExecution.



