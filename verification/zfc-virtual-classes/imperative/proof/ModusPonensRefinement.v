From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash ReadTwo TokenByte Representation ArenaFrame ClassStorage HistoryRefinement SemanticFrames HistoryStorage HistoryLookup ModusPonens CommandMP.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module ModusPonensRefinement.
Import IndexExecution SipHashExecution.
Definition argument_state s i middle j last tail := ReadTwo.second_state s 49 [50] i middle j last tail.
Lemma argument_history s logical i middle j last tail :
  (17 < length (memory s arraydef_0__meta))%nat -> HistoryRefinement.represents s logical ->
  HistoryRefinement.represents (argument_state s i middle j last tail) logical.
Proof.
  intros Hmeta [Hcount Hprefix]. split.
  - unfold argument_state. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hcount.
  - unfold argument_state. rewrite ReadTwo.second_other by discriminate. exact Hprefix.
Qed.
Lemma argument_classes s fs cs i middle j last tail :
  (17 < length (memory s arraydef_0__meta))%nat -> ClassStorage.represents s fs cs ->
  ClassStorage.represents (argument_state s i middle j last tail) fs cs.
Proof.
  intros Hmeta [Hcount Hclasses]. split.
  - unfold argument_state. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hcount.
  - unfold argument_state. rewrite ReadTwo.second_other by discriminate. exact Hclasses.
Qed.
Theorem generated_protocol s logical bs ns i j p q first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> Z.of_nat i <= maximum -> Z.of_nat j <= maximum ->
  Protocol.theorem_at logical i = Some (SetTheory.implies p q) -> Protocol.theorem_at logical j = Some p ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 50 :: first_separator :: decimalBytes i ++ middle_separator :: decimalBytes j ++ last_separator :: tail ->
  exists final fid,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 12 [i;j] []) (Protocol.OK (length (Protocol.history logical)))
      (Protocol.with_history logical (Protocol.history logical ++ [fid])) /\
    nth_error (Protocol.formulas logical) fid = Some q /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final (Protocol.with_history logical (Protocol.history logical ++ [fid])).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hiword Hjword Himp Hante Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hin.
  assert (Hopword : Z.of_nat 12 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _ => false) (fun _ => 0) 12 49 [50] i j first_separator middle_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hiword Hjword Hsep1 Hsep2 Hsep3 Hin) as Hreads.
  destruct Hreads as [Hopcode [Hfirst [Hsecond [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror
    [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := argument_state s i middle_separator j last_separator tail).
  change (17 < length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (20 <= length (memory arg arraydef_0__printBuffer))%nat in Hargbuffer.
  change (meta_value arg 8 = 0) in Hargerror.
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s 49 [50] i middle_separator j last_separator tail Hmeta) Harena). }
  assert (Harg_history : HistoryRefinement.represents arg logical) by now apply argument_history.
  assert (Harg_classes : ClassStorage.represents arg (Protocol.formulas logical) (Protocol.classes logical)) by now apply argument_classes.
  destruct (HistoryLookup.modus_ponens_nodes arg logical i j p q Harg_arena Harg_history Himp Hante)
    as [node [aid [bid [Hbi [Hbj [Hnode [Hni [Hnj [Htuple Hlookup]]]]]]]]].
  assert (Hile : (i < length (Protocol.history logical))%nat).
  { unfold Protocol.theorem_at in Himp. destruct (nth_error (Protocol.history logical) i) as [f|] eqn:Hentry; [apply nth_error_Some; congruence|discriminate]. }
  assert (Hjle : (j < length (Protocol.history logical))%nat).
  { unfold Protocol.theorem_at in Hante. destruct (nth_error (Protocol.history logical) j) as [f|] eqn:Hentry; [apply nth_error_Some; congruence|discriminate]. }
  assert (Hiref : Z.of_nat i < meta_value arg 3) by (rewrite (proj1 Harg_history); lia).
  assert (Hjref : Z.of_nat j < meta_value arg 3) by (rewrite (proj1 Harg_history); lia).
  set (final := HistoryStorage.result arg (length (Protocol.history logical)) (Z.of_nat bid)).
  pose proof (ModusPonensExecution.generated_modusPonens arg (fun _ => false) (CommandMPExecution.arguments (Z.of_nat i) (Z.of_nat j))
    (length (Protocol.history logical)) i j node (Z.of_nat aid) (Z.of_nat bid) observations
    ltac:(lia) Hargbuffer Hargerror (proj1 Harg_history) Hbound Hbi Hbj Hnode Hni Hnj Htuple eq_refl eq_refl) as Hmp.
  assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (unfold final; rewrite HistoryStorage.result_meta_length; lia).
  assert (Hfinalerror : meta_value final 8 = 0) by (unfold final; rewrite HistoryStorage.result_meta_other by lia; exact Hargerror).
  pose proof (CommandMPExecution.generated_command s bs ns _ _ arg final (Z.of_nat i) (Z.of_nat j) observations _
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hfirst Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror Hsecond Hargmeta Hargnumber Hargvalid Hargerror
    Hiref Hjref Hmp Hfinalmeta Hfinalerror) as Hrun.
  rewrite Hinput, Houtput in Hrun. exists final,bid. split; [exact Hrun|].
  assert (Hunique : NoDup (Protocol.formulas logical)) by (now apply (SemanticFrames.arena_NoDup s)).
  split.
  - eapply Protocol.step_accept with (t := Protocol.with_history logical (Protocol.history logical ++ [bid])).
    + eapply Protocol.accept_proof with (p := q).
      * now apply (Protocol.req_mp logical i j p q).
      * split; [exists []; now rewrite app_nil_r|]. split; [exact Hunique|]. split; [exact Hlookup|]. exists []; now rewrite app_nil_r.
    + now apply HistoryRefinement.retained_refl.
  - split; [exact Hlookup|]. split; [now apply HistoryStorage.result_arena|].
    split; [now apply HistoryStorage.result_classes|]. apply HistoryStorage.append_represents; [lia|exact Harg_history].
Qed.
End ModusPonensRefinement.
