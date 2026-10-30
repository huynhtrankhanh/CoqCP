From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash ReadTwo ParsedState TokenByte Representation FormulaEncoding ArenaFrame ClassStorage HistoryRefinement HistoryLookup HistoryStorage LogicalHistory SemanticFrames CommandRestate CommandRestateReject ReplyNO.
From NativeProof Require Import NativeArgumentReadsTwoFull NativeState NativeStateFrames NativeProtocolLift.
From Trusted Require Import Guarantees.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeWhitespaceRestate.
Import IndexExecution SipHashExecution.
Definition argument_state s i middle j last tail := ReadTwo.second_state s 49 [56] i middle j last tail.
Lemma logical_rejected logical i j : FormulaEncoding.unique (Protocol.formulas logical) ->
  nth_error (Protocol.history logical) i <> Some j -> NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req 18 [i;j] []) Protocol.NO logical.
Proof.
  intros Hunique Hbad Hnodup. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H; subst end].
  match goal with Ht : Protocol.theorem_at logical i = Some ?p, Hj : Protocol.formula_at logical j = Some ?p |- _ =>
    unfold Protocol.theorem_at in Ht;
    destruct (nth_error (Protocol.history logical) i) as [fid|] eqn:Hentry; [|discriminate];
    assert (Heq : fid = j) by (eapply Hunique; eassumption); subst fid; congruence end.
Qed.
Theorem generated_protocol s logical bs ns i j p first_separator prefix1 middle_separator prefix2 last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> Z.of_nat i <= maximum -> Z.of_nat j <= maximum ->
  nth_error (Protocol.history logical) i = Some j -> Protocol.formula_at logical j = Some p ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = 56 :: first_separator :: prefix1 ++ decimalBytes i ++ middle_separator :: prefix2 ++ decimalBytes j ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 18 [i;j] []) (Protocol.OK (length (Protocol.history logical)))
      (Protocol.with_history logical (Protocol.history logical ++ [j])) /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final (Protocol.with_history logical (Protocol.history logical ++ [j])).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hiword Hjword Hlookup Hformula Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
  assert (Hopword : Z.of_nat 18 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReadsTwoFull.generated_reads s (fun _ => false) (fun _ => 0) 18 49 [56] i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hiword Hjword Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin) as Hreads.
  destruct Hreads as [Hopcode [Hfirst [Hsecond [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror
    [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := argument_state s i middle_separator j last_separator tail).
  change (17 < length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s 49 [56] i middle_separator j last_separator tail Hmeta) Harena). }
  assert (Harg_history : HistoryRefinement.represents arg logical) by exact (ParsedState.two_history s logical 49 [56] i middle_separator j last_separator tail Hmeta Hhistory).
  assert (Harg_classes : ClassStorage.represents arg (Protocol.formulas logical) (Protocol.classes logical)) by exact (ParsedState.two_classes s _ _ 49 [56] i middle_separator j last_separator tail Hmeta Hclasses).
  destruct (HistoryLookup.native_lookup arg logical i j Harg_history Hlookup) as [Hnative Hnth].
  assert (Hiref : Z.of_nat i < meta_value arg 3).
  { rewrite (proj1 Harg_history). assert (i < length (Protocol.history logical))%nat by (apply nth_error_Some; congruence). lia. }
  assert (Hjref : Z.of_nat j < meta_value arg 1).
  { pose proof (proj1 (proj2 (proj1 Harg_arena))) as Hcount. rewrite Hcount.
    assert (j < length (Protocol.formulas logical))%nat by (apply nth_error_Some; unfold Protocol.formula_at in Hformula; congruence). lia. }
  pose proof (CommandRestateExecution.generated_command s bs ns _ _ arg (length (Protocol.history logical)) (Z.of_nat i) (Z.of_nat j) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hfirst Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror Hsecond Hargmeta Hargnumber Hargvalid Hargerror
    Hiref Hjref ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) (proj1 Harg_history) Hbound Hargbuffer) as Hrun.
  rewrite Hinput,Houtput in Hrun. exists (HistoryStorage.result arg (length (Protocol.history logical)) (Z.of_nat j)). split; [exact Hrun|].
  assert (Hunique : NoDup (Protocol.formulas logical)) by now apply (SemanticFrames.arena_NoDup s).
  split.
  - eapply Protocol.step_accept with (t := Protocol.with_history logical (Protocol.history logical ++ [j])).
    + eapply Protocol.accept_proof with (p := p).
      * apply (Protocol.req_restate logical i j p); [unfold Protocol.theorem_at; now rewrite Hlookup|exact Hformula].
      * split; [exists []; now rewrite app_nil_r|]. split; [exact Hunique|]. split; [exact Hformula|]. exists []; now rewrite app_nil_r.
    + now apply HistoryRefinement.retained_refl.
  - split; [now apply HistoryStorage.result_arena|]. split; [now apply HistoryStorage.result_classes|].
    apply HistoryStorage.append_represents; [lia|exact Harg_history].
Qed.
Theorem generated_rejected_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat i <= maximum -> Z.of_nat j <= maximum -> nth_error (Protocol.history logical) i <> Some j ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = 56 :: first_separator :: prefix1 ++ decimalBytes i ++ middle_separator :: prefix2 ++ decimalBytes j ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 18 [i;j] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\ HistoryRefinement.represents final logical.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hbad Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
  assert (Hopword : Z.of_nat 18 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReadsTwoFull.generated_reads s (fun _ => false) (fun _ => 0) 18 49 [56] i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hiword Hjword Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin) as Hreads.
  destruct Hreads as [Hopcode [Hfirst [Hsecond [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror
    [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := argument_state s i middle_separator j last_separator tail).
  change (17 < length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s 49 [56] i middle_separator j last_separator tail Hmeta) Harena). }
  assert (Harg_history : HistoryRefinement.represents arg logical) by exact (ParsedState.two_history s logical 49 [56] i middle_separator j last_separator tail Hmeta Hhistory).
  pose proof (proj1 (proj2 (proj1 Harg_arena))) as Hfcount. pose proof (proj1 Harg_history) as Hhcount.
  assert (Hrun : execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(ReplyNOExecution.reply_state arg,
    observations ++ [{|flushedOutput := stdout arg ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin arg|}]))).
  { destruct (Z_lt_dec (Z.of_nat i) (meta_value arg 3)) as [Hiref|Hibad];
      destruct (Z_lt_dec (Z.of_nat j) (meta_value arg 1)) as [Hjref|Hjbad].
    - assert (Hi : (i < length (Protocol.history logical))%nat) by (rewrite Hhcount in Hiref; lia).
      destruct (nth_error (Protocol.history logical) i) as [fid|] eqn:Hlookup; [|apply nth_error_None in Hlookup; lia].
      destruct (HistoryLookup.native_lookup arg logical i fid Harg_history Hlookup) as [Hnative Hnth].
      eapply CommandRestateReject.generated_mismatch_command; try eassumption.
      + now rewrite Nat2Z.id.
      + rewrite Nat2Z.id,Hnth. intro Heq. apply Hbad. assert (fid = j) by lia. now subst fid.
    - eapply CommandRestateReject.generated_invalid_command; try eassumption. right. lia.
    - eapply CommandRestateReject.generated_invalid_command; try eassumption. left. lia.
    - eapply CommandRestateReject.generated_invalid_command; try eassumption. left. lia. }
  rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state arg). split; [exact Hrun|].
  split; [apply logical_rejected; [exact (proj1 (proj2 (proj2 Harena)))|exact Hbad|now apply (SemanticFrames.arena_NoDup s)]|].
  split.
  - eapply ArenaFrame.storage_arena; [|exact Harg_arena]. apply ArenaFrame.storage_output.
  - split; [exact (ParsedState.two_classes s _ _ 49 [56] i middle_separator j last_separator tail Hmeta Hclasses)|exact Harg_history].
Qed.
Theorem generated_total_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat i <= maximum -> Z.of_nat j <= maximum -> Z.of_nat (length (Protocol.history logical)) < maximum -> LogicalHistory.valid logical ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = 56 :: first_separator :: prefix1 ++ decimalBytes i ++ middle_separator :: prefix2 ++ decimalBytes j ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 18 [i;j] []) reply next /\
    NativeRepresentation.canonical_arena final (Protocol.formulas next) /\
    ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) /\ HistoryRefinement.represents final next /\ LogicalHistory.valid next.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hbound Hvalid Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
  destruct (nth_error (Protocol.history logical) i) as [fid|] eqn:Hlookup.
  - destruct (Nat.eq_dec fid j) as [Heq|Hne].
    + subst fid. destruct (Hvalid i j Hlookup) as [p Hp].
      destruct (generated_protocol s logical bs ns i j p first_separator prefix1 middle_separator prefix2 last_separator tail observations
        Hmeta Htoken Hbuffer Hpending Herror Hbound Hiword Hjword Hlookup Hp Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
        as [final [Hrun [Hstep [Ha [Hc Hh]]]]].
      exists final,(Protocol.OK (length (Protocol.history logical))),(Protocol.with_history logical (Protocol.history logical ++ [j])).
      split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split; [exact Hc|]. split; [exact Hh|].
      eapply LogicalHistory.step_valid; eassumption.
    + destruct (generated_rejected_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
        Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword ltac:(congruence) Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
        as [final [Hrun [Hstep [Ha [Hc Hh]]]]].
      exists final,Protocol.NO,logical. split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split; [exact Hc|]. split; assumption.
  - destruct (generated_rejected_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword ltac:(congruence) Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
      as [final [Hrun [Hstep [Ha [Hc Hh]]]]].
    exists final,Protocol.NO,logical. split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split; [exact Hc|]. split; assumption.
Qed.
Theorem generated_total_state s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat i <= maximum -> Z.of_nat j <= maximum -> Z.of_nat (length (Protocol.history logical)) < maximum -> LogicalHistory.valid logical ->
  NativeState.represents s logical -> TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator ->
  TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = 56 :: first_separator :: prefix1 ++ decimalBytes i ++ middle_separator :: prefix2 ++ decimalBytes j ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 18 [i;j] []) reply next /\ NativeState.represents final next /\
    LogicalHistory.valid next /\ (Guarantees.safe logical -> Guarantees.safe next).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hbound Hvalid Hstate Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
 destruct(generated_total_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hbound Hvalid (NativeState.formula_representation _ _ Hstate)
   (NativeState.class_representation _ _ Hstate) (NativeState.history_representation _ _ Hstate) Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
 as(final & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory & Hvalid').
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeProtocolLift.canonical 18 49 [56] s bs ns first_separator
    (prefix1++decimalBytes i++middle_separator::prefix2++decimalBytes j++last_separator::tail) observations final _ logical (Protocol.Req 18 [i;j] []) reply next
    ltac:(lia) ltac:(lia) _ eq_refl eq_refl Hmeta Htoken Hpending Herror Hsep1 Hin Hrun Hstate Hstep Harena Hclasses Hhistory).
   unfold NativeStateFrames.nonbinding;repeat split;lia.
 - split;[exact Hvalid'|]. intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End NativeWhitespaceRestate.
