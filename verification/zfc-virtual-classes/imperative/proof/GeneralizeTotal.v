From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash ReadOne TokenByte Representation ArenaFrame ClassStorage HistoryRefinement LogicalHistory SemanticFrames CommandGeneralize GeneralizeRefinement ReplyNO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module GeneralizeTotal.
Import IndexExecution SipHashExecution GeneralizeRefinement.
Lemma logical_rejected logical value : nth_error (Protocol.history logical) value = None ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 13 [value] []) Protocol.NO logical.
Proof.
  intros Hlookup Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H; subst end].
  match goal with H : Protocol.theorem_at logical value = Some _ |- _ => unfold Protocol.theorem_at in H; rewrite Hlookup in H; discriminate end.
Qed.
Theorem generated_rejected_protocol s logical bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> nth_error (Protocol.history logical) value = None ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 51 :: first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 13 [value] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\ HistoryRefinement.represents final logical.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Harena Hclasses Hhistory Hsep1 Hsep2 Hin.
  assert (Hopword : Z.of_nat 13 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadOne.generated_reads s (fun _ => false) (fun _ => 0) 13 49 [51] value first_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hvalue Hsep1 Hsep2 Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  set (arg := argument_state s value last_separator tail).
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_history : HistoryRefinement.represents arg logical) by now apply argument_history.
  assert (Hreference : meta_value arg 3 <= Z.of_nat value).
  { rewrite (proj1 Harg_history). apply nth_error_None in Hlookup. lia. }
  pose proof (CommandGeneralizeExecution.generated_rejected_command s bs ns _ arg (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference) as Hrun.
  rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state arg). split; [exact Hrun|].
  split; [apply logical_rejected; [exact Hlookup|now apply (SemanticFrames.arena_NoDup s)]|].
  split.
  - eapply ArenaFrame.storage_arena; [|exact Harena]. eapply ArenaFrame.storage_trans;
      [exact (ReadOne.argument_storage s 49 [51] value last_separator tail Hmeta)|apply ArenaFrame.storage_output].
  - split; [now apply argument_classes|exact Harg_history].
Qed.
Theorem generated_total_protocol s logical bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> Z.of_nat value <= maximum -> LogicalHistory.valid logical ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 51 :: first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 13 [value] []) reply next /\
    NativeRepresentation.canonical_arena final (Protocol.formulas next) /\
    ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) /\ HistoryRefinement.represents final next /\ LogicalHistory.valid next.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hhistorybound Hvalue Hvalid Harena Hclasses Hhistory Hsep1 Hsep2 Hin.
  destruct (nth_error (Protocol.history logical) value) as [fid|] eqn:Hlookup.
  - destruct (Hvalid value fid Hlookup) as [p Hp].
    assert (Htheorem : Protocol.theorem_at logical value = Some p) by (unfold Protocol.theorem_at; rewrite Hlookup; exact Hp).
    destruct (GeneralizeRefinement.generated_protocol s logical bs ns value p first_separator last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hbound Hhistorybound Hvalue Htheorem Harena Hclasses Hhistory Hsep1 Hsep2 Hin)
      as [final [index [fs [Hrun [Hstep [Ha [Hc Hh]]]]]]].
    exists final,(Protocol.OK (length (Protocol.history logical))),(logical_after logical fs index).
    split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split; [exact Hc|]. split; [exact Hh|].
    eapply LogicalHistory.step_valid; eassumption.
  - destruct (generated_rejected_protocol s logical bs ns value first_separator last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Harena Hclasses Hhistory Hsep1 Hsep2 Hin)
      as [final [Hrun [Hstep [Ha [Hc Hh]]]]].
    exists final,Protocol.NO,logical. split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split; [exact Hc|]. split; assumption.
Qed.
End GeneralizeTotal.
