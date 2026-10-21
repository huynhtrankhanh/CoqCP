From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash ReadOne ParsedState TokenByte Representation ArenaFrame FormulaProjection ClassStorage HistoryRefinement HistoryLookup LogicalHistory SemanticFrames CommandInspect ReplyOK ReplyNO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module InspectRefinement.
Import IndexExecution SipHashExecution.
Lemma logical_rejected logical value : nth_error (Protocol.history logical) value = None ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 19 [value] []) Protocol.NO logical.
Proof.
  intros Hlookup Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end
      |congruence].
Qed.
Theorem generated_total_protocol s logical bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> LogicalHistory.valid logical ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 57 :: first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final reply,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 19 [value] []) reply logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\ HistoryRefinement.represents final logical.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hvalid Harena Hclasses Hhistory Hsep1 Hsep2 Hin.
  assert (Hopword : Z.of_nat 19 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadOne.generated_reads s (fun _ => false) (fun _ => 0) 19 49 [57] value first_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hvalue Hsep1 Hsep2 Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  set (arg := ReadOne.argument_state s 49 [57] value last_separator tail).
  change (17 < length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadOne.argument_storage s 49 [57] value last_separator tail Hmeta) Harena). }
  pose proof (ParsedState.one_history s logical 49 [57] value last_separator tail Hmeta Hhistory) as Harg_history.
  pose proof (ParsedState.one_classes s _ _ 49 [57] value last_separator tail Hmeta Hclasses) as Harg_classes.
  change (HistoryRefinement.represents arg logical) in Harg_history.
  change (ClassStorage.represents arg (Protocol.formulas logical) (Protocol.classes logical)) in Harg_classes.
  assert (Hunique : NoDup (Protocol.formulas logical)) by now apply (SemanticFrames.arena_NoDup s).
  destruct (nth_error (Protocol.history logical) value) as [fid|] eqn:Hlookup.
  - destruct (Hvalid value fid Hlookup) as [p Hp].
    destruct (HistoryLookup.native_lookup arg logical value fid Harg_history Hlookup) as [Hnative Hnth].
    pose proof (proj1 (proj2 (HistoryLookup.formula_reference s _ fid p Harena Hp))) as Hword.
    assert (Hreference : Z.of_nat value < meta_value arg 3).
    { rewrite (proj1 Harg_history). assert (value < length (Protocol.history logical))%nat by (apply nth_error_Some; congruence). lia. }
    pose proof (CommandInspectExecution.generated_command s bs ns _ arg fid (Z.of_nat value) observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference
      ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) Hargbuffer (proj2 Hword)) as Hrun.
    rewrite Hinput,Houtput in Hrun. exists (ReplyOKExecution.reply_state arg fid),(Protocol.OK fid). split; [exact Hrun|].
    split.
    + eapply Protocol.step_accept; [apply Protocol.accept_inspect; exact Hlookup|now apply HistoryRefinement.retained_refl].
    + split; [exact (FormulaProjection.storage_arena arg _ _ (FormulaProjection.reply_storage arg fid) Harg_arena)|].
      split; [now apply SemanticFrames.reply_classes|now apply SemanticFrames.reply_history].
  - assert (Hreference : meta_value arg 3 <= Z.of_nat value).
    { rewrite (proj1 Harg_history). apply nth_error_None in Hlookup. lia. }
    pose proof (CommandInspectExecution.generated_rejected_command s bs ns _ arg (Z.of_nat value) observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference) as Hrun.
    rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state arg),Protocol.NO. split; [exact Hrun|].
    split; [now apply logical_rejected|]. split.
    + eapply ArenaFrame.storage_arena; [|exact Harg_arena]. apply ArenaFrame.storage_output.
    + split; assumption.
Qed.
End InspectRefinement.
