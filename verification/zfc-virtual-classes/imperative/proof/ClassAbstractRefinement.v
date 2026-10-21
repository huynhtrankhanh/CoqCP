From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadOne ClassStorage ClassAbstractInput Representation HistoryRefinement.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module ClassAbstractRefinement.
Import IndexExecution SipHashExecution.
Definition logical_after logical p := Protocol.State (Protocol.formulas logical)
  (Protocol.classes logical ++ [VirtualClasses.abstract (VirtualClasses.core p)]) (Protocol.history logical)
  (Protocol.bindings logical) (Protocol.expressions logical).
Theorem logical_step logical value p :
  Protocol.formula_at logical value = Some p -> NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req 6 [value] []) (Protocol.OK (length (Protocol.classes logical))) (logical_after logical p).
Proof.
  intros Hlookup Hunique. eapply Protocol.step_accept; [apply Protocol.accept_abstract with (p := p); exact Hlookup|].
  apply HistoryRefinement.retained_refl. exact Hunique.
Qed.
Lemma result_history s logical value p sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> HistoryRefinement.represents s logical ->
  HistoryRefinement.represents (ClassAbstractInput.result s (length (Protocol.classes logical)) value sep tail) (logical_after logical p).
Proof.
  intros Hmeta [Hcount Hprefix]. split.
  - unfold ClassAbstractInput.result. rewrite ClassStorage.result_meta_other by lia.
    unfold ClassAbstractInput.argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount.
  - change (firstn (length (Protocol.history logical))
      (memory (ClassAbstractInput.result s (length (Protocol.classes logical)) value sep tail) arraydef_0__theorems) =
        map Z.of_nat (Protocol.history logical)).
    unfold ClassAbstractInput.result. rewrite ClassStorage.result_other by discriminate.
    unfold ClassAbstractInput.argument_state. rewrite ReadOne.argument_other by discriminate. exact Hprefix.
Qed.
Theorem generated_protocol s logical bs ns value p first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 55 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.classes logical)) < maximum -> Z.of_nat value <= maximum ->
  Protocol.formula_at logical value = Some p -> NoDup (Protocol.formulas logical) -> NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK (length (Protocol.classes logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 6 [value] []) (Protocol.OK (length (Protocol.classes logical))) (logical_after logical p) /\
    NativeRepresentation.canonical_arena final (Protocol.formulas (logical_after logical p)) /\
    ClassStorage.represents final (Protocol.formulas (logical_after logical p)) (Protocol.classes (logical_after logical p)) /\
    HistoryRefinement.represents final (logical_after logical p).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hword Hvalue Hlookup Hunique Harena Hclasses Hhistory Hsep1 Hsep2 Hin.
  assert (Hreference : Z.of_nat value < meta_value s 1).
  { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
    change (meta_value s 1 = Z.of_nat (length (Protocol.formulas logical))) in Hcount.
    assert (Hindex : (value < length (Protocol.formulas logical))%nat).
    { apply nth_error_Some. unfold Protocol.formula_at in Hlookup. congruence. }
    rewrite Hcount. lia. }
  exists (ClassAbstractInput.result s (length (Protocol.classes logical)) value last_separator tail). split.
  - exact (ClassAbstractInput.generated_pending s bs ns (length (Protocol.classes logical)) value first_separator last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror (proj1 Hclasses) Hword Hvalue Hreference Hsep1 Hsep2 Hin).
  - unfold Protocol.formula_at in Hlookup. split; [now apply logical_step|]. split; [now apply ClassAbstractInput.result_arena|].
    split; [now apply ClassAbstractInput.result_represents|now apply result_history].
Qed.
Theorem logical_rejected logical value : Protocol.formula_at logical value = None ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 6 [value] []) Protocol.NO logical.
Proof.
  intros Hlookup Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.formula_at logical value = Some _ |- _ => congruence end].
Qed.
Lemma rejected_history s logical value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> HistoryRefinement.represents s logical ->
  HistoryRefinement.represents (ClassAbstractInput.rejected s value sep tail) logical.
Proof.
  intros Hmeta [Hcount Hprefix]. split.
  - change (meta_value (ReadOne.argument_state s 54 [] value sep tail) 3 = Z.of_nat (length (Protocol.history logical))).
    rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount.
  - change (firstn (length (Protocol.history logical))
      (memory (ReadOne.argument_state s 54 [] value sep tail) arraydef_0__theorems) = map Z.of_nat (Protocol.history logical)).
    rewrite ReadOne.argument_other by discriminate. exact Hprefix.
Qed.
Theorem generated_rejected_protocol s logical bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 55 -> meta_value s 8 = 0 -> Z.of_nat value <= maximum ->
  Protocol.formula_at logical value = None -> NoDup (Protocol.formulas logical) ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 6 [value] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final logical.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Hunique Harena Hclasses Hhistory Hsep1 Hsep2 Hin.
  assert (Hreference : meta_value s 1 <= Z.of_nat value).
  { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
    change (meta_value s 1 = Z.of_nat (length (Protocol.formulas logical))) in Hcount.
    pose proof Hlookup as Hindex. unfold Protocol.formula_at in Hindex. apply nth_error_None in Hindex.
    rewrite Hcount. lia. }
  exists (ClassAbstractInput.rejected s value last_separator tail). split.
  - exact (ClassAbstractInput.generated_rejected s bs ns value first_separator last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hvalue Hreference Hsep1 Hsep2 Hin).
  - split; [now apply logical_rejected|]. split; [now apply ClassAbstractInput.rejected_arena|].
    split; [now apply ClassAbstractInput.rejected_represents|now apply rejected_history].
Qed.
Theorem generated_total_protocol s logical bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 55 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.classes logical)) < maximum -> Z.of_nat value <= maximum ->
  NoDup (Protocol.formulas logical) -> NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 6 [value] []) reply next /\
    NativeRepresentation.canonical_arena final (Protocol.formulas next) /\
    ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) /\
    HistoryRefinement.represents final next.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hword Hvalue Hunique Harena Hclasses Hhistory Hsep1 Hsep2 Hin.
  destruct (Protocol.formula_at logical value) as [p|] eqn:Hlookup.
  - destruct (generated_protocol s logical bs ns value p first_separator last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hword Hvalue Hlookup Hunique Harena Hclasses Hhistory Hsep1 Hsep2 Hin) as [final Hrun].
    exists final, (Protocol.OK (length (Protocol.classes logical))), (logical_after logical p). exact Hrun.
  - destruct (generated_rejected_protocol s logical bs ns value first_separator last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Hunique Harena Hclasses Hhistory Hsep1 Hsep2 Hin) as [final Hrun].
    exists final, Protocol.NO, logical. exact Hrun.
Qed.
End ClassAbstractRefinement.
