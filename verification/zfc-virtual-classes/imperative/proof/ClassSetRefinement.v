From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash TokenByte ClassStorage ClassSetInput Representation HistoryRefinement.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module ClassSetRefinement.
Import IndexExecution SipHashExecution.
Definition logical_after logical value := Protocol.State (Protocol.formulas logical)
  (Protocol.classes logical ++ [VirtualClasses.set value]) (Protocol.history logical)
  (Protocol.bindings logical) (Protocol.expressions logical).
Theorem logical_step logical value : NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req 5 [value] []) (Protocol.OK (length (Protocol.classes logical))) (logical_after logical value).
Proof.
  intro Hunique. eapply Protocol.step_accept; [apply Protocol.accept_set|].
  apply HistoryRefinement.retained_refl. exact Hunique.
Qed.
Lemma result_history s logical value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> HistoryRefinement.represents s logical ->
  HistoryRefinement.represents (ClassSetInput.result s (length (Protocol.classes logical)) value sep tail) (logical_after logical value).
Proof.
  intros Hmeta [Hcount Hprefix]. split.
  - unfold ClassSetInput.result. rewrite ClassStorage.result_meta_other by lia.
    rewrite ClassSetInput.argument_meta_other by (try exact Hmeta; lia). exact Hcount.
  - change (firstn (length (Protocol.history logical))
      (memory (ClassSetInput.result s (length (Protocol.classes logical)) value sep tail) arraydef_0__theorems) =
        map Z.of_nat (Protocol.history logical)).
    unfold ClassSetInput.result. rewrite ClassStorage.result_other by discriminate.
    rewrite ClassSetInput.argument_other by discriminate. exact Hprefix.
Qed.
Theorem generated_protocol s logical bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 54 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.classes logical)) < maximum -> Z.of_nat value <= maximum ->
  NoDup (Protocol.formulas logical) -> NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK (length (Protocol.classes logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 5 [value] []) (Protocol.OK (length (Protocol.classes logical))) (logical_after logical value) /\
    NativeRepresentation.canonical_arena final (Protocol.formulas (logical_after logical value)) /\
    ClassStorage.represents final (Protocol.formulas (logical_after logical value)) (Protocol.classes (logical_after logical value)) /\
    HistoryRefinement.represents final (logical_after logical value).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hword Hvalue Hunique Harena Hclasses Hhistory Hsep1 Hsep2 Hin.
  exists (ClassSetInput.result s (length (Protocol.classes logical)) value last_separator tail). split.
  - exact (ClassSetInput.generated_pending s bs ns (length (Protocol.classes logical)) value first_separator last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror (proj1 Hclasses) Hword Hvalue Hsep1 Hsep2 Hin).
  - split; [now apply logical_step|]. split; [now apply ClassSetInput.result_arena|].
    split; [now apply ClassSetInput.result_represents|now apply result_history].
Qed.
End ClassSetRefinement.
