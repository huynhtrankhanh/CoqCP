From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte UndoInput ResetInput CommandReset.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module HistoryRefinement.
Import IndexExecution SipHashExecution.
(* This is the active-history component of the native state representation.
   It makes no claim about the not-yet-refined class/name/schema encodings. *)
Definition represents native logical :=
  meta_value native 3 = Z.of_nat (length (Protocol.history logical)) /\
  firstn (length (Protocol.history logical)) (memory native arraydef_0__theorems) =
    map Z.of_nat (Protocol.history logical).
Definition undone logical := Protocol.with_history logical (removelast (Protocol.history logical)).
Lemma retained_refl logical : NoDup (Protocol.formulas logical) -> Protocol.retained_storage logical logical.
Proof.
  intro Hunique. unfold Protocol.retained_storage. split; [exists []; now rewrite app_nil_r|].
  split; [exact Hunique|]. split; [exists []; now rewrite app_nil_r|]. repeat split; reflexivity.
Qed.
Lemma empty_rejected logical : Protocol.history logical = [] ->
  forall r t, ~ Protocol.accepted logical (Protocol.Req 16 [] []) r t.
Proof.
  intros Hempty r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.history logical = _ ++ [_] |- _ =>
        rewrite Hempty in H; apply (f_equal (@length nat)) in H;
        rewrite length_app in H; cbn [length] in H; lia end].
Qed.
Theorem logical_undo logical : NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req 16 [] [])
    (UndoInputExecution.reply (length (Protocol.history logical))) (undone logical).
Proof.
  intro Hunique. destruct (Protocol.history logical) as [|h hs] eqn:Hhistory.
  - change (Protocol.step logical (Protocol.Req 16 [] []) Protocol.NO (undone logical)).
    assert (Hsame : undone logical = logical).
    { unfold undone. rewrite Hhistory. destruct logical as [fs cs hist bs es].
      cbn [Protocol.history] in Hhistory. subst hist. reflexivity. }
    rewrite Hsame. apply Protocol.step_reject; [now apply empty_rejected|now apply retained_refl].
  - destruct (@List.exists_last nat (h :: hs) ltac:(discriminate)) as [prefix [last Hsplit]].
    assert (Hfull : Protocol.history logical = prefix ++ [last]) by congruence.
    unfold undone. rewrite Hfull, removelast_last.
    assert (Hlen : length (h :: hs) = S (length prefix)).
    { rewrite Hsplit, length_app. cbn [length]. lia. }
    rewrite Hlen. cbn [UndoInputExecution.reply].
    eapply Protocol.step_accept; [eapply Protocol.accept_undo with (last := last); exact Hfull|].
    apply retained_refl. exact Hunique.
Qed.
Lemma prefix_shorten xs hs last :
  firstn (S (length hs)) xs = map Z.of_nat (hs ++ [last]) ->
  firstn (length hs) xs = map Z.of_nat hs.
Proof.
  intro Hprefix. pose proof (f_equal (firstn (length hs)) Hprefix) as Hcut.
  rewrite firstn_firstn, Nat.min_l in Hcut by lia.
  rewrite map_app, firstn_app, firstn_map, firstn_all, length_map, Nat.sub_diag in Hcut.
  cbn [firstn] in Hcut. now rewrite app_nil_r in Hcut.
Qed.
Theorem undo_represents native logical tail :
  (17 < length (memory native arraydef_0__meta))%nat -> represents native logical ->
  represents (UndoInputExecution.result native tail (length (Protocol.history logical))) (undone logical).
Proof.
  intros Hmeta [Hcount Hprefix]. unfold represents, undone. cbn [Protocol.with_history Protocol.history].
  destruct (Protocol.history logical) as [|h hs] eqn:Hhistory.
  - split; [exact (UndoInputExecution.result_history native tail 0 Hmeta Hcount)|reflexivity].
  - destruct (@List.exists_last nat (h :: hs) ltac:(discriminate)) as [prefix [last Hsplit]].
    rewrite Hsplit, removelast_last.
    assert (Hlen : length (prefix ++ [last]) = S (length prefix)).
    { rewrite length_app. cbn [length]. lia. }
    split.
    + rewrite UndoInputExecution.result_history by (try exact Hmeta; congruence). rewrite Hlen. reflexivity.
    + rewrite UndoInputExecution.result_named_objects by discriminate.
      apply (prefix_shorten _ prefix last). rewrite <- Hlen, <- Hsplit. exact Hprefix.
Qed.
Theorem generated_undo_history native logical bs ns sep tail observations :
  (17 < length (memory native arraydef_0__meta))%nat ->
  (1024 <= length (memory native arraydef_0__token))%nat ->
  (20 <= length (memory native arraydef_0__printBuffer))%nat ->
  meta_value native 15 = 50 -> meta_value native 8 = 0 ->
  Z.of_nat (length (Protocol.history logical)) <= maximum ->
  NoDup (Protocol.formulas logical) -> represents native logical ->
  TokenByteExecution.separator sep -> stdin native = 54 :: sep :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (native,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout native ++ Protocol.reply_bytes
        (UndoInputExecution.reply (length (Protocol.history logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 16 [] [])
      (UndoInputExecution.reply (length (Protocol.history logical))) (undone logical) /\
    represents final (undone logical).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hword Hunique Hrep Hsep Hin.
  exists (UndoInputExecution.result native tail (length (Protocol.history logical))). split.
  - exact (UndoInputExecution.generated_pending native bs ns (length (Protocol.history logical)) sep tail observations
      Hmeta Htoken Hbuffer Hpending Herror (proj1 Hrep) Hword Hsep Hin).
  - split; [now apply logical_undo|now apply undo_represents].
Qed.
Theorem logical_reset logical : NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req 17 [] []) (Protocol.OK 0) (Protocol.with_history logical []).
Proof.
  intro Hunique. eapply Protocol.step_accept; [apply Protocol.accept_reset|].
  apply retained_refl. exact Hunique.
Qed.
Theorem reset_represents native logical tail :
  (17 < length (memory native arraydef_0__meta))%nat ->
  represents (CommandResetExecution.reset_state (ResetInputExecution.parsed_reset native tail)) (Protocol.with_history logical []).
Proof.
  intro Hmeta. split; [|reflexivity]. apply ResetInputExecution.reset_history_zero.
  rewrite ResetInputExecution.parsed_meta_length. lia.
Qed.
Theorem generated_reset_history native logical bs ns sep tail observations :
  (17 < length (memory native arraydef_0__meta))%nat ->
  (1024 <= length (memory native arraydef_0__token))%nat ->
  (20 <= length (memory native arraydef_0__printBuffer))%nat ->
  meta_value native 15 = 50 -> meta_value native 8 = 0 ->
  NoDup (Protocol.formulas logical) ->
  TokenByteExecution.separator sep -> stdin native = 55 :: sep :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (native,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout native ++ Protocol.reply_bytes (Protocol.OK 0); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 17 [] []) (Protocol.OK 0) (Protocol.with_history logical []) /\
    represents final (Protocol.with_history logical []).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hunique Hsep Hin.
  exists (CommandResetExecution.reset_state (ResetInputExecution.parsed_reset native tail)). split.
  - exact (ResetInputExecution.generated_reset_pending native bs ns sep tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hsep Hin).
  - split; [now apply logical_reset|now apply reset_represents].
Qed.
End HistoryRefinement.
