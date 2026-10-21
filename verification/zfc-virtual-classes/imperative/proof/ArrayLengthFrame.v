From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From stdpp Require Import numbers list.
From Stdlib Require Import Strings.String Lists.List.

(* Stores preserve allocation lengths; growth of the watched array is
   excluded. The effect proof composes through helpers and finite loops. *)
Module ArrayLengthFrame.
Section Effects.
Context {I : Type} {T : I -> Type} (watched : I).
Definition safe_effect (effect : WithArrays I T) : Prop :=
  match effect with Grow _ _ name _ _ => name <> watched | _ => True end.
Fixpoint array_ro {R} (code : Action (WithArrays I T) withArraysReturnValue R) : Prop :=
  match code with Done _ _ _ _ => True | Dispatch _ _ _ effect next => safe_effect effect /\ forall value, array_ro (next value) end.
Context {V : Type}.
Definition safe_local (effect : WithLocalVariables I T V) : Prop :=
  match effect with DoWithArrays _ _ _ effect => safe_effect effect | _ => True end.
Fixpoint local_ro {R} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) : Prop :=
  match code with Done _ _ _ _ => True | Dispatch _ _ _ effect next => safe_local effect /\ forall value, local_ro (next value) end.
Definition safe_within (effect : WithinLoop I T V) : Prop :=
  match effect with DoWithLocalVariables _ _ _ effect => safe_local effect | _ => True end.
Fixpoint within_ro {R} (code : Action (WithinLoop I T V) withinLoopReturnValue R) : Prop :=
  match code with Done _ _ _ _ => True | Dispatch _ _ _ effect next => safe_within effect /\ forall value, within_ro (next value) end.
Lemma array_bind {A B} (code : Action (WithArrays I T) withArraysReturnValue A) next :
  array_ro code -> (forall value, array_ro (next value)) -> array_ro (R := B) (code >>= next).
Proof.
  induction code as [value|effect cont IH]; [intros _ Hnext; apply Hnext|].
  intros [Hsafe Hcont] Hnext. split; [exact Hsafe|]. intro r. now apply IH.
Qed.
Lemma local_bind {A B} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue A) next :
  local_ro code -> (forall value, local_ro (next value)) -> local_ro (R := B) (code >>= next).
Proof.
  induction code as [value|effect cont IH]; [intros _ Hnext; apply Hnext|].
  intros [Hsafe Hcont] Hnext. split; [exact Hsafe|]. intro r. now apply IH.
Qed.
Lemma within_bind {A B} (code : Action (WithinLoop I T V) withinLoopReturnValue A) next :
  within_ro code -> (forall value, within_ro (next value)) -> within_ro (R := B) (code >>= next).
Proof.
  induction code as [value|effect cont IH]; [intros _ Hnext; apply Hnext|].
  intros [Hsafe Hcont] Hnext. split; [exact Hsafe|]. intro r. now apply IH.
Qed.
Lemma local_lift {R} (code : Action (WithArrays I T) withArraysReturnValue R) :
  array_ro code -> local_ro (liftToWithLocalVariables code).
Proof.
  induction code as [value|effect cont IH]; [constructor|]. intros [Hsafe Hcont].
  cbn [liftToWithLocalVariables Action_rect local_ro]. split; [exact Hsafe|]. intro r. now apply IH.
Qed.
Lemma within_lift {R} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) :
  local_ro code -> within_ro (liftToWithinLoop code).
Proof.
  induction code as [value|effect cont IH]; [constructor|]. intros [Hsafe Hcont].
  cbn [liftToWithinLoop Action_rect within_ro]. split; [exact Hsafe|]. intro r. now apply IH.
Qed.
Lemma drop_ro (code : Action (WithinLoop I T V) withinLoopReturnValue unit) : within_ro code -> local_ro (dropWithinLoop code).
Proof.
  induction code as [value|effect cont IH]; [constructor|]. intros [Hsafe Hcont].
  destruct effect as [effect| |]; cbn [dropWithinLoop Action_rect local_ro].
  - split; [exact Hsafe|]. intro r. now apply IH.
  - constructor.
  - constructor.
Qed.
Lemma loop_ro count (body : nat -> Action (WithLocalVariables I T V) withLocalVariablesReturnValue LoopOutcome) :
  (forall index, local_ro (body index)) -> local_ro (loop count body).
Proof.
  intro Hbody. induction count as [|count IH]; [constructor|]. rewrite loop_S.
  apply local_bind; [apply Hbody|]. intros []; [exact IH|constructor].
Qed.
Lemma string_ro str (body : Z -> Action (WithLocalVariables I T V) withLocalVariablesReturnValue LoopOutcome) :
  (forall ch, local_ro (body ch)) -> local_ro (loopString str body).
Proof.
  intro Hbody. induction str as [|ch tail IH]; [constructor|]. cbn [loopString].
  apply local_bind; [apply Hbody|]. intros []; [exact IH|constructor].
Qed.
Lemma tape_ro (body : Z -> Action (WithLocalVariables I T V) withLocalVariablesReturnValue LoopOutcome) :
  (forall ch, local_ro (body ch)) -> local_ro (tapeEnd body).
Proof.
  intro Hbody. unfold tapeEnd. split; [constructor|]. intro remaining. apply loop_ro. intro index.
  apply local_bind; [split; [constructor|intro ch; constructor]|]. intro ch.
  lazymatch goal with |- local_ro (if ?guard then _ else _) => destruct guard; [constructor|apply Hbody] end.
Qed.
Context `{EqDecision V}.
Lemma eliminate_ro (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue unit) bs ns :
  local_ro code -> array_ro (eliminateLocalVariables bs ns code).
Proof.
  induction code as [value|effect cont IH] in bs,ns |- *; [constructor|]. intros [Hsafe Hcont].
  destruct effect; cbn [eliminateLocalVariables array_ro].
  - split; [exact Hsafe|]. intro r. now apply IH.
  - now apply IH.
  - now apply IH.
  - now apply IH.
  - now apply IH.
Qed.
End Effects.
Section Semantics.
Context {I : Type} {T : I -> Type} `{EqDecision I} (watched : I).
Lemma step_preserves (effect : WithArrays I T) (s : @Machine I T) (value : withArraysReturnValue effect) (final : @Machine I T) : safe_effect watched effect -> step effect s = Some (value,final) -> length (memory final watched) = length (memory s watched).
Proof.
  intros Hsafe Hrun. destruct effect as [effect|name slot|name slot item|name size zero].
  - destruct effect; cbn [step] in Hrun; try discriminate;
      try (injection Hrun as _ <-; reflexivity).
    destruct (stdin s); injection Hrun as _ <-; reflexivity.
  - cbn [step] in Hrun. case_decide; [injection Hrun as _ <-; reflexivity|discriminate].
  - cbn [step] in Hrun. case_decide; [|discriminate]. injection Hrun as _ <-.
    cbn [withMemory memory]. unfold modifyArray.
    destruct (decide (watched=name)) as [Hsame|Hdifferent]; [destruct Hsame; cbn; apply length_insert|reflexivity].
  - cbn [safe_effect] in Hsafe. cbn [step] in Hrun. injection Hrun as _ <-.
    cbn [withMemory memory]. now rewrite growArrays_other.
Qed.
Theorem exec_preserves {R} (code : Action (WithArrays I T) withArraysReturnValue R) s value final :
  array_ro watched code -> exec code s = Some (value,final) -> length (memory final watched) = length (memory s watched).
Proof.
  induction code as [x|effect cont IH] in s |- *.
  - intros _ Hrun. injection Hrun as _ <-. reflexivity.
  - intros [Hsafe Hcont] Hrun. cbn [exec] in Hrun.
    destruct (step effect s) as [[response middle]|] eqn:Hstep; [|discriminate]. cbn [optionBind fst snd] in Hrun.
    rewrite (IH response middle (Hcont response) Hrun). exact (step_preserves effect s response middle Hsafe Hstep).
Qed.
Theorem observed_preserves {R} (code : Action (WithArrays I T) withArraysReturnValue R) s observations value final after_observations :
  array_ro watched code -> execObserved code (s,observations) = Some (value,(final,after_observations)) -> length (memory final watched) = length (memory s watched).
Proof.
  intros Hro Hrun. apply (exec_preserves code s value final Hro).
  pose proof (execObserved_erases code (s,observations)) as Herased. rewrite Hrun in Herased. exact (eq_sym Herased).
Qed.
End Semantics.
Create HintDb array_length_frames.
Ltac ro := first
  [lazymatch goal with |- local_ro _ (Done _ _ _ _) => constructor end
  |lazymatch goal with |- within_ro _ (Done _ _ _ _) => constructor end
  |lazymatch goal with |- array_ro _ (Done _ _ _ _) => constructor end
  |lazymatch goal with |- local_ro _ (bind _ _) => apply local_bind; [ro|intro; ro] end
  |lazymatch goal with |- within_ro _ (bind _ _) => apply within_bind; [ro|intro; ro] end
  |lazymatch goal with |- array_ro _ (bind _ _) => apply array_bind; [ro|intro; ro] end
  |lazymatch goal with |- local_ro _ (liftToWithLocalVariables _) => apply local_lift; ro end
  |lazymatch goal with |- within_ro _ (liftToWithinLoop _) => apply within_lift; ro end
  |lazymatch goal with |- local_ro _ (dropWithinLoop _) => apply drop_ro; ro end
  |lazymatch goal with |- local_ro _ (loop _ _) => apply loop_ro; intro; ro end
  |lazymatch goal with |- local_ro _ (loopString _ _) => apply string_ro; intro; ro end
  |lazymatch goal with |- local_ro _ (tapeEnd _) => apply tape_ro; intro; ro end
  |lazymatch goal with |- local_ro _ (if ?guard then _ else _) => destruct guard; ro end
  |lazymatch goal with |- within_ro _ (if ?guard then _ else _) => destruct guard; ro end
  |lazymatch goal with |- local_ro _ (Dispatch _ _ _ _ _) => split; [cbn [safe_local safe_effect]; first [congruence|tauto]|intro; ro] end
  |lazymatch goal with |- within_ro _ (Dispatch _ _ _ _ _) => split; [cbn [safe_within safe_local safe_effect]; first [congruence|tauto]|intro; ro] end
  |lazymatch goal with |- array_ro _ (Dispatch _ _ _ _ _) => split; [cbn [safe_effect]; first [congruence|tauto]|intro; ro] end
  |match goal with H : forall bs ns, array_ro ?name (?proc bs ns) |- array_ro ?name (?proc ?bs ?ns) => exact (H bs ns) end
  |solve [eauto with array_length_frames]
  |contradiction
  |progress cbv beta iota zeta delta [numberLocalGet numberLocalSet booleanLocalGet booleanLocalSet
      retrieve store grow trap readChar writeChar flush shortCircuitAnd shortCircuitOr addInt subInt multInt
      andBits orBits xorBits shiftLeft shiftRight modIntUnsigned divIntUnsigned break continue]; ro].
End ArrayLengthFrame.
