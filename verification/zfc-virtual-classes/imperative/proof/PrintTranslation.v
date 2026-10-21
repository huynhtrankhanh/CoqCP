From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import PrintingFrame ObservedLocal.
From stdpp Require Import numbers list.

Module PrintTranslation.
Section LocalTranslation.
Context {V : Type}.
Definition local_translate {R}
  (code : Action (WithLocalVariables arrayIndex0 (arrayType _ environment0) V) withLocalVariablesReturnValue R) :
  Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) V) withLocalVariablesReturnValue R.
Proof.
  induction code as [value|effect cont IH].
  - exact (Done _ _ _ value).
  - destruct effect as [effect|name|name value|name|name value].
    + destruct effect as [effect|name slot|name slot value|name size zero].
      * exact (Dispatch _ _ _ (DoWithArrays arrayIndex1 (arrayType _ environment1) V (DoBasicEffect arrayIndex1 (arrayType _ environment1) effect)) IH).
      * destruct name. exact (Dispatch _ _ _ (DoWithArrays arrayIndex1 (arrayType _ environment1) V (Retrieve _ _ arraydef_0__printBuffer slot)) IH).
      * destruct name. exact (Dispatch _ _ _ (DoWithArrays arrayIndex1 (arrayType _ environment1) V (Store _ _ arraydef_0__printBuffer slot value)) IH).
      * destruct name. exact (Dispatch _ _ _ (DoWithArrays arrayIndex1 (arrayType _ environment1) V (Grow _ _ arraydef_0__printBuffer size zero)) IH).
    + exact (Dispatch _ _ _ (BooleanLocalGet arrayIndex1 (arrayType _ environment1) V name) IH).
    + exact (Dispatch _ _ _ (BooleanLocalSet arrayIndex1 (arrayType _ environment1) V name value) IH).
    + exact (Dispatch _ _ _ (NumberLocalGet arrayIndex1 (arrayType _ environment1) V name) IH).
    + exact (Dispatch _ _ _ (NumberLocalSet arrayIndex1 (arrayType _ environment1) V name value) IH).
Defined.
Context `{EqDecision V}.
Theorem eliminate_commutes
  (code : Action (WithLocalVariables arrayIndex0 (arrayType _ environment0) V) withLocalVariablesReturnValue unit)
  bs ns s observations :
  execObserved (PrintingFrame.translate_print (eliminateLocalVariables bs ns code)) (s,observations) =
  execObserved (eliminateLocalVariables bs ns (local_translate code)) (s,observations).
Proof.
  induction code as [value|effect cont IH] in bs, ns, s, observations |- *; [reflexivity|].
  destruct effect as [effect|name|name value|name|name value].
  - destruct effect as [effect|name slot|name slot value|name size zero]; [destruct effect|destruct name..].
    all: cbn [local_translate eliminateLocalVariables Action_rect PrintingFrame.translate_print translateArrays
      withArraysReturnValueDoBasicEffectArrayType withArraysReturnValue withLocalVariablesReturnValue eq_rect eq_rect_r execObserved].
    all: lazymatch goal with |- context [observedStep ?effect ?state] =>
      destruct (observedStep effect state) as [[response [after trace]]|]; cbn [optionBind fst snd]; [apply IH|reflexivity]
    end.
  - cbn [local_translate eliminateLocalVariables Action_rect]. apply IH.
  - cbn [local_translate eliminateLocalVariables Action_rect]. apply IH.
  - cbn [local_translate eliminateLocalVariables Action_rect]. apply IH.
  - cbn [local_translate eliminateLocalVariables Action_rect]. apply IH.
Qed.

Lemma local_bind_correct {A B}
  (code : Action (WithLocalVariables arrayIndex0 (arrayType _ environment0) V) withLocalVariablesReturnValue A)
  (next : A -> Action (WithLocalVariables arrayIndex0 (arrayType _ environment0) V) withLocalVariablesReturnValue B) state :
  ObservedLocal.execLocalObserved (local_translate (code >>= next)) state =
  optionBind (ObservedLocal.execLocalObserved (local_translate code) state)
    (fun r => ObservedLocal.execLocalObserved (local_translate (next (fst r))) (snd r)).
Proof.
  induction code as [value|effect cont IH] in state |- *; [reflexivity|].
  destruct effect as [effect|name|name value|name|name value].
  - destruct effect as [effect|name slot|name slot value|name size zero]; [|destruct name..].
    all: cbn [bind local_translate Action_rect ObservedLocal.execLocalObserved].
    all: lazymatch goal with |- context [ObservedLocal.localStepObserved ?effect ?state] =>
      destruct (ObservedLocal.localStepObserved effect state) as [[response after]|]; cbn [optionBind fst snd]; [apply IH|reflexivity]
    end.
  - cbn [bind local_translate Action_rect ObservedLocal.execLocalObserved].
    destruct (ObservedLocal.localStepObserved (BooleanLocalGet arrayIndex1 (arrayType _ environment1) V name) state) as [[response after]|]; cbn [optionBind fst snd]; [apply IH|reflexivity].
  - cbn [bind local_translate Action_rect ObservedLocal.execLocalObserved].
    destruct (ObservedLocal.localStepObserved (BooleanLocalSet arrayIndex1 (arrayType _ environment1) V name value) state) as [[response after]|]; cbn [optionBind fst snd]; [apply IH|reflexivity].
  - cbn [bind local_translate Action_rect ObservedLocal.execLocalObserved].
    destruct (ObservedLocal.localStepObserved (NumberLocalGet arrayIndex1 (arrayType _ environment1) V name) state) as [[response after]|]; cbn [optionBind fst snd]; [apply IH|reflexivity].
  - cbn [bind local_translate Action_rect ObservedLocal.execLocalObserved].
    destruct (ObservedLocal.localStepObserved (NumberLocalSet arrayIndex1 (arrayType _ environment1) V name value) state) as [[response after]|]; cbn [optionBind fst snd]; [apply IH|reflexivity].
Qed.
Lemma local_loop_correct fuel body state :
  ObservedLocal.execLocalObserved (local_translate (loop fuel body)) state =
  ObservedLocal.execLocalObserved (loop fuel (fun remaining => local_translate (body remaining))) state.
Proof.
  induction fuel as [|fuel IH] in state |- *; [reflexivity|].
  rewrite !loop_S, local_bind_correct, ObservedLocal.local_bind.
  destruct (ObservedLocal.execLocalObserved (local_translate (body fuel)) state) as [[outcome after]|]; [destruct outcome|]; cbn [optionBind fst snd]; try reflexivity.
  apply IH.
Qed.
End LocalTranslation.

End PrintTranslation.
