From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From NativeProof Require Import ObservedLocal Observation.
From stdpp Require Import numbers list.

Module LocalObservation.
Import ObservedLocal InternalObservation.
Section Evaluation.
Context {I : Type} {T : I -> Type} `{EqDecision I} {V : Type} `{EqDecision V}.
Lemma step_no_flush (effect : WithLocalVariables I T V) f observations :
  ~ local_flush effect -> localStepObserved effect (f,observations) =
    option_map (fun response => (fst response,(snd response,observations))) (localStep effect f).
Proof.
  intro Hnf. destruct effect as [effect|name|name value|name|name value]; try reflexivity.
  cbn [localStepObserved localStep fst snd]. unfold observedStep. cbn [fst snd].
  assert (Htrace : (match effect with DoBasicEffect _ _ Flush => observations ++
    [{|flushedOutput := stdout (machine f); unreadInput := stdin (machine f)|}] | _ => observations end) = observations).
  { destruct effect as [effect|name slot|name slot value|name size zero]; try reflexivity.
    destruct effect; try reflexivity. exfalso. apply Hnf. constructor. }
  rewrite Htrace. destruct (step effect (machine f)) as [[response after]|]; reflexivity.
Qed.
Theorem local_no_flush {R} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) f observations :
  local_nf code -> execLocalObserved code (f,observations) =
    option_map (fun response => (fst response,(snd response,observations))) (execLocal code f).
Proof.
  induction code as [value|effect cont IH] in f,observations |- *; [reflexivity|].
  intros [Hnf Hcont]. cbn [execLocalObserved execLocal]. rewrite step_no_flush by exact Hnf.
  destruct (localStep effect f) as [[response after]|]; cbn [option_map optionBind fst snd]; [apply IH,Hcont|reflexivity].
Qed.
Theorem plain_observed {R} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) f observations value final :
  local_nf code -> execLocal code f = Some (value,final) -> execLocalObserved code (f,observations) = Some (value,(final,observations)).
Proof. intros Hnf Hrun. rewrite local_no_flush, Hrun by exact Hnf. reflexivity. Qed.
End Evaluation.
End LocalObservation.
