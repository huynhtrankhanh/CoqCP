From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From stdpp Require Import numbers list.

(* Pointwise equality of local parameters suffices for equality of observed
   execution. The proof does not assume function extensionality. *)
Module LocalParameters.
Section Evaluation.
Context {I : Type} {T : I -> Type} `{EqDecision I} {V : Type} `{EqDecision V}.
Theorem observed_extensional
  (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue unit)
  bs ns bs' ns' s observations :
  (forall v, bs v = bs' v) -> (forall v, ns v = ns' v) ->
  execObserved (eliminateLocalVariables bs ns code) (s,observations) =
  execObserved (eliminateLocalVariables bs' ns' code) (s,observations).
Proof.
  induction code as [value|effect cont IH] in bs,ns,bs',ns',s,observations |- *; intros Hbool Hnum; [reflexivity|].
  destruct effect as [effect|name|name value|name|name value]; cbn [eliminateLocalVariables Action_rect execObserved].
  - destruct (observedStep effect (s,observations)) as [[response [after trace]]|]; cbn [optionBind fst snd]; [now apply IH|reflexivity].
  - rewrite Hbool. now apply IH.
  - apply IH; [|exact Hnum]. intro v. unfold update. case_decide; auto.
  - rewrite Hnum. now apply IH.
  - apply IH; [exact Hbool|]. intro v. unfold update. case_decide; auto.
Qed.
End Evaluation.
End LocalParameters.
