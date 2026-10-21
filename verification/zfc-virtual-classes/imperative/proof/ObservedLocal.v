From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From stdpp Require Import numbers list.

Module ObservedLocal.
Section Evaluation.
Context {I : Type} {T : I -> Type} `{EqDecision I} {V : Type} `{EqDecision V}.
Definition State := (@Execution.Frame I T V * list FlushSnapshot)%type.
Definition localStepObserved (effect : WithLocalVariables I T V) (state : State) :
  option (withLocalVariablesReturnValue effect * State) :=
  match effect with
  | DoWithArrays _ _ _ array_effect =>
      optionBind (observedStep array_effect (machine (fst state),snd state))
        (fun r => Some (fst r,(setMachine (fst state) (fst (snd r)),snd (snd r))))
  | BooleanLocalGet _ _ _ name => Some (bools (fst state) name,state)
  | BooleanLocalSet _ _ _ name value => Some (tt,(setBool (fst state) name value,snd state))
  | NumberLocalGet _ _ _ name => Some (nums (fst state) name,state)
  | NumberLocalSet _ _ _ name value => Some (tt,(setNum (fst state) name value,snd state))
  end.
Fixpoint execLocalObserved {R} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue R)
  (state : State) : option (R * State) :=
  match code with
  | Done _ _ _ value => Some (value,state)
  | Dispatch _ _ _ effect next => optionBind (localStepObserved effect state)
      (fun r => execLocalObserved (next (fst r)) (snd r))
  end.
Lemma local_bind {A B} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue A) next state :
  execLocalObserved (R := B) (code >>= next) state =
  optionBind (execLocalObserved code state) (fun r => execLocalObserved (next (fst r)) (snd r)).
Proof.
  induction code as [value|effect cont IH] in state |- *; [reflexivity|].
  cbn [bind execLocalObserved]. destruct (localStepObserved effect state) as [[value after]|]; cbn [optionBind fst snd]; [apply IH|reflexivity].
Qed.
Theorem eliminate_correct (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue unit) bs ns s observations :
  execObserved (eliminateLocalVariables bs ns code) (s,observations) =
  optionBind (execLocalObserved code ({|machine := s; bools := bs; nums := ns|},observations))
    (fun r => Some (fst r,(machine (fst (snd r)),snd (snd r)))).
Proof.
  induction code as [value|effect cont IH] in bs, ns, s, observations |- *; [reflexivity|].
  destruct effect as [effect|name|name value|name|name value].
  - cbn [eliminateLocalVariables Action_rect execObserved execLocalObserved localStepObserved fst snd machine].
    destruct (observedStep effect (s,observations)) as [[value [after trace]]|]; cbn [optionBind fst snd setMachine machine bools nums]; [apply IH|reflexivity].
  - cbn [eliminateLocalVariables Action_rect execLocalObserved localStepObserved localStep optionBind fst snd bools]. apply IH.
  - cbn [eliminateLocalVariables Action_rect execLocalObserved localStepObserved localStep optionBind fst snd setBool machine bools nums]. apply IH.
  - cbn [eliminateLocalVariables Action_rect execLocalObserved localStepObserved localStep optionBind fst snd nums]. apply IH.
  - cbn [eliminateLocalVariables Action_rect execLocalObserved localStepObserved localStep optionBind fst snd setNum machine bools nums]. apply IH.
Qed.
Lemma lift_correct {R} (code : Action (WithArrays I T) withArraysReturnValue R) f observations :
  execLocalObserved (liftToWithLocalVariables code) (f,observations) =
  optionBind (execObserved code (machine f,observations))
    (fun r => Some (fst r,(setMachine f (fst (snd r)),snd (snd r)))).
Proof.
  induction code as [value|effect cont IH] in f, observations |- *.
  - cbn [liftToWithLocalVariables Action_rect execLocalObserved execObserved optionBind fst snd]. destruct f. reflexivity.
  - cbn [liftToWithLocalVariables Action_rect execLocalObserved execObserved localStepObserved fst snd].
    destruct (observedStep effect (machine f,observations)) as [[value [after trace]]|]; cbn [optionBind fst snd]; [|reflexivity].
    rewrite IH. cbn [setMachine machine].
    destruct (execObserved (cont value) (after,trace)) as [[result [final observations']]|]; [destruct f|]; reflexivity.
Qed.

Lemma drop_lift {R}
  (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) next state :
  execLocalObserved (dropWithinLoop (liftToWithinLoop code >>= next)) state =
  optionBind (execLocalObserved code state) (fun r => execLocalObserved (dropWithinLoop (next (fst r))) (snd r)).
Proof.
  induction code as [value|effect cont IH] in state |- *; [reflexivity|].
  cbn [liftToWithinLoop Action_rect bind dropWithinLoop execLocalObserved].
  destruct (localStepObserved effect state) as [[value after]|]; cbn [optionBind fst snd]; [apply IH|reflexivity].
Qed.
Lemma drop_assoc {A B}
  (code : Action (WithinLoop I T V) withinLoopReturnValue A)
  (next : A -> Action (WithinLoop I T V) withinLoopReturnValue B)
  (last : B -> Action (WithinLoop I T V) withinLoopReturnValue unit) state :
  execLocalObserved (dropWithinLoop ((code >>= next) >>= last)) state =
  execLocalObserved (dropWithinLoop (code >>= fun v => next v >>= last)) state.
Proof.
  induction code as [value|effect cont IH] in state |- *; [reflexivity|].
  destruct effect as [effect| |]; cbn [bind dropWithinLoop Action_rect execLocalObserved]; try reflexivity.
  destruct (localStepObserved effect state) as [[value after]|]; cbn [optionBind fst snd]; [apply IH|reflexivity].
Qed.
End Evaluation.

End ObservedLocal.
