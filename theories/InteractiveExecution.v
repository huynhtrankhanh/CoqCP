From CoqCP Require Import Options Imperative Execution.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality.

(* Observe the exact byte streams at every explicit flush.  This distinguishes
   programs with identical final stdout but different interactive behaviour. *)
Record FlushSnapshot := { flushedOutput : list Z; unreadInput : list Z }.

Section ObservedExecution.
Context {I : Type} {T : I -> Type} `{EqDecision I}.
Definition ObservedMachine := (@Machine I T * list FlushSnapshot)%type.
Definition observedStep (effect : WithArrays I T) (state : ObservedMachine) :
  option (withArraysReturnValue effect * ObservedMachine) :=
  optionBind (step effect (fst state)) (fun response =>
    let observations := match effect with
      | DoBasicEffect _ _ Flush => snd state ++
          [{| flushedOutput := stdout (fst state); unreadInput := stdin (fst state) |}]
      | _ => snd state end in
    Some (fst response, (snd response, observations))).
Fixpoint execObserved {R} (code : Action (WithArrays I T) withArraysReturnValue R)
  (state : ObservedMachine) : option (R * ObservedMachine) :=
  match code with
  | Done _ _ _ value => Some (value, state)
  | Dispatch _ _ _ effect next => optionBind (observedStep effect state)
      (fun response => execObserved (next (fst response)) (snd response))
  end.
Lemma execObserved_bind {A B} (code : Action (WithArrays I T) withArraysReturnValue A)
  (next : A -> Action (WithArrays I T) withArraysReturnValue B) state :
  execObserved (code >>= next) state =
  optionBind (execObserved code state) (fun response => execObserved (next (fst response)) (snd response)).
Proof.
  induction code as [value | e cont IH] in state |- *; simpl; [reflexivity |].
  destruct (observedStep e state) as [[x state'] |]; simpl; [apply IH | reflexivity].
Qed.
Lemma execObserved_erases {R} (code : Action (WithArrays I T) withArraysReturnValue R) state :
  option_map (fun response => (fst response, fst (snd response))) (execObserved code state) =
  exec code (fst state).
Proof.
  induction code as [value | e cont IH] in state |- *; [reflexivity |].
  cbn [execObserved exec]. unfold observedStep.
  destruct (step e (fst state)) as [[x s] |]; [| reflexivity].
  cbn [optionBind fst snd]. apply IH.
Qed.

Definition isFlush (effect : WithArrays I T) : Prop :=
  match effect with DoBasicEffect _ _ Flush => True | _ => False end.
Fixpoint NoFlush {R} (code : Action (WithArrays I T) withArraysReturnValue R) : Prop :=
  match code with
  | Done _ _ _ _ => True
  | Dispatch _ _ _ effect next => ~ isFlush effect /\ forall response, NoFlush (next response)
  end.
Lemma NoFlush_bind {A B} (code : Action (WithArrays I T) withArraysReturnValue A)
  (next : A -> Action (WithArrays I T) withArraysReturnValue B)
  (hc : NoFlush code) (hn : forall value, NoFlush (next value)) : NoFlush (code >>= next).
Proof.
  induction code as [value | e cont IH]; [apply hn |].
  destruct hc as [he hcont]. cbn [bind NoFlush]. split; [exact he |].
  intro response. apply IH. apply hcont.
Qed.
Lemma NoFlush_arrayLoop count (body : nat -> Action (WithArrays I T) withArraysReturnValue unit)
  (h : forall index, NoFlush (body index)) : NoFlush (arrayLoop count body).
Proof.
  induction count as [| count IH]; [constructor |].
  cbn [arrayLoop]. apply NoFlush_bind; [apply h | intros []; exact IH].
Qed.
Lemma execObserved_NoFlush {R} (code : Action (WithArrays I T) withArraysReturnValue R)
  s observations (h : NoFlush code) :
  execObserved code (s, observations) =
  option_map (fun response => (fst response, (snd response, observations))) (exec code s).
Proof.
  induction code as [value | e cont IH] in s, observations, h |- *; [reflexivity |].
  destruct h as [he hc]. cbn [execObserved exec fst snd]. unfold observedStep. cbn [fst snd].
  destruct (step e s) as [[x s'] |]; [| reflexivity].
  assert (unchanged : (match e with DoBasicEffect _ _ Flush => observations ++
    [{| flushedOutput := stdout s; unreadInput := stdin s |}] | _ => observations end) = observations).
  { destruct e as [effect | name index | name index value | name size zero]; try reflexivity.
    destruct effect; try reflexivity. exfalso. apply he. constructor. }
  rewrite unchanged. cbn [optionBind fst snd]. apply IH. apply hc.
Qed.

(* Successful termination, complete output, full input consumption, and exact
   flush placement are obligations, rather than implications from success. *)
Definition endToEnd (program : Action (WithArrays I T) withArraysReturnValue unit)
  initial output observations : Prop :=
  exists final, execObserved program (initial, []) = Some (tt, (final, observations)) /\
    stdout final = output /\ stdin final = [].
End ObservedExecution.

Lemma observed_plain {I T} `{EqDecision I} {R}
  (code : Action (WithArrays I T) withArraysReturnValue R) s observations result final
  (hf : NoFlush code) (he : exec code s = Some (result, final)) :
  execObserved code (s, observations) = Some (result, (final, observations)).
Proof. rewrite execObserved_NoFlush by exact hf. rewrite he. reflexivity. Qed.

Lemma endToEnd_rejects_failure {I T} `{EqDecision I}
  (program : Action (WithArrays I T) withArraysReturnValue unit) initial output observations
  (h : execObserved program (initial, []) = None) : ~ endToEnd program initial output observations.
Proof. intros [final [executed _]]. rewrite h in executed. discriminate. Qed.
Lemma endToEnd_requires_flushes {I T} `{EqDecision I}
  (program : Action (WithArrays I T) withArraysReturnValue unit) initial output observations
  (h : NoFlush program) (hn : observations <> []) : ~ endToEnd program initial output observations.
Proof.
  intros [final [executed _]]. rewrite execObserved_NoFlush in executed by exact h.
  destruct (exec program initial) as [[value s] |]; cbn [option_map fst snd] in executed; [| discriminate].
  injection executed as _ _ same. apply hn. symmetry. exact same.
Qed.
Lemma endToEnd_erases {I T} `{EqDecision I}
  (program : Action (WithArrays I T) withArraysReturnValue unit) initial output observations
  (h : endToEnd program initial output observations) :
  exists final, exec program initial = Some (tt, final) /\ stdout final = output /\ stdin final = [].
Proof.
  destruct h as [final [executed result]]. exists final. split; [| exact result].
  pose proof (execObserved_erases program (initial, [])) as erased.
  rewrite executed in erased. cbn [option_map fst snd] in erased. symmetry. exact erased.
Qed.
