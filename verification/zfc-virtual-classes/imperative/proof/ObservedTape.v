From CoqCP Require Import Options Imperative Execution InteractiveExecution TapeEnd.
From NativeProof Require Import ObservedLocal.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ObservedTape.
Import ObservedLocal.
Section Evaluation.
Context {I : Type} {T : I -> Type} `{EqDecision I} {V : Type} `{EqDecision V}.
Lemma step_erases (effect : WithLocalVariables I T V) f observations :
  option_map (fun r => (fst r,fst (snd r))) (localStepObserved effect (f,observations)) = localStep effect f.
Proof.
  destruct effect as [effect|name|name value|name|name value]; [|reflexivity..].
  cbn [localStepObserved localStep fst snd]. unfold observedStep. cbn [fst snd].
  destruct (step effect (machine f)) as [[response after]|]; cbn [optionBind option_map fst snd]; reflexivity.
Qed.
Theorem local_erases {R} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) f observations :
  option_map (fun r => (fst r,fst (snd r))) (execLocalObserved code (f,observations)) = execLocal code f.
Proof.
  induction code as [value|effect cont IH] in f, observations |- *; [reflexivity|].
  cbn [execLocalObserved execLocal]. pose proof (step_erases effect f observations) as Hstep.
  destruct (localStepObserved effect (f,observations)) as [[response [after trace]]|] eqn:Hobserved.
  - cbn [option_map fst snd] in Hstep. rewrite <-Hstep. cbn [optionBind fst snd]. apply IH.
  - cbn [option_map] in Hstep. rewrite <-Hstep. reflexivity.
Qed.
Theorem input_length {R} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) f observations value final trace :
  execLocalObserved code (f,observations) = Some (value,(final,trace)) ->
  (length (stdin (machine final)) <= length (stdin (machine f)))%nat.
Proof.
  intro Hrun. pose proof (local_erases code f observations) as Herase. rewrite Hrun in Herase.
  cbn [option_map fst snd] in Herase. eapply execLocal_input_length. symmetry. exact Herase.
Qed.
Definition Body := Z -> Action (WithLocalVariables I T V) withLocalVariablesReturnValue LoopOutcome.
Inductive tape_execution (body : Body) : State -> State -> Prop :=
| eof f observations : stdin (machine f) = [] -> tape_execution body (f,observations) (f,observations)
| sentinel f observations tail : stdin (machine f) = (2^64-1) :: tail ->
    tape_execution body (f,observations) (setMachine f (withInput (machine f) tail),observations)
| stop f observations ch tail after trace :
    stdin (machine f) = ch :: tail -> ch <> 2^64-1 ->
    execLocalObserved (body ch) (setMachine f (withInput (machine f) tail),observations) = Some (Stop,(after,trace)) ->
    tape_execution body (f,observations) (after,trace)
| next f observations ch tail after trace final :
    stdin (machine f) = ch :: tail -> ch <> 2^64-1 ->
    execLocalObserved (body ch) (setMachine f (withInput (machine f) tail),observations) = Some (KeepGoing,(after,trace)) ->
    tape_execution body (after,trace) final -> tape_execution body (f,observations) final.
Lemma loop_step (body : Body) fuel (f : @Frame I T V) observations :
  execLocalObserved (loop (S fuel) (tape_body body)) (f,observations) =
  match stdin (machine f) with
  | [] => Some (tt,(f,observations))
  | ch :: tail =>
      let start := setMachine f (withInput (machine f) tail) in
      if Z.eq_dec ch (2^64-1) then Some (tt,(start,observations)) else
      optionBind (execLocalObserved (body ch) (start,observations)) (fun r =>
        match fst r with
        | Stop => Some (tt,snd r)
        | KeepGoing => execLocalObserved (loop fuel (tape_body body)) (snd r)
        end)
  end.
Proof.
  destruct f as [[values input output] bs ns]. destruct input as [|ch tail].
  all: rewrite loop_S, local_bind; unfold tape_body; rewrite local_bind.
  all: cbn [readChar execLocalObserved localStepObserved observedStep step optionBind machine nums bools setMachine withInput stdin fst snd].
  - reflexivity.
  - destruct (Z.eq_dec ch (2^64-1)); [reflexivity|].
    lazymatch goal with |- context [execLocalObserved (body ch) ?start] =>
      destruct (execLocalObserved (body ch) start) as [[outcome after]|]; [destruct outcome|]; reflexivity
    end.
Qed.
Theorem loop_complete body initial final : tape_execution body initial final -> forall fuel,
  (length (stdin (machine (fst initial))) < fuel)%nat ->
  execLocalObserved (loop fuel (tape_body body)) initial = Some (tt,final).
Proof.
  intro Hexec. induction Hexec as [f observations Hin|f observations tail Hin|
    f observations ch tail after trace Hin Hch Hbody|
    f observations ch tail after trace final Hin Hch Hbody Hnext IH];
    intros [|fuel] Hfuel; try (cbn [fst] in Hfuel; lia); rewrite loop_step, Hin; cbn zeta.
  - reflexivity.
  - destruct (Z.eq_dec (2^64-1) (2^64-1)); [reflexivity|congruence].
  - destruct (Z.eq_dec ch (2^64-1)); [congruence|]. now rewrite Hbody.
  - destruct (Z.eq_dec ch (2^64-1)); [congruence|]. rewrite Hbody. cbn [optionBind fst snd]. apply IH.
    pose proof (input_length _ _ _ _ _ _ Hbody) as Hlength.
    cbn [setMachine machine withInput stdin] in Hlength. cbn [fst] in Hfuel. rewrite Hin in Hfuel. cbn [length] in Hfuel. cbn [fst]. lia.
Qed.
Theorem loop_sound (body : Body) fuel (f : @Frame I T V) observations final :
  (length (stdin (machine f)) < fuel)%nat ->
  execLocalObserved (loop fuel (tape_body body)) (f,observations) = Some (tt,final) ->
  tape_execution body (f,observations) final.
Proof.
  induction fuel as [|fuel IH] in f, observations, final |- *; [lia|].
  intros Hfuel. rewrite loop_step. destruct (stdin (machine f)) as [|ch tail] eqn:Hin.
  - intro Hrun. injection Hrun as <-. now apply eof.
  - destruct (Z.eq_dec ch (2^64-1)) as [->|Hch].
    + intro Hrun. injection Hrun as <-. now apply sentinel.
    + cbn zeta. lazymatch goal with |- context [execLocalObserved (body ch) ?start] =>
        destruct (execLocalObserved (body ch) start) as [[outcome [after trace]]|] eqn:Hbody end.
      2: discriminate.
      cbn [optionBind fst snd]. destruct outcome.
      * intro Hrun. eapply next; [exact Hin|exact Hch|exact Hbody|]. apply IH; [|exact Hrun].
        pose proof (input_length _ _ _ _ _ _ Hbody) as Hlength.
        cbn [setMachine machine withInput stdin] in Hlength. cbn [length] in Hfuel. lia.
      * intro Hrun. injection Hrun as <-. eapply stop; [exact Hin|exact Hch|exact Hbody].
Qed.
Theorem tapeEnd_execution (body : Body) (f : @Frame I T V) observations final :
  execLocalObserved (tapeEnd body) (f,observations) = Some (tt,final) <-> tape_execution body (f,observations) final.
Proof.
  change (execLocalObserved (loop (S (length (stdin (machine f)))) (tape_body body)) (f,observations) = Some (tt,final) <-> tape_execution body (f,observations) final).
  split; [apply loop_sound; lia|intro Hexec; apply loop_complete; [exact Hexec|cbn [fst]; lia]].
Qed.
End Evaluation.
End ObservedTape.
