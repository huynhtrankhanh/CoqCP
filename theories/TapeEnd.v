From CoqCP Require Import Options Imperative Execution.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Section TapeExecution.
Context {I : Type} {T : I -> Type} `{EqDecision I}.

Lemma step_input_length (effect : WithArrays I T) (s : @Machine I T) value final :
  step effect s = Some (value,final) ->
  (length (stdin final) <= length (stdin s))%nat.
Proof.
  destruct effect as [effect |name index |name index value' |name size zero];
    cbn [step]; try (case_decide; [|discriminate]).
  - destruct effect; cbn; try discriminate;
      try (intro Hrun; injection Hrun as _ <-; reflexivity).
    destruct (stdin s) as [|ch tail] eqn:Hin; intro Hrun; injection Hrun as _ <-.
    + now rewrite Hin.
    + cbn [withInput stdin]. try rewrite Hin. cbn. lia.
  - intro Hrun. injection Hrun as _ <-. reflexivity.
  - intro Hrun. injection Hrun as _ <-. reflexivity.
  - intro Hrun. injection Hrun as _ <-. reflexivity.
Qed.

Context {V : Type} `{EqDecision V}.
Lemma localStep_input_length (effect : WithLocalVariables I T V) (f : @Frame I T V) value final :
  localStep effect f = Some (value,final) ->
  (length (stdin (machine final)) <= length (stdin (machine f)))%nat.
Proof.
  destruct effect as [effect |name |name item |name |name item]; cbn [localStep].
  - destruct (step effect (machine f)) as [[response after] |] eqn:Hstep; [|discriminate].
    cbn [optionBind]. intro Hrun. injection Hrun as _ <-.
    cbn [setMachine machine]. now apply step_input_length in Hstep.
  - intro Hrun. injection Hrun as _ <-. reflexivity.
  - intro Hrun. injection Hrun as _ <-. reflexivity.
  - intro Hrun. injection Hrun as _ <-. reflexivity.
  - intro Hrun. injection Hrun as _ <-. reflexivity.
Qed.

Theorem execLocal_input_length {R}
  (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) f value final :
  execLocal code f = Some (value,final) ->
  (length (stdin (machine final)) <= length (stdin (machine f)))%nat.
Proof.
  induction code as [value' |effect next IH] in f |- *; cbn [execLocal].
  - intro Hrun. injection Hrun as _ <-. reflexivity.
  - destruct (localStep effect f) as [[response after] |] eqn:Hstep; [|discriminate].
    cbn [optionBind]. intro Hrun.
    pose proof (IH response after Hrun) as Htail.
    pose proof (localStep_input_length effect f response after Hstep) as Hhead. lia.
Qed.

Definition tape_body
  (body : Z -> Action (WithLocalVariables I T V) withLocalVariablesReturnValue LoopOutcome)
  (_ : nat) := readChar I T V >>= fun ch =>
    if Z.eq_dec ch (2^64 - 1) then Done _ _ _ Stop else body ch.

(* This relation has no numeric fuel. Each continuation starts from the actual
   input left by the body, allowing arbitrary additional reads and nested loops. *)
Inductive tape_execution
  (body : Z -> Action (WithLocalVariables I T V) withLocalVariablesReturnValue LoopOutcome)
  : @Frame I T V -> @Frame I T V -> Prop :=
| tape_eof f : stdin (machine f) = [] -> tape_execution body f f
| tape_sentinel f tail : stdin (machine f) = (2^64 - 1) :: tail ->
    tape_execution body f (setMachine f (withInput (machine f) tail))
| tape_stop f ch tail after :
    stdin (machine f) = ch :: tail -> ch <> 2^64 - 1 ->
    execLocal (body ch) (setMachine f (withInput (machine f) tail)) = Some (Stop,after) ->
    tape_execution body f after
| tape_next f ch tail after final :
    stdin (machine f) = ch :: tail -> ch <> 2^64 - 1 ->
    execLocal (body ch) (setMachine f (withInput (machine f) tail)) = Some (KeepGoing,after) ->
    tape_execution body after final -> tape_execution body f final.

Definition byte_input (f : @Frame I T V) := Forall (fun x => 0 <= x < 256) (stdin (machine f)).

Lemma exec_tape_loop_S body fuel f :
  execLocal (loop (S fuel) (tape_body body)) f =
  match stdin (machine f) with
  | [] => Some (tt,f)
  | ch :: tail =>
      let start := setMachine f (withInput (machine f) tail) in
      if Z.eq_dec ch (2^64 - 1) then Some (tt,start) else
      optionBind (execLocal (body ch) start) (fun response =>
        match fst response with
        | Stop => Some (tt,snd response)
        | KeepGoing => execLocal (loop fuel (tape_body body)) (snd response)
        end)
  end.
Proof.
  destruct f as [[values input output] bs ns]. destruct input as [|ch tail].
  all: rewrite loop_S, execLocal_bind; unfold tape_body; rewrite execLocal_bind.
  all: cbn [readChar execLocal localStep step optionBind machine nums bools
    setMachine withInput stdin fst snd].
  - reflexivity.
  - destruct (Z.eq_dec ch (2^64 - 1)); cbn [execLocal optionBind fst snd]; [reflexivity |].
    lazymatch goal with |- context [execLocal (body ch) ?start] =>
      destruct (execLocal (body ch) start) as [[outcome after] |];
        [destruct outcome |]; reflexivity
    end.
Qed.

Theorem tape_loop_sound body fuel f final :
  (length (stdin (machine f)) < fuel)%nat ->
  execLocal (loop fuel (tape_body body)) f = Some (tt,final) ->
  tape_execution body f final.
Proof.
  induction fuel as [|fuel IH] in f, final |- *; [lia |].
  intros Hfuel. rewrite exec_tape_loop_S.
  destruct (stdin (machine f)) as [|ch tail] eqn:Hin.
  - intro Hrun. injection Hrun as <-. now apply tape_eof.
  - destruct (Z.eq_dec ch (2^64 - 1)) as [-> |Hch].
    + intro Hrun. injection Hrun as <-. now apply tape_sentinel.
    + cbn zeta.
      lazymatch goal with |- context [execLocal (body ch) ?start] =>
        destruct (execLocal (body ch) start) as [[outcome after] |] eqn:Hbody
      end.
      all: cbn [optionBind fst snd].
      2: { intro Hrun. discriminate Hrun. }
      destruct outcome.
      * intro Hrun. eapply tape_next; [exact Hin |exact Hch |exact Hbody |].
        apply (IH after final); [|exact Hrun].
        pose proof (execLocal_input_length _ _ _ _ Hbody) as Hlength.
        cbn [setMachine machine withInput stdin] in Hlength. cbn in Hfuel. lia.
      * intro Hrun. injection Hrun as <-.
        eapply tape_stop; [exact Hin |exact Hch |exact Hbody].
Qed.

Theorem tape_loop_complete body f final :
  tape_execution body f final -> forall fuel,
    (length (stdin (machine f)) < fuel)%nat ->
    execLocal (loop fuel (tape_body body)) f = Some (tt,final).
Proof.
  intro Hexec. induction Hexec as
    [f Hin |f tail Hin |f ch tail after Hin Hch Hbody
    |f ch tail after final Hin Hch Hbody Hnext IH];
    intros [|fuel] Hfuel; try lia; rewrite exec_tape_loop_S, Hin; cbn zeta.
  - reflexivity.
  - destruct (Z.eq_dec (2^64 - 1) (2^64 - 1)); [reflexivity |congruence].
  - destruct (Z.eq_dec ch (2^64 - 1)); [congruence |].
    now rewrite Hbody.
  - destruct (Z.eq_dec ch (2^64 - 1)); [congruence |].
    rewrite Hbody. cbn [optionBind fst snd]. apply IH.
    pose proof (execLocal_input_length _ _ _ _ Hbody) as Hlength.
    cbn [setMachine machine withInput stdin] in Hlength. rewrite Hin in Hfuel. cbn in Hfuel. lia.
Qed.

Theorem tapeEnd_execution body f final :
  execLocal (tapeEnd body) f = Some (tt,final) <-> tape_execution body f final.
Proof.
  unfold tapeEnd. cbn [execLocal localStep step optionBind fst snd].
  change (execLocal (loop (S (length (stdin (machine f)))) (tape_body body)) f =
    Some (tt,final) <-> tape_execution body f final).
  split.
  - apply tape_loop_sound. lia.
  - intro Hrun. apply (tape_loop_complete body f final Hrun). lia.
Qed.

End TapeExecution.
