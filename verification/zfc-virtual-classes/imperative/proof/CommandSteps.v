From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit.
From stdpp Require Import numbers list.

(* Proof-producing symbolic steps for the command procedure's local environment.
   The caller supplies the metadata bounds proof; all generated equalities are
   checked by Rocq. Explicit result types keep primitive setters nondependent. *)
Module CommandSteps.
Import IndexExecution SipHashExecution ObservedLocal CommandQuitExecution.
Ltac action_head term := lazymatch term with ?head ?arg => action_head head | _ => term end.
Ltac primitive bound :=
  progress (match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state] =>
    lazymatch state with (?frame,?trace) =>
    let expression := constr:(@execLocalObserved I T EI V EV R code state) in
    let head := action_head code in
    first [constr_eq head (@Done) |constr_eq head (@bind) |constr_eq head (@numberLocalGet)
      |constr_eq head (@numberLocalSet) |constr_eq head (@retrieve) |constr_eq head (@store)
      |constr_eq head (@liftToWithLocalVariables) |constr_eq head (@shortCircuitAnd) |constr_eq head (@shortCircuitOr)
      |constr_eq head (@writeChar) |constr_eq head (@flush)];
    lazymatch head with
    | @Done => lazymatch code with @Done ?E ?F ?A ?value => change expression with (Some (value,state)) end
    | @bind => lazymatch code with bind ?first ?next =>
        let Hbind := fresh "Hbind" in
        assert (Hbind : expression = optionBind (execLocalObserved first state)
          (fun response => execLocalObserved (R := R) (next (fst response)) (snd response))) by
          (exact (local_bind first next state)); rewrite Hbind; clear Hbind end
    | @numberLocalGet => lazymatch code with numberLocalGet _ _ _ ?name =>
        change expression with (Some (nums frame name,state)) end
    | @numberLocalSet => lazymatch code with numberLocalSet _ _ _ ?name ?value =>
        change expression with (Some (tt,(setNum frame name value,trace))) end
    | @retrieve => lazymatch code with retrieve _ _ _ arraydef_0__meta ?slot =>
        let Hstep := fresh "Hstep" in
        assert (Hstep : expression = Some (meta_value (machine frame) (Z.to_nat slot),state)) by
          (exact (local_read_meta frame slot trace ltac:(bound frame slot)));
        rewrite Hstep; clear Hstep end
    | @store => lazymatch code with store _ _ _ arraydef_0__meta ?slot ?value =>
        let Hstep := fresh "Hstep" in
        assert (Hstep : expression = Some (tt,(setMachine frame (store_meta (machine frame) (Z.to_nat slot) value),trace))) by
          (exact (local_store_meta frame slot value trace ltac:(bound frame slot)));
        rewrite Hstep; clear Hstep end
    | @liftToWithLocalVariables => lazymatch code with liftToWithLocalVariables ?callee =>
        let Hlift := fresh "Hlift" in
        assert (Hlift : expression = optionBind (execObserved callee (machine frame,trace))
          (fun response => Some (fst response,(setMachine frame (fst (snd response)),snd (snd response))))) by
          (exact (lift_correct callee frame trace)); rewrite Hlift; clear Hlift end
    | @shortCircuitAnd => unfold shortCircuitAnd at 1
    | @shortCircuitOr => unfold shortCircuitOr at 1
    | @writeChar => lazymatch code with writeChar _ _ _ ?ch =>
        change expression with (Some (tt,(setMachine frame (withOutput (machine frame) (stdout (machine frame) ++ [ch])),trace))) end
    | @flush =>
        let Hflush := fresh "Hflush" in
        assert (Hflush : expression = Some (tt,(frame,trace ++ [{|flushedOutput := stdout (machine frame); unreadInput := stdin (machine frame)|}]))) by
          (destruct frame; reflexivity); rewrite Hflush; clear Hflush
    end
    end
  end).
End CommandSteps.
