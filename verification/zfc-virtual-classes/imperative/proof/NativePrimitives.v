From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module NativePrimitives.
Import IndexExecution SipHashExecution ObservedLocal.
Section Locals.
Context {V : Type} `{EqDecision V}.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) V.
Lemma read_array (f : Frame) name slot default observations :
  (Z.to_nat slot < length (memory (machine f) name))%nat ->
  execLocalObserved (retrieve _ _ _ name slot) (f,observations) =
    Some (List.nth (Z.to_nat slot) (memory (machine f) name) default,(f,observations)).
Proof.
  intro Hbound. cbn [retrieve execLocalObserved localStepObserved fst snd].
  unfold observedStep. cbn [step optionBind fst snd]. case_decide; [|lia].
  rewrite nth_lt_default with (default := default). destruct f. reflexivity.
Qed.
Lemma store_array (f : Frame) name slot value observations :
  (Z.to_nat slot < length (memory (machine f) name))%nat ->
  execLocalObserved (store _ _ _ name slot value) (f,observations) =
    Some (tt,(setMachine f (withMemory (machine f) (modifyArray (memory (machine f)) name (Z.to_nat slot) value)),observations)).
Proof.
  intro Hbound. cbn [store execLocalObserved localStepObserved fst snd].
  unfold observedStep. cbn [step optionBind fst snd]. case_decide; [destruct f; reflexivity|lia].
Qed.
Lemma grow_array (f : Frame) name size zero observations :
  execLocalObserved (grow _ _ _ name size zero) (f,observations) =
    Some (tt,(setMachine f (withMemory (machine f) (growArrays (memory (machine f)) name (Z.to_nat size) zero)),observations)).
Proof. destruct f. reflexivity. Qed.
Lemma read_meta (f : Frame) slot observations :
  (Z.to_nat slot < length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved (retrieve _ _ _ arraydef_0__meta slot) (f,observations) =
    Some (meta_value (machine f) (Z.to_nat slot),(f,observations)).
Proof. exact (read_array f arraydef_0__meta slot 0 observations). Qed.
Lemma put_meta (f : Frame) slot value observations :
  (Z.to_nat slot < length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved (store _ _ _ arraydef_0__meta slot value) (f,observations) =
    Some (tt,(setMachine f (store_meta (machine f) (Z.to_nat slot) value),observations)).
Proof. exact (store_array f arraydef_0__meta slot value observations). Qed.
End Locals.

Ltac action_head term := lazymatch term with ?head ?arg => action_head head | _ => term end.
Ltac default_for name := lazymatch name with
  | arraydef_0__sipState => constr:((0%Z,0%Z,0%Z,0%Z))
  | arraydef_0__formulas => constr:((0%Z,0%Z,0%Z))
  | arraydef_0__classes => constr:((0%Z,0%Z))
  | arraydef_0__renameMemo => constr:((0%Z,0%Z,0%Z,0%Z))
  | arraydef_0__renameMemoScratch => constr:((0%Z,0%Z,0%Z,0%Z))
  | arraydef_0__frames => constr:((0%Z,0%Z,0%Z,0%Z))
  | arraydef_0__bindings => constr:((0%Z,0%Z,0%Z,0%Z,0%Z))
  | arraydef_0__schemaNodes => constr:((0%Z,0%Z,0%Z,0%Z,0%Z,0%Z,0%Z))
  | _ => constr:(0%Z)
  end.
(* [bound frame name slot] is supplied by the caller's concrete invariant.
   These tactics produce equalities checked by the kernel; they never assume
   that an array access or helper execution succeeds. *)
Ltac primitive bound := progress (match goal with
  |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state] =>
  lazymatch state with (?frame,?trace) =>
  let expression := constr:(@execLocalObserved I T EI V EV R code state) in
  let head := action_head code in
  first [constr_eq head (@Done) |constr_eq head (@bind) |constr_eq head (@numberLocalGet)
    |constr_eq head (@numberLocalSet) |constr_eq head (@booleanLocalGet) |constr_eq head (@booleanLocalSet)
    |constr_eq head (@retrieve) |constr_eq head (@store) |constr_eq head (@grow)
    |constr_eq head (@liftToWithLocalVariables) |constr_eq head (@shortCircuitAnd) |constr_eq head (@shortCircuitOr)];
  lazymatch head with
  | @Done => lazymatch code with @Done ?E ?F ?A ?value => change expression with (Some (value,(frame,trace))) end
  | @bind => lazymatch code with bind ?first ?next =>
      let Hbind := fresh "Hbind" in
      assert (Hbind : expression = optionBind (execLocalObserved first state)
        (fun response => execLocalObserved (R := R) (next (fst response)) (snd response))) by
        (exact (local_bind first next state)); rewrite Hbind; clear Hbind end
  | @numberLocalGet => lazymatch code with numberLocalGet _ _ _ ?name => change expression with (Some (nums frame name,(frame,trace))) end
  | @numberLocalSet => lazymatch code with numberLocalSet _ _ _ ?name ?value => change expression with (Some (tt,(setNum frame name value,trace))) end
  | @booleanLocalGet => lazymatch code with booleanLocalGet _ _ _ ?name => change expression with (Some (bools frame name,(frame,trace))) end
  | @booleanLocalSet => lazymatch code with booleanLocalSet _ _ _ ?name ?value => change expression with (Some (tt,(setBool frame name value,trace))) end
  | @retrieve => lazymatch code with retrieve _ _ _ ?name ?slot =>
      let Hstep := fresh "Hstep" in
      lazymatch name with
      | arraydef_0__meta => assert (Hstep : expression = Some (meta_value (machine frame) (Z.to_nat slot),(frame,trace))) by
          (exact (read_meta frame slot trace ltac:(bound frame name slot)))
      | _ => let zero := default_for name in
          assert (Hstep : expression = Some (List.nth (Z.to_nat slot) (memory (machine frame) name) zero,(frame,trace))) by
            (exact (read_array frame name slot zero trace ltac:(bound frame name slot)))
      end; rewrite Hstep; clear Hstep end
  | @store => lazymatch code with store _ _ _ ?name ?slot ?value =>
      let Hstep := fresh "Hstep" in
      lazymatch name with
      | arraydef_0__meta => assert (Hstep : expression = Some (tt,(setMachine frame (store_meta (machine frame) (Z.to_nat slot) value),trace))) by
          (exact (put_meta frame slot value trace ltac:(bound frame name slot)))
      | _ => assert (Hstep : expression = Some (tt,(setMachine frame (withMemory (machine frame)
          (modifyArray (memory (machine frame)) name (Z.to_nat slot) value)),trace))) by
          (exact (store_array frame name slot value trace ltac:(bound frame name slot)))
      end; rewrite Hstep; clear Hstep end
  | @grow => lazymatch code with grow _ _ _ ?name ?size ?zero =>
      let Hstep := fresh "Hstep" in assert (Hstep : expression = Some (tt,(setMachine frame (withMemory (machine frame)
        (growArrays (memory (machine frame)) name (Z.to_nat size) zero)),trace))) by
        (exact (grow_array frame name size zero trace)); rewrite Hstep; clear Hstep end
  | @liftToWithLocalVariables => lazymatch code with liftToWithLocalVariables ?callee =>
      let Hlift := fresh "Hlift" in
      assert (Hlift : expression = optionBind (execObserved callee (machine frame,trace))
        (fun response => Some (fst response,(setMachine frame (fst (snd response)),snd (snd response))))) by
        (exact (lift_correct callee frame trace)); rewrite Hlift; clear Hlift end
  | @shortCircuitAnd => unfold shortCircuitAnd at 1
  | @shortCircuitOr => unfold shortCircuitOr at 1
  end
end end).
End NativePrimitives.
