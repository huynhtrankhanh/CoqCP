From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal.
From stdpp Require Import numbers list.
Module SchemaEvaluationControl.
Import IndexExecution SipHashExecution ObservedLocal.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) withLocalVariablesReturnValue R.
Definition LoopAction R := Action (WithinLoop arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) withinLoopReturnValue R.
Fixpoint straight {R} (code:LoopAction R) : Prop := match code with
| Done _ _ _ _=>True
| Dispatch _ _ _ effect next=>match effect as e return (withinLoopReturnValue e->LoopAction R)->Prop with
  | DoWithLocalVariables _ _ _ effect=>fun cont=>forall response,straight (cont response)
  | _=>fun _=>False end next end.
Lemma straight_lift {R} (code:LocalAction R) : straight (liftToWithinLoop code).
Proof. induction code;cbn [straight liftToWithinLoop Action_rect];auto. Qed.
Lemma straight_bind {A B} (code:LoopAction A) (next:A->LoopAction B) :
 straight code -> (forall value,straight (next value)) -> straight (code >>= next).
Proof.
 induction code as [value|effect cont IH].
 - cbn [straight bind]. auto.
 - destruct effect;cbn [straight bind];try tauto.
   intros Hcode Hnext response. apply IH;auto.
Qed.
Lemma straight_drop_tail (code:LoopAction unit) (next:LoopAction unit) f observations final after :
 straight code -> execLocalObserved (dropWithinLoop code) (f,observations)=Some (KeepGoing,(final,after)) ->
 execLocalObserved (dropWithinLoop (code >>= fun _=>next)) (f,observations)=
 execLocalObserved (dropWithinLoop next) (final,after).
Proof.
 induction code as [value|effect cont IH] in f,observations,final,after|-*.
 - destruct value. cbn [dropWithinLoop Action_rect execLocalObserved] in *. intros _ Hrun.
   injection Hrun as <- <-. reflexivity.
 - destruct effect as [effect| |];cbn [straight];try tauto.
   intros Hcode Hrun.
   cbn [dropWithinLoop Action_rect execLocalObserved] in Hrun.
   cbn [bind dropWithinLoop Action_rect execLocalObserved].
   destruct (localStepObserved effect (f,observations)) as [[value [middle trace]]|];cbn [optionBind fst snd] in *;[|discriminate].
   eapply IH;[apply Hcode|exact Hrun].
Qed.
Lemma drop_lift_final (code:LocalAction unit) state :
 execLocalObserved (dropWithinLoop (liftToWithinLoop code)) state =
 optionBind (execLocalObserved code state) (fun r=>Some (KeepGoing,snd r)).
Proof.
 induction code as [value|effect cont IH] in state|-*.
 - destruct value. reflexivity.
 - cbn [liftToWithinLoop dropWithinLoop Action_rect execLocalObserved].
   destruct (localStepObserved effect state) as [[value after]|];cbn [optionBind fst snd];[apply IH|reflexivity].
Qed.
Ltac straight_program :=
 repeat first [apply straight_lift|apply straight_bind|exact I|intro|match goal with b:bool |- _=>destruct b end].
End SchemaEvaluationControl.
