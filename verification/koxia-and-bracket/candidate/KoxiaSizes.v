From CoqCP Require Import Options Imperative.
From Submission Require Import KoxiaRoots KoxiaFourier KoxiaIntegers.
From stdpp Require Import numbers.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Fixpoint ceilingStage fuel target stage :=
  match fuel with
  | O => stage
  | S fuel => if bool_decide (stageSize stage<target) then ceilingStage fuel target (S stage) else stage
  end.
Theorem ceilingStage_bounds fuel target stage : (stage<=20)%nat -> (20-stage<=fuel)%nat ->
  target<=1048576 -> stageSize stage<2*target ->
  (stage<=ceilingStage fuel target stage<=20)%nat /\
  target<=stageSize (ceilingStage fuel target stage)<2*target.
Proof.
  induction fuel as [|fuel IH] in stage |- *.
  - intros stageBound fuelBound targetBound upper.
    assert (stage=20)%nat by lia. subst stage. cbn [ceilingStage]. split; [lia|].
    split; [exact targetBound|exact upper].
  - intros stageBound fuelBound targetBound upper. cbn [ceilingStage].
    destruct (bool_decide (stageSize stage<target)) eqn:small.
    + apply bool_decide_eq_true in small.
      assert (nextBound : (S stage<=20)%nat).
      { destruct (Nat.eq_dec stage (20%nat)) as [last|before]; [subst stage; change (1048576<target) in small; lia|lia]. }
      destruct (IH (S stage) nextBound ltac:(lia) targetBound ltac:(rewrite stageSize_succ; lia)) as [stages sizes].
      split; [lia|exact sizes].
    + apply bool_decide_eq_false in small. split; lia.
Qed.
Theorem ceilingStage_correct target : 1<=target<=1048576 ->
  (ceilingStage 20 target 0<=20)%nat /\ target<=stageSize (ceilingStage 20 target 0)<2*target.
Proof.
  intros range. destruct (ceilingStage_bounds 20 target 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(change (1<2*target); lia)) as [bound sizes].
  split; [lia|exact sizes].
Qed.

Section MachineDoubling.
Context {I : Type} {T : I -> Type} {V : Type} `{EqDecision V}.
Variable sizeName targetName : V.
Definition doublingBody : nat -> Action (WithLocalVariables I T V) withLocalVariablesReturnValue LoopOutcome :=
  fun _ => dropWithinLoop
    (liftToWithinLoop
      (numberLocalGet _ _ _ sizeName >>= fun size => numberLocalGet _ _ _ targetName >>= fun target =>
       Done _ _ _ (negb (bool_decide (size<target)))) >>= fun finished =>
     (if finished then break _ _ _ >>= fun _ => Done _ _ _ tt else Done _ _ _ tt) >>= fun _ =>
     liftToWithinLoop (multInt 64 (numberLocalGet _ _ _ sizeName) (Done _ _ _ 2) >>= fun doubled =>
       numberLocalSet _ _ _ sizeName doubled) >>= fun _ => Done _ _ _ tt).
Lemma update_own (nums : V -> Z) name : update nums name (nums name)=nums.
Proof. apply functional_extensionality. intro query. unfold update. destruct (decide (query=name)) as [->|different]; reflexivity. Qed.
Ltac normalize_doubling := repeat progress
  (autorewrite with advance_program; try rewrite <- !bindAssoc;
   try rewrite @dropWithinLoopLiftToWithinLoop; try rewrite @dropWithinLoop_1; cbn [bind]).
Lemma doublingStep b nums remaining continuation :
  eliminateLocalVariables b nums (doublingBody remaining >>= continuation)=
  if bool_decide (nums sizeName<nums targetName) then
    eliminateLocalVariables b (update nums sizeName (coerceInt (nums sizeName*2) 64)) (continuation KeepGoing)
  else eliminateLocalVariables b nums (continuation Stop).
Proof.
  unfold doublingBody,numberLocalGet,numberLocalSet,multInt. normalize_doubling.
  destruct (bool_decide (nums sizeName<nums targetName)); cbn [negb]; normalize_doubling; reflexivity.
Qed.
Theorem doublingLoopNormalized b nums fuel stage target continuation : sizeName<>targetName ->
  (stage+fuel<=20)%nat -> nums sizeName=stageSize stage -> nums targetName=target ->
  eliminateLocalVariables b nums (loop fuel doublingBody >>= continuation)=
  eliminateLocalVariables b (update nums sizeName (stageSize (ceilingStage fuel target stage))) (continuation tt).
Proof.
  induction fuel as [|fuel IH] in stage,nums |- *.
  - intros different stageBound sizeEq targetEq. cbn [ceilingStage loop].
    rewrite <-sizeEq,update_own. reflexivity.
  - intros different stageBound sizeEq targetEq.
    rewrite loop_S,<-bindAssoc,doublingStep,sizeEq,targetEq. cbn [ceilingStage].
    destruct (bool_decide (stageSize stage<target)) eqn:small.
    + assert (nextSize : coerceInt (stageSize stage*2) 64=stageSize (S stage)).
      { rewrite stageSize_succ. replace (stageSize stage*2) with (2*stageSize stage) by ring.
        apply coerce64_small. pose proof (stageSize_positive (S stage)) as positive.
        pose proof (stageSize_bound (S stage) ltac:(lia)) as bound.
        rewrite stageSize_succ in positive,bound.
        change (0<=2*stageSize stage<18446744073709551616). lia. }
      rewrite nextSize.
      rewrite (IH (update nums sizeName (stageSize (S stage))) (S stage) different
        ltac:(lia) ltac:(apply lookupSame)
        ltac:(rewrite lookupDifferent by congruence; exact targetEq)).
      rewrite updateSame. reflexivity.
    + rewrite <-sizeEq,update_own. reflexivity.
Qed.
End MachineDoubling.
