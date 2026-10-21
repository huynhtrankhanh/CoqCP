From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index ObservedLocal CommandQuit.
From Stdlib Require Import Strings.String Strings.Ascii Lists.List ZArith.ZArith.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module CommandText.
Import IndexExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Definition body ch := dropWithinLoop
  (liftToWithinLoop (Done _ _ _ ch >>= fun value => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command value) >>=
    fun _ => Done _ _ _ tt).
Definition text str := loopString str body.
Fixpoint bytes str : list Z := match str with EmptyString => [] | String ch rest => Z.of_N (N_of_ascii ch) :: bytes rest end.
Lemma body_execution ch (f : Frame) observations :
  execLocalObserved (body ch) (f,observations) = Some (KeepGoing,(setMachine f (withOutput (machine f) (stdout (machine f) ++ [ch])),observations)).
Proof. destruct f. reflexivity. Qed.
Theorem text_execution str (f : Frame) observations :
  execLocalObserved (text str) (f,observations) = Some (tt,(setMachine f (withOutput (machine f) (stdout (machine f) ++ bytes str)),observations)).
Proof.
  induction str as [|ch str IH] in f |- *.
  - destruct f as [[values input output] bs ns]. cbn [text loopString bytes execLocalObserved withOutput machine stdout setMachine]. now rewrite app_nil_r.
  - change (execLocalObserved (body (Z.of_N (N_of_ascii ch)) >>= fun outcome =>
      match outcome with KeepGoing => text str | Stop => Done _ _ _ tt end) (f,observations) =
      Some (tt,(setMachine f (withOutput (machine f) (stdout (machine f) ++ bytes (String ch str))),observations))).
    rewrite ObservedLocal.local_bind,body_execution. cbn [optionBind fst snd]. rewrite IH.
    destruct f. cbn [bytes machine setMachine withOutput stdout]. now rewrite <-app_assoc.
Qed.
Lemma output_memory (s : Machine) output name : memory (withOutput s output) name = memory s name.
Proof. reflexivity. Qed.
End CommandText.
