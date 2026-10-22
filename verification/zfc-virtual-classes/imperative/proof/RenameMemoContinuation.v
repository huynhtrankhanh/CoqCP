From CoqCP Require Import Options.
From Trusted Require Import SetTheory.
From NativeProof Require Import RenameStack.
From Stdlib Require Import Lists.List.
Import ListNotations.
Module RenameMemoContinuation.
Import SetTheory RenameStack.
(* Each waiting frame records which renamed child result it expects.
   This strengthens the old aggregate meaning equality enough to justify
   installing a parent's result in the semantic memo table on return. *)
Fixpoint correct rho stack result target : Prop :=
  match stack with
  | []=>result=target
  | visit p depth::tail=>correct rho tail (renamed rho depth p) target
  | left_done p q depth::tail=>result=renamed rho depth p /\ correct rho tail (renamed rho depth (implies p q)) target
  | right_done p q depth left_value::tail=>left_value=renamed rho depth p /\ result=renamed rho depth q /\
      correct rho tail (renamed rho depth (implies p q)) target
  | body_done p depth::tail=>result=renamed rho (S depth) p /\ correct rho tail (renamed rho depth (all p)) target
  end.
Theorem initial rho source depth result : correct rho [visit source depth] result (renamed rho depth source).
Proof. reflexivity. Qed.
Theorem finished rho result target : correct rho [] result target -> result=target.
Proof. exact (fun H=>H). Qed.
Theorem cached rho source depth stack result target : correct rho (visit source depth::stack) result target ->
  correct rho stack (renamed rho depth source) target.
Proof. exact (fun H=>H). Qed.
Theorem tick_preserves rho stack result target : correct rho stack result target ->
  correct rho (fst (tick rho (stack,result))) (snd (tick rho (stack,result))) target.
Proof.
  destruct stack as [|task stack]; [exact (fun H=>H)|].
  destruct task as [p depth|p q depth|p q depth left_value|p depth].
  - destruct p; cbn [tick fst snd correct renamed SetTheory.rename]; intro H; first [exact H|split; [reflexivity|exact H]].
  - cbn [tick fst snd correct]. intros [Hresult Htail]. split; [exact Hresult|]. split; [reflexivity|exact Htail].
  - cbn [tick fst snd correct]. intros [Hleft [Hresult Htail]]. now rewrite Hleft,Hresult.
  - cbn [tick fst snd correct]. intros [Hresult Htail]. now rewrite Hresult.
Qed.
Theorem aggregate_meaning rho stack result target : correct rho stack result target -> meaning rho stack result=target.
Proof.
  induction stack as [|task stack IH] in result |- *; [exact (fun H=>H)|].
  destruct task as [p depth|p q depth|p q depth left_value|p depth]; cbn [correct meaning frame_meaning].
  - apply IH.
  - intros [-> Htail]. apply IH. exact Htail.
  - intros [-> [-> Htail]]. apply IH. exact Htail.
  - intros [-> Htail]. apply IH. exact Htail.
Qed.
End RenameMemoContinuation.
