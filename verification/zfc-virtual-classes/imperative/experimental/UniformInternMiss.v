From CoqCP Require Import Options Imperative Execution.
From UniformInternFixture Require Import UniformInternProgram UniformInternLoop UniformInternHit.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module UniformInternMiss.
Import UniformInternLoop UniformInternHit.

Definition overflow_frame (f : Frame) :=
  setMachine (setNum f vardef_0__uniformIntern_count maximum)
    (store_meta (machine f) 8 1).

Theorem miss_overflow (f : Frame) size :
  nums f vardef_0__uniformIntern_found = 0 ->
  (0 < length (memory (machine f) arraydef_0__uniformState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformState) (0,0) = (maximum,size) ->
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  execLocal after_scan f = Some (tt,overflow_frame f).
Proof.
  destruct f as [s bs ns]. cbn [nums machine]. intros Hfound Hstate Hentry Hmeta.
  unfold after_scan, overflow_frame, store_meta, maximum in *.
  cbn zeta.
  cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    shortCircuitAnd retrieve numberLocalGet numberLocalSet store break subInt
    execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
    Imperative.update decide decide_rel
    variableIndexEqualityDecidablevarsfuncdef_0__uniformIntern varsfuncdef_0__uniformIntern_rec].
  rewrite Hfound, bool_decide_true by reflexivity.
  destruct (Nat.lt_dec (Z.to_nat 0) (length (memory s arraydef_0__uniformState))); [|lia].
  rewrite nth_lt_default with (default := (0,0)).
  destruct (memory s arraydef_0__uniformState) as [|entry rest] eqn:E; [cbn in Hstate; lia|].
  cbn in Hentry. subst entry. cbn.
  rewrite bool_decide_true by reflexivity.
  destruct (Nat.lt_dec (Z.to_nat 8) (length (memory s arraydef_0__meta))); [|lia]. reflexivity.
Qed.
End UniformInternMiss.
