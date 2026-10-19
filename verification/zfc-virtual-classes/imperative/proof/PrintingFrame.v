From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith Lia.
Open Scope Z_scope.

Module PrintingFrame.
Import IndexExecution.
Definition translate_print {R}
  (code : Action (WithArrays arrayIndex0 (arrayType _ environment0)) withArraysReturnValue R) :=
  translateArrays code (arrayType _ environment1)
    (fun name => match name with arraydef_0_PrintInt64_buffer => arraydef_0__printBuffer end)
    (fun name => match name with arraydef_0_PrintInt64_buffer => eq_refl end).

Lemma modify_print_other values slot value name : name <> arraydef_0__printBuffer ->
  @modifyArray arrayIndex1 arrayIndexEqualityDecidable1 (arrayType _ environment1)
    values arraydef_0__printBuffer slot value name = values name.
Proof. destruct name; intro H; try congruence; reflexivity. Qed.

(* Any action translated from PrintInt64's single-array environment can
   modify only printBuffer. This also covers its loops and future changes to
   its formatting code, without assuming that the formatter terminates. *)
Theorem translated_print_preserves {R} code (s final : Machine) (value : R) name :
  name <> arraydef_0__printBuffer ->
  exec (translate_print code) s = Some (value, final) ->
  memory final name = memory s name.
Proof.
  intro Hname. induction code as [x |effect next IH] in s, final |- *.
  - cbn [translate_print translateArrays exec]. intro H. injection H as _ <-. reflexivity.
  - destruct effect as [effect |array slot |array slot item |array minimum zero].
    + destruct effect; cbn [translate_print translateArrays
        withArraysReturnValueDoBasicEffectArrayType exec step optionBind].
      * discriminate.
      * intro H. now apply IH in H.
      * change (optionBind (match stdin s with
          | [] => Some (2^64-1,s)
          | ch :: chars => Some (ch,withInput s chars)
          end) (fun response => exec (translate_print (next (fst response))) (snd response)) =
          Some (value, final) -> memory final name = memory s name).
        destruct (stdin s) as [|ch chars]; cbn [optionBind].
        -- intro H. now apply IH in H.
        -- intro H. apply IH in H. exact H.
      * intro H. apply IH in H. exact H.
      * intro H. apply IH in H. exact H.
    + destruct array. cbn [translate_print translateArrays Action_rect exec step].
      case_decide; cbn [optionBind]; [intro H; now apply IH in H |discriminate].
    + destruct array. cbn [translate_print translateArrays Action_rect exec step].
      case_decide; cbn [optionBind]; [|discriminate].
      intro H. apply IH in H. rewrite H. cbn [withMemory memory]. now apply modify_print_other.
    + destruct array. cbn [translate_print translateArrays Action_rect exec step optionBind].
      intro H. apply IH in H. rewrite H. cbn [withMemory memory].
      now apply growArrays_other.
Qed.

Section LocalFrame.
Context {V : Type} `{EqDecision V}.
Definition local_preserves {R} name
  (code : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) V)
    withLocalVariablesReturnValue R) :=
  forall f value final, execLocal code f = Some (value,final) ->
    memory (machine final) name = memory (machine f) name.

Lemma local_done {R} name (value : R) : local_preserves name (Done _ _ _ value).
Proof. intros f result final Hrun. injection Hrun as _ <-. reflexivity. Qed.

Lemma local_bind {A B} name
  (code : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) V)
    withLocalVariablesReturnValue A) next :
  local_preserves name code ->
  (forall value, local_preserves name (next value)) ->
  local_preserves (R := B) name (code >>= next).
Proof.
  intros Hcode Hnext f value final Hrun. rewrite execLocal_bind in Hrun.
  destruct (execLocal code f) as [[middle middle_frame] |] eqn:Hfirst; [|discriminate].
  cbn [optionBind fst snd] in Hrun.
  rewrite (Hnext middle middle_frame value final Hrun). now apply Hcode in Hfirst.
Qed.

Lemma local_dispatch {R} name effect next :
  (forall f response final, localStep effect f = Some (response,final) ->
    memory (machine final) name = memory (machine f) name) ->
  (forall response, local_preserves name (next response)) ->
  local_preserves (R := R) name (Dispatch _ _ _ effect next).
Proof.
  intros Heffect Hnext f value final Hrun. cbn [execLocal] in Hrun.
  destruct (localStep effect f) as [[middle middle_frame] |] eqn:Hfirst; [|discriminate].
  cbn [optionBind fst snd] in Hrun.
  rewrite (Hnext middle middle_frame value final Hrun). now apply Heffect in Hfirst.
Qed.

Lemma local_print {R} name code : name <> arraydef_0__printBuffer ->
  local_preserves (R := R) name (liftToWithLocalVariables (translate_print code)).
Proof.
  intros Hname f value final Hrun. rewrite execLocal_lift in Hrun.
  destruct (exec (translate_print code) (machine f)) as [[result after] |] eqn:Hprint;
    [|discriminate].
  cbn [optionBind fst snd] in Hrun. injection Hrun as _ <-.
  cbn [machine setMachine].
  exact (translated_print_preserves code (machine f) after result name Hname Hprint).
Qed.
End LocalFrame.

Ltac local_frame :=
  first [apply local_done
  |apply local_print; assumption
  |apply local_bind; [local_frame |intro; local_frame]
  |apply local_dispatch;
    [intros ? ? ? Hrun;
     cbv beta iota zeta delta [localStep step optionBind numberLocalGet
       machine setMachine withOutput] in Hrun;
     injection Hrun as _ <-; reflexivity
    |intro; local_frame]
  ].

Theorem generated_ok_preserves s bs ns final name :
  name <> arraydef_0__printBuffer ->
  exec (funcdef_0__ok bs ns) s = Some (tt, final) ->
  memory final name = memory s name.
Proof.
  intro Hname.
  assert (Hframe : local_preserves name funcdef_0__ok_body).
  { unfold funcdef_0__ok_body.
    apply local_bind.
    - cbv beta iota zeta delta [loopString dropWithinLoop liftToWithinLoop
        Action_rect bind writeChar]. local_frame.
    - intros [].
      cbn [numberLocalGet writeChar flush].
      change (local_preserves name
        ((numberLocalGet _ _ _ vardef_0__ok_value >>= fun value =>
          liftToWithLocalVariables (translate_print (funcdef_0_PrintInt64_unsigned
            (fun _ => false) (update (fun _ => 0) vardef_0_PrintInt64_unsigned_num value))))
        >>= fun _ => writeChar _ _ _ (coerceInt 10 8) >>= fun _ =>
          flush _ _ _ >>= fun _ => Done _ _ _ tt)).
      local_frame.
  }
  unfold funcdef_0__ok. rewrite exec_eliminate.
  destruct (execLocal funcdef_0__ok_body {|machine := s; bools := bs; nums := ns|})
    as [[result after] |] eqn:Hlocal; [|discriminate].
  cbn [optionBind fst snd]. intro Hrun. injection Hrun as _ <-.
  apply Hframe in Hlocal. exact Hlocal.
Qed.
End PrintingFrame.
