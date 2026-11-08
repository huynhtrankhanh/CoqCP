From CoqCP Require Import Options Imperative Execution.
From UniformInternFixture Require Import UniformInternProgram UniformInternLoop.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module UniformInternHit.
Import UniformInternLoop.

(* Actual generated continuation after the collision-scan loop. *)
Definition after_scan : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__uniformIntern_body in funcdef_0__uniformIntern_body in
  lazymatch code with context [bind (bind _ (fun x => loop _ _)) ?next] =>
    let tail := eval cbn beta in (next tt) in exact tail
  end).

(* Extract the enclosing count-read, scan, and continuation as one generated
   Action. The callback's loop body is independent of its range counter. *)
Definition scan_segment : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__uniformIntern_body in funcdef_0__uniformIntern_body in
  multimatch code with context [bind ?before ?next] =>
    lazymatch before with bind ?read ?callback =>
      let test := eval cbn beta in (callback 0%Z) in
      lazymatch test with loop _ _ => exact (bind before next) end
    end
  end).

Lemma read_state (f : Frame) :
  (0 < length (memory (machine f) arraydef_0__uniformState))%nat ->
  execLocal (retrieve _ _ _ arraydef_0__uniformState 0) f =
    Some (List.nth 0 (memory (machine f) arraydef_0__uniformState) (0,0),f).
Proof.
  destruct f. intro H. cbn [retrieve execLocal localStep step].
  case_decide; [|lia]. rewrite nth_lt_default with (default := (0,0)). reflexivity.
Qed.
Lemma local_done {R} (f : Frame) (value : R) :
  execLocal (Done _ _ _ value) f = Some (value,f).
Proof. reflexivity. Qed.

Theorem found_return (f : Frame) :
  nums f vardef_0__uniformIntern_found = 1 ->
  execLocal after_scan f = Some (tt,f).
Proof.
  destruct f as [s bs ns]. cbn [nums]. intro Hfound.
  unfold after_scan. cbn zeta.
  cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    shortCircuitAnd retrieve numberLocalGet numberLocalSet store break subInt
    execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
    Imperative.update decide decide_rel
    variableIndexEqualityDecidablevarsfuncdef_0__uniformIntern varsfuncdef_0__uniformIntern_rec].
  rewrite Hfound, bool_decide_false by lia. reflexivity.
Qed.

(* This is the generated scan callback followed by its generated continuation;
   the bucket and hash setup preceding it is a separate proof obligation. *)
Theorem scan_hit_then_return fuel (f : Frame) count pointer result :
  entries_valid f count -> Z.of_nat count <= maximum ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__uniformIntern_current = Z.of_nat pointer -> (pointer <= count)%nat ->
  observed_result f = None -> scan_index f fuel pointer = Some result ->
  exists final,
    execLocal (loop fuel scan_body >>= fun _ => after_scan) f = Some (tt,final) /\
    observed_result final = Some result.
Proof.
  intros Hvalid Hlimit Hmeta Hpointer Hbound Hinitial Hscan.
  destruct (scan_loop_refines fuel f count pointer Hvalid Hlimit Hmeta Hpointer Hbound Hinitial)
    as [final [Hrun Hresult]]. exists final. split.
  - rewrite execLocal_bind, Hrun. cbn [optionBind fst snd].
    apply found_return. unfold observed_result in Hresult.
    rewrite Hscan in Hresult.
    destruct (bool_decide (nums final vardef_0__uniformIntern_found = 1)) eqn:Hfound;
      [apply bool_decide_eq_true in Hfound; exact Hfound|discriminate].
  - now rewrite Hresult.
Qed.

Theorem generated_segment_hit (f : Frame) count size pointer result :
  (0 < length (memory (machine f) arraydef_0__uniformState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformState) (0,0) = (Z.of_nat count,size) ->
  entries_valid f count -> Z.of_nat count <= maximum ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__uniformIntern_current = Z.of_nat pointer -> (pointer <= count)%nat ->
  observed_result f = None -> scan_index f count pointer = Some result ->
  exists final, execLocal scan_segment f = Some (tt,final) /\ observed_result final = Some result.
Proof.
  intros Hstate Hcount Hvalid Hlimit Hmeta Hpointer Hbound Hinitial Hscan.
  unfold scan_segment.
  repeat rewrite execLocal_bind. repeat rewrite local_done. cbn [optionBind fst snd].
  assert (Hread := read_state f Hstate). setoid_rewrite Hread.
  cbn [optionBind fst snd]. rewrite Hcount. repeat rewrite local_done. cbn [optionBind fst snd].
  try rewrite Nat2Z.id.
  destruct (scan_loop_refines count f count pointer Hvalid Hlimit Hmeta Hpointer Hbound Hinitial)
    as [final [Hrun Hresult]]. exists final. split.
  - setoid_rewrite Hrun. cbn [optionBind fst snd]. apply found_return.
    unfold observed_result in Hresult. rewrite Hscan in Hresult.
    destruct (bool_decide (nums final vardef_0__uniformIntern_found = 1)) eqn:Hfound;
      [apply bool_decide_eq_true in Hfound; exact Hfound|discriminate].
  - now rewrite Hresult.
Qed.
End UniformInternHit.
