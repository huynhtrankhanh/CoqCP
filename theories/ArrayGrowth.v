From CoqCP Require Import Options Imperative.
From stdpp Require Import numbers list.

Lemma growList_old_element {A} (values : list A) size zero index
  (h : (index < length values)%nat) :
  nth index (growList values size zero) zero = nth index values zero.
Proof. unfold growList. apply app_nth1. exact h. Qed.

Lemma growList_new_element {A} (values : list A) size (zero : A) index
  (hOld : (length values <= index)%nat) (hNew : (index < size)%nat) :
  nth index (growList values size zero) zero = zero.
Proof. unfold growList. rewrite app_nth2; [| exact hOld]. apply nth_repeat. Qed.

Inductive GrowthArray := data.
#[export] Instance growthArrayEquality : EqDecision GrowthArray := ltac:(solve_decision).
Definition growthType (_ : GrowthArray) := (Z * bool)%type.
Definition initialGrowthArrays (_ : GrowthArray) : list (Z * bool) := [(65%Z, true)].
Definition growthProgram : Action (WithArrays GrowthArray growthType) withArraysReturnValue unit :=
  Dispatch _ _ _ (Grow _ _ data 3%Z (0%Z, false)) (fun _ =>
  Dispatch _ _ _ (Store _ _ data 2%Z (66%Z, true)) (fun _ =>
  Dispatch _ _ _ (Grow _ _ data 1%Z (0%Z, false)) (fun _ => Done _ _ _ tt))).

Example growthExecution :
  match runProgram initialGrowthArrays growthProgram [] with
  | Some (values, _, _) => values data
  | None => []
  end = [(65%Z, true); (0%Z, false); (66%Z, true)].
Proof. vm_compute. reflexivity. Qed.

Example growthThroughMapping :
  match runProgram initialGrowthArrays
    (translateArrays growthProgram growthType (fun name => name) ltac:(intros; reflexivity)) [] with
  | Some (values, _, _) => values data
  | None => []
  end = [(65%Z, true); (0%Z, false); (66%Z, true)].
Proof. vm_compute. reflexivity. Qed.
