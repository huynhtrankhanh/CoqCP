(* Merge sort and its proofs adapted from stdpp/sorting.v.
All files in this development are distributed under the terms of the 3-clause
BSD license (https://opensource.org/licenses/BSD-3-Clause), included below.

Copyright: std++ developers and contributors

------------------------------------------------------------------------------

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the copyright holder nor the names of its contributors
      may be used to endorse or promote products derived from this software
      without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)
From stdpp Require Export orders list.
From stdpp Require Import options.
Section sorted_defs.
Context {A : Type} (R : relation A).
Inductive HdRel (a : A) : list A -> Prop :=
| HdRel_nil : HdRel a []
| HdRel_cons b l : R a b -> HdRel a (b :: l).
Inductive Sorted : list A -> Prop :=
| Sorted_nil : Sorted []
| Sorted_cons a l : Sorted l -> HdRel a l -> Sorted (a :: l).
Inductive StronglySorted : list A -> Prop :=
| SSorted_nil : StronglySorted []
| SSorted_cons a l : StronglySorted l -> Forall (R a) l -> StronglySorted (a :: l).
Lemma Sorted_StronglySorted `{!Transitive R} l : Sorted l -> StronglySorted l.
Proof.
  intros Hs; induction Hs as [|a l Hs IH Hhd]; constructor; auto.
  destruct Hhd as [|b l Hab]; constructor; auto.
  inversion IH as [|? ? _ Hb]; subst.
  eapply Forall_impl; [exact Hb |]. intros x Hbx. eapply transitivity; eauto.
Qed.
End sorted_defs.
#[global] Hint Constructors HdRel Sorted : core.
Section merge_sort.
  Context {A} (R : relation A) `{∀ x y, Decision (R x y)}.

  Fixpoint list_merge (l1 : list A) : list A → list A :=
    fix list_merge_aux l2 :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x1 :: l1, x2 :: l2 =>
       if decide (R x1 x2) then x1 :: list_merge l1 (x2 :: l2)
       else x2 :: list_merge_aux l2
    end.
  Global Arguments list_merge !_ !_ / : assert.

  Local Notation stack := (list (option (list A))).
  Fixpoint merge_list_to_stack (st : stack) (l : list A) : stack :=
    match st with
    | [] => [Some l]
    | None :: st => Some l :: st
    | Some l' :: st => None :: merge_list_to_stack st (list_merge l' l)
    end.
  Fixpoint merge_stack (st : stack) : list A :=
    match st with
    | [] => []
    | None :: st => merge_stack st
    | Some l :: st => list_merge l (merge_stack st)
    end.
  Fixpoint merge_sort_aux (st : stack) (l : list A) : list A :=
    match l with
    | [] => merge_stack st
    | x :: l => merge_sort_aux (merge_list_to_stack st [x]) l
    end.
  Definition merge_sort : list A → list A := merge_sort_aux [].
End merge_sort.
Section merge_sort_correct.
  Context  {A} (R : relation A) `{∀ x y, Decision (R x y)}.

  Lemma list_merge_nil_l l2 : list_merge R [] l2 = l2.
  Proof. by destruct l2. Qed.
  Lemma list_merge_nil_r l1 : list_merge R l1 [] = l1.
  Proof. by destruct l1. Qed.
  Lemma list_merge_cons x1 x2 l1 l2 :
    list_merge R (x1 :: l1) (x2 :: l2) =
      if decide (R x1 x2) then x1 :: list_merge R l1 (x2 :: l2)
      else x2 :: list_merge R (x1 :: l1) l2.
  Proof. done. Qed.
  Lemma HdRel_list_merge x l1 l2 :
    HdRel R x l1 → HdRel R x l2 → HdRel R x (list_merge R l1 l2).
  Proof.
    destruct 1 as [|x1 l1 IH1], 1 as [|x2 l2 IH2];
      rewrite ?list_merge_cons; simpl; repeat case_decide; auto.
  Qed.
  Lemma Sorted_list_merge `{!Total R} l1 l2 :
    Sorted R l1 → Sorted R l2 → Sorted R (list_merge R l1 l2).
  Proof.
    intros Hl1. revert l2. induction Hl1 as [|x1 l1 IH1];
      induction 1 as [|x2 l2 IH2]; rewrite ?list_merge_cons; simpl;
      repeat case_decide;
      repeat match goal with H : ¬R _ _ |- _ => apply total_not in H end;
      constructor; eauto using HdRel_list_merge, HdRel_cons.
  Qed.
  Lemma merge_Permutation l1 l2 : list_merge R l1 l2 ≡ₚ l1 ++ l2.
  Proof.
    revert l2. induction l1 as [|x1 l1 IH1]; intros l2;
      induction l2 as [|x2 l2 IH2]; rewrite ?list_merge_cons; simpl;
      repeat case_decide; auto.
    - by rewrite (right_id_L [] (++)).
    - by rewrite IH2, Permutation_middle.
  Qed.

  Local Notation stack := (list (option (list A))).
  Inductive merge_stack_Sorted : stack → Prop :=
    | merge_stack_Sorted_nil : merge_stack_Sorted []
    | merge_stack_Sorted_cons_None st :
       merge_stack_Sorted st → merge_stack_Sorted (None :: st)
    | merge_stack_Sorted_cons_Some l st :
       Sorted R l → merge_stack_Sorted st → merge_stack_Sorted (Some l :: st).
  Fixpoint merge_stack_flatten (st : stack) : list A :=
    match st with
    | [] => []
    | None :: st => merge_stack_flatten st
    | Some l :: st => l ++ merge_stack_flatten st
    end.

  Lemma Sorted_merge_list_to_stack `{!Total R} st l :
    merge_stack_Sorted st → Sorted R l →
    merge_stack_Sorted (merge_list_to_stack R st l).
  Proof.
    intros Hst. revert l.
    induction Hst; repeat constructor; naive_solver auto using Sorted_list_merge.
  Qed.
  Lemma merge_list_to_stack_Permutation st l :
    merge_stack_flatten (merge_list_to_stack R st l) ≡ₚ
      l ++ merge_stack_flatten st.
  Proof.
    revert l. induction st as [|[l'|] st IH]; intros l; simpl; auto.
    by rewrite IH, merge_Permutation, (assoc_L _), (comm (++) l).
  Qed.
  Lemma Sorted_merge_stack `{!Total R} st :
    merge_stack_Sorted st → Sorted R (merge_stack R st).
  Proof. induction 1; simpl; auto using Sorted_list_merge. Qed.
  Lemma merge_stack_Permutation st : merge_stack R st ≡ₚ merge_stack_flatten st.
  Proof.
    induction st as [|[] ? IH]; intros; simpl; auto.
    by rewrite merge_Permutation, IH.
  Qed.
  Lemma Sorted_merge_sort_aux `{!Total R} st l :
    merge_stack_Sorted st → Sorted R (merge_sort_aux R st l).
  Proof.
    revert st. induction l; simpl;
      auto using Sorted_merge_stack, Sorted_merge_list_to_stack.
  Qed.
  Lemma merge_sort_aux_Permutation st l :
    merge_sort_aux R st l ≡ₚ merge_stack_flatten st ++ l.
  Proof.
    revert st. induction l as [|?? IH]; simpl; intros.
    - by rewrite (right_id_L [] (++)), merge_stack_Permutation.
    - rewrite IH, merge_list_to_stack_Permutation; simpl.
      by rewrite Permutation_middle.
  Qed.
  Lemma Sorted_merge_sort `{!Total R} l : Sorted R (merge_sort R l).
  Proof. apply Sorted_merge_sort_aux. by constructor. Qed.
  Lemma merge_sort_Permutation l : merge_sort R l ≡ₚ l.
  Proof. unfold merge_sort. by rewrite merge_sort_aux_Permutation. Qed.
  Lemma StronglySorted_merge_sort `{!Transitive R, !Total R} l :
    StronglySorted R (merge_sort R l).
  Proof. auto using Sorted_StronglySorted, Sorted_merge_sort. Qed.
End merge_sort_correct.
