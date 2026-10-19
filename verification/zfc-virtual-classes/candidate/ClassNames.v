From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses.
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Submission Require Import Checker.
Require Import Trusted.Spec.
Import ListNotations SetTheory VirtualClasses.

Module ClassNames.
(* Names are byte strings in the frontend. The reference model admits lists
   of naturals; restricting the wire encoding to bytes is a parser obligation. *)
Definition name := list nat.
Definition name_eq_dec : forall a b : name, {a = b} + {a <> b} := list_eq_dec Nat.eq_dec.
Fixpoint lookup (n : name) (bindings : list (name * class)) : option class :=
  match bindings with
  | [] => None
  | (key, value) :: tail => if name_eq_dec n key then Some value else lookup n tail
  end.

(* Existence of a set extensionally representing a class. A set variable uses
   ordinary equality, while an abstraction uses its predicate expansion. *)
Definition is_set (c : class) : formula :=
  match c with
  | set i => ex (equal 0 (S i))
  | abstract _ => ex (all (SetTheory.iff (member 0 1)
      (predicate c (fun n => S (S n)) 0)))
  end.

Theorem set_variables_are_sets i : derives (is_set (set i)).
Proof.
  unfold is_set, ex, neg.
  eapply d_mp.
  - eapply d_mp.
    + exact (d_s (all (implies (equal 0 (S i)) falsity)) (equal i i) falsity).
    + exact (d_inst (implies (equal 0 (S i)) falsity) i).
  - eapply d_mp; [apply d_k | apply d_refl].
Qed.

(* A bounded predicate defines a set by Separation. This produces a genuine
   theorem of the object theory, with no Rocq assumption about a ZFC model. *)
Definition bounded_class p := abstract (core (SetTheory.conj (member 0 1) p)).
Theorem bounded_classes_are_sets p : derives (is_set (bounded_class p)).
Proof. exact (d_set _ (ax_separation p)). Qed.

Record registry := {
  definitions : list (name * class);
  certified_sets : list (name * class)
}.
Definition empty := {| definitions := []; certified_sets := [] |}.
Inductive command :=
| define_class (n : name) (c : class)
| certify_set (n : name) (c : certificate).

Definition step (theorems : Trusted.Spec.state) (r : registry) (cmd : command) :=
  match cmd with
  | define_class n c =>
      match lookup n (definitions r) with
      | Some _ => (false, r)
      | None => (true, {| definitions := (n, c) :: definitions r;
                         certified_sets := certified_sets r |})
      end
  | certify_set n c =>
      match lookup n (definitions r), infer theorems c with
      | Some cls, Some conclusion =>
          if formula_eqb conclusion (is_set cls) then
            (true, {| definitions := definitions r;
                      certified_sets := (n, cls) :: certified_sets r |})
          else (false, r)
      | _, _ => (false, r)
      end
  end.

Definition safe (r : registry) := forall n c, In (n, c) (certified_sets r) ->
  lookup n (definitions r) = Some c /\ derives (is_set c).

Lemma empty_safe : safe empty.
Proof. intros n c H. inversion H. Qed.

Lemma fresh_preserves_lookup bindings fresh value n c :
  lookup fresh bindings = None -> lookup n bindings = Some c ->
  lookup n ((fresh, value) :: bindings) = Some c.
Proof.
  intros Hfresh Hn. cbn [lookup]. destruct (name_eq_dec n fresh) as [He | He].
  - subst n. congruence.
  - exact Hn.
Qed.

Theorem step_safe theorems r cmd : Trusted.Spec.safe theorems -> safe r ->
  safe (snd (step theorems r cmd)).
Proof.
  intros Hproofs Hr. destruct cmd as [n cls | n cert]; cbn [step].
  - destruct (lookup n (definitions r)) as [old |] eqn:Hlookup; cbn [snd]; [exact Hr |].
    intros key value Hin. specialize (Hr key value Hin) as [Hkey Hset]. split; [|exact Hset].
    now apply fresh_preserves_lookup.
  - destruct (lookup n (definitions r)) as [cls |] eqn:Hlookup; [|exact Hr].
    destruct (infer theorems cert) as [p |] eqn:Hinfer; [|exact Hr].
    destruct (formula_eqb p (is_set cls)) eqn:He; cbn [snd]; [|exact Hr].
    intros key value [Hnew | Hold].
    + injection Hnew as <- <-. split; [exact Hlookup |].
      apply formula_eqb_spec in He. subst p. eapply judges_sound; [exact Hproofs |].
      exact (infer_sound theorems cert (is_set cls) Hinfer).
    + now apply Hr.
Qed.

Theorem accepts_set_proof theorems r n cls :
  lookup n (definitions r) = Some cls -> derives (is_set cls) ->
  exists cert, fst (step theorems r (certify_set n cert)) = true.
Proof.
  intros Hlookup Hproof.
  destruct (derives_certificate _ Hproof theorems) as [cert Hcert]. exists cert.
  cbn [step]. rewrite Hlookup, (infer_complete _ _ _ Hcert).
  rewrite (proj2 (formula_eqb_spec _ _) eq_refl). reflexivity.
Qed.

Theorem naming_adds_no_theorem theorems r n cls :
  lookup n (definitions r) = None ->
  certified_sets (snd (step theorems r (define_class n cls))) = certified_sets r.
Proof. intro H. cbn [step]. now rewrite H. Qed.

Example naming_is_not_set_comprehension :
  certified_sets (snd (step [] empty
    (define_class [85] (abstract (core (equal 0 0)))))) = [].
Proof. reflexivity. Qed.
Example cannot_certify_with_a_reflexivity_theorem :
  fst (step []
    {| definitions := [([85], abstract (core (equal 0 0)))]; certified_sets := [] |}
    (certify_set [85] (axiom_use (Refl 0)))) = false.
Proof. reflexivity. Qed.
End ClassNames.
