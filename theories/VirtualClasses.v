From CoqCP Require Import Options SetTheory.

Module VirtualClasses.
Import SetTheory.

(* Class expressions are notation for predicates on sets. There is no
   quantifier over classes, no class universe, and no comprehension axiom. *)
Inductive statement : Type :=
| core (p : formula)
| implication (p q : statement)
| universal (p : statement)
| class_equal (a b : class)
| class_member (a b : class)
with class : Type :=
| set (i : nat)
| abstract (body : statement).

Definition cons (x : nat) (rho : nat -> nat) (i : nat) :=
  match i with 0 => x | S n => rho n end.

(* Predicate substitution is simultaneous, with the bound argument handled
   separately from parameters. Fresh witnesses are inserted by shifting every
   parameter, including parameters nested inside class abstractions. *)
Fixpoint erase (p : statement) : formula :=
  match p with
  | core p => p
  | implication p q => implies (erase p) (erase q)
  | universal p => all (erase p)
  | class_equal (set i) (set j) => equal i j
  | class_equal a b => all (iff (predicate a S 0) (predicate b S 0))
  | class_member (set i) b => predicate b (fun n => n) i
  | class_member a b => ex (conj
      (all (iff (member 0 1) (predicate a (fun n => S (S n)) 0)))
      (predicate b S 0))
  end
with predicate (a : class) (rho : nat -> nat) (x : nat) : formula :=
  match a with
  | set i => member x (rho i)
  | abstract p => rename (cons x rho) (erase p)
  end.

(* The inference relation is independent of the executable checker. Restating
   a theorem permits exactly definitional expansion of virtual classes. *)
Inductive proves : statement -> Prop :=
| p_set p : set_axiom p -> proves (core p)
| p_k p q : proves (core (implies p (implies q p)))
| p_s p q r : proves (core (implies (implies p (implies q r))
    (implies (implies p q) (implies p r))))
| p_dne p : proves (core (implies (neg (neg p)) p))
| p_inst p j : proves (core (implies (all p) (rename (instantiate j) p)))
| p_dist p q : proves (core (implies (all (implies (shift p) q)) (implies p (all q))))
| p_refl i : proves (core (equal i i))
| p_mem_left i j k : proves (core (implies (equal i j) (implies (member i k) (member j k))))
| p_mem_right i j k : proves (core (implies (equal i j) (implies (member k i) (member k j))))
| p_eq i j k : proves (core (implies (equal i j) (implies (equal i k) (equal j k))))
| p_mp p q : proves (implication p q) -> proves p -> proves q
| p_gen p : proves p -> proves (universal p)
| p_expand p q : proves p -> erase p = erase q -> proves q.

Definition consistent := ~ proves (core falsity).
End VirtualClasses.
