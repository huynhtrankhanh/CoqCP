From CoqCP Require Import Options.
From Stdlib Require Import Arith.PeanoNat Lists.List.

(* A first-order set-theory language. Indices are de Bruijn indices; free
   variables are parameters, not metavariables which may be captured. *)
Module SetTheory.
Inductive formula : Type :=
| falsity
| equal (i j : nat)
| member (i j : nat)
| implies (p q : formula)
| all (p : formula).

Definition neg p := implies p falsity.
Definition conj p q := neg (implies p (neg q)).
Definition disj p q := implies (neg p) q.
Definition iff p q := conj (implies p q) (implies q p).
Definition ex p := neg (all (neg p)).

Definition up (rho : nat -> nat) (i : nat) :=
  match i with 0 => 0 | S n => S (rho n) end.
Fixpoint rename (rho : nat -> nat) (p : formula) : formula :=
  match p with
  | falsity => falsity
  | equal i j => equal (rho i) (rho j)
  | member i j => member (rho i) (rho j)
  | implies p q => implies (rename rho p) (rename rho q)
  | all p => all (rename (up rho) p)
  end.
Definition shift := rename S.
Definition instantiate (j i : nat) := match i with 0 => j | S n => n end.

Definition formula_eq_dec : forall p q : formula, {p = q} + {p <> q}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition formula_eqb p q := if formula_eq_dec p q then true else false.

(* Nonlogical axiom schemas. Pairing, Union and Power use the bounding
   versions: Separation recovers their exact versions. *)
Definition extensionality :=
  implies (all (iff (member 0 1) (member 0 2))) (equal 0 1).
Definition foundation :=
  implies (ex (member 0 1))
    (ex (conj (member 0 1) (all (implies (member 0 1) (neg (member 0 2)))))).
Definition pairing := ex (conj (member 1 0) (member 2 0)).
Definition union :=
  ex (all (all (implies (member 0 1) (implies (member 1 3) (member 0 2))))).
Definition power :=
  ex (all (implies (all (implies (member 0 1) (member 0 3))) (member 0 1))).
Definition infinity :=
  ex (conj (ex (conj (member 0 1) (all (neg (member 0 1)))))
    (all (implies (member 0 1)
      (ex (conj (member 0 2)
        (all (iff (member 0 1) (disj (member 0 2) (equal 0 2))))))))).

Definition sep_rename i := match i with 0 => 0 | S n => S (S n) end.
Definition separation p :=
  ex (all (iff (member 0 1) (conj (member 0 2) (rename sep_rename p)))).
Definition repl_left i :=
  match i with 0 => 2 | 1 => 1 | S (S n) => S (S (S n)) end.
Definition repl_right i :=
  match i with 0 => 2 | 1 => 0 | S (S n) => S (S (S n)) end.
Definition repl_image i :=
  match i with 0 => 0 | 1 => 1 | S (S n) => S (S (S n)) end.
Definition replacement p :=
  implies
    (all (implies (member 0 1) (all (all
      (implies (rename repl_left p) (implies (rename repl_right p) (equal 1 0)))))))
    (ex (all (implies (ex (conj (member 0 3) (rename repl_image p))) (member 0 1)))).

(* Choice in the disjoint-family formulation. In a pairwise disjoint family
   of nonempty sets, a transversal meets every member in exactly one element.
   All free variables in these three formulas denote the family a. *)
Definition nonempty_members := all (implies (member 0 1) (ex (member 0 1))).
Definition disjoint_members := all (all
  (implies (member 1 2) (implies (member 0 2)
    (implies (ex (conj (member 0 2) (member 0 1))) (equal 1 0))))).
Definition transversal := ex (all (implies (member 0 2)
  (ex (conj (member 0 1) (conj (member 0 2)
    (all (implies (member 0 2) (implies (member 0 3) (equal 0 1))))))))).
Definition choice := implies (conj nonempty_members disjoint_members) transversal.

Inductive set_axiom : formula -> Prop :=
| ax_ext : set_axiom extensionality
| ax_found : set_axiom foundation
| ax_pair : set_axiom pairing
| ax_union : set_axiom union
| ax_power : set_axiom power
| ax_infinity : set_axiom infinity
| ax_separation p : set_axiom (separation p)
| ax_replacement p : set_axiom (replacement p)
| ax_choice : set_axiom choice.

(* Classical Hilbert predicate calculus with equality. Its axioms are data in
   the object theory, not assumptions introduced into Rocq's metatheory. *)
Inductive derives : formula -> Prop :=
| d_set p : set_axiom p -> derives p
| d_k p q : derives (implies p (implies q p))
| d_s p q r : derives (implies (implies p (implies q r))
                            (implies (implies p q) (implies p r)))
| d_dne p : derives (implies (neg (neg p)) p)
| d_inst p j : derives (implies (all p) (rename (instantiate j) p))
| d_dist p q : derives (implies (all (implies (shift p) q)) (implies p (all q)))
| d_refl i : derives (equal i i)
| d_mem_left i j k : derives (implies (equal i j) (implies (member i k) (member j k)))
| d_mem_right i j k : derives (implies (equal i j) (implies (member k i) (member k j)))
| d_eq i j k : derives (implies (equal i j) (implies (equal i k) (equal j k)))
| d_mp p q : derives (implies p q) -> derives p -> derives q
| d_gen p : derives p -> derives (all p).



(* Finite, explicit schema witnesses for an executable proof checker. *)
Inductive axiom : Type :=
| K (p q : formula) | Srule (p q r : formula) | DNE (p : formula)
| Inst (p : formula) (j : nat) | Dist (p q : formula)
| Refl (i : nat) | MemLeft (i j k : nat) | MemRight (i j k : nat)
| EqTrans (i j k : nat)
| Ext | Found | Pair | Union | Power | Infinity
| Separation (p : formula) | Replacement (p : formula) | Choice.
Definition axiom_formula a :=
  match a with
  | K p q => implies p (implies q p)
  | Srule p q r => implies (implies p (implies q r)) (implies (implies p q) (implies p r))
  | DNE p => implies (neg (neg p)) p
  | Inst p j => implies (all p) (rename (instantiate j) p)
  | Dist p q => implies (all (implies (shift p) q)) (implies p (all q))
  | Refl i => equal i i
  | MemLeft i j k => implies (equal i j) (implies (member i k) (member j k))
  | MemRight i j k => implies (equal i j) (implies (member k i) (member k j))
  | EqTrans i j k => implies (equal i j) (implies (equal i k) (equal j k))
  | Ext => extensionality | Found => foundation | Pair => pairing
  | Union => union | Power => power | Infinity => infinity
  | Separation p => separation p | Replacement p => replacement p | Choice => choice
  end.
End SetTheory.
