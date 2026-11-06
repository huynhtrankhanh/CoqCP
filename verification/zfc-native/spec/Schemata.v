From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses.
From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations SetTheory VirtualClasses.

Module Schemata.
Definition shifted_class depth c :=
  match c with
  | set i => set (depth + i)
  | abstract p => abstract (core (rename (up (fun i => depth + i)) (erase p)))
  end.

Inductive formula_template :=
| literal_formula (p : formula)
| template_imp (p q : formula_template)
| template_all (p : formula_template)
| template_equal (a b : class_template)
| template_member (a b : class_template)
with class_template :=
| literal_class (c : class)
| metavariable (index : nat)
| template_abstract (p : formula_template).

Fixpoint instantiate_formula (rho : nat -> class) depth p : formula :=
  match p with
  | literal_formula p => p
  | template_imp p q => implies (instantiate_formula rho depth p) (instantiate_formula rho depth q)
  | template_all p => all (instantiate_formula rho (S depth) p)
  | template_equal a b => erase (class_equal (instantiate_class rho depth a) (instantiate_class rho depth b))
  | template_member a b => erase (class_member (instantiate_class rho depth a) (instantiate_class rho depth b))
  end
with instantiate_class (rho : nat -> class) depth c : class :=
  match c with
  | literal_class c => c
  | metavariable i => shifted_class depth (rho i)
  | template_abstract p => abstract (core (instantiate_formula rho (S depth) p))
  end.

Fixpoint formula_arity p := match p with
| literal_formula _ => 0
| template_imp p q => Nat.max (formula_arity p) (formula_arity q)
| template_all p => formula_arity p
| template_equal a b | template_member a b => Nat.max (class_arity a) (class_arity b)
end
with class_arity c := match c with
| literal_class _ => 0 | metavariable i => S i
| template_abstract p => formula_arity p end.

Inductive axiom_template :=
| template_axiom (tag : nat) (p q r : formula_template) (i j k : nat).
Definition instantiate_axiom rho depth a : option axiom :=
  let '(template_axiom tag p q r i j k) := a in
  let fp := instantiate_formula rho depth p in
  let fq := instantiate_formula rho depth q in
  let fr := instantiate_formula rho depth r in
  match tag with
  | 0 => Some (K fp fq) | 1 => Some (Srule fp fq fr) | 2 => Some (DNE fp)
  | 3 => Some (Inst fp j) | 4 => Some (Dist fp fq) | 5 => Some (Refl i)
  | 6 => Some (MemLeft i j k) | 7 => Some (MemRight i j k) | 8 => Some (EqTrans i j k)
  | 9 => Some Ext | 10 => Some Found | 11 => Some Pair | 12 => Some Union
  | 13 => Some Power | 14 => Some Infinity | 15 => Some (Separation fp)
  | 16 => Some (Replacement fp) | 17 => Some Choice | _ => None
  end.

Inductive proof_template :=
| template_ax (a : axiom_template)
| template_mp (implication antecedent : proof_template)
| template_gen (p : proof_template)
| saved_theorem (p : formula) (checked : derives p).

Fixpoint infer rho depth c : option formula :=
  match c with
  | template_ax a => option_map axiom_formula (instantiate_axiom rho depth a)
  | template_mp ci ca =>
      match infer rho depth ci, infer rho depth ca with
      | Some (implies p q), Some p' => if formula_eqb p p' then Some q else None
      | _, _ => None
      end
  | template_gen c => option_map all (infer rho (S depth) c)
  | saved_theorem p _ => Some p
  end.

Definition axiom_arity a := let '(template_axiom tag p q r _ _ _) := a in
  match tag with
  | 0 | 4 => Nat.max (formula_arity p) (formula_arity q)
  | 1 => Nat.max (formula_arity p) (Nat.max (formula_arity q) (formula_arity r))
  | 2 | 3 | 15 | 16 => formula_arity p | _ => 0 end.
Fixpoint proof_arity c := match c with
| template_ax a => axiom_arity a
| template_mp a b => Nat.max (proof_arity a) (proof_arity b)
| template_gen c => proof_arity c | saved_theorem _ _ => 0 end.

End Schemata.
