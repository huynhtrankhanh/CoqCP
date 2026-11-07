From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses Schemata.
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.
Import ListNotations SetTheory VirtualClasses Schemata.
Module UniformSchemata.
Fixpoint statement_eq_dec (x y:statement) {struct x} : {x=y}+{x<>y}
with class_eq_dec (x y:class) {struct x} : {x=y}+{x<>y}.
Proof.
 - decide equality; try apply formula_eq_dec; try apply class_eq_dec.
 - decide equality; try apply Nat.eq_dec; try apply statement_eq_dec.
Defined.
Fixpoint template_eq_dec (x y:formula_template) {struct x} : {x=y}+{x<>y}
with class_template_eq_dec (x y:class_template) {struct x} : {x=y}+{x<>y}.
Proof.
 - decide equality; try apply formula_eq_dec; try apply class_template_eq_dec.
 - decide equality; try apply Nat.eq_dec; try apply class_eq_dec; try apply template_eq_dec.
Defined.

(* A schema certificate is checked once, independently of its eventual class
   arguments. The resulting expression is all an instance needs to evaluate. *)
Inductive symbolic : Type :=
| sym_template (p : formula_template)
| sym_formula (p : formula)
| sym_imp (p q : symbolic)
| sym_all (p : symbolic)
| sym_gen (p : symbolic)
| sym_shift (p : symbolic)
| sym_instantiate (j : nat) (p : symbolic)
| sym_axiom (a : axiom_template)
| sym_axiom_part (a : axiom_template) (side : bool).

Definition axiom_template_eq_dec (a b : axiom_template) : {a = b} + {a <> b}.
Proof. decide equality; try apply Nat.eq_dec; apply template_eq_dec. Defined.
Fixpoint symbolic_eq_dec (a b : symbolic) : {a = b} + {a <> b}.
Proof. decide equality; try apply Nat.eq_dec; try apply template_eq_dec;
  try apply formula_eq_dec; try apply Bool.bool_dec; apply axiom_template_eq_dec. Defined.

Fixpoint sym_concrete (p : formula) : symbolic :=
 match p with
 | implies a b => sym_imp (sym_concrete a) (sym_concrete b)
 | all a => sym_all (sym_concrete a)
 | _ => sym_formula p
 end.
Fixpoint sym_term (p : formula_template) : symbolic :=
 match p with
 | literal_formula f => sym_concrete f
 | template_imp a b => sym_imp (sym_term a) (sym_term b)
 | template_all a => sym_gen (sym_term a)
 | _ => sym_template p
 end.
Fixpoint evaluate (rho : nat -> class) depth (s : symbolic) : formula :=
  match s with
  | sym_template p => instantiate_formula rho depth p
  | sym_formula p => p
  | sym_imp p q => implies (evaluate rho depth p) (evaluate rho depth q)
  | sym_all p => all (evaluate rho depth p)
  | sym_gen p => all (evaluate rho (S depth) p)
  | sym_shift p => shift (evaluate rho depth p)
  | sym_instantiate j p => rename (instantiate j) (evaluate rho depth p)
  | sym_axiom a => match instantiate_axiom rho depth a with
                   | Some ax => axiom_formula ax | None => falsity end
  | sym_axiom_part a side =>
      match instantiate_axiom rho depth a with
      | Some ax => match axiom_formula ax with
                   | implies p q => if side then p else q
                   | _ => falsity end
      | None => falsity end
  end.

Definition symbolic_axiom (a : axiom_template) : option symbolic :=
 let '(template_axiom tag p q r i j k) := a in
 let P := sym_term p in let Q := sym_term q in let R := sym_term r in
 let eq x y := sym_formula (equal x y) in
 let mem x y := sym_formula (member x y) in
 match tag with
 | 0 => Some (sym_imp P (sym_imp Q P))
 | 1 => Some (sym_imp (sym_imp P (sym_imp Q R)) (sym_imp (sym_imp P Q) (sym_imp P R)))
 | 2 => Some (sym_imp (sym_imp (sym_imp P (sym_formula falsity)) (sym_formula falsity)) P)
 | 3 => Some (sym_imp (sym_all P) (sym_instantiate j P))
 | 4 => Some (sym_imp (sym_all (sym_imp (sym_shift P) Q)) (sym_imp P (sym_all Q)))
 | 5 => Some (eq i i)
 | 6 => Some (sym_imp (eq i j) (sym_imp (mem i k) (mem j k)))
 | 7 => Some (sym_imp (eq i j) (sym_imp (mem k i) (mem k j)))
 | 8 => Some (sym_imp (eq i j) (sym_imp (eq i k) (eq j k)))
 | 9 => Some (sym_concrete extensionality)
 | 10 => Some (sym_concrete foundation)
 | 11 => Some (sym_concrete pairing)
 | 12 => Some (sym_concrete union)
 | 13 => Some (sym_concrete power)
 | 14 => Some (sym_concrete infinity)
 | 15 | 16 => Some (sym_imp (sym_axiom_part a true) (sym_axiom_part a false))
 | 17 => Some (sym_concrete choice)
 | _ => None
 end.

Fixpoint certify (c : proof_template) : option symbolic :=
 match c with
 | template_ax a => symbolic_axiom a
 | template_mp ci ca =>
   match certify ci, certify ca with
   | Some (sym_imp p q), Some p' =>
       if symbolic_eq_dec p p' then Some q else None
   | _, _ => None
   end
 | template_gen c => option_map sym_gen (certify c)
 | saved_theorem p _ => Some (sym_concrete p)
 end.

Lemma evaluate_sym_concrete rho depth p :
 evaluate rho depth (sym_concrete p) = p.
Proof. induction p; cbn [sym_concrete evaluate]; congruence. Qed.
Lemma evaluate_sym_term rho depth p :
 evaluate rho depth (sym_term p) = instantiate_formula rho depth p.
Proof.
 revert depth. induction p as [f|p IHp q IHq|p IHp|a b|a b]; intros depth;
 cbn [sym_term evaluate instantiate_formula];
 try rewrite evaluate_sym_concrete; try rewrite IHp, IHq; try rewrite IHp; reflexivity.
Qed.

Lemma symbolic_axiom_matches a s rho depth :
 symbolic_axiom a = Some s ->
 option_map axiom_formula (instantiate_axiom rho depth a) = Some (evaluate rho depth s).
Proof.
 destruct a as [tag p q r i j k].
 do 18 (destruct tag as [|tag]; [cbn [symbolic_axiom]; intro H; inversion H; subst;
    cbn [instantiate_axiom evaluate axiom_formula neg];
    repeat rewrite evaluate_sym_term; repeat rewrite evaluate_sym_concrete; reflexivity|]).
 discriminate.
Qed.

Theorem certify_agrees c s : certify c = Some s ->
 forall rho depth, infer rho depth c = Some (evaluate rho depth s).
Proof.
 revert s. induction c as [a|ci IHi ca IHa|c IH|p checked]; intros s; cbn [certify].
 - intro H. intros. cbn [infer]. now apply symbolic_axiom_matches.
 - destruct (certify ci) as [si|] eqn:Hi; try discriminate.
   destruct si as [t|f|lhs rhs|u|u|u|j u|a|a side]; try discriminate.
   destruct (certify ca) as [sa|] eqn:Ha; try discriminate.
   destruct (symbolic_eq_dec lhs sa) as [Heq|Hneq]; try discriminate.
   intro H; inversion H; subst. intros rho depth.
   cbn [infer]. rewrite (IHi _ eq_refl rho depth), (IHa _ eq_refl rho depth).
   cbn [evaluate]. unfold formula_eqb.
   destruct (formula_eq_dec (evaluate rho depth sa) (evaluate rho depth sa)); congruence.
 - destruct (certify c) as [sc|] eqn:Hc; try discriminate.
   intro H; inversion H; subst. intros rho depth.
   cbn [infer evaluate]. rewrite (IH _ eq_refl rho (S depth)). reflexivity.
 - intro H; inversion H; subst. intros; cbn [infer]. now rewrite evaluate_sym_concrete.
Qed.

Lemma infer_axiom_derivable a : derives (axiom_formula a).
Proof. destruct a; cbn [axiom_formula]; constructor; constructor. Qed.
Theorem infer_sound rho depth cert p : Schemata.infer rho depth cert = Some p -> derives p.
Proof.
  induction cert as [a|ci IHi ca IHa|c IH|q Hq] in depth,p |- *; cbn [Schemata.infer].
  - destruct (Schemata.instantiate_axiom rho depth a) as [a'|]; [|discriminate]. cbn [option_map]. intro H. injection H as <-. apply infer_axiom_derivable.
  - destruct (Schemata.infer rho depth ci) as [f|] eqn:Hi; [|discriminate].
    destruct f as [|i j|i j|a b|a]; try discriminate.
    destruct (Schemata.infer rho depth ca) as [f|] eqn:Ha; [|discriminate].
    unfold formula_eqb. destruct (formula_eq_dec a f) as [Hsame|Hdifferent]; [subst f|discriminate].
    intro H. injection H as <-. eapply d_mp; [exact (IHi depth (implies a b) Hi)|exact (IHa depth a Ha)].
  - destruct (Schemata.infer rho (S depth) c) as [q|] eqn:Hc; [|discriminate].
    cbn [option_map]. intro H. injection H as <-. apply d_gen. exact (IH (S depth) q Hc).
  - intro H. injection H as <-. exact Hq.
Qed.

Theorem certify_sound c s : certify c = Some s ->
 forall rho depth, derives (evaluate rho depth s).
Proof.
 intros H rho depth. eapply (infer_sound rho depth c).
 now apply certify_agrees.
Qed.
End UniformSchemata.
