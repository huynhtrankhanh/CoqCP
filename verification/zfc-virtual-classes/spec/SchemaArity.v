From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses Schemata UniformSchemata.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import SetTheory VirtualClasses Schemata.

Module SchemaArity.

(* Only the supplied prefix of a substitution can affect a template. *)
Fixpoint formula_ext (p : formula_template) : forall rho sigma depth,
  (forall i, i < formula_arity p -> rho i = sigma i) ->
  instantiate_formula rho depth p = instantiate_formula sigma depth p
with class_ext (c : class_template) : forall rho sigma depth,
  (forall i, i < class_arity c -> rho i = sigma i) ->
  instantiate_class rho depth c = instantiate_class sigma depth c.
Proof.
 - destruct p as [f|p q|p|a b|a b]; intros rho sigma depth H; cbn in *; try reflexivity.
   + f_equal; apply formula_ext; intros; apply H; lia.
   + f_equal; apply formula_ext; assumption.
   + rewrite (class_ext a rho sigma depth), (class_ext b rho sigma depth);
       try reflexivity; intros; apply H; lia.
   + rewrite (class_ext a rho sigma depth), (class_ext b rho sigma depth);
       try reflexivity; intros; apply H; lia.
 - destruct c; intros rho sigma depth H; cbn in *; try reflexivity.
   + f_equal. apply H. lia.
   + f_equal. f_equal. apply formula_ext. assumption.
Qed.

Lemma axiom_ext a rho sigma depth :
  (forall i, i < axiom_arity a -> rho i = sigma i) ->
  instantiate_axiom rho depth a = instantiate_axiom sigma depth a.
Proof.
  destruct a as [tag p q r i j k].
  do 18 (destruct tag as [|tag]; [cbn [axiom_arity instantiate_axiom]; intro H;
    try reflexivity; repeat (f_equal; try (apply formula_ext; intros; apply H; lia))|]).
  reflexivity.
Qed.

Theorem infer_ext c rho sigma depth :
  (forall i, i < proof_arity c -> rho i = sigma i) ->
  infer rho depth c = infer sigma depth c.
Proof.
  induction c as [a|ci IHi ca IHa|c IH|p checked] in depth |- *;
    cbn [proof_arity infer]; intro H; try reflexivity.
  - now rewrite (axiom_ext a rho sigma depth H).
  - rewrite IHi, IHa; try reflexivity; intros; apply H; lia.
  - rewrite IH; [reflexivity|exact H].
Qed.

Theorem certified_conclusion_ext c s rho sigma depth :
  UniformSchemata.certify c = Some s ->
  (forall i, i < proof_arity c -> rho i = sigma i) ->
  UniformSchemata.evaluate rho depth s = UniformSchemata.evaluate sigma depth s.
Proof.
  intros Hcert Hprefix.
  pose proof (infer_ext c rho sigma depth Hprefix) as H.
  rewrite (UniformSchemata.certify_agrees c s Hcert rho depth),
          (UniformSchemata.certify_agrees c s Hcert sigma depth) in H.
  now injection H.
Qed.

Theorem certified_argument_default c s (args : list class) d1 d2 depth :
  length args = proof_arity c -> UniformSchemata.certify c = Some s ->
  UniformSchemata.evaluate (fun i => List.nth i args d1) depth s =
  UniformSchemata.evaluate (fun i => List.nth i args d2) depth s.
Proof.
  intros Harity Hcert. eapply certified_conclusion_ext; [exact Hcert|].
  intros i Hi. apply List.nth_indep. lia.
Qed.

End SchemaArity.
