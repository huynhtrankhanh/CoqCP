From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses Schemata.

Module SchemataSoundness.
Import SetTheory VirtualClasses Schemata.

Theorem instance_sound rho depth c p : infer rho depth c = Some p -> derives p.
Proof.
  induction c as [a |ci IHi ca IHa |c IH |q Hq] in depth, p |- *; cbn [infer].
  - destruct (instantiate_axiom rho depth a) as [a' |]; [|discriminate].
    cbn [option_map]. intro Heq. injection Heq as <-.
    destruct a'; cbn [axiom_formula]; constructor; constructor.
  - destruct (infer rho depth ci) as [f |] eqn:Hi; [|discriminate].
    destruct f as [|i j|i j|a b|a]; try discriminate.
    destruct (infer rho depth ca) as [f |] eqn:Ha; [|discriminate].
    destruct (formula_eqb a f) eqn:Heq; [|discriminate].
    unfold formula_eqb in Heq. destruct (formula_eq_dec a f) as [Hsame |Hdifferent]; [subst f |discriminate]. intro Hout. injection Hout as <-.
    eapply d_mp; [exact (IHi depth (implies a b) Hi) |exact (IHa depth a Ha)].
  - destruct (infer rho (S depth) c) as [q |] eqn:Hc; [|discriminate].
    cbn [option_map]. intro Heq. injection Heq as <-. apply d_gen. exact (IH (S depth) q Hc).
  - intro Heq. injection Heq as <-. exact Hq.
Qed.

Example class_parameters_are_not_captured :
  instantiate_formula (fun _ => set 5) 0
    (template_all (template_member (literal_class (set 0)) (metavariable 0))) =
  all (member 0 6).
Proof. reflexivity. Qed.
End SchemataSoundness.
