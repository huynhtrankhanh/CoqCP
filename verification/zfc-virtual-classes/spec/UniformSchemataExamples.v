From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses Schemata UniformSchemata UniformSchemaRegression.
Import SetTheory VirtualClasses Schemata UniformSchemata UniformSchemaRegression.

(* Accidental equality in one substitution does not certify a schema. *)
Example accidental_match_rejected : certify certificate = None.
Proof. vm_compute. reflexivity. Qed.

(* The consequent contains two freely chosen class metavariables. *)
Definition uniformly_valid :=
 template_mp (template_ax (template_axiom 0 psi phi phi 0 0 0))
             (template_ax (template_axiom 5 psi psi psi 0 0 0)).
Example uniformly_valid_certified :
 certify uniformly_valid = Some (sym_imp (sym_template phi) (sym_formula (equal 0 0))).
Proof. vm_compute. reflexivity. Qed.

Example arbitrary_class_arguments (rho : nat -> class) depth :
 derives (implies (instantiate_formula rho depth phi) (equal 0 0)).
Proof.
 pose proof (certify_sound _ _ uniformly_valid_certified rho depth) as H.
 exact H.
Qed.

(* Implications in template arguments and saved concrete theorems are exposed
   to the uniform MP check rather than treated as opaque leaves. *)
Definition implication_template := template_imp phi (template_imp psi phi).
Definition template_imp_mp :=
 template_mp (template_ax (template_axiom 0 implication_template psi psi 0 0 0))
             (template_ax (template_axiom 0 phi psi psi 0 0 0)).
Example template_imp_accepted : exists s, certify template_imp_mp = Some s.
Proof. eexists. vm_compute. reflexivity. Qed.
Definition saved_mp :=
 template_mp (saved_theorem _ (d_k (equal 0 0) (equal 0 0)))
             (template_ax (template_axiom 5 psi psi psi 0 0 0)).
Example saved_implication_accepted : exists s, certify saved_mp = Some s.
Proof. eexists. vm_compute. reflexivity. Qed.

(* Every ZFC axiom here has an exposed top-level implication; in particular,
   Separation and Replacement retain a symbolic parameter in their parts. *)
Definition has_symbolic_implication tag :=
 match symbolic_axiom (template_axiom tag phi psi psi 0 0 0) with
 | Some (sym_imp _ _) => true | _ => false end.
Example zfc_axiom_implications_exposed :
 has_symbolic_implication 9 = true /\ has_symbolic_implication 10 = true /\
 has_symbolic_implication 11 = true /\ has_symbolic_implication 12 = true /\
 has_symbolic_implication 13 = true /\ has_symbolic_implication 14 = true /\
 has_symbolic_implication 15 = true /\ has_symbolic_implication 16 = true /\
 has_symbolic_implication 17 = true.
Proof. vm_compute. repeat split. Qed.

Print Assumptions certify_agrees.
Print Assumptions certify_sound.
Print Assumptions arbitrary_class_arguments.
