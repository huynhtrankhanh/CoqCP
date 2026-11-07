From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses Schemata.
Import SetTheory VirtualClasses Schemata.

(* An existing proof template can have a valid instance without being uniform.
   A statement-only instantiator must reject this certificate before naming it. *)
Module UniformSchemaRegression.
Definition phi := template_equal (metavariable 0) (metavariable 1).
Definition psi := literal_formula (equal 0 0).
Definition certificate :=
 template_mp (template_ax (template_axiom 0 phi psi psi 0 0 0))
             (template_ax (template_axiom 5 psi psi psi 0 0 0)).
Definition same (_:nat) := set 0.
Definition different (i:nat) := if Nat.eqb i 0 then set 0 else set 1.
Example matching_instance : infer same 0 certificate = Some (implies (equal 0 0) (equal 0 0)).
Proof. vm_compute. reflexivity. Qed.
Example mismatching_instance : infer different 0 certificate = None.
Proof. vm_compute. reflexivity. Qed.
End UniformSchemaRegression.
