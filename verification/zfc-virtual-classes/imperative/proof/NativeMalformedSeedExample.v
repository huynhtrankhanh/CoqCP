From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Import ListNotations.
Open Scope Z_scope.
Module NativeMalformedSeedExample.
Definition initial input : Machine := {| memory := arrays _ environment1; stdin := input; stdout := [] |}.
Definition observed input :=
 match execObserved (funcdef_0__main (fun x => match x with end) (fun x => match x with end)) (initial input,[]) with
 | Some (tt,(s,trace)) => Some (stdout s, map flushedOutput trace, stdin s)
 | None => None end.
Theorem missing_seed : observed [] = Some ([83;69;69;68;10;69;82;82;10], [[83;69;69;68;10];[83;69;69;68;10;69;82;82;10]], []).
Proof. vm_compute. reflexivity. Qed.
Theorem malformed_first : forall tail, observed (120::32::tail) = Some ([83;69;69;68;10;69;82;82;10], [[83;69;69;68;10];[83;69;69;68;10;69;82;82;10]], tail).
Proof. intros tail. vm_compute. reflexivity. Qed.
Theorem malformed_second : forall tail, observed (48::32::120::32::tail) = Some ([83;69;69;68;10;69;82;82;10], [[83;69;69;68;10];[83;69;69;68;10;69;82;82;10]], tail).
Proof. intros tail. vm_compute. reflexivity. Qed.
Theorem overflow_first : forall tail, observed ([49;56;52;52;54;55;52;52;48;55;51;55;48;57;53;53;49;54;49;54;32]++tail) = Some ([83;69;69;68;10;69;82;82;10], [[83;69;69;68;10];[83;69;69;68;10;69;82;82;10]], tail).
Proof. intros tail. vm_compute. reflexivity. Qed.
Theorem malformed_command : forall tail, observed ([48;32;48;10;120;32]++tail) = Some ([83;69;69;68;10;82;69;65;68;89;10;69;82;82;10], [[83;69;69;68;10];[83;69;69;68;10;82;69;65;68;89;10];[83;69;69;68;10;82;69;65;68;89;10;69;82;82;10]], tail).
Proof. intros tail. vm_compute. reflexivity. Qed.
Theorem nondigit_first : forall ch tail, 0<=ch<=255 -> (ch<48 \/ 57<ch) -> ch<>32 -> ch<>9 -> ch<>10 -> ch<>13 -> observed (ch::32::tail) = Some ([83;69;69;68;10;69;82;82;10], [[83;69;69;68;10];[83;69;69;68;10;69;82;82;10]], tail).
Proof. intros ch tail Hrange Hbad H32 H9 H10 H13. remember (Z.to_nat ch) as n eqn:Hn. assert (ch=Z.of_nat n) by (subst n; symmetry; apply Z2Nat.id; lia). subst ch. clear Hn. let rec cases x count := lazymatch count with O=>lia | S ?rest=>destruct x as [|x];[try lia;vm_compute;reflexivity|cases x rest] end in cases n 256%nat. Qed.
Theorem nondigit_second : forall ch tail, 0<=ch<=255 -> (ch<48 \/ 57<ch) -> ch<>32 -> ch<>9 -> ch<>10 -> ch<>13 -> observed (48::32::ch::32::tail) = Some ([83;69;69;68;10;69;82;82;10], [[83;69;69;68;10];[83;69;69;68;10;69;82;82;10]], tail).
Proof. intros ch tail Hrange Hbad H32 H9 H10 H13. remember (Z.to_nat ch) as n eqn:Hn. assert (ch=Z.of_nat n) by (subst n; symmetry; apply Z2Nat.id; lia). subst ch. clear Hn. let rec cases x count := lazymatch count with O=>lia | S ?rest=>destruct x as [|x];[try lia;vm_compute;reflexivity|cases x rest] end in cases n 256%nat. Qed.
Theorem nondigit_command : forall ch tail, 0<=ch<=255 -> (ch<48 \/ 57<ch) -> ch<>32 -> ch<>9 -> ch<>10 -> ch<>13 -> observed (48::32::48::10::ch::32::tail) = Some ([83;69;69;68;10;82;69;65;68;89;10;69;82;82;10], [[83;69;69;68;10];[83;69;69;68;10;82;69;65;68;89;10];[83;69;69;68;10;82;69;65;68;89;10;69;82;82;10]], tail).
Proof. intros ch tail Hrange Hbad H32 H9 H10 H13. remember (Z.to_nat ch) as n eqn:Hn. assert (ch=Z.of_nat n) by (subst n; symmetry; apply Z2Nat.id; lia). subst ch. clear Hn. let rec cases x count := lazymatch count with O=>lia | S ?rest=>destruct x as [|x];[try lia;vm_compute;reflexivity|cases x rest] end in cases n 256%nat. Qed.
End NativeMalformedSeedExample.
