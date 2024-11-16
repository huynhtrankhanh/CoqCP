From CoqCP Require Import DisjointSetUnionCode Options.
From stdpp Require Import numbers list.

Lemma maxScoreIsAttainable : interact state (map (fun x => (0%Z, Z.of_nat x)) (seq 1 99)) = 5049%Z.
Proof. reflexivity. Qed.
