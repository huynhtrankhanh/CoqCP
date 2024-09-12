From CoqCP Require Import Options.
From stdpp Require Import numbers list.

Inductive Tree :=
| Unit
| Unite (a b : Tree).

Fixpoint leafCount (x : Tree) :=
  match x with
  | Unit => 1
  | Unite a b => leafCount a + leafCount b
  end.

Fixpoint score (x : Tree) :=
  match x with
  | Unit => 0
  | Unite a b => leafCount a + leafCount b + score a + score b
  end.

Fixpoint leftUniteCount (x : Tree) :=
  match x with
  | Unite a _ => 1 + leftUniteCount a
  | Unit => 0
  end.

Fixpoint totalUniteCount (x : Tree) :=
  match x with
  | Unite a b => 1 + totalUniteCount a + totalUniteCount b
  | Unit => 0
  end.

Lemma leftUniteCountLeqTotalUniteCount (x : Tree) : leftUniteCount x <= totalUniteCount x.
Proof.
  induction x as [| a IHa b IHb].
  - easy.
  - simpl. lia.
Qed.

Lemma rewriteRule1 (a b : Tree) : score (Unite Unit (Unite a b)) = score (Unite (Unite a b) Unit).
Proof. simpl. lia. Qed.

Lemma rule1_a (a b : Tree) : leftUniteCount (Unite Unit (Unite a b)) < leftUniteCount (Unite (Unite a b) Unit).
Proof. simpl. lia. Qed.

Lemma rule1_b (a b : Tree) : totalUniteCount (Unite Unit (Unite a b)) = totalUniteCount (Unite (Unite a b) Unit).
Proof. simpl. lia. Qed.

Lemma rule1_c (a b : Tree) : leafCount (Unite Unit (Unite a b)) = leafCount (Unite (Unite a b) Unit).
Proof. simpl. lia. Qed.

Lemma rewriteRule2 (a b c d : Tree) (h : leafCount a >= leafCount d) : score (Unite (Unite a b) (Unite c d)) <= score (Unite (Unite (Unite a b) c) d).
Proof. simpl. lia. Qed.

Lemma rule2_a (a b c d : Tree) : leftUniteCount (Unite (Unite a b) (Unite c d)) < leftUniteCount (Unite (Unite (Unite a b) c) d).
Proof. simpl. lia. Qed.

Lemma rule2_b (a b c d : Tree) : totalUniteCount (Unite (Unite a b) (Unite c d)) = totalUniteCount (Unite (Unite (Unite a b) c) d).
Proof. simpl. lia. Qed.

Lemma rule2_c (a b c d : Tree) : leafCount (Unite (Unite a b) (Unite c d)) = leafCount (Unite (Unite (Unite a b) c) d).
Proof. simpl. lia. Qed.

Lemma rewriteRule3 (a b c d : Tree) (h : leafCount a < leafCount d) : score (Unite (Unite a b) (Unite c d)) < score (Unite (Unite (Unite d c) b) a).
Proof. simpl. lia. Qed.

Lemma rule3_b (a b c d : Tree) : totalUniteCount (Unite (Unite a b) (Unite c d)) = totalUniteCount (Unite (Unite (Unite d c) b) a).
Proof. simpl. lia. Qed.

Lemma rule3_c (a b c d : Tree) : leafCount (Unite (Unite a b) (Unite c d)) = leafCount (Unite (Unite (Unite d c) b) a).
Proof. simpl. lia. Qed.

Lemma oneLeqLeafCount (a : Tree) : 1 <= leafCount a.
Proof. induction a as [| a IHa b IHb]; simpl; now (done || lia). Qed.

Lemma scoreUpperBound (x : Tree) : score x <= (leafCount x) * (leafCount x).
Proof.
  induction x as [| a IHa b IHb].
  - simpl. lia.
  - simpl. pose proof oneLeqLeafCount a. pose proof oneLeqLeafCount b.
    assert (h : forall a b, 1 <= a -> 1 <= b -> a * a + b * b + a + b <= (a + b) * (a + b)).
    { intros x y hx hy. rewrite (ltac:(lia) : (x + y) * (x + y) = x * x + 2 * x * y + y * y).
      pose proof (ltac:(intros; lia) : x + y <= 2 * x * y -> x * x + y * y + x + y <= x * x + 2 * x * y + y * y) as hi.
      apply hi. clear hi. zify.
      pose proof (ltac:(intros; lia) : ((Z.of_nat x * Z.of_nat y - Z.of_nat x) + (Z.of_nat x * Z.of_nat y - Z.of_nat y) >= 0)%Z -> (Z.of_nat x + Z.of_nat y ≤ 2 * Z.of_nat x * Z.of_nat y)%Z) as hi. apply hi. clear hi.
      pose proof (ltac:(intros; lia) : forall (a b : Z), (a * b - b = (a - 1) * b)%Z) as hi. rewrite hi. clear hi.
      pose proof (ltac:(intros; lia) : forall (a b : Z), (a * b - a = (b - 1) * a)%Z) as hi. rewrite hi. clear hi.
      pose proof (ltac:(intros; lia) : forall (a b : Z), (0 <= a)%Z -> (0 <= b)%Z -> (0 <= a * b)%Z) as h.
      pose proof h ((Z.of_nat y - 1)%Z) (Z.of_nat x) ltac:(lia) ltac:(lia).
      pose proof h ((Z.of_nat x - 1)%Z) (Z.of_nat y) ltac:(lia) ltac:(lia).
      lia. }
    pose proof h (leafCount a) (leafCount b) ltac:(assumption) ltac:(assumption). lia.
Qed.
