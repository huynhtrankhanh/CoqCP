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

Fixpoint constructTree (n : nat) : Tree :=
  match n with
  | O => Unit
  | S n => Unite (constructTree n) Unit
  end.

Lemma constructTreeSize (n : nat) : leafCount (constructTree n) = S n.
Proof.
  induction n as [| n IH].
  - easy.
  - simpl. lia.
Qed.

Fixpoint generateProduct {A B : Type} (a : list A) (b : list B) : list (A * B) :=
  match a with
  | [] => []
  | head :: tail => map (fun x => (head, x)) b ++ generateProduct tail b
  end.

Lemma inProductList {A B : Type} (a : list A) (b : list B) (elementA : A) (hA : In elementA a) (elementB : B) (hB : In elementB b) : In (elementA, elementB) (generateProduct a b).
Proof.
  induction a as [| head tail IH].
  - simpl in hA. exfalso. exact hA.
  - destruct hA as [hL | hR].
    + subst head. simpl. apply in_or_app. left. clear IH.
      induction b as [| head1 tail1 IH1]; [(simpl in hB); exfalso; exact hB |]. simpl. destruct hB as [h1 | h2]. { left. rewrite h1. trivial. } right. exact (IH1 h2).
    + simpl. apply in_or_app. right. exact (IH hR).
Qed.

Lemma inProductList2 {A B : Type} (a : list A) (b : list B) (elementA : A) (elementB : B) (h : In (elementA, elementB) (generateProduct a b)) : In elementA a /\ In elementB b.
Proof.
  induction a as [| head tail IH].
  - simpl in h. exfalso. exact h.
  - simpl in h. rewrite in_app_iff in h. destruct h as [h | h].
    + clear IH. induction b as [| head1 tail1 IH1]. { simpl in h. exfalso. exact h. } simpl in h. destruct h as [h | h]. { rewrite pair_eq in h. destruct h as [hA hB]. subst head. subst head1. split; simpl; left; trivial. } pose proof IH1 h as [hA hB]. split. { assumption. } simpl. right. assumption.
    + pose proof IH h as [hA hB]. split. { simpl. right. assumption. } assumption.
Qed.

Lemma enumerateTrees (n : nat) : { x : list Tree | forall tree : Tree, leafCount tree = n <-> In tree x }.
Proof.
  induction (lt_wf n) as [n _ IH].
  - destruct (decide (n = 0)) as [h | h].
    + apply (exist _ []). subst n. intros tree. pose proof oneLeqLeafCount tree. simpl. split; lia.
    + destruct (decide (n = 1)) as [h1 | h1].
      * subst n. apply (exist _ [Unit]). intros tree.
        destruct tree as [| tree1 tree2]. { simpl. intuition tauto. }
        simpl. pose proof oneLeqLeafCount tree1. pose proof oneLeqLeafCount tree2. split. { lia. } intro h1. destruct h1 as [h1 | h1]. { pose proof (ltac:(easy) : Unit <> Unite tree1 tree2) h1. exfalso. assumption. } exfalso. assumption.
      * assert (h2 : forall (leftSize : nat) (hLeft : leftSize < n) (hLeft2 : 0 < leftSize), {x : list Tree | forall tree : Tree, (match tree with | Unit => False | Unite a b => leafCount a <= leftSize /\ leafCount b = n - leafCount a end) <-> In tree x}).
        { intros left hLeft hLeft2.
          induction left as [| left IH2]; [lia |].
          pose proof IH (S left) ltac:(lia) as [a ha].
          pose proof IH (n - S left) ltac:(lia) as [b hb].
          destruct (decide (left = 0)) as [h2 | h2].
          - apply (exist _ (map (fun (x : Tree * Tree) => let (a, b) := x in Unite a b) (generateProduct a b))).
            intros [| a1 b1]. { split; intro hTree. { exfalso. exact hTree. } remember (generateProduct a b) as l eqn:hl. induction l as [| head tail IH3] in hTree |-. { simpl in hTree. exact hTree. } destruct hTree as [hTree | hTree]. { destruct head as [aa bb]. exact ((ltac:(easy) : Unite aa bb <> Unit) hTree). } tauto. }
            pose proof oneLeqLeafCount a1. rewrite (ltac:(lia) : leafCount a1 <= S left <-> leafCount a1 = S left).
            split.
            { intros [hTree1 hTree2].
              pose proof in_map (fun (x : Tree * Tree) => let (a, b) := x in Unite a b) (generateProduct a b) (a1, b1) as step. simpl in step. apply step. apply inProductList. { rewrite <- ha. assumption. } rewrite <- hb. lia. }
            { rewrite in_map_iff. intros [[aa bb] [h4 h3]].
              pose proof inProductList2 a b aa bb h3 as [hIn1 hIn2]. rewrite <- ha in hIn1. injection h4. intros hbb haa. subst aa bb. split. { exact hIn1. } pose proof hb b1 as hb1. rewrite hIn1, hb1. assumption. }
          - pose proof IH2 ltac:(lia) ltac:(lia) as [previous hPrevious]. apply (exist _ (map (fun (x : Tree * Tree) => let (a, b) := x in Unite a b) (generateProduct a b) ++ previous)). intros [| aa bb].
            + split. { tauto. } intro h3. pose proof in_app_or _ _ _ h3 as [H | H].
              * remember (generateProduct a b) as l eqn:hl. induction l as [| head tail IH3] in H |-. { simpl in H. exact H. }
                destruct H as [H | H]. { destruct head as [aa bb]. exact ((ltac:(easy) : Unite aa bb <> Unit) H). } exact (IH3 H).
              * pose proof hPrevious Unit as [_ step]. exact (step H).
            + split.
              * intros [haa hbb]. apply in_or_app.
                pose proof (ltac:(lia) : leafCount aa <= left \/ leafCount aa = S left) as [hIf | hIf].
                { right. rewrite <- (hPrevious (Unite aa bb)). simpl. lia. }
                left. rewrite in_map_iff. exists (aa, bb). split. { trivial. } apply inProductList. { rewrite <- ha. lia. } { rewrite <- hb. lia. }
              * intro hmap. pose proof in_app_or _ _ _ hmap as [H | H].
                { rewrite in_map_iff in H. destruct H as [[a1 b1] [hinj hin]]. injection hinj. intros hbb haa. subst bb aa. pose proof inProductList2 _ _ _ _ hin as [hina hinb]. rewrite <- ha in hina. split. { lia. } rewrite hina. rewrite hb. exact hinb. }
                pose proof hPrevious (Unite aa bb) as step. simpl in step. rewrite <- step in H. lia. }
          pose proof h2 (n - 1) ltac:(lia) ltac:(lia) as [l hl].
          apply (exist _ l).