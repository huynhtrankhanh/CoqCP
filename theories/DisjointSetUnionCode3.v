From CoqCP Require Import DisjointSetUnion DisjointSetUnionCode DisjointSetUnionCode2 Options.
From stdpp Require Import numbers list.

Lemma maxScoreIsAttainable : interact state (map (fun x => (0%Z, Z.of_nat x)) (seq 1 99)) = 5049%Z.
Proof. reflexivity. Qed.

Lemma maxScoreIsMax (x : list (Z * Z)) (hN : forall a b, In (a, b) x -> Z.le 0 a /\ Z.lt a 256 /\ Z.le 0 b /\ Z.lt b 256) : (interact state x <= 5049)%Z.
Proof.
  rewrite interactEqualsModelScore; [| assumption].
  unfold modelScore.
  remember (dsuFromInteractions _ _) as nx eqn:xn.
  pose proof maxScore3 nx as qk.
  assert (md : dsuLeafCount nx = 100%Z).
  { subst nx.
    clear.
    remember (repeat _ _) as dsu eqn:hdsu.
    rewrite (ltac:(subst dsu; easy) : 100%Z = dsuLeafCount dsu).
    assert (jh : noIllegalIndices (repeat (Ancestor Unit) 100)).
    { intros aa jj kk.
      rewrite nth_repeat in kk. easy. }
    rewrite <- hdsu in jh.
    clear hdsu. revert dsu jh.
    induction x as [| [a b] tail IH]. { easy. }
    simpl. intros dsu hj.
    case_decide as yu.
    - rewrite IH.
      + rewrite unitePreservesLeafCount. { reflexivity. }
        assumption.
      + apply unitePreservesNoIllegalIndices. exact hj.
    - apply IH. tauto. }
  rewrite !md in qk. simpl in qk. lia.
Qed.
