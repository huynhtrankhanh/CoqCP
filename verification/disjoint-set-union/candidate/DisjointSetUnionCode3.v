From CoqCP Require Import DisjointSetUnion Options.
From Submission Require Import DisjointSetUnionCode DisjointSetUnionCode2.
From stdpp Require Import numbers list.

Lemma maxScoreIsAttainable : modelScore (map (fun x => (0%Z, Z.of_nat x)) (seq 1 99)) = 5049%Z.
(* Lazy reduction avoids eagerly expanding all intermediate unary scores in
   the portable runtime; the kernel still checks the same concrete equality. *)
Proof. lazy. reflexivity. Qed.

Lemma maxScoreIsMax (x : list (Z * Z)) (hN : forall a b, In (a, b) x -> Z.le 0 a /\ Z.lt a 256 /\ Z.le 0 b /\ Z.lt b 256) : (modelScore x <= 5049)%Z.
Proof.
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
  rewrite !md in qk.
  apply Nat2Z.inj_le in qk.
  change (Z.of_nat (Z.to_nat (dsuScore nx)) <= 5049)%Z in qk.
  unfold dsuScore in qk |- *.
  rewrite Nat2Z.id in qk. exact qk.
Qed.
