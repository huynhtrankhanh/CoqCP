From CoqCP Require Import Options.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia ZArith.ZArith.
Open Scope Z_scope.

(* Fixed-depth lower-bound search. At a singleton interval every subsequent
   predicate call is false, so the same answer is retained. *)
Fixpoint search (fuel : nat) (lo hi : Z) (test : Z -> bool) : Z :=
  match fuel with
  | O => lo
  | S fuel' =>
      let mid := (lo+hi)/2 in
      if test mid then search fuel' (mid+1) hi test
      else search fuel' lo mid test
  end.

Lemma search_correct fuel lo hi test answer :
  (forall m, test m = Z.ltb m answer) ->
  lo <= answer <= hi -> hi-lo < 2 ^ Z.of_nat fuel ->
  search fuel lo hi test = answer.
Proof.
  intros Htest. revert lo hi.
  induction fuel as [|fuel IH]; intros lo hi Hrange Hwidth.
  - simpl in *. lia.
  - simpl search. rewrite Htest.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hwidth by lia.
    set (mid := (lo+hi)/2).
    assert (Hmid : 2*mid <= lo+hi < 2*mid+2).
    { unfold mid. pose proof (Z.div_mod (lo+hi) 2 ltac:(lia)) as Hd.
      pose proof (Z.mod_pos_bound (lo+hi) 2 ltac:(lia)) as Hm. lia. }
    destruct (mid <? answer) eqn:E.
    + apply Z.ltb_lt in E. apply IH; lia.
    + apply Z.ltb_ge in E. apply IH; lia.
Qed.
