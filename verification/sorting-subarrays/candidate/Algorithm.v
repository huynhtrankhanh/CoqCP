From CoqCP Require Import Options.
From Stdlib Require Import Lists.List Lia ZArith.ZArith.
From Submission Require Import Simulation Threshold Search.
Require Trusted.Spec.

Module Algorithm.
  Definition program (a : list Z) (k : nat) (qs : list Trusted.Spec.query) : Z :=
    search 31 (-1000000000)%Z 1000000000%Z (decide a k qs).

  Theorem correct : Trusted.Spec.required_solver program.
  Proof.
    intros a k qs [Hn [Hk [Hq [Ha Hqs]]]]. unfold program.
    apply search_correct.
    - intro m. now apply decide_correct.
    - assert (Hb : Forall (fun x => (-1000000000 <= x <= 1000000000)%Z) a).
      { rewrite List.Forall_forall in Ha |- *. intros x Hx. exact (proj1 (Ha x Hx)). }
      pose proof (execute_bounds _ _ _ qs Hb) as Hout.
      rewrite List.Forall_forall in Hout. apply Hout.
      apply nth_In. rewrite execute_length by exact Hqs. lia.
    - vm_compute. reflexivity.
  Qed.
End Algorithm.
