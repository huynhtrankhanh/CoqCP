From CoqCP Require Import Options.

Require Export Trusted.Spec.
From Stdlib Require Import Arith PeanoNat Lia List Sorting.Permutation.
Import ListNotations.

(* Query k labels zero-based input index x with its k-th binary digit. *)

Fixpoint decode (rounds x : nat) :=
  match rounds with
  | 0 => 0
  | S k => decode k x + bit k x * 2^k
  end.
(* The solver consumes only the ten replies, without access to the permutation. *)
Fixpoint decode_replies (rounds index : nat) (replies : list (list nat)) :=
  match rounds with
  | 0 => 0
  | S k => decode_replies k index replies + nth index (nth k replies []) 0 * 2^k
  end.
Definition solve_replies (n : nat) (replies : list (list nat)) :=
  map (fun i => S (decode_replies 10 i replies)) (seq 0 n).
Definition transcript (a : list nat) := map (response a) (seq 0 10).
Definition solve (a : list nat) := solve_replies (length a) (transcript a).

Lemma power_positive k : 0 < 2^k.
Proof. pose proof (Nat.pow_nonzero 2 k ltac:(lia)). lia. Qed.

Lemma bit_binary k x : bit k x = 0 \/ bit k x = 1.
Proof. unfold bit. pose proof (Nat.mod_upper_bound (x / 2^k) 2 ltac:(lia)). lia. Qed.

Lemma decode_mod rounds x : decode rounds x = x mod 2^rounds.
Proof.
  induction rounds as [| k IH].
  - cbn [decode Nat.pow]. symmetry. apply Nat.mod_1_r.
  - cbn [decode]. rewrite IH. unfold bit.
    replace (2 ^ S k) with (2^k * 2) by (cbn [Nat.pow]; lia).
    rewrite Nat.Div0.mod_mul_r.
    lia.
Qed.

Lemma decode_replies_correct rounds a index
  (hr : rounds <= 10) (hi : index < length a) :
  decode_replies rounds index (transcript a) = decode rounds (nth index a 1 - 1).
Proof.
  induction rounds as [| k IH]; [reflexivity |].
  cbn [decode_replies decode]. rewrite IH by lia.
  unfold transcript.
  rewrite (nth_indep _ [] (response a 0)) by
    (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia.
  unfold response.
  rewrite (nth_indep _ 0 (bit k (1-1))) by (rewrite length_map; exact hi).
  cbn [Nat.add]. rewrite (map_nth (fun x => bit k (x-1)) a 1 index). reflexivity.
Qed.

Lemma enumerate_list a : map (fun i => nth i a 1) (seq 0 (length a)) = a.
Proof.
  apply nth_ext with (d := 1) (d' := 1).
  - rewrite length_map, length_seq. reflexivity.
  - intros i hi. rewrite length_map, length_seq in hi.
    rewrite (nth_indep _ 1 (nth 0 a 1)) by (rewrite length_map, length_seq; exact hi).
    rewrite (map_nth (fun i => nth i a 1) (seq 0 (length a)) 0 i).
    rewrite seq_nth by exact hi. reflexivity.
Qed.

Lemma solve_is_decode a : solve a = map (fun x => S (decode 10 (x-1))) a.
Proof.
  unfold solve, solve_replies.
  rewrite <- (enumerate_list a) at 2.
  rewrite map_map. apply map_ext_in. intros i hi.
  apply in_seq in hi. cbv beta. rewrite decode_replies_correct by lia. reflexivity.
Qed.

Lemma query_valid n k : length (query n k) = n /\
  Forall (fun b => b = 0 \/ b = 1) (query n k).
Proof.
  split.
  - unfold query. rewrite length_map, length_seq. reflexivity.
  - unfold query. apply Forall_forall. intros b hb.
    apply in_map_iff in hb. destruct hb as (x & <- & _). apply bit_binary.
Qed.

(* This is precisely the grader's b[a_i], including the one-based indexing. *)
Lemma response_is_permuted_query n a k (h : valid n a) :
  response a k = map (fun x => nth (x-1) (query n k) 0) a.
Proof.
  apply map_ext_in. intros x hx.
  destruct h as [_ hp].
  assert (hr : 1 <= x < 1+n).
  { apply in_seq. eapply Permutation_in; [exact hp | exact hx]. }
  unfold query. rewrite (nth_indep _ 0 (bit k 0)) by
    (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Theorem solve_correct n a (h : valid n a) :
  solve a = a /\ length a = n /\
  (forall k, k < 10 -> length (query n k) = n /\
    Forall (fun b => b = 0 \/ b = 1) (query n k)) /\
  length (seq 0 10) <= 10.
Proof.
  destruct h as [hn hp]. split.
  - rewrite solve_is_decode. rewrite <- (map_id a) at 2. apply map_ext_in.
    intros x hx.
    assert (hr : 1 <= x < 1+n).
    { apply in_seq. eapply Permutation_in; [exact hp | exact hx]. }
    rewrite decode_mod. change (S ((x-1) mod 1024) = x).
    rewrite Nat.mod_small by lia. lia.
  - split.
    + pose proof (Permutation_length hp). rewrite length_seq in *. assumption.
    + split.
      * intros k _. apply query_valid.
      * rewrite length_seq. lia.
Qed.

Print Assumptions solve_correct.

Theorem interaction_correct n a (h : valid n a) :
  solve_replies n
    (map (fun k => map (fun x => nth (x-1) (query n k) 0) a) (seq 0 10)) = a.
Proof.
  destruct (solve_correct n a h) as [answer [hlen _]].
  unfold solve in answer. rewrite hlen in answer.
  replace (map (fun k => map (fun x => nth (x-1) (query n k) 0) a) (seq 0 10))
    with (transcript a); [exact answer |].
  unfold transcript. apply map_ext. intro k. apply response_is_permuted_query. exact h.
Qed.
Print Assumptions interaction_correct.
