From CoqCP Require Import Options Imperative Execution.
From Trusted Require Import SetTheory.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash HashTable Rehash Rebuild Clear InternCore InternInvariant Intern FormulaEncoding Representation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module BootstrapExecution.
Import SetTheory IndexExecution SipHashExecution HashTableInvariant RehashExecution RebuildExecution ClearExecution InternInvariant InternExecution FormulaEncoding NativeRepresentation.
Lemma empty_table s :
  (28 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat -> meta_value s 1 = 0 ->
  0 < meta_value s 20 <= maximum ->
  length (memory s arraydef_0__formulaBuckets) = Z.to_nat (meta_value s 20) ->
  (forall b, (b < length (memory s arraydef_0__formulaBuckets))%nat -> head_at s b = 0) -> table s 0.
Proof.
  intros Hm Hs Hcount [Hp Hlimit] Hlength Hheads.
  split.
  - unfold ready. split; [exact Hm|]. split; [exact Hs|]. split; [exact Hp|].
    split; [rewrite Hlength, Z2Nat.id by lia; lia|]. split; [lia|]. split; [lia|unfold maximum; lia].
  - split; [exact Hcount|]. split; [exact Hlimit|]. split; [exact Hlength|]. split; [lia|].
    split; [now apply empty_indexed|]. intros i j Hi Hj Heq. lia.
Qed.
Lemma empty_arena s : table s 0 -> canonical_arena s [].
Proof.
  intro Htable. split; [exact Htable|]. split; [intros i Hi; cbn [length] in Hi; lia|].
  split; [intros i j p Hi; destruct i; discriminate|]. intros i Hi. cbn [length] in Hi. lia.
Qed.
Definition seeded key0 key1 input output : Machine :=
  let s := {| memory := arrays _ environment1; stdin := input; stdout := output |} in
  store_meta (store_meta (store_meta s 26 key0) 27 key1) 20 1024.
Lemma seeded_buckets key0 key1 input output :
  memory (seeded key0 key1 input output) arraydef_0__formulaBuckets = repeat 0 1024.
Proof. unfold seeded. now rewrite !store_meta_other by discriminate. Qed.
Theorem seeded_empty_arena key0 key1 input output : canonical_arena (seeded key0 key1 input output) [].
Proof.
  apply empty_arena, empty_table.
  - change (28 < 32)%nat. lia.
  - change (0 < 1)%nat. lia.
  - vm_compute. reflexivity.
  - change (0 < 1024 <= maximum). unfold maximum. lia.
  - rewrite seeded_buckets, repeat_length. vm_compute. reflexivity.
  - intros b Hb. unfold head_at. rewrite seeded_buckets. apply List.nth_repeat.
Qed.
Local Opaque funcdef_0__formulaHash funcdef_0__rehashFormulas InternCoreExecution.after_resize hash_tuple.

Lemma intern_cannot_fail_at_zero s bs ns : table s 0 -> meta_value s 8 = 0 ->
  exists final, exec (funcdef_0__intern bs ns) s = Some (tt,final) /\ logical_frame s final /\
    InternExecution.canonical s final 0 (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b).
Proof.
  intros Htable Hflag.
  pose proof Htable as [Hready _]. pose proof Hready as [_ [_ [Hpositive _]]].
  set (f := {| machine := s; bools := bs; nums := ns |}).
  set (start := setNum f vardef_0__intern_found 0).
  destruct (generated_lookup start 0 Htable ltac:(cbn; exact Hpositive) Hflag ltac:(reflexivity))
    as [last [Hrun [Hframe Hpost]]].
  exists (machine last). split; [|split; assumption].
  unfold funcdef_0__intern. rewrite exec_eliminate, InternCoreExecution.actual_body. fold f.
  rewrite (InternCoreExecution.skip_resize funcdef_0__rehashFormulas funcdef_0__formulaHash f).
  - fold start. rewrite Hrun. reflexivity.
  - destruct Hready as [Hm _]. change (20 < length (memory s arraydef_0__meta))%nat. lia.
  - change (meta_value s 1 <> meta_value s 20). rewrite (proj1 (proj2 Htable)). lia.
Qed.
Theorem generated_bootstrap_false_framed s bs ns :
  ns vardef_0__intern_tag = 0 -> ns vardef_0__intern_a = 0 -> ns vardef_0__intern_b = 0 ->
  canonical_arena s [] -> meta_value s 8 = 0 ->
  exists final, exec (funcdef_0__intern bs ns) s = Some (tt,final) /\
    logical_frame s final /\ canonical_arena final [falsity] /\ meta_value final 0 = 0 /\ meta_value final 8 = 0.
Proof.
  intros Htag Ha Hb Harena Hflag.
  destruct (intern_cannot_fail_at_zero _ bs ns (proj1 Harena) Hflag)
    as [final [Hrun [Hframe Hcanonical]]].
  rewrite Htag, Ha, Hb in Hcanonical.
  assert (Hraw : normal (0,0,0)) by (unfold normal; left; repeat split; reflexivity).
  assert (Hdecode : decode [] (0,0,0) = Some falsity) by reflexivity.
  pose proof (canonical_semantics s final [] (0,0,0) falsity Harena Hraw Hdecode Hcanonical) as Hsem.
  destruct Hsem as [next [Hnext [Hlookup [extra Hextra]]]].
  destruct Hcanonical as [Hsuccess [count [index [Halloc [Htable [Hi [Hresult [Htuple Hprefix]]]]]]]].
  assert (Hcount : count = 1%nat) by (destruct Halloc as [->|[-> _]]; lia).
  assert (Hindex : index = 0%nat) by lia. subst count index.
  assert (Hlen : length next = 1%nat).
  { pose proof (proj1 (proj2 (proj1 Hnext))) as Hmeta. pose proof (proj1 (proj2 Htable)) as Hmeta'. lia. }
  destruct next as [|p rest]; cbn [length] in Hlen; [lia|]. destruct rest as [|q rest]; [|cbn [length] in Hlen; lia].
  rewrite Hresult, Nat2Z.id in Hlookup. cbn [nth_error] in Hlookup. injection Hlookup as ->.
  exists final. split; [exact Hrun|]. split; [exact Hframe|]. split; [exact Hnext|]. split; assumption.
Qed.
Theorem generated_bootstrap_false_arguments s bs ns :
  ns vardef_0__intern_tag = 0 -> ns vardef_0__intern_a = 0 -> ns vardef_0__intern_b = 0 ->
  canonical_arena s [] -> meta_value s 8 = 0 ->
  exists final, exec (funcdef_0__intern bs ns) s = Some (tt,final) /\
    canonical_arena final [falsity] /\ meta_value final 0 = 0 /\ meta_value final 8 = 0.
Proof.
  intros Htag Ha Hb Harena Hflag.
  destruct (generated_bootstrap_false_framed s bs ns Htag Ha Hb Harena Hflag) as [final [Hrun [Hframe Hpost]]].
  exists final. split; assumption.
Qed.
Theorem generated_bootstrap_false_from_empty s :
  canonical_arena s [] -> meta_value s 8 = 0 ->
  exists final, exec (funcdef_0__intern (fun _ => false) (fun _ => 0)) s = Some (tt,final) /\
    canonical_arena final [falsity] /\ meta_value final 0 = 0 /\ meta_value final 8 = 0.
Proof. apply generated_bootstrap_false_arguments; reflexivity. Qed.
Theorem generated_bootstrap_false key0 key1 input output :
  exists final, exec (funcdef_0__intern (fun _ => false) (fun _ => 0)) (seeded key0 key1 input output) = Some (tt,final) /\
    canonical_arena final [falsity] /\ meta_value final 0 = 0 /\ meta_value final 8 = 0.
Proof.
  apply generated_bootstrap_false_from_empty.
  - apply seeded_empty_arena.
  - vm_compute. reflexivity.
Qed.
End BootstrapExecution.
