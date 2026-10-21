From CoqCP Require Import Options Imperative Execution.
From Trusted Require Import SetTheory.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash HashTable Rehash Rebuild InternInvariant Intern FormulaEncoding.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module NativeRepresentation.
Import SetTheory IndexExecution SipHashExecution HashTableInvariant RehashExecution RebuildExecution InternInvariant InternExecution FormulaEncoding.
Definition represents (s : Machine) (meaning : list formula) :=
  forall i, (i < length meaning)%nat -> decode meaning (tuple_at s i) = Some (List.nth i meaning falsity).
Definition normal_arena (s : Machine) n := forall i, (i < n)%nat -> normal (tuple_at s i).
Definition canonical_arena s meaning := table s (length meaning) /\ represents s meaning /\
  FormulaEncoding.unique meaning /\ normal_arena s (length meaning).
Lemma represented_lookup s meaning i p : represents s meaning -> nth_error meaning i = Some p ->
  decode meaning (tuple_at s i) = Some p.
Proof.
  intros Hrep Hi. assert (Hb : (i < length meaning)%nat) by (apply nth_error_Some; congruence).
  rewrite Hrep by exact Hb. now rewrite (@List.nth_error_nth formula meaning i p falsity Hi).
Qed.
Lemma represents_same s t meaning :
  (forall i, (i < length meaning)%nat -> tuple_at t i = tuple_at s i) ->
  represents s meaning -> represents t meaning.
Proof. intros Hprefix Hrep i Hi. rewrite Hprefix by exact Hi. now apply Hrep. Qed.
Lemma represents_app s t meaning raw p :
  (forall i, (i < length meaning)%nat -> tuple_at t i = tuple_at s i) ->
  tuple_at t (length meaning) = raw -> represents s meaning -> decode meaning raw = Some p ->
  represents t (meaning ++ [p]).
Proof.
  intros Hprefix Hnew Hrep Hdecode i Hi. unfold represents in Hrep.
  rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.lt_dec i (length meaning)) as [Hold|Hlast].
  - rewrite Hprefix, app_nth1 by exact Hold. now apply decode_extend, Hrep.
  - assert (i = length meaning) as -> by lia. rewrite Hnew, app_nth2 by lia. rewrite Nat.sub_diag.
    cbn [List.nth]. now apply decode_extend.
Qed.
Lemma normal_same s t (meaning : list formula) :
  (forall i, (i < length meaning)%nat -> tuple_at t i = tuple_at s i) ->
  normal_arena s (length meaning) -> normal_arena t (length meaning).
Proof. intros Hprefix Hnormal i Hi. rewrite Hprefix by exact Hi. now apply Hnormal. Qed.
Lemma normal_app s t (meaning : list formula) raw (p : formula) :
  (forall i, (i < length meaning)%nat -> tuple_at t i = tuple_at s i) ->
  tuple_at t (length meaning) = raw -> normal_arena s (length meaning) -> normal raw ->
  normal_arena t (length (meaning ++ [p])).
Proof.
  intros Hprefix Hnew Hnormal Hraw i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.lt_dec i (length meaning)) as [Hold|Hlast].
  - rewrite Hprefix by exact Hold. now apply Hnormal.
  - assert (i = length meaning) as -> by lia. now rewrite Hnew.
Qed.
Lemma fresh_meaning_absent s t meaning raw p :
  represents s meaning -> FormulaEncoding.unique meaning -> normal_arena s (length meaning) -> normal raw ->
  decode meaning raw = Some p ->
  (forall i, (i < length meaning)%nat -> tuple_at t i = tuple_at s i) ->
  tuple_at t (length meaning) = raw -> HashTableInvariant.unique t (S (length meaning)) ->
  forall i, nth_error meaning i <> Some p.
Proof.
  intros Hrep Hunique Hnormal Hraw Hdecode Hprefix Hnew Hids i Hi.
  assert (Hb : (i < length meaning)%nat) by (apply nth_error_Some; congruence).
  pose proof (represented_lookup _ _ _ _ Hrep Hi) as Hdecoded.
  assert (Heq : tuple_at s i = raw) by (apply (decode_injective meaning _ _ p Hunique (Hnormal i Hb) Hraw Hdecoded Hdecode)).
  assert (Heq' : tuple_at t i = tuple_at t (length meaning)) by (rewrite Hprefix by exact Hb; now rewrite Heq, Hnew).
  pose proof (Hids i (length meaning) ltac:(lia) ltac:(lia) Heq'). lia.
Qed.

Theorem canonical_semantics s t meaning raw p :
  canonical_arena s meaning -> normal raw -> decode meaning raw = Some p ->
  InternExecution.canonical s t (length meaning) raw ->
  exists next, canonical_arena t next /\
    nth_error next (Z.to_nat (meta_value t 0)) = Some p /\
    exists extra, next = meaning ++ extra.
Proof.
  intros [Htable [Hrep [Hunique Hnormal]]] Hraw Hdecode [Hflag [count [index [Halloc [Hnexttable [Hi [Hresult [Htuple Hprefix]]]]]]]].
  destruct Halloc as [->|[-> ->]].
  - exists meaning. split.
    + split; [exact Hnexttable|]. split; [now apply (represents_same s)|]. split; [exact Hunique|]. now apply (normal_same s).
    + split.
      * rewrite Hresult, Nat2Z.id.
        pose proof (Hrep index Hi) as Hpi. rewrite <- Hprefix, Htuple, Hdecode in Hpi by exact Hi.
        rewrite List.nth_error_nth' with (d := falsity) by exact Hi. congruence.
      * exists []. now rewrite app_nil_r.
  - exists (meaning ++ [p]).
    assert (Hlen : length (meaning ++ [p]) = S (length meaning)) by (rewrite length_app; cbn [length]; lia).
    split.
    + split; [now rewrite Hlen|]. split; [now apply (represents_app s t meaning raw p)|]. split.
      * apply unique_append; [exact Hunique|]. apply (fresh_meaning_absent s t meaning raw p); try assumption.
        exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hnexttable)))))).
      * now apply (normal_app s t meaning raw p).
    + split.
      * rewrite Hresult, Nat2Z.id, nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
      * exists [p]. reflexivity.
Qed.

Theorem generated_intern_refines s bs ns meaning p :
  canonical_arena s meaning -> meta_value s 8 = 0 ->
  normal (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) ->
  decode meaning (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) = Some p ->
  exists final, exec (funcdef_0__intern bs ns) s = Some (tt,final) /\ logical_frame s final /\
    (meta_value final 8 = 0 -> exists next, canonical_arena final next /\
      nth_error next (Z.to_nat (meta_value final 0)) = Some p /\ exists extra, next = meaning ++ extra).
Proof.
  intros Harena Hflag Hraw Hdecode.
  destruct (generated_intern_correct s bs ns (length meaning) (proj1 Harena) Hflag)
    as [final [Hrun [Hframe [Herror|Hcanonical]]]].
  - exists final. split; [exact Hrun|]. split; [exact Hframe|]. contradiction.
  - exists final. split; [exact Hrun|]. split; [exact Hframe|]. intro Hsuccess.
    exact (canonical_semantics s final meaning
      (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) p Harena Hraw Hdecode Hcanonical).
Qed.
End NativeRepresentation.
