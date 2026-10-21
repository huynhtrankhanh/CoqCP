From CoqCP Require Import Options Imperative Execution.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module FormulaEncoding.
Import SetTheory IndexExecution.
Definition raw_node := (Z * Z * Z)%type.
Definition decode (meaning : list formula) (entry : raw_node) : option formula :=
  let '(tag, a, b) := entry in
  if Z.eq_dec tag 0 then Some falsity else
  if Z.eq_dec tag 1 then Some (equal (Z.to_nat a) (Z.to_nat b)) else
  if Z.eq_dec tag 2 then Some (member (Z.to_nat a) (Z.to_nat b)) else
  if Z.eq_dec tag 3 then
    match nth_error meaning (Z.to_nat a), nth_error meaning (Z.to_nat b) with
    | Some p, Some q => Some (implies p q)
    | _, _ => None
    end
  else if Z.eq_dec tag 4 then option_map all (nth_error meaning (Z.to_nat a))
  else None.

Lemma nth_error_extend {A} (xs ys : list A) i x :
  nth_error xs i = Some x -> nth_error (xs ++ ys) i = Some x.
Proof.
  intro H. rewrite nth_error_app1; [exact H |].
  apply nth_error_Some. congruence.
Qed.

Lemma decode_extend meaning extra raw p :
  decode meaning raw = Some p -> decode (meaning ++ extra) raw = Some p.
Proof.
  destruct raw as [[tag a] b]. unfold decode.
  repeat match goal with |- context [Z.eq_dec ?x ?y] => destruct (Z.eq_dec x y) end;
    try tauto.
  - destruct (nth_error meaning (Z.to_nat a)) as [q |] eqn:Ha; [|discriminate].
    destruct (nth_error meaning (Z.to_nat b)) as [r |] eqn:Hb; [|discriminate].
    rewrite (nth_error_extend _ extra _ _ Ha), (nth_error_extend _ extra _ _ Hb).
    tauto.
  - destruct (nth_error meaning (Z.to_nat a)) as [q |] eqn:Ha; [|discriminate].
    rewrite (nth_error_extend _ extra _ _ Ha). tauto.
Qed.

Definition unique (meaning : list formula) := forall i j p,
  nth_error meaning i = Some p -> nth_error meaning j = Some p -> i = j.

Definition normal (raw : raw_node) :=
  let '(tag,a,b) := raw in
  (tag = 0 /\ a = 0 /\ b = 0) \/
  ((tag = 1 \/ tag = 2 \/ tag = 3) /\ word a /\ word b) \/
  (tag = 4 /\ word a /\ b = 0).

Lemma natural_index_injective a b : word a -> word b ->
  Z.to_nat a = Z.to_nat b -> a = b.
Proof. unfold word. intros. apply Z2Nat.inj; lia. Qed.

Theorem formula_id_equality meaning i j p q :
  unique meaning -> word i -> word j ->
  nth_error meaning (Z.to_nat i) = Some p ->
  nth_error meaning (Z.to_nat j) = Some q ->
  (i = j <-> p = q).
Proof.
  intros Hunique Hi Hj Hpi Hqj. split.
  - intros ->. rewrite Hqj in Hpi. now injection Hpi.
  - intros ->. apply natural_index_injective; try assumption. eapply Hunique; eassumption.
Qed.

Lemma decode_implication meaning raw p q :
  normal raw -> decode meaning raw = Some (implies p q) ->
  exists a b, raw = (3,a,b) /\ word a /\ word b /\
    nth_error meaning (Z.to_nat a) = Some p /\
    nth_error meaning (Z.to_nat b) = Some q.
Proof.
  destruct raw as [[tag a] b]. unfold normal.
  intros [[-> [-> ->]] | [[Htag [Ha Hb]] | [-> [Ha ->]]]] Hdecode.
  all: try (destruct Htag as [-> | [-> | ->]]).
  all: unfold decode in Hdecode.
  all: repeat match goal with
    H : context [Z.eq_dec ?x ?y] |- _ => destruct (Z.eq_dec x y); try lia
  end.
  all: repeat match goal with
    H : context [match nth_error ?ms ?i with Some _ => _ | None => _ end] |- _ =>
      destruct (nth_error ms i) as [? |] eqn:?; try discriminate
    | H : context [option_map _ (nth_error ?ms ?i)] |- _ =>
      destruct (nth_error ms i) as [? |] eqn:?; try discriminate
  end.
  all: try discriminate.
  injection Hdecode as <- <-. exists a, b. split; [reflexivity |].
  split; [exact Ha |]. split; [exact Hb |]. split; assumption.
Qed.

Lemma decode_injective meaning raw raw' p :
  unique meaning -> normal raw -> normal raw' ->
  decode meaning raw = Some p -> decode meaning raw' = Some p -> raw = raw'.
Proof.
  intros Hunique. destruct raw as [[tag a] b], raw' as [[tag' a'] b'].
  unfold normal. intros [[-> [-> ->]] | [[Htag [Ha Hb]] | [-> [Ha ->]]]]
    [[-> [-> ->]] | [[Htag' [Ha' Hb']] | [-> [Ha' ->]]]] Hd Hd'.
  all: try (destruct Htag as [-> | [-> | ->]]).
  all: try (destruct Htag' as [-> | [-> | ->]]).
  all: unfold decode in Hd, Hd'.
  all: repeat match goal with
    H : context [Z.eq_dec ?x ?y] |- _ => destruct (Z.eq_dec x y); try lia
  end.
  all: cbn [option_map] in Hd, Hd'.
  all: repeat match goal with
    H : context [match nth_error ?ms ?i with Some _ => _ | None => _ end] |- _ =>
      destruct (nth_error ms i) as [? |] eqn:?; cbn [option_map] in *; try discriminate
    | H : context [option_map _ (nth_error ?ms ?i)] |- _ =>
      destruct (nth_error ms i) as [? |] eqn:?; cbn [option_map] in *; try discriminate
  end.
  all: inversion Hd; inversion Hd'; subst; try congruence.
  all: repeat match goal with
    H : equal _ _ = equal _ _ |- _ => injection H; clear H; intros
    | H : member _ _ = member _ _ |- _ => injection H; clear H; intros
    | H : implies _ _ = implies _ _ |- _ => injection H; clear H; intros
    | H : all _ = all _ |- _ => injection H; clear H; intros
  end; subst.
  all: repeat match goal with
    H : Z.to_nat ?x = Z.to_nat ?y |- _ =>
      tryif constr_eq x y then clear H else
        (apply natural_index_injective in H; try assumption; subst)
  end.
  all: repeat match goal with
    H : nth_error ?ms (Z.to_nat ?x) = Some ?q,
    H' : nth_error ?ms (Z.to_nat ?y) = Some ?q |- _ =>
      tryif constr_eq x y then fail else idtac;
      let Heq := fresh "Hindex" in
      assert (Heq : x = y) by
        (apply natural_index_injective; try assumption; eapply Hunique; eassumption);
      subst
  end.
  all: reflexivity.
Qed.

Lemma unique_append meaning p : unique meaning ->
  (forall i, nth_error meaning i <> Some p) -> unique (meaning ++ [p]).
Proof.
  intros Hunique Habsent i j q Hi Hj.
  assert (Hib : (i < length (meaning ++ [p]))%nat).
  { apply nth_error_Some. rewrite Hi. discriminate. }
  assert (Hjb : (j < length (meaning ++ [p]))%nat).
  { apply nth_error_Some. rewrite Hj. discriminate. }
  rewrite length_app in Hib, Hjb. cbn [length] in Hib, Hjb.
  destruct (Nat.lt_dec i (length meaning)) as [Hil |Hil];
    destruct (Nat.lt_dec j (length meaning)) as [Hjl |Hjl].
  - rewrite nth_error_app1 in Hi, Hj by assumption. eapply Hunique; eassumption.
  - assert (j = length meaning) by lia. subst j.
    rewrite nth_error_app1 in Hi by exact Hil.
    rewrite nth_error_app2, Nat.sub_diag in Hj by lia. cbn [nth_error] in Hj.
    injection Hj as <-. exfalso. now apply (Habsent i).
  - assert (i = length meaning) by lia. subst i.
    rewrite nth_error_app1 in Hj by exact Hjl.
    rewrite nth_error_app2, Nat.sub_diag in Hi by lia. cbn [nth_error] in Hi.
    injection Hi as <-. exfalso. now apply (Habsent j).
  - lia.
Qed.

End FormulaEncoding.
