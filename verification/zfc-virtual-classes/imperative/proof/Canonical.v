From CoqCP Require Import Options Imperative Execution SetTheory.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow Intern Fresh Representation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module CanonicalArena.
Import SetTheory IndexExecution InternExecution FreshExecution NativeRepresentation.

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

Lemma related_lookup_right {A B} (R : A -> B -> Prop) xs ys i y :
  Forall2 R xs ys -> nth_error ys i = Some y ->
  exists x, nth_error xs i = Some x /\ R x y.
Proof.
  intro H. induction H as [|x z xs ys Hxz Htail IH] in i |- *.
  - destruct i; discriminate.
  - destruct i as [|i]; cbn [nth_error].
    + intro Heq. injection Heq as <-. exists x. auto.
    + exact (IH i).
Qed.

Lemma fresh_meaning_absent s bs ns count meaning p :
  represents s meaning -> unique meaning ->
  Forall normal (memory s arraydef_0__formulas) ->
  normal (sought (start_frame s bs ns)) ->
  decode meaning (sought (start_frame s bs ns)) = Some p ->
  length (memory s arraydef_0__formulas) = count ->
  find_from (start_frame s bs ns) 0 count = None ->
  forall index, nth_error meaning index <> Some p.
Proof.
  intros Hrep Hunique Hnormal Hnew Hdecode Hlength Hfind index Hlookup.
  destruct (related_lookup_right _ _ _ _ _ Hrep Hlookup) as [raw [Hraw Hmeaning]].
  assert (Hnormraw : normal raw).
  { apply (proj1 (Forall_forall _ _) Hnormal). now apply nth_error_In in Hraw. }
  assert (Heq : raw = sought (start_frame s bs ns)).
  { now apply decode_injective with (meaning := meaning) (p := p). }
  assert (Hbound : (index < count)%nat).
  { rewrite <- Hlength.
    change (index < @List.length raw_node (memory s arraydef_0__formulas))%nat.
    apply nth_error_Some. rewrite Hraw. discriminate. }
  apply (find_from_none _ _ _ Hfind index ltac:(lia)).
  change (@List.nth raw_node index (memory s arraydef_0__formulas) (0,0,0) =
    sought (start_frame s bs ns)).
  rewrite (@List.nth_error_nth raw_node (memory s arraydef_0__formulas)
    index raw (0,0,0) Hraw). exact Heq.
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

Definition canonical s meaning := represents s meaning /\ unique meaning /\
  Forall normal (memory s arraydef_0__formulas).

Lemma canonical_store_result s meaning index :
  canonical s meaning -> canonical (store_meta s 0 index) meaning.
Proof.
  intros [Hrep [Hunique Hnormal]]. split; [now apply store_meta_represents |].
  split; [exact Hunique |]. rewrite store_meta_other by discriminate. exact Hnormal.
Qed.

Lemma canonical_fresh s bs ns count meaning p :
  canonical s meaning -> length (memory s arraydef_0__formulas) = count ->
  normal (sought (start_frame s bs ns)) ->
  decode meaning (sought (start_frame s bs ns)) = Some p ->
  find_from (start_frame s bs ns) 0 count = None ->
  canonical (fresh_state s count (sought (start_frame s bs ns))) (meaning ++ [p]).
Proof.
  intros [Hrep [Hunique Hnormal]] Hlength Hnew Hdecode Hfind.
  split; [now apply fresh_represents |]. split.
  - apply unique_append; [exact Hunique |].
    now apply fresh_meaning_absent with (s := s) (bs := bs) (ns := ns) (count := count).
  - rewrite fresh_formulas by exact Hlength. apply Forall_app. split; [exact Hnormal |].
    constructor; [exact Hnew |constructor].
Qed.

Theorem generated_intern_canonical s bs ns count meaning p :
  ready s -> length (memory s arraydef_0__formulas) = count ->
  canonical s meaning -> normal (sought (start_frame s bs ns)) ->
  decode meaning (sought (start_frame s bs ns)) = Some p ->
  exists final,
    exec (funcdef_0__intern bs ns) s = Some (tt, final) /\
    (List.nth 8 (memory final arraydef_0__meta) 0 = 0 ->
      exists next, canonical final next).
Proof.
  intros [Hmeta [Hcount [Hflag Hlimit]]] Hlength Hcanonical Hnormal Hdecode.
  rewrite Hlength in Hcount, Hlimit.
  exists (intern_output s bs ns count). split.
  - now apply generated_intern_correct.
  - unfold intern_output.
    destruct (find_from (start_frame s bs ns) 0 count) as [index |] eqn:Hfind.
    + intros _. exists meaning. now apply canonical_store_result.
    + destruct (Z.eq_dec (Z.of_nat count) maximum).
      * rewrite full_flag by exact Hmeta. discriminate.
      * intros _. exists (meaning ++ [p]). now apply canonical_fresh.
Qed.
End CanonicalArena.
