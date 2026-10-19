From CoqCP Require Import Options Imperative Execution SetTheory.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow Intern Fresh Representation Canonical
  PrintingFrame Append Inference InternFrame Generalization ModusPonens.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module NativeState.
Import SetTheory IndexExecution NativeRepresentation CanonicalArena AppendExecution
  NativeInference GeneralizationExecution.

Lemma represented_formula_unique s meaning other p :
  represents s meaning -> represents s other ->
  forall index q, nth_error meaning index = Some p ->
    nth_error other index = Some q -> p = q.
Proof.
  intros Hrep Hother.
  induction p as [|i j|i j|p IHp q IHq|p IH] ; intros index value Hp Hvalue;
    destruct (related_lookup_right _ _ _ _ _ Hrep Hp) as [[[tag a] b] [Hraw Hd]];
    destruct (represented_lookup _ _ _ _ Hother Hraw) as [value' [Hvalue' Hd']];
    rewrite Hvalue in Hvalue'; injection Hvalue' as <-;
    unfold decode in Hd, Hd'.
  all: repeat match goal with
    H : context [Z.eq_dec ?x ?y] |- _ => destruct (Z.eq_dec x y); try lia
  end.
  all: repeat match goal with
    H : context [match nth_error ?xs ?n with Some _ => _ | None => _ end] |- _ =>
      destruct (nth_error xs n) as [? |] eqn:?; cbn [option_map] in *; try discriminate
    | H : context [option_map _ (nth_error ?xs ?n)] |- _ =>
      destruct (nth_error xs n) as [? |] eqn:?; cbn [option_map] in *; try discriminate
  end.
  all: try discriminate.
  all: inversion Hd; inversion Hd'; subst; try reflexivity.
  all: f_equal; eauto.
Qed.

Theorem represents_unique s meaning other :
  represents s meaning -> represents s other -> meaning = other.
Proof.
  intros Hrep Hother. apply List.nth_error_ext. intro index.
  destruct (nth_error meaning index) as [p |] eqn:Hp;
    destruct (nth_error other index) as [q |] eqn:Hq; try reflexivity.
  - f_equal. now apply (represented_formula_unique s meaning other p Hrep Hother index q).
  - pose proof (Forall2_length Hrep) as Hlen.
    pose proof (Forall2_length Hother) as Hlen'.
    assert (Hbound : (index < length meaning)%nat).
    { apply nth_error_Some. rewrite Hp. discriminate. }
    apply nth_error_None in Hq. lia.
  - pose proof (Forall2_length Hrep) as Hlen.
    pose proof (Forall2_length Hother) as Hlen'.
    assert (Hbound : (index < length other)%nat).
    { apply nth_error_Some. rewrite Hq. discriminate. }
    apply nth_error_None in Hp. lia.
Qed.

Lemma append_post_ready s final count node :
  ready s -> append_post s final count node -> ready final.
Proof.
  intros [Hmeta [Hcount [Hflag Hlimit]]]
    [Hhistory [Hnew_count [Hslots [Hlength Hframe]]]].
  unfold ready. rewrite Hlength.
  rewrite (Hframe arraydef_0__formulas) by discriminate.
  rewrite Hslots by discriminate. rewrite Hslots by discriminate. auto.
Qed.

Lemma append_post_history_ready s final count node :
  history_ready s count -> Z.of_nat count < maximum ->
  append_post s final count node -> history_ready final (S count).
Proof.
  intros [Hmeta [Hcount [Hlimit Hallocated]]] Hspace
    [Hhistory [Hnew_count [Hslots [Hlength Hframe]]]].
  unfold history_ready. rewrite Hlength, Hnew_count, Hhistory, length_insert, growList_length.
  split; [exact Hmeta |]. split; [reflexivity |]. split; lia.
Qed.

Lemma append_post_canonical s final count node meaning :
  canonical s meaning -> append_post s final count node -> canonical final meaning.
Proof.
  intros [Hrep [Hunique Hnormal]] [_ [_ [_ [_ Hframe]]]].
  unfold canonical, represents in *. rewrite Hframe by discriminate. auto.
Qed.

Definition history_words (s : Machine) := Forall word (memory s arraydef_0__theorems).
Lemma append_post_words s final count node :
  (count <= length (memory s arraydef_0__theorems))%nat ->
  history_words s -> word node -> append_post s final count node -> history_words final.
Proof.
  intros Hallocated Hwords Hnode [Hhistory _].
  unfold history_words in *. rewrite Hhistory. now apply update_grown_history.
Qed.

Definition session s meaning count := ready s /\ history_ready s count /\
  canonical s meaning /\ history_safe s meaning /\ history_words s.

Theorem generated_append_accepted s bs ns count final :
  history_ready s count ->
  exec (funcdef_0__appendTheorem bs ns) s = Some (tt,final) ->
  List.nth 8 (memory final arraydef_0__meta) 0 = 0 ->
  List.nth 8 (memory s arraydef_0__meta) 0 = 0 /\
  Z.of_nat count < maximum /\ append_post s final count (ns vardef_0__appendTheorem_node).
Proof.
  intros [Hm [Hc [Hl Ha]]] Hrun Hfinal.
  assert (Hclear : List.nth 8 (memory s arraydef_0__meta) 0 = 0).
  { destruct (Z.eq_dec (List.nth 8 (memory s arraydef_0__meta) 0) 0) as [H |H]; [exact H |].
    rewrite (generated_append_error s bs ns Hm H) in Hrun.
    injection Hrun as <-. contradiction. }
  assert (Hspace : Z.of_nat count < maximum).
  { destruct (Z.eq_dec (Z.of_nat count) maximum) as [Hfull |Hspace]; [|lia].
    rewrite (generated_append_full s bs ns Hm (eq_trans Hc Hfull) Hclear) in Hrun.
    injection Hrun as <-. rewrite full_flag in Hfinal by exact Hm. discriminate. }
  split; [exact Hclear |]. split; [exact Hspace |].
  exact (generated_append_fits_post s bs ns count final Hm Hc Hclear Hspace Hrun).
Qed.

Theorem generated_append_session s bs ns count final meaning :
  session s meaning count -> valid_id meaning (ns vardef_0__appendTheorem_node) ->
  word (ns vardef_0__appendTheorem_node) ->
  exec (funcdef_0__appendTheorem bs ns) s = Some (tt,final) ->
  List.nth 8 (memory final arraydef_0__meta) 0 = 0 -> session final meaning (S count).
Proof.
  intros [Hready [Hhistory [Hcanonical [Hsafe Hwords]]]] Hvalid Hword Hrun Hclear.
  destruct (generated_append_accepted s bs ns count final Hhistory Hrun Hclear)
    as [_ [Hspace Hpost]].
  unfold session. split; [now apply append_post_ready with (s := s) (count := count)
    (node := ns vardef_0__appendTheorem_node) |].
  split; [now apply append_post_history_ready with (s := s)
    (node := ns vardef_0__appendTheorem_node) |].
  split; [now apply append_post_canonical with (s := s) (count := count)
    (node := ns vardef_0__appendTheorem_node) |].
  split.
  - destruct Hhistory as [Hm [Hc [Hl Ha]]]. now apply generated_append_safe with
      (bs := bs) (ns := ns) (s := s) (count := count).
  - destruct Hhistory as [_ [_ [_ Ha]]].
    now apply append_post_words with (s := s) (count := count)
      (node := ns vardef_0__appendTheorem_node).
Qed.

Theorem generated_intern_session s bs ns meaning count p :
  session s meaning count ->
  normal (InternExecution.sought (InternExecution.start_frame s bs ns)) ->
  decode meaning (InternExecution.sought (InternExecution.start_frame s bs ns)) = Some p ->
  exists middle,
    exec (funcdef_0__intern bs ns) s = Some (tt,middle) /\
    (List.nth 8 (memory middle arraydef_0__meta) 0 = 0 ->
      exists next index extra,
        next = meaning ++ extra /\ session middle next count /\
        nth_error next index = Some p /\
        List.nth 0 (memory middle arraydef_0__meta) 0 = Z.of_nat index /\ word (Z.of_nat index)).
Proof.
  intros [Hready [Hhistory [Hcanonical [Hsafe Hwords]]]] Hnormal Hdecode.
  destruct (generated_intern_history s bs ns meaning p Hready (proj1 Hcanonical) Hsafe Hdecode)
    as [middle [Hrun Haccept]].
  exists middle. split; [exact Hrun |]. intro Hclear.
  destruct (Haccept Hclear) as
    [next [index [extra [Hnext [Hextend [Hlookup [Hresult [Hready' Hsafe']]]]]]]].
  destruct (generated_intern_canonical s bs ns (length (memory s arraydef_0__formulas))
    meaning p Hready eq_refl Hcanonical Hnormal Hdecode)
    as [middle' [Hrun' Hcanonical']].
  rewrite Hrun in Hrun'. injection Hrun' as <-.
  destruct (Hcanonical' Hclear) as [other Hother].
  assert (Hequal : other = next).
  { eapply represents_unique; [exact (proj1 Hother) |exact Hnext]. }
  subst other.
  assert (Hactual : middle = FreshExecution.intern_output s bs ns
      (length (memory s arraydef_0__formulas))).
  { destruct Hready as [Hm [Hc [Hf Hl]]].
    rewrite (FreshExecution.generated_intern_correct s bs ns
      (length (memory s arraydef_0__formulas)) Hm Hc Hf eq_refl Hl) in Hrun.
    now injection Hrun. }
  exists next, index, extra. split; [exact Hextend |]. split.
  - unfold session. split; [exact Hready' |]. split.
    + rewrite Hactual. now apply InternFrame.intern_output_history_ready.
    + split; [exact Hother |]. split; [exact Hsafe' |].
      unfold history_words in *. rewrite Hactual.
      destruct (InternFrame.intern_output_frame s bs ns
        (length (memory s arraydef_0__formulas))) as [_ [_ Hframe]].
      now rewrite Hframe by discriminate.
  - split; [exact Hlookup |]. split; [exact Hresult |].
    unfold word. split; [lia |].
    assert (Hbound : (index < length next)%nat).
    { apply nth_error_Some. rewrite Hlookup. discriminate. }
    pose proof (Forall2_length Hnext) as Hlength.
    destruct Hready' as [_ [_ [_ Hlimit]]].
    change (@List.length raw_node (memory middle arraydef_0__formulas) = length next) in Hlength.
    change (Z.of_nat (@List.length raw_node (memory middle arraydef_0__formulas)) <= maximum) in Hlimit.
    lia.
Qed.

Theorem generated_generalization_session s bs ns meaning count index final :
  session s meaning count ->
  ns vardef_0__generalize_theorem = Z.of_nat index -> (index < count)%nat ->
  exec (funcdef_0__generalize bs ns) s = Some (tt,final) ->
  List.nth 8 (memory final arraydef_0__meta) 0 = 0 ->
  exists next extra, next = meaning ++ extra /\ session final next (S count).
Proof.
  intros Hsession Hindex Hindex_count Hrun Hfinal.
  pose proof Hsession as [Hready [Hhistory [Hcanonical [Hsafe Hwords]]]].
  set (source := List.nth index (memory s arraydef_0__theorems) 0).
  assert (Hbound : (index < length (memory s arraydef_0__theorems))%nat).
  { destruct Hhistory as [_ [_ [_ Ha]]]. lia. }
  assert (Hin : In source (memory s arraydef_0__theorems)).
  { unfold source. now apply List.nth_In. }
  destruct (Hsafe source Hin) as [p [Hsource Hproof]].
  assert (Hword : word source).
  { apply (proj1 (Forall_forall _ _) Hwords). exact Hin. }
  assert (Hnormal : normal (InternExecution.sought
    (InternExecution.start_frame s (fun _ => false) (intern_arguments source)))).
  { change (normal (4,source,0)). right. right. auto. }
  destruct (generated_intern_session s (fun _ => false) (intern_arguments source)
    meaning count (all p) Hsession Hnormal (intern_arguments_decode s meaning source p Hsource))
    as [middle [Hintern Haccept]].
  assert (Hmiddle : middle = generalized_state s source).
  { destruct Hready as [Hm [Hc [Hf Hl]]].
    rewrite (FreshExecution.generated_intern_correct s (fun _ => false) (intern_arguments source)
      (length (memory s arraydef_0__formulas)) Hm Hc Hf eq_refl Hl) in Hintern.
    now injection Hintern. }
  subst middle.
  rewrite (generated_generalize_step s bs ns index source Hready Hindex Hbound eq_refl) in Hrun.
  assert (Hmiddle_history : history_ready (generalized_state s source) count).
  { now apply InternFrame.intern_output_history_ready. }
  destruct (generated_append_accepted _ _ _ count final Hmiddle_history Hrun Hfinal)
    as [Hclear _].
  destruct (Haccept Hclear) as [next [result [extra [Hextend [Hnext [Hlookup [Hresult Hword_result]]]]]]].
  exists next, extra. split; [exact Hextend |].
  eapply generated_append_session; [exact Hnext | | |exact Hrun |exact Hfinal].
  - change (valid_id next (List.nth 0 (memory (generalized_state s source) arraydef_0__meta) 0)).
    rewrite Hresult. unfold valid_id. rewrite Nat2Z.id.
    exists (all p). split; [exact Hlookup |now apply d_gen].
  - change (word (List.nth 0 (memory (generalized_state s source) arraydef_0__meta) 0)).
    now rewrite Hresult.
Qed.
Lemma session_memory_frame s final meaning count :
  (forall name, memory final name = memory s name) ->
  session s meaning count -> session final meaning count.
Proof.
  intros Hframe. unfold session, ready, history_ready, canonical, represents,
    history_safe, history_words. now repeat rewrite Hframe.
Qed.

Theorem generated_modus_ponens_session s bs ns meaning count ci ca final :
  session s meaning count ->
  ns vardef_0__modusPonens_implication = Z.of_nat ci ->
  ns vardef_0__modusPonens_antecedent = Z.of_nat ca ->
  (ci < count)%nat -> (ca < count)%nat ->
  exec (funcdef_0__modusPonens bs ns) s = Some (tt,final) ->
  List.nth 8 (memory final arraydef_0__meta) 0 = 0 ->
  session final meaning count \/ session final meaning (S count).
Proof.
  intros Hsession Hci Hca Hci_count Hca_count Hrun Hclear.
  pose proof Hsession as [Hready [Hhistory [[Hrep [Hunique Hnormal]] [Hsafe Hwords]]]].
  set (implication := List.nth ci (memory s arraydef_0__theorems) 0).
  set (antecedent := List.nth ca (memory s arraydef_0__theorems) 0).
  assert (Hci_bound : (ci < length (memory s arraydef_0__theorems))%nat).
  { destruct Hhistory as [_ [_ [_ Ha]]]. lia. }
  assert (Hca_bound : (ca < length (memory s arraydef_0__theorems))%nat).
  { destruct Hhistory as [_ [_ [_ Ha]]]. lia. }
  assert (Himp_in : In implication (memory s arraydef_0__theorems)).
  { unfold implication. now apply List.nth_In. }
  assert (Hant_in : In antecedent (memory s arraydef_0__theorems)).
  { unfold antecedent. now apply List.nth_In. }
  destruct (Hsafe implication Himp_in) as [p [Hp Hproof]].
  destruct (related_lookup_right _ _ _ _ _ Hrep Hp)
    as [[[tag a] result] [Hraw Hdecode]].
  assert (Hnode_bound : (Z.to_nat implication < length (memory s arraydef_0__formulas))%nat).
  { change (Z.to_nat implication < @List.length raw_node (memory s arraydef_0__formulas))%nat.
    apply nth_error_Some. rewrite Hraw. discriminate. }
  rewrite (ModusPonensExecution.generated_mp_branch s bs ns ci ca implication antecedent tag a result
    Hci Hca Hci_bound Hca_bound eq_refl eq_refl Hnode_bound
    (@List.nth_error_nth raw_node _ _ _ (0,0,0) Hraw)) in Hrun.
  case_bool_decide as Htest.
  - destruct Htest as [-> ->]. right.
    assert (Hnode_normal : normal (3,antecedent,result)).
    { apply (proj1 (Forall_forall _ _) Hnormal). now apply nth_error_In in Hraw. }
    assert (Hword : word result).
    { unfold normal in Hnode_normal.
      destruct Hnode_normal as [[Htag _] | [[Htag [Ha Hb]] | [Htag _]]];
        try discriminate; exact Hb. }
    eapply generated_append_session; [exact Hsession | | |exact Hrun |exact Hclear].
    + change (valid_id meaning result).
      now apply modus_ponens_ids with (s := s) (implication := implication)
        (antecedent := antecedent).
    + exact Hword.
  - left. apply session_memory_frame with (s := s); [|exact Hsession].
    intro name. eapply ModusPonensExecution.generated_no_preserves. exact Hrun.
Qed.
End NativeState.
