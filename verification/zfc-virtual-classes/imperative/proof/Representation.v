From CoqCP Require Import Options Imperative Execution SetTheory.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow Intern Fresh.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module NativeRepresentation.
Import SetTheory IndexExecution InternExecution FreshExecution.

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

Definition represents (s : Machine) (meaning : list formula) :=
  Forall2 (fun raw p => decode meaning raw = Some p)
    (memory s arraydef_0__formulas) meaning.

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

Lemma related_lookup {A B} (R : A -> B -> Prop) xs ys i x :
  Forall2 R xs ys -> nth_error xs i = Some x ->
  exists y, nth_error ys i = Some y /\ R x y.
Proof.
  intro H. induction H as [|z y xs ys Hxy Htail IH] in i |- *.
  - destruct i; discriminate.
  - destruct i as [|i]; cbn [nth_error].
    + intro Heq. injection Heq as <-. exists y. auto.
    + exact (IH i).
Qed.

Lemma represented_lookup s meaning index raw :
  represents s meaning -> nth_error (memory s arraydef_0__formulas) index = Some raw ->
  exists p, nth_error meaning index = Some p /\ decode meaning raw = Some p.
Proof. apply related_lookup. Qed.

Lemma store_meta_represents s meaning slot value :
  represents s meaning -> represents (store_meta s slot value) meaning.
Proof.
  unfold represents. rewrite store_meta_other by discriminate. tauto.
Qed.

Lemma fresh_represents s meaning count raw p :
  represents s meaning -> length (memory s arraydef_0__formulas) = count ->
  decode meaning raw = Some p ->
  represents (fresh_state s count raw) (meaning ++ [p]).
Proof.
  intros Hrep Hlength Hdecode. unfold represents. rewrite fresh_formulas by exact Hlength.
  apply Forall2_app.
  - eapply Forall2_impl; [|exact Hrep]. intros node q Hq. now apply decode_extend.
  - constructor; [now apply decode_extend | constructor].
Qed.

Lemma nth_insert_other {A} (xs : list A) i j value default :
  i <> j -> List.nth i (<[j := value]> xs) default = List.nth i xs default.
Proof.
  induction xs as [|x xs IH] in i, j |- *; [destruct i, j; reflexivity |].
  destruct i as [|i], j as [|j]; cbn; try reflexivity; [congruence |].
  intro H. apply IH. congruence.
Qed.

Lemma fresh_result s count raw : (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 0 (memory (fresh_state s count raw) arraydef_0__meta) 0 = Z.of_nat count.
Proof.
  intro H. rewrite fresh_metadata, nth_insert_other by discriminate.
  apply OverflowExecution.nth_insert_same. lia.
Qed.

Lemma fresh_flag s count raw :
  List.nth 8 (memory (fresh_state s count raw) arraydef_0__meta) 0 =
  List.nth 8 (memory s arraydef_0__meta) 0.
Proof. rewrite fresh_metadata. repeat rewrite nth_insert_other by discriminate. reflexivity. Qed.

Lemma full_flag s : (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 8 (memory (store_meta s 8 1) arraydef_0__meta) 0 = 1.
Proof.
  intro H. unfold store_meta. cbn [withMemory memory]. rewrite modify_meta.
  now apply OverflowExecution.nth_insert_same.
Qed.

Definition ready (s : Machine) :=
  (8 < length (memory s arraydef_0__meta))%nat /\
  List.nth 1 (memory s arraydef_0__meta) 0 =
    Z.of_nat (length (memory s arraydef_0__formulas)) /\
  List.nth 8 (memory s arraydef_0__meta) 0 = 0 /\
  Z.of_nat (length (memory s arraydef_0__formulas)) <= maximum.

Lemma fresh_ready s count raw :
  ready s -> length (memory s arraydef_0__formulas) = count ->
  Z.of_nat count < maximum -> ready (fresh_state s count raw).
Proof.
  intros [Hmeta [Hcount [Hflag Hlimit]]] Hlength Hspace.
  unfold ready. rewrite fresh_formulas by exact Hlength.
  rewrite fresh_metadata. repeat rewrite length_insert.
  split; [exact Hmeta |]. split.
  - rewrite OverflowExecution.nth_insert_same.
    + rewrite length_app. cbn [length]. rewrite Hlength. f_equal. lia.
    + rewrite length_insert. lia.
  - split.
    + repeat rewrite nth_insert_other by discriminate. exact Hflag.
    + rewrite length_app. cbn [length]. rewrite Hlength, Nat2Z.inj_add. cbn. lia.
Qed.

Lemma store_result_ready s index : ready s -> ready (store_meta s 0 index).
Proof.
  intros [Hmeta [Hcount [Hflag Hlimit]]]. unfold ready.
  rewrite (store_meta_other s 0 index arraydef_0__formulas ltac:(discriminate)).
  rewrite store_meta_length.
  split; [exact Hmeta |]. split.
  - unfold store_meta. cbn [withMemory memory]. rewrite modify_meta.
    rewrite nth_count_insert_result. exact Hcount.
  - split; [now rewrite store_result_flag |exact Hlimit].
Qed.

Theorem intern_output_ready s bs ns count :
  ready s -> length (memory s arraydef_0__formulas) = count ->
  List.nth 8 (memory (intern_output s bs ns count) arraydef_0__meta) 0 = 0 ->
  ready (intern_output s bs ns count).
Proof.
  intros Hready Hlength. unfold intern_output.
  destruct (find_from (start_frame s bs ns) 0 count) as [index |].
  - intros _. now apply store_result_ready.
  - destruct (Z.eq_dec (Z.of_nat count) maximum) as [Heq |Hneq].
    + rewrite full_flag; [discriminate |exact (proj1 Hready)].
    + intros _. apply fresh_ready; try assumption.
      destruct Hready as [_ [_ [_ Hbound]]]. rewrite Hlength in Hbound. lia.
Qed.

Definition accepted_result (s final : Machine) meaning p :=
  exists extended index extra,
    represents final extended /\ extended = meaning ++ extra /\
    nth_error extended index = Some p /\
    List.nth 0 (memory final arraydef_0__meta) 0 = Z.of_nat index.

Theorem generated_intern_represents s bs ns count meaning p :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 1 (memory s arraydef_0__meta) 0 = Z.of_nat count ->
  List.nth 8 (memory s arraydef_0__meta) 0 = 0 ->
  length (memory s arraydef_0__formulas) = count -> Z.of_nat count <= maximum ->
  represents s meaning -> decode meaning (sought (start_frame s bs ns)) = Some p ->
  exists final,
    exec (funcdef_0__intern bs ns) s = Some (tt, final) /\
    (List.nth 8 (memory final arraydef_0__meta) 0 = 0 ->
      accepted_result s final meaning p) /\
    (forall name, name <> arraydef_0__meta -> name <> arraydef_0__formulas ->
      memory final name = memory s name) /\
    stdin final = stdin s /\ stdout final = stdout s.
Proof.
  intros Hmeta Hcount Hflag Hlength Hlimit Hrep Hdecode.
  exists (intern_output s bs ns count). split.
  - now apply generated_intern_correct.
  - unfold intern_output.
    destruct (find_from (start_frame s bs ns) 0 count) as [index |] eqn:Hfind.
    + split.
      * intro Hclear. destruct (find_from_sound _ _ _ _ Hfind) as [Hrange Hraw].
        change (List.nth index (memory s arraydef_0__formulas) (0,0,0) =
          sought (start_frame s bs ns)) in Hraw.
        assert (Hlookup : nth_error (memory s arraydef_0__formulas) index =
          Some (sought (start_frame s bs ns))).
        { rewrite <- Hraw. apply nth_error_nth'. lia. }
        destruct (represented_lookup _ _ _ _ Hrep Hlookup) as [q [Hq Hmeaning]].
        rewrite Hdecode in Hmeaning. injection Hmeaning as <-.
        exists meaning, index, []. split; [now apply store_meta_represents |].
        split; [now rewrite app_nil_r |]. split; [exact Hq |].
        apply store_result_read. lia.
      * split; [intros; now apply store_meta_other |]. split; reflexivity.
    + destruct (Z.eq_dec (Z.of_nat count) maximum).
      * split.
        -- rewrite full_flag by exact Hmeta. discriminate.
        -- split; [intros; now apply store_meta_other |]. split; reflexivity.
      * split.
        -- intro Hclear. exists (meaning ++ [p]), count, [p].
           split; [now apply fresh_represents |]. split; [reflexivity |]. split.
           ++ pose proof (Forall2_length Hrep) as Hsizes.
              change (@List.length raw_node (memory s arraydef_0__formulas) = count) in Hlength.
              change (@List.length raw_node (memory s arraydef_0__formulas) = length meaning) in Hsizes.
              rewrite nth_error_app2 by lia.
              replace (count - length meaning)%nat with 0%nat by lia. reflexivity.
           ++ now apply fresh_result.
        -- split; [intros; now apply fresh_other |]. apply fresh_io.
Qed.

Definition history_safe (s : Machine) (meaning : list formula) :=
  forall id, In id (memory s arraydef_0__theorems) ->
  exists p, nth_error meaning (Z.to_nat id) = Some p /\ derives p.

Lemma history_safe_extend s final meaning extra :
  memory final arraydef_0__theorems = memory s arraydef_0__theorems ->
  history_safe s meaning -> history_safe final (meaning ++ extra).
Proof.
  intros Hmemory Hsafe id Hin. rewrite Hmemory in Hin.
  destruct (Hsafe id Hin) as [p [Hlookup Hproof]].
  exists p. split; [now apply nth_error_extend |exact Hproof].
Qed.

Theorem generated_intern_history s bs ns meaning p :
  ready s -> represents s meaning -> history_safe s meaning ->
  decode meaning (sought (start_frame s bs ns)) = Some p ->
  exists final,
    exec (funcdef_0__intern bs ns) s = Some (tt, final) /\
    (List.nth 8 (memory final arraydef_0__meta) 0 = 0 ->
      exists next index extra,
        represents final next /\ next = meaning ++ extra /\
        nth_error next index = Some p /\
        List.nth 0 (memory final arraydef_0__meta) 0 = Z.of_nat index /\
        ready final /\ history_safe final next).
Proof.
  intros Hready Hrep Hsafe Hdecode.
  pose proof Hready as Hready_all.
  destruct Hready as [Hmeta [Hcount [Hflag Hlimit]]].
  destruct (generated_intern_represents s bs ns
    (length (memory s arraydef_0__formulas)) meaning p
    Hmeta Hcount Hflag eq_refl Hlimit Hrep Hdecode)
    as [final [Hrun [Haccept [Hframe Hio]]]].
  exists final. split; [exact Hrun |]. intro Hclear.
  destruct (Haccept Hclear) as [next [index [extra [Hnext [Hextend [Hlookup Hresult]]]]]].
  exists next, index, extra. split; [exact Hnext |]. split; [exact Hextend |].
  split; [exact Hlookup |]. split; [exact Hresult |]. split.
  - pose proof (generated_intern_correct s bs ns
      (length (memory s arraydef_0__formulas)) Hmeta Hcount Hflag eq_refl Hlimit) as Hactual.
    rewrite Hactual in Hrun. injection Hrun as <-.
    apply intern_output_ready with (count := length (memory s arraydef_0__formulas));
      [exact Hready_all |reflexivity |exact Hclear].
  - rewrite Hextend. apply history_safe_extend with (s := s); [|exact Hsafe].
    apply Hframe; discriminate.
Qed.
End NativeRepresentation.
