From CoqCP Require Import Options Imperative Execution SetTheory.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow Intern Fresh Representation Append Inference InternFrame.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module GeneralizationExecution.
Import IndexExecution InternExecution FreshExecution NativeRepresentation AppendExecution
  NativeInference InternFrame.

Definition intern_arguments source :=
  update (update (update (fun _ => 0) vardef_0__intern_tag 4)
    vardef_0__intern_a source) vardef_0__intern_b 0.
Definition generalized_state s source :=
  intern_output s (fun _ => false) (intern_arguments source)
    (length (memory s arraydef_0__formulas)).

Theorem generated_generalize_step s bs ns index source :
  ready s -> ns vardef_0__generalize_theorem = Z.of_nat index ->
  (index < length (memory s arraydef_0__theorems))%nat ->
  List.nth index (memory s arraydef_0__theorems) 0 = source ->
  exec (funcdef_0__generalize bs ns) s =
    exec (funcdef_0__appendTheorem (fun _ => false)
      (update (fun _ => 0) vardef_0__appendTheorem_node
        (List.nth 0 (memory (generalized_state s source) arraydef_0__meta) 0)))
      (generalized_state s source).
Proof.
  intros [Hmeta [Hcount [Hflag Hlimit]]] Hindex Hbound Hsource.
  change (@List.nth Z index (memory s arraydef_0__theorems) 0 = source) in Hsource.
  pose proof (generated_intern_correct s (fun _ => false) (intern_arguments source)
    (length (memory s arraydef_0__formulas)) Hmeta Hcount Hflag eq_refl Hlimit) as Hintern.
  change (exec (funcdef_0__intern (fun _ => false) (intern_arguments source)) s =
    Some (tt, generalized_state s source)) in Hintern.
  assert (Hfinal_meta : (0 < length (memory (generalized_state s source) arraydef_0__meta))%nat).
  { unfold generalized_state. destruct (intern_output_frame s (fun _ => false)
      (intern_arguments source) (length (memory s arraydef_0__formulas))) as [Hlength _].
    rewrite Hlength. lia. }
  unfold intern_arguments in Hintern.
  unfold funcdef_0__generalize. rewrite exec_eliminate. unfold funcdef_0__generalize_body.
  repeat first [rewrite execLocal_bind | rewrite execLocal_lift
    | rewrite Hindex | rewrite Nat2Z.id
    | rewrite nth_lt_default with (default := 0%Z)
    | rewrite Hsource | rewrite Hintern
    | progress cbn [bind numberLocalGet retrieve execLocal localStep step optionBind
        nums bools machine setMachine fst snd]
    | case_decide; [|lia]
  ].
  lazymatch goal with
  | |- optionBind (optionBind (optionBind ?lhs ?k1) ?k2) ?k3 = ?rhs =>
    change (optionBind (optionBind (optionBind rhs k1) k2) k3 = rhs);
    destruct rhs as [[[] after] |]; reflexivity
  end.
Qed.
Lemma generated_append_formula_frame s bs ns count final :
  history_ready s count ->
  exec (funcdef_0__appendTheorem bs ns) s = Some (tt,final) ->
  memory final arraydef_0__formulas = memory s arraydef_0__formulas.
Proof.
  intros [Hmeta [Hcount [Hlimit Hallocated]]] Hrun.
  destruct (Z.eq_dec (List.nth 8 (memory s arraydef_0__meta) 0) 0) as [Hclear |Herror].
  - destruct (Z.eq_dec (Z.of_nat count) maximum) as [Hfull |Hspace].
    + rewrite (generated_append_full s bs ns Hmeta (eq_trans Hcount Hfull) Hclear) in Hrun.
      injection Hrun as <-. now apply store_meta_other.
    + destruct (generated_append_fits_post s bs ns count final Hmeta Hcount Hclear
        ltac:(lia) Hrun) as [_ [_ [_ [_ Hframe]]]].
      apply Hframe; discriminate.
  - rewrite (generated_append_error s bs ns Hmeta Herror) in Hrun.
    now injection Hrun as <-.
Qed.

Lemma intern_arguments_decode s meaning source p :
  nth_error meaning (Z.to_nat source) = Some p ->
  decode meaning (sought (start_frame s (fun _ => false) (intern_arguments source))) =
    Some (SetTheory.all p).
Proof.
  intro Hsource.
  change (option_map SetTheory.all (nth_error meaning (Z.to_nat source)) =
    Some (SetTheory.all p)).
  now rewrite Hsource.
Qed.

Theorem generated_generalization_safe s bs ns count index final meaning :
  ready s -> history_ready s count -> represents s meaning -> history_safe s meaning ->
  ns vardef_0__generalize_theorem = Z.of_nat index -> (index < count)%nat ->
  exec (funcdef_0__generalize bs ns) s = Some (tt,final) ->
  exists next extra, next = meaning ++ extra /\ represents final next /\ history_safe final next.
Proof.
  intros Hready Hhistory Hrep Hsafe Hindex Hindex_count Hrun.
  set (source := List.nth index (memory s arraydef_0__theorems) 0).
  assert (Hbound : (index < length (memory s arraydef_0__theorems))%nat).
  { destruct Hhistory as [_ [_ [_ Hallocated]]]. lia. }
  assert (Hsource_in : In source (memory s arraydef_0__theorems)).
  { unfold source. now apply List.nth_In. }
  destruct (Hsafe source Hsource_in) as [p [Hsource Hproof]].
  rewrite (generated_generalize_step s bs ns index source Hready Hindex Hbound eq_refl) in Hrun.
  assert (Hmiddle_history : history_ready (generalized_state s source) count).
  { now apply intern_output_history_ready. }
  destruct (Z.eq_dec
    (List.nth 8 (memory (generalized_state s source) arraydef_0__meta) 0) 0)
    as [Hclear |Herror].
  - destruct (generated_intern_history s (fun _ => false) (intern_arguments source)
      meaning (SetTheory.all p) Hready Hrep Hsafe
      (intern_arguments_decode s meaning source p Hsource))
      as [middle [Hintern Haccept]].
    destruct Hready as [Hmeta [Hcount [Hflag Hlimit]]].
    pose proof (generated_intern_correct s (fun _ => false) (intern_arguments source)
      (length (memory s arraydef_0__formulas)) Hmeta Hcount Hflag eq_refl Hlimit) as Hactual.
    fold (generalized_state s source) in Hactual.
    rewrite Hactual in Hintern. injection Hintern as <-.
    destruct (Haccept Hclear) as
      [next [result [extra [Hnext [Hextend [Hlookup [Hresult [Hnext_ready Hnext_safe]]]]]]]].
    exists next, extra. split; [exact Hextend |]. split.
    + unfold represents. rewrite (generated_append_formula_frame _ _ _ _ _ Hmiddle_history Hrun).
      exact Hnext.
    + destruct Hmiddle_history as [Hm [Hc [Hl Ha]]].
      eapply generated_append_safe; try eassumption.
      change (valid_id next (List.nth 0 (memory (generalized_state s source) arraydef_0__meta) 0)).
      rewrite Hresult. unfold valid_id. rewrite Nat2Z.id.
      exists (SetTheory.all p). split; [exact Hlookup |now apply SetTheory.d_gen].
  - assert (Hfailed : generalized_state s source = store_meta s 8 1).
    { now apply intern_output_failed. }
    destruct Hmiddle_history as [Hm _].
    rewrite (generated_append_error _ _ _ Hm Herror) in Hrun.
    injection Hrun as <-. rewrite Hfailed.
    exists meaning, []. split; [now rewrite app_nil_r |]. split.
    + now apply store_meta_represents.
    + now apply store_meta_safe.
Qed.
Theorem generated_generalization_post s bs ns count index final meaning p :
  ready s -> history_ready s count -> represents s meaning -> history_safe s meaning ->
  ns vardef_0__generalize_theorem = Z.of_nat index -> (index < count)%nat ->
  nth_error meaning
    (Z.to_nat (List.nth index (memory s arraydef_0__theorems) 0)) = Some p ->
  exec (funcdef_0__generalize bs ns) s = Some (tt,final) ->
  List.nth 8 (memory final arraydef_0__meta) 0 = 0 ->
  exists next result extra,
    next = meaning ++ extra /\ represents final next /\ history_safe final next /\
    nth_error next result = Some (SetTheory.all p) /\
    nth_error (memory final arraydef_0__theorems) count = Some (Z.of_nat result) /\
    List.nth 3 (memory final arraydef_0__meta) 0 = Z.of_nat (S count).
Proof.
  intros Hready Hhistory Hrep Hsafe Hindex Hindex_count Hsource Hrun Hfinal_clear.
  set (source := List.nth index (memory s arraydef_0__theorems) 0) in *.
  assert (Hbound : (index < length (memory s arraydef_0__theorems))%nat).
  { destruct Hhistory as [_ [_ [_ Hallocated]]]. lia. }
  destruct (Hsafe source ltac:(unfold source; now apply List.nth_In)) as [q [Hq Hproof]].
  rewrite Hsource in Hq. injection Hq as <-.
  rewrite (generated_generalize_step s bs ns index source Hready Hindex Hbound eq_refl) in Hrun.
  pose proof (intern_output_history_ready s (fun _ => false) (intern_arguments source)
    (length (memory s arraydef_0__formulas)) count Hhistory) as Hmiddle_history.
  change (history_ready (generalized_state s source) count) in Hmiddle_history.
  destruct Hmiddle_history as [Hm [Hc [Hl Ha]]].
  assert (Hclear : List.nth 8 (memory (generalized_state s source) arraydef_0__meta) 0 = 0).
  { destruct (Z.eq_dec (List.nth 8 (memory (generalized_state s source) arraydef_0__meta) 0) 0)
      as [Hclear |Herror]; [exact Hclear |].
    rewrite (generated_append_error _ _ _ Hm Herror) in Hrun.
    injection Hrun as <-. contradiction. }
  assert (Hspace : Z.of_nat count < maximum).
  { destruct (Z.eq_dec (Z.of_nat count) maximum) as [Hfull |Hspace]; [|lia].
    rewrite (generated_append_full _ _ _ Hm (eq_trans Hc Hfull) Hclear) in Hrun.
    injection Hrun as <-. rewrite full_flag in Hfinal_clear by exact Hm. discriminate. }
  destruct (generated_intern_history s (fun _ => false) (intern_arguments source)
    meaning (SetTheory.all p) Hready Hrep Hsafe
    (intern_arguments_decode s meaning source p Hsource)) as [middle [Hintern Haccept]].
  destruct Hready as [Hmeta [Hcount [Hflag Hlimit]]].
  pose proof (generated_intern_correct s (fun _ => false) (intern_arguments source)
    (length (memory s arraydef_0__formulas)) Hmeta Hcount Hflag eq_refl Hlimit) as Hactual.
  fold (generalized_state s source) in Hactual.
  rewrite Hactual in Hintern. injection Hintern as <-.
  destruct (Haccept Hclear) as
    [next [result [extra [Hnext [Hextend [Hlookup [Hresult [Hnext_ready Hnext_safe]]]]]]]].
  destruct (generated_append_fits_post _ _ _ count final Hm Hc Hclear Hspace Hrun)
    as [Hhistory_written [Hnew_count Hframe]].
  exists next, result, extra. split; [exact Hextend |]. split.
  - unfold represents. rewrite (generated_append_formula_frame (generalized_state s source) _ _ count final
      ltac:(unfold history_ready; auto) Hrun). exact Hnext.
  - split.
    + eapply generated_append_safe; try eassumption.
      change (valid_id next
          (List.nth 0 (memory (generalized_state s source) arraydef_0__meta) 0)).
      rewrite Hresult. unfold valid_id. rewrite Nat2Z.id.
      exists (SetTheory.all p). split; [exact Hlookup |now apply SetTheory.d_gen].
    + split; [exact Hlookup |]. split; [|exact Hnew_count].
      rewrite Hhistory_written, lookupSame, Hresult.
      rewrite nth_error_nth' with (d := 0%Z).
      * rewrite OverflowExecution.nth_insert_same; [reflexivity |].
        rewrite growList_length. lia.
      * rewrite length_insert, growList_length. lia.
Qed.
End GeneralizationExecution.
