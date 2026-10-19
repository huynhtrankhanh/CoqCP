From CoqCP Require Import Options Imperative Execution SetTheory.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Representation Canonical Append Inference.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ModusPonensExecution.
Import IndexExecution NativeRepresentation AppendExecution NativeInference.

Theorem generated_no_preserves s bs ns final name :
  exec (funcdef_0__no bs ns) s = Some (tt,final) -> memory final name = memory s name.
Proof.
  unfold funcdef_0__no. rewrite exec_eliminate. unfold funcdef_0__no_body.
  cbv beta iota zeta delta [loopString dropWithinLoop liftToWithinLoop Action_rect
    bind writeChar flush execLocal localStep step optionBind withOutput
    setMachine machine bools nums fst snd].
  intro Hrun. injection Hrun as <-. reflexivity.
Qed.

Theorem generated_mp_branch s bs ns ci ca implication antecedent tag a result :
  ns vardef_0__modusPonens_implication = Z.of_nat ci ->
  ns vardef_0__modusPonens_antecedent = Z.of_nat ca ->
  (ci < length (memory s arraydef_0__theorems))%nat ->
  (ca < length (memory s arraydef_0__theorems))%nat ->
  List.nth ci (memory s arraydef_0__theorems) 0 = implication ->
  List.nth ca (memory s arraydef_0__theorems) 0 = antecedent ->
  (Z.to_nat implication < length (memory s arraydef_0__formulas))%nat ->
  List.nth (Z.to_nat implication) (memory s arraydef_0__formulas) (0,0,0) = (tag,a,result) ->
  exec (funcdef_0__modusPonens bs ns) s =
    if bool_decide (tag = 3 /\ a = antecedent) then
      exec (funcdef_0__appendTheorem (fun _ => false)
        (update (fun _ => 0) vardef_0__appendTheorem_node result)) s
    else exec (funcdef_0__no (fun _ => false) (fun _ => 0)) s.
Proof.
  intros Hci Hca Hci_bound Hca_bound Himp Hant Hnode_bound Hnode.
  change (@List.nth Z ci (memory s arraydef_0__theorems) 0 = implication) in Himp.
  change (@List.nth Z ca (memory s arraydef_0__theorems) 0 = antecedent) in Hant.
  change (@List.nth (Z * Z * Z)%type (Z.to_nat implication)
    (memory s arraydef_0__formulas) (0,0,0) = (tag,a,result)) in Hnode.
  destruct (Z.eq_dec tag 3) as [Htag |Htag];
    destruct (Z.eq_dec a antecedent) as [Ha |Ha].
  all: unfold funcdef_0__modusPonens; rewrite exec_eliminate;
    unfold funcdef_0__modusPonens_body.
  all: repeat first [
    rewrite execLocal_bind | rewrite execLocal_lift
    | rewrite Hci | rewrite Hca | rewrite Nat2Z.id
    | rewrite nth_lt_default with (default := 0%Z)
    | rewrite nth_lt_default with (default := (0,0,0))
    | rewrite Himp | rewrite Hant | rewrite Hnode
    | rewrite lookupSame | rewrite lookupDifferent by discriminate
    | match goal with |- context [bool_decide ?P] =>
        first [rewrite (bool_decide_true P) by (intuition congruence)
          |rewrite (bool_decide_false P) by (intuition congruence)]
      end
    | progress cbn [shortCircuitAnd bind numberLocalGet numberLocalSet retrieve
        execLocal localStep step optionBind nums bools machine setMachine setNum
        fst snd Imperative.update decide decide_rel
        variableIndexEqualityDecidablevarsfuncdef_0__modusPonens
        varsfuncdef_0__modusPonens_rec]
    | case_decide; [|lia]
  ].
  all: lazymatch goal with |- context [exec ?callee ?initial] =>
    destruct (exec callee initial) as [[[] after] |]; reflexivity
  end.
Qed.

Theorem generated_modus_ponens_safe s bs ns count ci ca final meaning :
  history_ready s count -> represents s meaning -> history_safe s meaning ->
  ns vardef_0__modusPonens_implication = Z.of_nat ci ->
  ns vardef_0__modusPonens_antecedent = Z.of_nat ca ->
  (ci < count)%nat -> (ca < count)%nat ->
  exec (funcdef_0__modusPonens bs ns) s = Some (tt,final) -> history_safe final meaning.
Proof.
  intros [Hmeta [Hcount [Hlimit Hallocated]]] Hrep Hsafe Hci Hca Hci_count Hca_count Hrun.
  set (implication := List.nth ci (memory s arraydef_0__theorems) 0).
  set (antecedent := List.nth ca (memory s arraydef_0__theorems) 0).
  assert (Hci_bound : (ci < length (memory s arraydef_0__theorems))%nat) by lia.
  assert (Hca_bound : (ca < length (memory s arraydef_0__theorems))%nat) by lia.
  assert (Himp_in : In implication (memory s arraydef_0__theorems)).
  { unfold implication. now apply List.nth_In. }
  assert (Hant_in : In antecedent (memory s arraydef_0__theorems)).
  { unfold antecedent. now apply List.nth_In. }
  destruct (Hsafe _ Himp_in) as [p [Hp Hproof]].
  destruct (CanonicalArena.related_lookup_right _ _ _ _ _ Hrep Hp)
    as [[[tag a] result] [Hraw Hdecode]].
  assert (Hnode_bound : (Z.to_nat implication < length (memory s arraydef_0__formulas))%nat).
  { change (Z.to_nat implication < @List.length raw_node (memory s arraydef_0__formulas))%nat.
    apply nth_error_Some. rewrite Hraw. discriminate. }
  assert (Hnode : List.nth (Z.to_nat implication)
    (memory s arraydef_0__formulas) (0,0,0) = (tag,a,result)).
  { exact (@List.nth_error_nth raw_node (memory s arraydef_0__formulas)
      (Z.to_nat implication) (tag,a,result) (0,0,0) Hraw). }
  rewrite (generated_mp_branch s bs ns ci ca implication antecedent tag a result
    Hci Hca Hci_bound Hca_bound eq_refl eq_refl Hnode_bound Hnode) in Hrun.
  case_bool_decide as Hcheck.
  - destruct Hcheck as [-> ->].
    eapply generated_append_safe; try eassumption.
    change (valid_id meaning result).
    now apply modus_ponens_ids with (s := s) (implication := implication) (antecedent := antecedent).
  - apply history_safe_frame with (s := s); [|exact Hsafe].
    eapply generated_no_preserves. exact Hrun.
Qed.

Theorem generated_modus_ponens_accepts s bs ns ci ca implication antecedent meaning p q :
  CanonicalArena.canonical s meaning -> word antecedent ->
  ns vardef_0__modusPonens_implication = Z.of_nat ci ->
  ns vardef_0__modusPonens_antecedent = Z.of_nat ca ->
  nth_error (memory s arraydef_0__theorems) ci = Some implication ->
  nth_error (memory s arraydef_0__theorems) ca = Some antecedent ->
  nth_error meaning (Z.to_nat implication) = Some (SetTheory.implies p q) ->
  nth_error meaning (Z.to_nat antecedent) = Some p ->
  exists result, nth_error meaning (Z.to_nat result) = Some q /\
    exec (funcdef_0__modusPonens bs ns) s =
      exec (funcdef_0__appendTheorem (fun _ => false)
        (update (fun _ => 0) vardef_0__appendTheorem_node result)) s.
Proof.
  intros [Hrep [Hunique Hnormal]] Hantecedent Hci Hca Hproofci Hproofca Himp Harg.
  destruct (CanonicalArena.related_lookup_right _ _ _ _ _ Hrep Himp)
    as [raw [Hraw Hdecode]].
  assert (Hnormalraw : CanonicalArena.normal raw).
  { apply (proj1 (Forall_forall _ _) Hnormal). now apply nth_error_In in Hraw. }
  destruct (CanonicalArena.decode_implication _ _ _ _ Hnormalraw Hdecode)
    as [left [result [-> [Hleftword [Hresultword [Hleft Hresult]]]]]].
  assert (Hleft_id : left = antecedent).
  { apply (proj2 (CanonicalArena.formula_id_equality _ _ _ _ _
      Hunique Hleftword Hantecedent Hleft Harg)). reflexivity. }
  subst left. exists result. split; [exact Hresult |].
  assert (Hci_bound : (ci < length (memory s arraydef_0__theorems))%nat).
  { apply nth_error_Some. rewrite Hproofci. discriminate. }
  assert (Hca_bound : (ca < length (memory s arraydef_0__theorems))%nat).
  { apply nth_error_Some. rewrite Hproofca. discriminate. }
  assert (Hnode_bound : (Z.to_nat implication < length (memory s arraydef_0__formulas))%nat).
  { change (Z.to_nat implication < @List.length raw_node (memory s arraydef_0__formulas))%nat.
    apply nth_error_Some. rewrite Hraw. discriminate. }
  rewrite (generated_mp_branch s bs ns ci ca implication antecedent 3 antecedent result
    Hci Hca Hci_bound Hca_bound
    (@List.nth_error_nth Z _ _ _ 0 Hproofci)
    (@List.nth_error_nth Z _ _ _ 0 Hproofca) Hnode_bound
    (@List.nth_error_nth raw_node _ _ _ (0,0,0) Hraw)).
  rewrite bool_decide_true by auto. reflexivity.
Qed.
End ModusPonensExecution.
