From CoqCP Require Import Options Imperative Execution SetTheory.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Representation Append.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module NativeInference.
Import SetTheory IndexExecution NativeRepresentation AppendExecution.

Lemma axiom_derivable witness : derives (axiom_formula witness).
Proof. destruct witness; cbn [axiom_formula]; constructor; constructor. Qed.

Theorem modus_ponens_ids s meaning implication antecedent result :
  represents s meaning -> history_safe s meaning ->
  In implication (memory s arraydef_0__theorems) ->
  In antecedent (memory s arraydef_0__theorems) ->
  nth_error (memory s arraydef_0__formulas) (Z.to_nat implication) =
    Some (3,antecedent,result) ->
  valid_id meaning result.
Proof.
  intros Hrep Hsafe Himp Harg Hnode.
  destruct (represented_lookup _ _ _ _ Hrep Hnode) as [p [Hp Hdecode]].
  change ((match nth_error meaning (Z.to_nat antecedent),
    nth_error meaning (Z.to_nat result) with
    | Some lp, Some rp => Some (implies lp rp)
    | _, _ => None end) = Some p) in Hdecode.
  destruct (nth_error meaning (Z.to_nat antecedent)) as [left |] eqn:Hleft; [|discriminate].
  destruct (nth_error meaning (Z.to_nat result)) as [right |] eqn:Hright; [|discriminate].
  injection Hdecode as <-.
  destruct (Hsafe _ Himp) as [p [Himplication Hproof]].
  rewrite Hp in Himplication. injection Himplication as <-.
  destruct (Hsafe _ Harg) as [p [Hantecedent Hargproof]].
  rewrite Hleft in Hantecedent. injection Hantecedent as <-.
  exists right. split; [exact Hright |]. now apply d_mp with (p := left).
Qed.

Theorem generalization_ids s meaning source result :
  represents s meaning -> history_safe s meaning ->
  In source (memory s arraydef_0__theorems) ->
  nth_error (memory s arraydef_0__formulas) (Z.to_nat result) = Some (4,source,0) ->
  valid_id meaning result.
Proof.
  intros Hrep Hsafe Hin Hnode.
  destruct (represented_lookup _ _ _ _ Hrep Hnode) as [p [Hp Hdecode]].
  change (option_map all (nth_error meaning (Z.to_nat source)) = Some p) in Hdecode.
  destruct (Hsafe _ Hin) as [q [Hq Hproof]]. rewrite Hq in Hdecode.
  injection Hdecode as <-. exists (all q). split; [exact Hp |now apply d_gen].
Qed.

Theorem axiom_id meaning result witness :
  nth_error meaning (Z.to_nat result) = Some (axiom_formula witness) ->
  valid_id meaning result.
Proof. intro H. exists (axiom_formula witness). split; [exact H |apply axiom_derivable]. Qed.

Theorem restate_id s meaning id :
  history_safe s meaning -> In id (memory s arraydef_0__theorems) -> valid_id meaning id.
Proof. intros Hsafe Hin. exact (Hsafe _ Hin). Qed.

Definition history_ready (s : Machine) count :=
  (8 < length (memory s arraydef_0__meta))%nat /\
  List.nth 3 (memory s arraydef_0__meta) 0 = Z.of_nat count /\
  Z.of_nat count <= maximum /\ (count <= length (memory s arraydef_0__theorems))%nat.

Theorem append_modus_ponens s bs ns count final meaning implication antecedent :
  history_ready s count -> represents s meaning -> history_safe s meaning ->
  In implication (memory s arraydef_0__theorems) ->
  In antecedent (memory s arraydef_0__theorems) ->
  nth_error (memory s arraydef_0__formulas) (Z.to_nat implication) =
    Some (3,antecedent,ns vardef_0__appendTheorem_node) ->
  exec (funcdef_0__appendTheorem bs ns) s = Some (tt,final) -> history_safe final meaning.
Proof.
  intros [Hmeta [Hcount [Hlimit Hallocated]]] Hrep Hsafe Himp Harg Hnode Hrun.
  eapply generated_append_safe; try eassumption.
  now apply modus_ponens_ids with (s := s) (implication := implication) (antecedent := antecedent).
Qed.

Theorem append_generalization s bs ns count final meaning source :
  history_ready s count -> represents s meaning -> history_safe s meaning ->
  In source (memory s arraydef_0__theorems) ->
  nth_error (memory s arraydef_0__formulas) (Z.to_nat (ns vardef_0__appendTheorem_node)) =
    Some (4,source,0) ->
  exec (funcdef_0__appendTheorem bs ns) s = Some (tt,final) -> history_safe final meaning.
Proof.
  intros [Hmeta [Hcount [Hlimit Hallocated]]] Hrep Hsafe Hin Hnode Hrun.
  eapply generated_append_safe; try eassumption.
  now apply generalization_ids with (s := s) (source := source).
Qed.

Theorem append_axiom s bs ns count final meaning witness :
  history_ready s count -> history_safe s meaning ->
  nth_error meaning (Z.to_nat (ns vardef_0__appendTheorem_node)) =
    Some (axiom_formula witness) ->
  exec (funcdef_0__appendTheorem bs ns) s = Some (tt,final) -> history_safe final meaning.
Proof.
  intros [Hmeta [Hcount [Hlimit Hallocated]]] Hsafe Hformula Hrun.
  eapply generated_append_safe; try eassumption. now apply axiom_id with (witness := witness).
Qed.
End NativeInference.
