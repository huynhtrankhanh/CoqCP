From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Intern Fresh Representation Append Inference.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module InternFrame.
Import IndexExecution InternExecution FreshExecution NativeRepresentation NativeInference.

Lemma store_meta_slot s written value slot : slot <> written ->
  List.nth slot (memory (store_meta s written value) arraydef_0__meta) 0 =
  List.nth slot (memory s arraydef_0__meta) 0.
Proof.
  intro H. unfold store_meta. cbn [withMemory memory].
  rewrite modify_meta. now apply nth_insert_other.
Qed.

Theorem intern_output_frame s bs ns count :
  let final := intern_output s bs ns count in
  length (memory final arraydef_0__meta) = length (memory s arraydef_0__meta) /\
  (forall slot, slot <> 0%nat -> slot <> 1%nat -> slot <> 8%nat ->
    List.nth slot (memory final arraydef_0__meta) 0 =
    List.nth slot (memory s arraydef_0__meta) 0) /\
  (forall name, name <> arraydef_0__meta -> name <> arraydef_0__formulas ->
    memory final name = memory s name).
Proof.
  unfold intern_output.
  destruct (find_from (start_frame s bs ns) 0 count) as [index |].
  - split; [apply store_meta_length |]. split.
    + intros. now apply store_meta_slot.
    + intros. now apply store_meta_other.
  - destruct (Z.eq_dec (Z.of_nat count) maximum).
    + split; [apply store_meta_length |]. split.
      * intros. now apply store_meta_slot.
      * intros. now apply store_meta_other.
    + split.
      * rewrite fresh_metadata. now repeat rewrite length_insert.
      * split.
        -- intros. rewrite fresh_metadata. now repeat rewrite nth_insert_other.
        -- intros. now apply fresh_other.
Qed.

Theorem intern_output_history_ready s bs ns count history_count :
  history_ready s history_count ->
  history_ready (intern_output s bs ns count) history_count.
Proof.
  intros [Hmeta [Hcount [Hlimit Hallocated]]].
  destruct (intern_output_frame s bs ns count) as [Hlength [Hslots Hother]].
  unfold history_ready. rewrite Hlength, Hslots by discriminate.
  rewrite Hother by discriminate. auto.
Qed.

Theorem intern_output_failed s bs ns count :
  ready s ->
  List.nth 8 (memory (intern_output s bs ns count) arraydef_0__meta) 0 <> 0 ->
  intern_output s bs ns count = store_meta s 8 1.
Proof.
  intros [_ [_ [Hclear _]]]. unfold intern_output.
  destruct (find_from (start_frame s bs ns) 0 count) as [index |].
  - rewrite store_result_flag, Hclear. contradiction.
  - destruct (Z.eq_dec (Z.of_nat count) maximum); [tauto |].
    rewrite fresh_flag, Hclear. contradiction.
Qed.
End InternFrame.
