From CoqCP Require Import Options Imperative Execution.
From UniformMemoFixture Require Import UniformMemoProgram UniformMemoChains UniformMemoLoop UniformMemoPrelude Index Overflow SipHash UniformMemoHash.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module UniformMemoStorage.
Import UniformMemoLoop UniformMemoPrelude IndexExecution OverflowExecution SipHashExecution UniformMemoHash.

(* Relate the full generated lookup to a scan of the original entries.  The
   initial-state hypotheses below remain essential: in particular, neither
   acyclic bucket chains nor completeness of the hash-table indexing is
   established here. *)
Lemma reset_other (f : Frame) count size name : name <> arraydef_0__uniformMemoState ->
  memory (reset_machine f count size) name = memory (machine f) name.
Proof. intros H. unfold reset_machine, withMemory, modifyArray. cbn. case_decide; congruence. Qed.
Lemma hash_meta_length s tag a b :
  length (memory (hash_state s tag a b) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold hash_state. rewrite !store_meta_length, hash_work_other by discriminate. reflexivity. Qed.
Lemma post_meta_length (f : Frame) count size :
  let hashed := hash_state (reset_machine f count size) 51 (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth) in
  length (memory hashed arraydef_0__meta) = length (memory (machine f) arraydef_0__meta).
Proof. cbv beta iota zeta. rewrite hash_meta_length, reset_other by discriminate. reflexivity. Qed.
Lemma reset_same (f : Frame) count size :
  memory (reset_machine f count size) arraydef_0__uniformMemoState =
  <[0%nat := (count,size,0,0)]> (memory (machine f) arraydef_0__uniformMemoState).
Proof. reflexivity. Qed.
Lemma post_preserves_other (f : Frame) count size name :
  name <> arraydef_0__meta -> name <> arraydef_0__sipState ->
  name <> arraydef_0__uniformMemoState ->
  memory (hash_state (reset_machine f count size) 51
    (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth)) name =
  memory (machine f) name.
Proof. intros H1 H2 H3. rewrite hash_preserves_array by assumption. now apply reset_other. Qed.
Lemma post_state (f : Frame) count size :
  memory (hash_state (reset_machine f count size) 51
    (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth)) arraydef_0__uniformMemoState =
  <[0%nat := (count,size,0,0)]> (memory (machine f) arraydef_0__uniformMemoState).
Proof. rewrite hash_preserves_array by discriminate. apply reset_same. Qed.
Lemma post_state_length (f : Frame) count size :
  length (memory (hash_state (reset_machine f count size) 51
    (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth)) arraydef_0__uniformMemoState) =
  length (memory (machine f) arraydef_0__uniformMemoState).
Proof. rewrite post_state. apply length_insert. Qed.
Lemma post_state_nth (f : Frame) count size :
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  List.nth 0 (memory (hash_state (reset_machine f count size) 51
    (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth)) arraydef_0__uniformMemoState) (0,0,0,0) =
  (count,size,0,0).
Proof. intro H. rewrite post_state. apply nth_insert_same. lia. Qed.
Lemma post_start_entries (f : Frame) count size bucket pointer :
  entries_valid f count ->
  entries_valid (scan_start (setMachine (reset_frame f (Z.of_nat count) size)
    (hash_state (reset_machine f (Z.of_nat count) size) 51
      (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth))) bucket pointer) count.
Proof.
  intro H. unfold entries_valid in *. unfold scan_start, reset_frame.
  cbn [machine setNum setMachine]. rewrite post_preserves_other by discriminate. exact H.
Qed.
Lemma post_start_none (f : Frame) count size bucket pointer :
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  observed_result (scan_start (setMachine (reset_frame f (Z.of_nat count) size)
    (hash_state (reset_machine f (Z.of_nat count) size) 51
      (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth))) bucket pointer) = None.
Proof.
  intro H. unfold observed_result, scan_start, reset_frame.
  cbn [machine setNum setMachine]. rewrite post_state_nth by exact H. cbn.
  rewrite bool_decide_false by lia. reflexivity.
Qed.
Definition selected_bucket (f : Frame) size :=
  Z.to_nat (siphash24 (meta_value (machine f) 26) (meta_value (machine f) 27) 51
    (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth) mod size).
Definition selected_pointer (f : Frame) size :=
  Z.to_nat (List.nth (selected_bucket f size) (memory (machine f) arraydef_0__uniformMemoBuckets) 0).

Theorem lookup_from_initial_storage (f : Frame) count size oldfound oldvalue :
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) =
    (Z.of_nat count,size,oldfound,oldvalue) ->
  0 < size ->
  (28 < length (memory (machine f) arraydef_0__meta))%nat ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  0 < meta_value (machine f) 20 ->
  Z.of_nat (length (memory (machine f) arraydef_0__uniformMemoBuckets)) = size ->
  0 <= List.nth (selected_bucket f size) (memory (machine f) arraydef_0__uniformMemoBuckets) 0 <= Z.of_nat count ->
  entries_valid f count -> Z.of_nat count <= maximum ->
  let post := setMachine (reset_frame f (Z.of_nat count) size)
    (hash_state (reset_machine f (Z.of_nat count) size) 51
      (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth)) in
  let start := scan_start post (selected_bucket f size) (selected_pointer f size) in
  exists final, execLocal funcdef_0__uniformMemoGet_body f = Some (tt,final) /\
    observed_result final = scan_values start count (selected_pointer f size).
Proof.
  intros Hstate Hvalue Hsize Hmeta Hsip Hmod Hlength Hpointer Hentries Hlimit post start.
  assert (Hresetmeta : (28 < length (memory (reset_machine f (Z.of_nat count) size) arraydef_0__meta))%nat)
    by (rewrite reset_other by discriminate; exact Hmeta).
  assert (Hresetsip : (0 < length (memory (reset_machine f (Z.of_nat count) size) arraydef_0__sipState))%nat)
    by (rewrite reset_other by discriminate; exact Hsip).
  assert (Hresetmod : 0 < meta_value (reset_machine f (Z.of_nat count) size) 20).
  { unfold meta_value. rewrite reset_other by discriminate. exact Hmod. }
  assert (Hdigest : 0 <= siphash24 (meta_value (machine f) 26) (meta_value (machine f) 27) 51
    (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth) mod size < size)
    by (apply Z.mod_pos_bound; exact Hsize).
  assert (Hbucket : (selected_bucket f size < length (memory (machine f) arraydef_0__uniformMemoBuckets))%nat).
  { unfold selected_bucket. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
  assert (Hpointerval : Z.of_nat (selected_pointer f size) =
    List.nth (selected_bucket f size) (memory (machine f) arraydef_0__uniformMemoBuckets) 0).
  { unfold selected_pointer. apply Z2Nat.id. lia. }
  assert (Hpointerbound : (selected_pointer f size <= count)%nat).
  { apply Nat2Z.inj_le. rewrite Hpointerval. lia. }
  eapply (lookup_with_verified_hash_and_modulo f count size oldfound oldvalue
    (selected_bucket f size) (selected_pointer f size) 0 0); try eassumption.
  - lia.
  - unfold post, reset_frame. cbn [machine setMachine]. rewrite post_meta_length. exact Hmeta.
  - unfold selected_bucket. rewrite Z2Nat.id by lia.
    unfold meta_value. rewrite !reset_other by discriminate. reflexivity.
  - unfold post, reset_frame. cbn [machine setMachine]. rewrite post_preserves_other by discriminate. symmetry. exact Hpointerval.
  - unfold post, reset_frame. cbn [machine setMachine]. rewrite post_state_length. exact Hstate.
  - unfold post, reset_frame. cbn [machine setMachine]. now apply post_state_nth.
  - unfold start, post. now apply post_start_none.
Qed.
Lemma scan_values_ext f g fuel pointer :
  memory (machine f) arraydef_0__uniformMemoEntries = memory (machine g) arraydef_0__uniformMemoEntries ->
  nums f vardef_0__uniformMemoGet_node = nums g vardef_0__uniformMemoGet_node ->
  nums f vardef_0__uniformMemoGet_depth = nums g vardef_0__uniformMemoGet_depth ->
  scan_values f fuel pointer = scan_values g fuel pointer.
Proof.
  intros Hmem Hnode Hdepth. induction fuel as [|fuel IH] in pointer |- *; [reflexivity|].
  destruct pointer as [|pointer]; [reflexivity|]. cbn [scan_values].
  rewrite Hmem, Hnode, Hdepth. destruct (List.nth pointer
    (memory (machine g) arraydef_0__uniformMemoEntries) (0,0,0,0)) as [[[key depth] value] link].
  destruct (bool_decide (key = nums g vardef_0__uniformMemoGet_node /\
    depth = nums g vardef_0__uniformMemoGet_depth)); [reflexivity|apply IH].
Qed.
Lemma post_start_scan (f : Frame) count size bucket pointer fuel idx :
  scan_values (scan_start (setMachine (reset_frame f (Z.of_nat count) size)
    (hash_state (reset_machine f (Z.of_nat count) size) 51
      (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth))) bucket pointer) fuel idx =
  scan_values f fuel idx.
Proof.
  apply scan_values_ext.
  - unfold scan_start, reset_frame. cbn [machine setNum setMachine].
    rewrite post_preserves_other by discriminate. reflexivity.
  - unfold scan_start, reset_frame. cbn [nums setNum setMachine].
    repeat rewrite update_other by discriminate. reflexivity.
  - unfold scan_start, reset_frame. cbn [nums setNum setMachine].
    repeat rewrite update_other by discriminate. reflexivity.
Qed.
Corollary lookup_initial_scan (f : Frame) count size oldfound oldvalue :
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) =
    (Z.of_nat count,size,oldfound,oldvalue) ->
  0 < size -> (28 < length (memory (machine f) arraydef_0__meta))%nat ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  0 < meta_value (machine f) 20 ->
  Z.of_nat (length (memory (machine f) arraydef_0__uniformMemoBuckets)) = size ->
  0 <= List.nth (selected_bucket f size) (memory (machine f) arraydef_0__uniformMemoBuckets) 0 <= Z.of_nat count ->
  entries_valid f count -> Z.of_nat count <= maximum ->
  exists final, execLocal funcdef_0__uniformMemoGet_body f = Some (tt,final) /\
    observed_result final = scan_values f count (selected_pointer f size).
Proof.
  intros Hstate Hvalue Hsize Hmeta Hsip Hmod Hlength Hpointer Hentries Hlimit.
  destruct (lookup_from_initial_storage f count size oldfound oldvalue Hstate Hvalue Hsize Hmeta Hsip Hmod Hlength Hpointer Hentries Hlimit)
    as [final [Hexec Hscan]].
  exists final. split; [exact Hexec|]. rewrite Hscan. apply post_start_scan.
Qed.
Corollary lookup_initial_natural_scan (f : Frame) count size oldfound oldvalue key depth :
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) =
    (Z.of_nat count,size,oldfound,oldvalue) ->
  0 < size -> (28 < length (memory (machine f) arraydef_0__meta))%nat ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  0 < meta_value (machine f) 20 ->
  Z.of_nat (length (memory (machine f) arraydef_0__uniformMemoBuckets)) = size ->
  0 <= List.nth (selected_bucket f size) (memory (machine f) arraydef_0__uniformMemoBuckets) 0 <= Z.of_nat count ->
  entries_valid f count -> nonnegative_entries f count -> Z.of_nat count <= maximum ->
  nums f vardef_0__uniformMemoGet_node = Z.of_nat key ->
  nums f vardef_0__uniformMemoGet_depth = Z.of_nat depth ->
  exists final, execLocal funcdef_0__uniformMemoGet_body f = Some (tt,final) /\
    observed_result final = option_map Z.of_nat (UniformMemoChains.scan (natural_table f) count (selected_pointer f size) key depth).
Proof.
  intros Hstate Hvalue Hsize Hmeta Hsip Hmod Hlength Hpointer Hentries Hnonneg Hlimit Hkey Hdepth.
  destruct (lookup_initial_scan f count size oldfound oldvalue Hstate Hvalue Hsize Hmeta Hsip Hmod Hlength Hpointer Hentries Hlimit)
    as [final [Hexec Hscan]].
  exists final. split; [exact Hexec|]. rewrite Hscan.
  apply (scan_values_natural count f count (selected_pointer f size) key depth); try assumption.
  unfold selected_pointer. apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia.
Qed.
End UniformMemoStorage.
