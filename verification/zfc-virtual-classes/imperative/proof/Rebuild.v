From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash HashScan InternTail HashTable Rehash.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module RebuildExecution.
Import IndexExecution SipHashExecution InternTailExecution HashTableInvariant RehashExecution.
Definition ready (s : Machine) count :=
  (28 < length (memory s arraydef_0__meta))%nat /\
  (0 < length (memory s arraydef_0__sipState))%nat /\
  0 < meta_value s 20 /\
  meta_value s 20 <= Z.of_nat (length (memory s arraydef_0__formulaBuckets)) /\
  (count <= length (memory s arraydef_0__formulas))%nat /\
  (count <= length (memory s arraydef_0__formulaLinks))%nat /\ Z.of_nat count <= maximum.
Definition step_state (s : Machine) i := relink_state (hashed_entry s i) i (entry_bucket s i).
Definition step_frame (f : Frame) i := relink_frame f (hashed_entry (machine f) i) i (entry_bucket (machine f) i).

Lemma hashed_other s i name : name <> arraydef_0__meta -> name <> arraydef_0__sipState ->
  memory (hashed_entry s i) name = memory s name.
Proof. intros. unfold hashed_entry. destruct (tuple_at s i) as [[x y] z]. now apply hash_preserves_array. Qed.
Lemma hashed_meta s i j : j <> 21%nat -> j <> 28%nat -> meta_value (hashed_entry s i) j = meta_value s j.
Proof. intros. unfold hashed_entry. destruct (tuple_at s i) as [[x y] z]. now apply hash_preserves_meta. Qed.
Lemma hashed_meta_length s i : length (memory (hashed_entry s i) arraydef_0__meta) =
  length (memory s arraydef_0__meta).
Proof. unfold hashed_entry. destruct (tuple_at s i) as [[x y] z]. apply hash_meta_length. Qed.
Lemma hashed_sip_length s i : length (memory (hashed_entry s i) arraydef_0__sipState) =
  length (memory s arraydef_0__sipState).
Proof. unfold hashed_entry. destruct (tuple_at s i) as [[x y] z]. unfold hash_state.
  rewrite !store_meta_other by discriminate. apply hash_work_length. Qed.
Lemma step_formula s i : memory (step_state s i) arraydef_0__formulas = memory s arraydef_0__formulas.
Proof. unfold step_state. rewrite relink_other by discriminate. now apply hashed_other. Qed.
Lemma step_meta s i j : j <> 21%nat -> j <> 28%nat -> meta_value (step_state s i) j = meta_value s j.
Proof. intros. unfold step_state, meta_value. rewrite relink_other by discriminate. now apply hashed_meta. Qed.
Lemma step_ready s i count : ready s count -> ready (step_state s i) count.
Proof.
  intros [Hmeta [Hsip [Hpositive [Hcapacity [Hformulas [Hlinks Hlimit]]]]]].
  unfold ready, step_state. split.
  - rewrite relink_other by discriminate. now rewrite hashed_meta_length.
  - split; [rewrite relink_other by discriminate; now rewrite hashed_sip_length|].
    split; [change (0 < meta_value (step_state s i) 20); now rewrite step_meta by lia|].
    split.
    + unfold meta_value. rewrite relink_other by discriminate. fold (meta_value (hashed_entry s i) 20).
      rewrite hashed_meta by lia. rewrite relink_buckets, length_insert, hashed_other by discriminate. exact Hcapacity.
    + split; [rewrite relink_other by discriminate; now rewrite hashed_other by discriminate|].
      split; [rewrite relink_links, length_insert, hashed_other by discriminate; exact Hlinks|exact Hlimit].
Qed.
Lemma step_key s i tuple : keyed_bucket (step_state s i) tuple = keyed_bucket s tuple.
Proof. unfold keyed_bucket. destruct tuple as [[x y] z]. now rewrite !step_meta by lia. Qed.
Lemma indexed_bucket_ext s n h k : (forall tuple, h tuple = k tuple) -> indexed s n h -> indexed s n k.
Proof.
  intros Heq [Htable [Hheads Hindexed]]. split; [exact Htable|]. split; [exact Hheads|].
  intros i Hi. destruct (Hindexed i Hi) as [Hrange Hchain]. rewrite <- Heq. split; assumption.
Qed.
Lemma step_indexed s i count h : ready s count -> (i < count)%nat -> indexed s i h ->
  (forall tuple, h tuple = keyed_bucket s tuple) -> indexed (step_state s i) (S i) h.
Proof.
  intros Hready Hi Hindexed Hkey.
  destruct Hready as [Hmeta [Hsip [Hpositive [Hcapacity [Hformulas [Hlinks Hlimit]]]]]].
  assert (Htuple : tuple_at (hashed_entry s i) i = tuple_at s i).
  { unfold tuple_at. now rewrite hashed_other by discriminate. }
  unfold step_state. rewrite entry_bucket_correct by assumption. rewrite <- Hkey, <- Htuple.
  apply relink_indexed.
  - now apply hashed_indexed.
  - rewrite hashed_other by discriminate. lia.
  - rewrite hashed_other by discriminate. lia.
  - rewrite Htuple, hashed_other by discriminate. rewrite Hkey. unfold keyed_bucket.
    destruct (tuple_at s i) as [[x y] z].
    pose proof (Z.mod_pos_bound (siphash24 (meta_value s 26) (meta_value s 27) x y z)
      (meta_value s 20) Hpositive) as Hbounds.
    pose proof (Z2Nat.id (siphash24 (meta_value s 26) (meta_value s 27) x y z mod meta_value s 20) ltac:(lia)). lia.
Qed.

Theorem generated_step f count total remaining index :
  ready (machine f) count -> (index < count)%nat -> total - Z.of_nat remaining - 1 = Z.of_nat index ->
  execLocal (relink_body funcdef_0__formulaHash total remaining) f = Some (KeepGoing,step_frame f index).
Proof.
  intros [Hmeta [Hsip [Hpositive [Hcapacity [Hformulas [Hlinks Hlimit]]]]]] Hi Hindex.
  apply generated_relink; try assumption; lia.
Qed.

Theorem generated_rebuild_loop fuel (f : Frame) count start h :
  (start + fuel = count)%nat -> ready (machine f) count -> indexed (machine f) start h ->
  (forall tuple, h tuple = keyed_bucket (machine f) tuple) ->
  exists final, execLocal (loop fuel (relink_body funcdef_0__formulaHash (Z.of_nat count))) f = Some (tt,final) /\
    ready (machine final) count /\ indexed (machine final) count h /\
    (forall tuple, h tuple = keyed_bucket (machine final) tuple) /\
    memory (machine final) arraydef_0__formulas = memory (machine f) arraydef_0__formulas.
Proof.
  induction fuel as [|fuel IH] in f, start |- *.
  - intros Hsum Hready Hindexed Hkey. assert (start = count) as -> by lia.
    exists f. split; [reflexivity|]. split; [exact Hready|]. split; [exact Hindexed|]. split; [exact Hkey|reflexivity].
  - intros Hsum Hready Hindexed Hkey.
    rewrite loop_S, execLocal_bind.
    rewrite (generated_step f count (Z.of_nat count) fuel start Hready ltac:(lia) ltac:(lia)).
    cbn [optionBind fst snd].
    assert (Hready' : ready (machine (step_frame f start)) count) by (apply step_ready; exact Hready).
    assert (Hindexed' : indexed (machine (step_frame f start)) (S start) h).
    { apply (step_indexed _ _ count); [exact Hready|lia|exact Hindexed|exact Hkey]. }
    assert (Hkey' : forall tuple, h tuple = keyed_bucket (machine (step_frame f start)) tuple).
    { intro tuple. change (h tuple = keyed_bucket (step_state (machine f) start) tuple).
      rewrite step_key. apply Hkey. }
    destruct (IH (step_frame f start) (S start) ltac:(lia) Hready' Hindexed' Hkey')
      as [final [Hrun [Hready'' [Hindexed'' [Hkey'' Hformula]]]]].
    exists final. split; [exact Hrun|]. split; [exact Hready''|]. split; [exact Hindexed''|].
    split; [exact Hkey''|]. rewrite Hformula. apply step_formula.
Qed.

Definition preserved (s t : Machine) :=
  (forall name, name <> arraydef_0__meta -> name <> arraydef_0__sipState ->
    name <> arraydef_0__formulaLinks -> name <> arraydef_0__formulaBuckets -> memory t name = memory s name) /\
  (forall i, i <> 21%nat -> i <> 28%nat -> meta_value t i = meta_value s i) /\
  stdin t = stdin s /\ stdout t = stdout s.
Lemma step_preserved s i : preserved s (step_state s i).
Proof.
  split.
  - intros name Hmeta Hsip Hlinks Hbucket. unfold step_state.
    rewrite relink_other by assumption. now apply hashed_other.
  - split; [intros; now apply step_meta|].
    unfold step_state, hashed_entry. destruct (tuple_at s i) as [[x y] z].
    split; reflexivity.
Qed.
Lemma preserved_refl s : preserved s s.
Proof. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. Qed.
Lemma preserved_trans s t u : preserved s t -> preserved t u -> preserved s u.
Proof.
  intros [Harray [Hmeta [Hin Hout]]] [Harray' [Hmeta' [Hin' Hout']]].
  split; [intros; now rewrite Harray', Harray by assumption|].
  split; [intros; now rewrite Hmeta', Hmeta by assumption|]. split; congruence.
Qed.
Theorem generated_rebuild_preserved fuel (f : Frame) count start final :
  (start + fuel = count)%nat -> ready (machine f) count ->
  execLocal (loop fuel (relink_body funcdef_0__formulaHash (Z.of_nat count))) f = Some (tt,final) ->
  preserved (machine f) (machine final).
Proof.
  induction fuel as [|fuel IH] in f, start |- *.
  - intros Hsum Hready Hrun. cbn [loop execLocal] in Hrun. injection Hrun as <-. apply preserved_refl.
  - intros Hsum Hready Hrun. rewrite loop_S, execLocal_bind in Hrun.
    rewrite (generated_step f count (Z.of_nat count) fuel start Hready ltac:(lia) ltac:(lia)) in Hrun.
    cbn [optionBind fst snd] in Hrun.
    apply (preserved_trans _ (machine (step_frame f start))).
    + apply step_preserved.
    + apply (IH (step_frame f start) (S start)); [lia| |exact Hrun]. now apply step_ready.
Qed.

Lemma step_length s i name : length (memory (step_state s i) name) = length (memory s name).
Proof.
  destruct name; unfold step_state; now repeat first
    [rewrite relink_other by discriminate |rewrite relink_links |rewrite relink_buckets
    |rewrite length_insert |rewrite hashed_other by discriminate
    |rewrite hashed_meta_length |rewrite hashed_sip_length].
Qed.
Theorem generated_rebuild_lengths fuel (f : Frame) count start final :
  (start + fuel = count)%nat -> ready (machine f) count ->
  execLocal (loop fuel (relink_body funcdef_0__formulaHash (Z.of_nat count))) f = Some (tt,final) ->
  forall name, length (memory (machine final) name) = length (memory (machine f) name).
Proof.
  induction fuel as [|fuel IH] in f, start |- *.
  - intros Hsum Hready Hrun name. cbn [loop execLocal] in Hrun. injection Hrun as <-. reflexivity.
  - intros Hsum Hready Hrun name. rewrite loop_S, execLocal_bind in Hrun.
    rewrite (generated_step f count (Z.of_nat count) fuel start Hready ltac:(lia) ltac:(lia)) in Hrun.
    cbn [optionBind fst snd] in Hrun.
    rewrite (IH (step_frame f start) (S start) ltac:(lia) (step_ready _ _ _ Hready) Hrun name).
    apply step_length.
Qed.
End RebuildExecution.
