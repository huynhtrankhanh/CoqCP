From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts SipHash HashScan InternTail HashTable.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module RehashExecution.
Import IndexExecution SipHashExecution InternTailExecution HashTableInvariant.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas.
Definition LocalAction R := Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas)
  withLocalVariablesReturnValue R.
Definition hash_function := (varsfuncdef_0__formulaHash -> bool) ->
  (varsfuncdef_0__formulaHash -> Z) -> Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit.

(* Select the rebuilding loop after doubling, clearing and installing the new
   bucket count. The only abstraction replaces its call to the hash procedure. *)
Definition relink_body (hash_proc : hash_function) (total : Z) (remaining : nat) : LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__rehashFormulas_body in funcdef_0__rehashFormulas_body in
  lazymatch code with bind _ ?next =>
    let code := eval cbn beta in (next tt) in
    lazymatch code with bind (bind _ ?branch) _ =>
      let code := eval cbn beta iota in (branch false) in
      lazymatch code with bind _ ?next =>
        let code := eval cbn beta in (next tt) in
        lazymatch code with bind _ ?next =>
          let code := eval cbn beta in (next tt) in
          lazymatch code with bind _ ?next =>
            let code := eval cbn beta in (next tt) in
            lazymatch code with bind _ ?next =>
              let code := eval cbn beta in (next tt) in
              lazymatch code with bind (bind _ ?count_body) _ =>
                let code := eval cbn beta in (count_body total) in
                lazymatch code with loop _ ?body =>
                  let code := eval cbn beta zeta in (body remaining) in
                  let generalized := eval pattern funcdef_0__formulaHash in code in
                  lazymatch generalized with ?family _ => exact (family hash_proc) end
                end
              end
            end
          end
        end
      end
    end
  end).
Definition hash_arguments x y z : varsfuncdef_0__formulaHash -> Z :=
  update (update (update (fun _ => 0) vardef_0__formulaHash_tag x)
    vardef_0__formulaHash_a y) vardef_0__formulaHash_b z.
Lemma local_read_array (f : Frame) name slot (default : arrayType _ environment1 name) :
  (Z.to_nat slot < length (memory (machine f) name))%nat ->
  execLocal (retrieve _ _ _ name slot) f = Some (List.nth (Z.to_nat slot) (memory (machine f) name) default,f).
Proof. destruct f. intro H. cbn [retrieve execLocal localStep step]. case_decide; [|lia].
  rewrite nth_lt_default with (default := default). reflexivity. Qed.
Lemma local_write_array (f : Frame) name slot value :
  (Z.to_nat slot < length (memory (machine f) name))%nat ->
  execLocal (R := unit) (store _ _ _ name slot value) f =
    Some (tt,setMachine f (withMemory (machine f) (modifyArray (memory (machine f)) name (Z.to_nat slot) value))).
Proof. intro H. cbn [store execLocal localStep step]. case_decide; [reflexivity|lia]. Qed.
Lemma local_get (f : Frame) name :
  execLocal (R := Z) (numberLocalGet _ _ _ name) f = Some (nums f name,f).
Proof. reflexivity. Qed.
Lemma local_set (f : Frame) name value :
  execLocal (R := unit) (numberLocalSet _ _ _ name value) f = Some (tt,setNum f name value).
Proof. reflexivity. Qed.
Definition relink_state (s : Machine) index bucket :=
  let written := withMemory s (modifyArray (memory s) arraydef_0__formulaLinks index (head_at s bucket)) in
  withMemory written (modifyArray (memory written) arraydef_0__formulaBuckets bucket (Z.of_nat (S index))).
Definition relink_frame (f : Frame) s index bucket :=
  setMachine (setNum (setMachine f s) vardef_0__rehashFormulas_bucket (Z.of_nat bucket))
    (relink_state s index bucket).

Lemma get_dispatch {R} (f : Frame) name (next : Z -> LocalAction R) :
  execLocal (Dispatch _ _ _ (NumberLocalGet _ _ _ name) next) f = execLocal (next (nums f name)) f.
Proof. reflexivity. Qed.
Lemma set_dispatch {R} (f : Frame) name value (next : unit -> LocalAction R) :
  execLocal (Dispatch _ _ _ (NumberLocalSet _ _ _ name value) next) f =
    execLocal (next tt) (setNum f name value).
Proof. reflexivity. Qed.
Lemma update_here {A} (ns : varsfuncdef_0__rehashFormulas -> A) name value :
  Imperative.update ns name value name = value.
Proof. unfold Imperative.update. case_decide; [reflexivity|congruence]. Qed.
Lemma local_done {R} (value : R) (f : Frame) :
  execLocal (Done _ _ _ value) f = Some (value,f).
Proof. reflexivity. Qed.

Section Composition.
Variable hash_proc : hash_function.
Theorem relink_composition (f : Frame) total remaining index x y z hashed bucket :
  total - Z.of_nat remaining - 1 = Z.of_nat index ->
  Z.of_nat (S index) <= maximum ->
  (index < length (memory (machine f) arraydef_0__formulas))%nat ->
  List.nth index (memory (machine f) arraydef_0__formulas) (0,0,0) = (x,y,z) ->
  exec (hash_proc (fun _ => false) (hash_arguments x y z)) (machine f) = Some (tt,hashed) ->
  (21 < length (memory hashed arraydef_0__meta))%nat ->
  meta_value hashed 21 = Z.of_nat bucket ->
  (index < length (memory hashed arraydef_0__formulaLinks))%nat ->
  (bucket < length (memory hashed arraydef_0__formulaBuckets))%nat ->
  execLocal (relink_body hash_proc total remaining) f = Some (KeepGoing,relink_frame f hashed index bucket).
Proof.
  intros Hindex Hlimit Hformulas Hentry Hhash Hmeta Hbucket Hlinks Hbucketbound.
  destruct f as [s bs ns]. cbn [machine] in *.
  change (@List.nth (arrayType _ environment1 arraydef_0__formulas) index (memory s arraydef_0__formulas) (0,0,0) = (x,y,z)) in Hentry.
  unfold relink_body. unfold hash_arguments in Hhash.
  repeat first [rewrite execLocal_bind |rewrite dropWithinLoop_1 |rewrite exec_drop_lift
    |rewrite execLocal_lift |rewrite local_get |rewrite local_set |rewrite local_done |rewrite get_dispatch |rewrite set_dispatch
    |rewrite local_read_meta by (cbn [machine setMachine setNum]; exact Hmeta)
    |rewrite (local_read_array _ arraydef_0__formulas _ (0,0,0)) by (cbn [machine setMachine setNum]; try rewrite Hindex; try rewrite Nat2Z.id; exact Hformulas)
    |rewrite (local_read_array _ arraydef_0__formulaBuckets _ 0%Z) by (cbn [machine setMachine setNum]; try rewrite Nat2Z.id; exact Hbucketbound)
    |rewrite local_write_array by
        (cbn [machine setMachine setNum withMemory memory]; try rewrite Nat2Z.id;
         first [exact Hlinks |exact Hbucketbound |rewrite modify_other by discriminate; exact Hbucketbound])
    |rewrite update_here |rewrite Hbucket |rewrite Hindex |rewrite Nat2Z.id |rewrite Hentry |rewrite Hhash
    |progress replace (Z.to_nat 21) with 21%nat by reflexivity
    |progress replace (Z.of_nat index + 1) with (Z.of_nat (S index)) by lia
    |match goal with |- context [coerceInt ?value 64] =>
        rewrite (coerce_word value) by (unfold word, maximum in *; lia) end
    |progress cbn [bind optionBind nums bools machine
        setNum setMachine fst snd addInt Imperative.update
        variableIndexEqualityDecidablevarsfuncdef_0__rehashFormulas varsfuncdef_0__rehashFormulas_rec]
  ].
  reflexivity.
Qed.
End Composition.

Definition hashed_entry (s : Machine) index :=
  let '(x,y,z) := tuple_at s index in hash_state s x y z.
Definition entry_bucket (s : Machine) index := Z.to_nat (meta_value (hashed_entry s index) 21).
Lemma hash_meta_length s x y z :
  length (memory (hash_state s x y z) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold hash_state. rewrite !store_meta_length, hash_work_other by discriminate. reflexivity. Qed.

Theorem generated_relink (f : Frame) total remaining index :
  total - Z.of_nat remaining - 1 = Z.of_nat index -> Z.of_nat (S index) <= maximum ->
  (28 < length (memory (machine f) arraydef_0__meta))%nat ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  0 < meta_value (machine f) 20 ->
  meta_value (machine f) 20 <= Z.of_nat (length (memory (machine f) arraydef_0__formulaBuckets)) ->
  (index < length (memory (machine f) arraydef_0__formulas))%nat ->
  (index < length (memory (machine f) arraydef_0__formulaLinks))%nat ->
  execLocal (relink_body funcdef_0__formulaHash total remaining) f =
    Some (KeepGoing,relink_frame f (hashed_entry (machine f) index) index (entry_bucket (machine f) index)).
Proof.
  intros Hindex Hlimit Hmeta Hsip Hpositive Hcapacity Hformula Hlinks.
  unfold entry_bucket, hashed_entry. destruct (tuple_at (machine f) index) as [[x y] z] eqn:Hentry.
  assert (Hbounds : 0 <= meta_value (hash_state (machine f) x y z) 21 < meta_value (machine f) 20).
  { rewrite hash_bucket by assumption. now apply Z.mod_pos_bound. }
  apply (relink_composition funcdef_0__formulaHash f total remaining index x y z).
  - exact Hindex.
  - exact Hlimit.
  - exact Hformula.
  - exact Hentry.
  - apply generated_hash; assumption.
  - rewrite hash_meta_length. lia.
  - rewrite Z2Nat.id by lia. reflexivity.
  - rewrite hash_preserves_array by discriminate. exact Hlinks.
  - rewrite hash_preserves_array by discriminate.
    pose proof (Z2Nat.id (meta_value (hash_state (machine f) x y z) 21) ltac:(lia)). lia.
Qed.

Lemma relink_links s i bucket : memory (relink_state s i bucket) arraydef_0__formulaLinks =
  <[i := head_at s bucket]> (memory s arraydef_0__formulaLinks).
Proof. unfold relink_state. cbn [withMemory memory]. now repeat first [rewrite modify_other by discriminate |rewrite modify_same]. Qed.
Lemma relink_buckets s i bucket : memory (relink_state s i bucket) arraydef_0__formulaBuckets =
  <[bucket := Z.of_nat (S i)]> (memory s arraydef_0__formulaBuckets).
Proof. unfold relink_state. cbn [withMemory memory]. now repeat first [rewrite modify_other by discriminate |rewrite modify_same]. Qed.
Lemma relink_other s i bucket name : name <> arraydef_0__formulaLinks -> name <> arraydef_0__formulaBuckets ->
  memory (relink_state s i bucket) name = memory s name.
Proof. intros. unfold relink_state. cbn [withMemory memory]. now rewrite !modify_other by assumption. Qed.
Lemma relink_io s i bucket : stdin (relink_state s i bucket) = stdin s /\
  stdout (relink_state s i bucket) = stdout s.
Proof. split; reflexivity. Qed.
Lemma insert_nth_identity {A} (xs : list A) i default : <[i := List.nth i xs default]> xs = xs.
Proof. induction xs as [|x xs IH] in i |- *; destruct i; cbn; try reflexivity. now rewrite IH. Qed.

Lemma indexed_preserved s t n bucket_of :
  memory t arraydef_0__formulas = memory s arraydef_0__formulas ->
  memory t arraydef_0__formulaLinks = memory s arraydef_0__formulaLinks ->
  memory t arraydef_0__formulaBuckets = memory s arraydef_0__formulaBuckets ->
  indexed s n bucket_of -> indexed t n bucket_of.
Proof.
  intros Hformula Hlinks Hbucket [Htable [Hheads Hindexed]].
  split; [now apply (HashScanExecution.table_valid_preserved s)|]. split.
  - intros b Hb. rewrite Hbucket in Hb. unfold head_at. rewrite Hbucket. now apply Hheads.
  - intros i Hi. destruct (Hindexed i Hi) as [Hrange Hchain].
    unfold tuple_at. rewrite Hformula. split; [now rewrite Hbucket|].
    unfold head_at. rewrite Hbucket. now apply (HashScanExecution.in_chain_preserved s).
Qed.

Theorem relink_indexed s n bucket_of :
  indexed s n bucket_of ->
  (n < length (memory s arraydef_0__formulas))%nat ->
  (n < length (memory s arraydef_0__formulaLinks))%nat ->
  (bucket_of (tuple_at s n) < length (memory s arraydef_0__formulaBuckets))%nat ->
  indexed (relink_state s n (bucket_of (tuple_at s n))) (S n) bucket_of.
Proof.
  intros Hindexed Hformulas Hlinks Hbucket.
  apply (indexed_preserved (append_state s n (bucket_of (tuple_at s n)) (tuple_at s n))).
  - rewrite relink_other by discriminate. rewrite append_formulas, growList_no_shrink by lia.
    unfold tuple_at. now rewrite insert_nth_identity.
  - rewrite relink_links, append_links, growList_no_shrink by lia. reflexivity.
  - rewrite relink_buckets, append_buckets. reflexivity.
  - now apply append_indexed.
Qed.

Definition keyed_bucket (s : Machine) (tuple : Z * Z * Z) :=
  let '(x,y,z) := tuple in
  Z.to_nat (siphash24 (meta_value s 26) (meta_value s 27) x y z mod meta_value s 20).
Lemma entry_bucket_correct s index :
  (28 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat ->
  entry_bucket s index = keyed_bucket s (tuple_at s index).
Proof.
  intros Hmeta Hsip. unfold entry_bucket, hashed_entry, keyed_bucket.
  destruct (tuple_at s index) as [[x y] z]. now rewrite hash_bucket.
Qed.
Lemma hashed_indexed s n bucket_of : indexed s n bucket_of ->
  indexed (hashed_entry s n) n bucket_of.
Proof.
  intro H. unfold hashed_entry. destruct (tuple_at s n) as [[x y] z].
  apply (indexed_preserved s); [| | |exact H]; now apply hash_preserves_array.
Qed.

Theorem generated_relink_indexed (f : Frame) total remaining index :
  total - Z.of_nat remaining - 1 = Z.of_nat index -> Z.of_nat (S index) <= maximum ->
  (28 < length (memory (machine f) arraydef_0__meta))%nat ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  0 < meta_value (machine f) 20 ->
  meta_value (machine f) 20 <= Z.of_nat (length (memory (machine f) arraydef_0__formulaBuckets)) ->
  (index < length (memory (machine f) arraydef_0__formulas))%nat ->
  (index < length (memory (machine f) arraydef_0__formulaLinks))%nat ->
  indexed (machine f) index (keyed_bucket (machine f)) ->
  exists final, execLocal (relink_body funcdef_0__formulaHash total remaining) f = Some (KeepGoing,final) /\
    indexed (machine final) (S index) (keyed_bucket (machine f)) /\
    memory (machine final) arraydef_0__formulas = memory (machine f) arraydef_0__formulas.
Proof.
  intros Hindex Hlimit Hmeta Hsip Hpositive Hcapacity Hformulas Hlinks Hindexed.
  exists (relink_frame f (hashed_entry (machine f) index) index (entry_bucket (machine f) index)).
  split; [now apply generated_relink|].
  assert (Hformula : memory (hashed_entry (machine f) index) arraydef_0__formulas =
    memory (machine f) arraydef_0__formulas).
  { unfold hashed_entry. destruct (tuple_at (machine f) index) as [[x y] z].
    now apply hash_preserves_array. }
  assert (Hlink : memory (hashed_entry (machine f) index) arraydef_0__formulaLinks =
    memory (machine f) arraydef_0__formulaLinks).
  { unfold hashed_entry. destruct (tuple_at (machine f) index) as [[x y] z].
    now apply hash_preserves_array. }
  assert (Hbucket : memory (hashed_entry (machine f) index) arraydef_0__formulaBuckets =
    memory (machine f) arraydef_0__formulaBuckets).
  { unfold hashed_entry. destruct (tuple_at (machine f) index) as [[x y] z].
    now apply hash_preserves_array. }
  cbn [relink_frame machine setMachine setNum]. split.
  - rewrite entry_bucket_correct by assumption.
    assert (Htuple : tuple_at (hashed_entry (machine f) index) index = tuple_at (machine f) index).
    { unfold tuple_at. now rewrite Hformula. }
    rewrite <- Htuple. apply relink_indexed.
    + now apply hashed_indexed.
    + now rewrite Hformula.
    + now rewrite Hlink.
    + rewrite Htuple, Hbucket. unfold keyed_bucket.
      destruct (tuple_at (machine f) index) as [[x y] z].
      pose proof (Z.mod_pos_bound (siphash24 (meta_value (machine f) 26) (meta_value (machine f) 27) x y z)
        (meta_value (machine f) 20) Hpositive) as Hbounds.
      pose proof (Z2Nat.id (siphash24 (meta_value (machine f) 26) (meta_value (machine f) 27) x y z
        mod meta_value (machine f) 20) ltac:(lia)). lia.
  - rewrite relink_other by discriminate. exact Hformula.
Qed.
End RehashExecution.
