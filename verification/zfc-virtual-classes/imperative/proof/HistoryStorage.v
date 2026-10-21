From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash InternTail ReplyOK FormulaProjection Representation ClassStorage HistoryRefinement ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module HistoryStorage.
Import IndexExecution SipHashExecution.
Definition grown (s : Machine) n := withMemory s (growArrays (memory s) arraydef_0__theorems (S n) 0).
Definition written s n value := withMemory (grown s n) (modifyArray (memory (grown s n)) arraydef_0__theorems n value).
Definition result s n value := store_meta (ReplyOKExecution.reply_state (written s n value) n) 3 (Z.of_nat (S n)).
Lemma grown_other s n name : name <> arraydef_0__theorems -> memory (grown s n) name = memory s name.
Proof. intro Hname. unfold grown. cbn [withMemory memory]. now rewrite growArrays_other. Qed.
Lemma written_other s n value name : name <> arraydef_0__theorems -> memory (written s n value) name = memory s name.
Proof. intro Hname. unfold written. cbn [withMemory memory]. rewrite InternTailExecution.modify_other by exact Hname.
  now apply grown_other. Qed.
Lemma grown_meta s n i : meta_value (grown s n) i = meta_value s i.
Proof. unfold meta_value. now rewrite grown_other by discriminate. Qed.
Lemma written_meta s n value i : meta_value (written s n value) i = meta_value s i.
Proof. unfold meta_value. now rewrite written_other by discriminate. Qed.
Lemma written_history s n value : memory (written s n value) arraydef_0__theorems =
  <[n := value]> (growList (memory s arraydef_0__theorems) (S n) 0).
Proof. unfold written, grown. cbn [withMemory memory]. now rewrite InternTailExecution.modify_same, growArrays_same. Qed.
Lemma write_prefix {A} (xs : list A) n entry zero : (n <= length xs)%nat ->
  firstn (S n) (<[n := entry]> (growList xs (S n) zero)) = firstn n xs ++ [entry].
Proof.
  induction n as [|n IH] in xs |- *.
  - intros _. destruct xs; reflexivity.
  - intro Hlength. destruct xs as [|x xs]; [cbn [length] in Hlength; lia|].
    change (x :: firstn (S n) (<[n := entry]> (growList xs (S n) zero)) = x :: (firstn n xs ++ [entry])).
    exact (f_equal (cons x) (IH xs ltac:(cbn [length] in Hlength; lia))).
Qed.
Lemma result_other s n value name : name <> arraydef_0__meta -> name <> arraydef_0__printBuffer -> name <> arraydef_0__theorems ->
  memory (result s n value) name = memory s name.
Proof. intros Hm Hp Ht. unfold result. rewrite store_meta_other by exact Hm.
  rewrite ReplyOKExecution.reply_other by exact Hp. now apply written_other. Qed.
Lemma result_history s n value : memory (result s n value) arraydef_0__theorems = memory (written s n value) arraydef_0__theorems.
Proof. unfold result. now rewrite store_meta_other, ReplyOKExecution.reply_other by discriminate. Qed.
Lemma result_meta_length s n value : length (memory (result s n value) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold result. rewrite store_meta_length, ReplyOKExecution.reply_other, written_other by discriminate. reflexivity. Qed.
Lemma result_count s n value : (3 < length (memory s arraydef_0__meta))%nat -> meta_value (result s n value) 3 = Z.of_nat (S n).
Proof. intro Hmeta. unfold result. apply meta_store_same. rewrite ReplyOKExecution.reply_other, written_other by discriminate. exact Hmeta. Qed.
Lemma result_meta_other s n value i : i <> 3%nat -> meta_value (result s n value) i = meta_value s i.
Proof. intro Hi. unfold result. rewrite meta_store_other by exact Hi. unfold meta_value.
  now rewrite ReplyOKExecution.reply_other, written_other by discriminate. Qed.
Lemma prefix_capacity s logical : HistoryRefinement.represents s logical ->
  (length (Protocol.history logical) <= length (memory s arraydef_0__theorems))%nat.
Proof. intros [_ Hprefix]. apply (f_equal (@length Z)) in Hprefix.
  rewrite firstn_length, length_map in Hprefix. lia. Qed.
Theorem append_represents s logical fid :
  (3 < length (memory s arraydef_0__meta))%nat -> HistoryRefinement.represents s logical ->
  HistoryRefinement.represents (result s (length (Protocol.history logical)) (Z.of_nat fid))
    (Protocol.with_history logical (Protocol.history logical ++ [fid])).
Proof.
  intros Hmeta Hrep. pose proof (prefix_capacity s logical Hrep) as Hcapacity.
  destruct Hrep as [Hcount Hprefix]. split.
  - rewrite result_count by exact Hmeta. cbn [Protocol.with_history Protocol.history]. rewrite length_app. cbn [length]. f_equal. lia.
  - cbn [Protocol.with_history Protocol.history]. rewrite length_app. cbn [length].
    replace (length (Protocol.history logical) + 1)%nat with (S (length (Protocol.history logical))) by lia.
    rewrite result_history, written_history, write_prefix by exact Hcapacity. rewrite Hprefix, map_app. reflexivity.
Qed.
Lemma result_projection s n value : FormulaProjection.storage s (result s n value).
Proof.
  assert (Hwritten : FormulaProjection.storage s (written s n value)).
  { split; [now rewrite written_other by discriminate|]. split.
    - intros name Hname. apply written_other. unfold FormulaProjection.needed in Hname.
      destruct Hname as [Heq|[Heq|[Heq|Heq]]]; subst name; discriminate.
    - repeat split; apply written_meta. }
  refine (FormulaProjection.storage_trans s (written s n value) _ Hwritten _).
  refine (FormulaProjection.storage_trans _ (ReplyOKExecution.reply_state (written s n value) n) _ (FormulaProjection.reply_storage _ n) _).
  apply FormulaProjection.strong_storage. apply ArenaFrame.storage_meta; lia.
Qed.
Lemma result_arena s meaning n value : NativeRepresentation.canonical_arena s meaning ->
  NativeRepresentation.canonical_arena (result s n value) meaning.
Proof. intro Harena. exact (FormulaProjection.storage_arena s (result s n value) meaning (result_projection s n value) Harena). Qed.
Lemma result_classes s meaning classes n value : ClassStorage.represents s meaning classes ->
  ClassStorage.represents (result s n value) meaning classes.
Proof. intros [Hcount Hclasses]. split; [now rewrite result_meta_other by lia|].
  now rewrite result_other by discriminate. Qed.
End HistoryStorage.
