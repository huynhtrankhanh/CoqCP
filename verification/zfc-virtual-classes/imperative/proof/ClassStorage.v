From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash InternTail FormulaEncoding FormulaProjection ReplyOK Representation ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module ClassStorage.
Import IndexExecution SipHashExecution.
Definition grown (s : Machine) n := withMemory s
  (growArrays (memory s) arraydef_0__classes (S n) (0,0)).
Definition written s n entry := withMemory (grown s n)
  (modifyArray (memory (grown s n)) arraydef_0__classes n entry).
Definition result s n entry := store_meta (ReplyOKExecution.reply_state (written s n entry) n) 2 (Z.of_nat (S n)).
Lemma grown_other s n name : name <> arraydef_0__classes -> memory (grown s n) name = memory s name.
Proof. intro Hname. unfold grown. cbn [memory withMemory]. now rewrite growArrays_other. Qed.
Lemma grown_meta s n i : meta_value (grown s n) i = meta_value s i.
Proof. unfold meta_value. now rewrite grown_other by discriminate. Qed.
Lemma written_other s n entry name : name <> arraydef_0__classes -> memory (written s n entry) name = memory s name.
Proof. intro Hname. unfold written, grown. cbn [memory withMemory].
  rewrite InternTailExecution.modify_other, growArrays_other by exact Hname. reflexivity. Qed.
Lemma written_meta s n entry i : meta_value (written s n entry) i = meta_value s i.
Proof. unfold meta_value. now rewrite written_other by discriminate. Qed.
Lemma written_classes s n entry : memory (written s n entry) arraydef_0__classes =
  <[n := entry]> (growList (memory s arraydef_0__classes) (S n) (0,0)).
Proof. unfold written, grown. cbn [memory withMemory].
  now rewrite InternTailExecution.modify_same, growArrays_same. Qed.
Lemma insert_grown {A} (xs : list A) entry zero :
  <[length xs := entry]> (growList xs (S (length xs)) zero) = xs ++ [entry].
Proof.
  unfold growList. replace (S (length xs) - length xs)%nat with 1%nat by lia.
  cbn [repeat]. induction xs as [|x xs IH]; [reflexivity|]. exact (f_equal (cons x) IH).
Qed.
Lemma written_app s n entry : length (memory s arraydef_0__classes) = n ->
  memory (written s n entry) arraydef_0__classes = memory s arraydef_0__classes ++ [entry].
Proof. intro Hlength. rewrite written_classes, <- Hlength. apply insert_grown. Qed.
Lemma result_other s n entry name : name <> arraydef_0__meta -> name <> arraydef_0__printBuffer -> name <> arraydef_0__classes ->
  memory (result s n entry) name = memory s name.
Proof. intros Hm Hp Hc. unfold result. rewrite store_meta_other by exact Hm.
  rewrite ReplyOKExecution.reply_other by exact Hp. now apply written_other. Qed.
Lemma result_classes s n entry : memory (result s n entry) arraydef_0__classes = memory (written s n entry) arraydef_0__classes.
Proof. unfold result. rewrite store_meta_other, ReplyOKExecution.reply_other by discriminate. reflexivity. Qed.
Lemma result_meta_length s n entry : length (memory (result s n entry) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold result. rewrite store_meta_length, ReplyOKExecution.reply_other, written_other by discriminate. reflexivity. Qed.
Lemma result_count s n entry : (2 < length (memory s arraydef_0__meta))%nat -> meta_value (result s n entry) 2 = Z.of_nat (S n).
Proof. intro Hmeta. unfold result. apply meta_store_same.
  rewrite ReplyOKExecution.reply_other, written_other by discriminate. exact Hmeta. Qed.
Lemma result_meta_other s n entry i : i <> 2%nat -> meta_value (result s n entry) i = meta_value s i.
Proof. intro Hi. unfold result. rewrite meta_store_other by exact Hi. unfold meta_value.
  now rewrite ReplyOKExecution.reply_other, written_other by discriminate. Qed.
Lemma written_projection s n entry : FormulaProjection.storage s (written s n entry).
Proof.
  split; [now rewrite written_other by discriminate|]. split.
  - intros name Hname. apply written_other. unfold FormulaProjection.needed in Hname.
    destruct Hname as [Heq|[Heq|[Heq|Heq]]]; subst name; discriminate.
  - repeat split; apply written_meta.
Qed.
Lemma result_projection s n entry : FormulaProjection.storage s (result s n entry).
Proof.
  refine (FormulaProjection.storage_trans s (written s n entry) _ (written_projection s n entry) _).
  refine (FormulaProjection.storage_trans _ (ReplyOKExecution.reply_state (written s n entry) n) _
    (FormulaProjection.reply_storage _ n) _).
  apply FormulaProjection.strong_storage. apply ArenaFrame.storage_meta; lia.
Qed.
Lemma result_arena s n entry meaning : NativeRepresentation.canonical_arena s meaning ->
  NativeRepresentation.canonical_arena (result s n entry) meaning.
Proof. intro Harena. exact (FormulaProjection.storage_arena s (result s n entry) meaning (result_projection s n entry) Harena). Qed.
Definition decode meaning (entry : Z * Z) : option VirtualClasses.class :=
  let '(tag,value) := entry in
  if Z.eq_dec tag 0 then Some (VirtualClasses.set (Z.to_nat value)) else
  if Z.eq_dec tag 1 then option_map (fun p => VirtualClasses.abstract (VirtualClasses.core p)) (nth_error meaning (Z.to_nat value))
  else None.
Definition represents s meaning classes := meta_value s 2 = Z.of_nat (length classes) /\
  Forall2 (fun entry cls => decode meaning entry = Some cls) (memory s arraydef_0__classes) classes.
Lemma represents_length s meaning classes : represents s meaning classes -> length (memory s arraydef_0__classes) = length classes.
Proof. intros [_ Hclasses]. now apply Forall2_length in Hclasses. Qed.
Lemma decode_extend meaning extra entry cls : decode meaning entry = Some cls -> decode (meaning ++ extra) entry = Some cls.
Proof.
  destruct entry as [tag value]. unfold decode. destruct (Z.eq_dec tag 0); [tauto|].
  destruct (Z.eq_dec tag 1); [|tauto]. destruct (nth_error meaning (Z.to_nat value)) as [p|] eqn:Hp; [|discriminate].
  rewrite (FormulaEncoding.nth_error_extend _ extra _ _ Hp). tauto.
Qed.
Theorem append_represents s meaning classes entry cls :
  (2 < length (memory s arraydef_0__meta))%nat -> represents s meaning classes -> decode meaning entry = Some cls ->
  represents (result s (length classes) entry) meaning (classes ++ [cls]).
Proof.
  intros Hmeta Hrep Hdecode. destruct Hrep as [Hcount Hclasses]. split.
  - rewrite result_count by exact Hmeta. rewrite length_app. cbn [length]. f_equal. lia.
  - rewrite result_classes, written_app by (now apply Forall2_length in Hclasses).
    apply Forall2_app; [exact Hclasses|]. constructor; [exact Hdecode|constructor].
Qed.
End ClassStorage.
