From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash InternTail ClassStorage NameCopy NameRepresentation ReplyOK FormulaProjection Representation HistoryRefinement.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module BindingStorage.
Import IndexExecution SipHashExecution.
Definition grown_names (s : Machine) offset size := withMemory s (growArrays (memory s) arraydef_0__names (offset + size) 0).
Definition copied s offset size := NameCopyExecution.copy_remaining (grown_names s offset size) offset size size.
Definition grown_bindings s count offset size := withMemory (copied s offset size)
  (growArrays (memory (copied s offset size)) arraydef_0__bindings (S count) (0,0,0,0,0)).
Definition raw offset size value (kind : Z) := (Z.of_nat offset,Z.of_nat size,Z.of_nat value,0%Z,kind).
Definition written s count offset size value kind := withMemory (grown_bindings s count offset size)
  (modifyArray (memory (grown_bindings s count offset size)) arraydef_0__bindings count (raw offset size value kind)).
Definition updated_bytes s count offset size value kind := store_meta (written s count offset size value kind) 5 (Z.of_nat (offset + size)).
Definition result s count offset size value kind := store_meta
  (ReplyOKExecution.reply_state (updated_bytes s count offset size value kind) value) 4 (Z.of_nat (S count)).
Lemma grown_names_other s offset size name : name <> arraydef_0__names -> memory (grown_names s offset size) name = memory s name.
Proof. intro H. unfold grown_names. cbn [withMemory memory]. now rewrite growArrays_other. Qed.
Lemma grown_names_length s offset size : length (memory (grown_names s offset size) arraydef_0__names) =
  Nat.max (length (memory s arraydef_0__names)) (offset + size).
Proof. unfold grown_names. cbn [withMemory memory]. now rewrite growArrays_same,growList_length. Qed.
Lemma copied_other s offset size name : name <> arraydef_0__names -> memory (copied s offset size) name = memory s name.
Proof. intro H. unfold copied. now rewrite NameCopyExecution.copy_other,grown_names_other. Qed.
Lemma copied_length s offset size : length (memory (copied s offset size) arraydef_0__names) =
  Nat.max (length (memory s arraydef_0__names)) (offset + size).
Proof. unfold copied. now rewrite NameCopyExecution.copy_length,grown_names_length. Qed.
Lemma grown_bindings_other s count offset size name : name <> arraydef_0__bindings -> memory (grown_bindings s count offset size) name = memory (copied s offset size) name.
Proof. intro H. unfold grown_bindings. cbn [withMemory memory]. now rewrite growArrays_other. Qed.
Lemma written_other s count offset size value kind name : name <> arraydef_0__bindings -> memory (written s count offset size value kind) name = memory (copied s offset size) name.
Proof. intro H. unfold written. cbn [withMemory memory]. rewrite InternTailExecution.modify_other by exact H. now apply grown_bindings_other. Qed.
Lemma result_other s count offset size value kind name : name <> arraydef_0__meta -> name <> arraydef_0__printBuffer ->
  name <> arraydef_0__names -> name <> arraydef_0__bindings -> memory (result s count offset size value kind) name = memory s name.
Proof.
  intros Hm Hp Hn Hb. unfold result,updated_bytes. rewrite store_meta_other,ReplyOKExecution.reply_other,store_meta_other by assumption.
  rewrite written_other,copied_other by assumption. reflexivity.
Qed.
Lemma written_meta s count offset size value kind i : meta_value (written s count offset size value kind) i = meta_value s i.
Proof. unfold meta_value. now rewrite written_other,copied_other by discriminate. Qed.
Lemma written_meta_length s count offset size value kind : length (memory (written s count offset size value kind) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. now rewrite written_other,copied_other by discriminate. Qed.
Lemma result_meta_length s count offset size value kind : length (memory (result s count offset size value kind) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold result,updated_bytes. rewrite store_meta_length,ReplyOKExecution.reply_other,store_meta_length by discriminate. apply written_meta_length. Qed.
Lemma result_count s count offset size value kind : (4 < length (memory s arraydef_0__meta))%nat -> meta_value (result s count offset size value kind) 4 = Z.of_nat (S count).
Proof. intro H. unfold result. apply meta_store_same. unfold updated_bytes. rewrite ReplyOKExecution.reply_other,store_meta_length,written_meta_length by discriminate. exact H. Qed.
Lemma result_bytes s count offset size value kind : (5 < length (memory s arraydef_0__meta))%nat -> meta_value (result s count offset size value kind) 5 = Z.of_nat (offset + size).
Proof.
  intro H. unfold result,updated_bytes. rewrite meta_store_other by lia. unfold meta_value at 1.
  rewrite ReplyOKExecution.reply_other by discriminate. apply meta_store_same. now rewrite written_meta_length.
Qed.
Lemma result_meta_other s count offset size value kind i : i <> 4%nat -> i <> 5%nat ->
  meta_value (result s count offset size value kind) i = meta_value s i.
Proof.
  intros Hi4 Hi5. unfold result,updated_bytes. rewrite meta_store_other by exact Hi4. unfold meta_value at 1.
  rewrite ReplyOKExecution.reply_other by discriminate. change (meta_value (store_meta (written s count offset size value kind) 5 (Z.of_nat (offset + size))) i = meta_value s i).
  rewrite meta_store_other by exact Hi5. apply written_meta.
Qed.
Lemma result_names s count offset size value kind : memory (result s count offset size value kind) arraydef_0__names = memory (copied s offset size) arraydef_0__names.
Proof. unfold result,updated_bytes. now rewrite store_meta_other,ReplyOKExecution.reply_other,store_meta_other,written_other by discriminate. Qed.
Lemma result_bindings s count offset size value kind : memory (result s count offset size value kind) arraydef_0__bindings =
  <[count := raw offset size value kind]> (growList (memory s arraydef_0__bindings) (S count) (0,0,0,0,0)).
Proof.
  unfold result,updated_bytes,written. rewrite store_meta_other,ReplyOKExecution.reply_other,store_meta_other by discriminate.
  cbn [withMemory memory]. rewrite InternTailExecution.modify_same. unfold grown_bindings. cbn [withMemory memory].
  rewrite growArrays_same,copied_other by discriminate. reflexivity.
Qed.
Lemma result_bindings_app s count offset size value kind : length (memory s arraydef_0__bindings) = count ->
  memory (result s count offset size value kind) arraydef_0__bindings = memory s arraydef_0__bindings ++ [raw offset size value kind].
Proof. intro H. rewrite result_bindings,<-H. apply ClassStorage.insert_grown. Qed.
Lemma copied_before s offset size i : (offset <= length (memory s arraydef_0__names))%nat -> (i < offset)%nat ->
  List.nth i (memory (copied s offset size) arraydef_0__names) 0 = List.nth i (memory s arraydef_0__names) 0.
Proof.
  intros Hoffset Hi. unfold copied. rewrite NameCopyExecution.copy_before by lia. unfold grown_names. cbn [withMemory memory].
  rewrite growArrays_same. unfold growList. rewrite app_nth1 by lia. reflexivity. 
Qed.
Lemma copied_filled s offset size i : (i < size)%nat ->
  List.nth (offset + i) (memory (copied s offset size) arraydef_0__names) 0 = List.nth i (memory s arraydef_0__token) 0.
Proof.
  intro Hi. unfold copied. rewrite NameCopyExecution.copy_filled by (try rewrite grown_names_length; lia).
  now rewrite grown_names_other by discriminate.
Qed.
Lemma result_names_length s count offset size value kind : length (memory s arraydef_0__names) = offset ->
  length (memory (result s count offset size value kind) arraydef_0__names) = (offset + size)%nat.
Proof. intro H. rewrite result_names,copied_length,H,Nat.max_r by lia. reflexivity. Qed.
Lemma result_names_before s count offset size value kind i : length (memory s arraydef_0__names) = offset -> (i < offset)%nat ->
  List.nth i (memory (result s count offset size value kind) arraydef_0__names) 0 = List.nth i (memory s arraydef_0__names) 0.
Proof. intros H Hi. rewrite result_names. apply copied_before; lia. Qed.
Lemma result_names_filled s count offset size value kind i : (i < size)%nat ->
  List.nth (offset + i) (memory (result s count offset size value kind) arraydef_0__names) 0 = List.nth i (memory s arraydef_0__token) 0.
Proof. intro Hi. rewrite result_names. now apply copied_filled. Qed.
Lemma entry_rep_prefix oldbytes newbytes raw item : (length oldbytes <= length newbytes)%nat ->
  (forall i, (i < length oldbytes)%nat -> List.nth i newbytes 0 = List.nth i oldbytes 0) ->
  NameRepresentation.entry_rep oldbytes raw item -> NameRepresentation.entry_rep newbytes raw item.
Proof.
  intros Hlength Hprefix. destruct raw as [[[[offset size] value] flag] kind],item as [name meaning].
  intros [Hsize [Hoffset [Hword [Hvalue [Hflag [Hspan [Hbytes [Hdecode Hvalid]]]]]]]].
  split; [exact Hsize|]. split; [exact Hoffset|]. split; [exact Hword|]. split; [exact Hvalue|].
  split; [exact Hflag|]. split; [lia|]. split.
  - intros j Hj. rewrite Hprefix by lia. now apply Hbytes.
  - split; assumption.
Qed.
Theorem append_represents s bindings name value kind meaning :
  (5 < length (memory s arraydef_0__meta))%nat -> NameRepresentation.represents s bindings -> NameRepresentation.token_rep s name ->
  Z.of_nat (length bindings) < maximum ->
  Z.of_nat (length (memory s arraydef_0__names) + length name) <= maximum -> Z.of_nat value <= maximum ->
  NameRepresentation.decode (Z.of_nat value) 0 kind = Some meaning -> Protocol.valid_name name ->
  NameRepresentation.represents (result s (length bindings) (length (memory s arraydef_0__names)) (length name) value kind)
    (bindings ++ [(name,meaning)]).
Proof.
  intros Hmeta Hrep Htoken Hcountword Hbytesword Hvalue Hdecode Hvalid.
  pose proof (NameRepresentation.represents_length s bindings Hrep) as Hbindinglen.
  destruct Hrep as [Hcount [Hbytes [Hcountlimit [Hbytelimit Hentries]]]].
  set (final := result s (length bindings) (length (memory s arraydef_0__names)) (length name) value kind).
  assert (Hnamelen : length (memory final arraydef_0__names) = (length (memory s arraydef_0__names) + length name)%nat)
    by (unfold final; now apply result_names_length).
  change (NameRepresentation.represents final (bindings ++ [(name,meaning)])).
  split.
  - unfold final. rewrite result_count by lia. rewrite length_app. cbn [length]. f_equal. lia.
  - split.
    + rewrite Hnamelen. exact (result_bytes s (length bindings) (length (memory s arraydef_0__names)) (length name) value kind Hmeta).
    + split; [rewrite length_app; cbn [length]; lia|]. split; [now rewrite Hnamelen|].
      assert (Hbindings : memory final arraydef_0__bindings = memory s arraydef_0__bindings ++
        [raw (length (memory s arraydef_0__names)) (length name) value kind]) by
        exact (result_bindings_app s (length bindings) (length (memory s arraydef_0__names)) (length name) value kind Hbindinglen).
      rewrite Hbindings.
      apply Forall2_app.
      * eapply Forall2_impl; [exact Hentries|]. intros raw item Hentry.
        apply (entry_rep_prefix (memory s arraydef_0__names) (memory final arraydef_0__names) raw item); try assumption.
        -- eapply Nat.le_trans with (m := (length (memory s arraydef_0__names) + length name)%nat); [apply Nat.le_add_r|].
           apply Nat.eq_le_incl. exact (eq_sym Hnamelen).
        -- intros i Hi. exact (result_names_before s (length bindings) (length (memory s arraydef_0__names)) (length name) value kind i eq_refl Hi).
      * constructor; [|constructor]. unfold raw,NameRepresentation.entry_rep.
        split; [reflexivity|]. split; [lia|]. split.
        -- unfold word. rewrite <-Nat2Z.inj_add. lia.
        -- split; [unfold word; lia|]. split; [left; reflexivity|]. split.
           ++ rewrite Nat2Z.id. apply Nat.eq_le_incl. exact (eq_sym Hnamelen).
           ++ split.
              ** intros j Hj. rewrite Nat2Z.id. transitivity (List.nth j (memory s arraydef_0__token) 0).
                 --- exact (result_names_filled s (length bindings) (length (memory s arraydef_0__names)) (length name) value kind j Hj).
                 --- exact ((proj2 (proj2 Htoken)) j Hj).
              ** split; assumption.
Qed.
Lemma grown_names_meta s offset size i : meta_value (grown_names s offset size) i = meta_value s i.
Proof. unfold meta_value. now rewrite grown_names_other by discriminate. Qed.
Lemma copied_meta s offset size i : meta_value (copied s offset size) i = meta_value s i.
Proof. unfold meta_value. now rewrite copied_other by discriminate. Qed.
Lemma grown_bindings_meta s count offset size i : meta_value (grown_bindings s count offset size) i = meta_value s i.
Proof. unfold meta_value. now rewrite grown_bindings_other,copied_other by discriminate. Qed.
Lemma copied_input s offset size : stdin (copied s offset size) = stdin s.
Proof. unfold copied. rewrite NameCopyExecution.copy_input. reflexivity. Qed.
Lemma copied_output s offset size : stdout (copied s offset size) = stdout s.
Proof. unfold copied. rewrite NameCopyExecution.copy_output. reflexivity. Qed.
Lemma written_input s count offset size value kind : stdin (written s count offset size value kind) = stdin s.
Proof. unfold written,grown_bindings. cbn [withMemory stdin]. apply copied_input. Qed.
Lemma written_output s count offset size value kind : stdout (written s count offset size value kind) = stdout s.
Proof. unfold written,grown_bindings. cbn [withMemory stdout]. apply copied_output. Qed.
Lemma result_projection s count offset size value kind : FormulaProjection.storage s (result s count offset size value kind).
Proof.
  split; [apply result_meta_length|]. split.
  - intros name Hname. apply result_other; unfold FormulaProjection.needed in Hname;
      destruct Hname as [Heq|[Heq|[Heq|Heq]]]; subst name; discriminate.
  - repeat split; apply result_meta_other; lia.
Qed.
Lemma result_arena s fs count offset size value kind : NativeRepresentation.canonical_arena s fs ->
  NativeRepresentation.canonical_arena (result s count offset size value kind) fs.
Proof. intro H. exact (FormulaProjection.storage_arena s _ fs (result_projection s count offset size value kind) H). Qed.
Lemma result_classes s fs classes count offset size value kind : ClassStorage.represents s fs classes ->
  ClassStorage.represents (result s count offset size value kind) fs classes.
Proof.
  intros [Hcount Hclasses]. split; [now rewrite result_meta_other by lia|]. now rewrite result_other by discriminate.
Qed.
Lemma result_history s logical count offset size value kind : HistoryRefinement.represents s logical ->
  HistoryRefinement.represents (result s count offset size value kind) logical.
Proof.
  intros [Hcount Hhistory]. split; [now rewrite result_meta_other by lia|]. now rewrite result_other by discriminate.
Qed.
End BindingStorage.
