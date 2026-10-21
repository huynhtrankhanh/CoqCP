From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash InternTail Stack HistoryStorage RenameFrames FormulaProjection Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module FrameReplace.
Import IndexExecution SipHashExecution.
Definition write (s : Machine) slot raw := withMemory s (modifyArray (memory s) arraydef_0__frames slot raw).
Lemma write_other s slot raw name : name <> arraydef_0__frames -> memory (write s slot raw) name = memory s name.
Proof. intros Hname. unfold write. cbn [withMemory memory]. now apply InternTailExecution.modify_other. Qed.
Lemma write_frames s slot raw : memory (write s slot raw) arraydef_0__frames = <[slot := raw]> (memory s arraydef_0__frames).
Proof. unfold write. cbn [withMemory memory]. apply InternTailExecution.modify_same. Qed.
Lemma write_meta s slot raw i : meta_value (write s slot raw) i = meta_value s i.
Proof. unfold meta_value. now rewrite write_other by discriminate. Qed.
Lemma replace_prefix {A} (xs : list A) slot raw (zero : A) : (slot < length xs)%nat ->
  firstn (S slot) (<[slot := raw]> xs) = firstn slot xs ++ [raw].
Proof.
  intros Hbound. pose proof (HistoryStorage.write_prefix xs slot raw zero ltac:(lia)) as Hprefix.
  now rewrite growList_no_shrink in Hprefix by lia.
Qed.
Theorem replace_top s fs old new stack raw : (10 < length (memory s arraydef_0__meta))%nat ->
  RenameFrames.represents s fs (old :: stack) -> RenameFrames.entry fs raw new ->
  RenameFrames.represents (write s (length stack) raw) fs (new :: stack).
Proof.
  intros Hmeta Hrep Hnew. pose proof (RenameFrames.capacity s fs (old :: stack) Hrep) as Hcapacity.
  pose proof Hrep as [Hcount [Hword Hentries]]. split; [now rewrite write_meta|]. split; [exact Hword|].
  assert (Hbound : (length stack < length (memory s arraydef_0__frames))%nat).
  { eapply Nat.lt_le_trans; [apply Nat.lt_succ_diag_r|exact Hcapacity]. }
  cbn [length rev]. rewrite write_frames,replace_prefix with (zero := (0,0,0,0)) by exact Hbound.
  apply Forall2_app.
  - pose proof (RenameFrames.pop s fs old stack Hmeta Hrep) as [_ [_ Htail]].
    rewrite store_meta_other in Htail by discriminate. exact Htail.
  - constructor; [exact Hnew|constructor].
Qed.
Lemma write_projection s slot raw : FormulaProjection.storage s (write s slot raw).
Proof.
  split; [now rewrite write_other by discriminate|]. split.
  - intros name Hneeded. apply write_other. unfold FormulaProjection.needed in Hneeded.
    destruct Hneeded as [-> | [-> | [-> | ->]]]; discriminate.
  - repeat split; apply write_meta.
Qed.
Lemma write_arena s slot raw fs : NativeRepresentation.canonical_arena s fs -> NativeRepresentation.canonical_arena (write s slot raw) fs.
Proof. intros Harena. exact (FormulaProjection.storage_arena s _ fs (write_projection s slot raw) Harena). Qed.
Lemma push_other s count node depth name : name <> arraydef_0__meta -> name <> arraydef_0__frames ->
  memory (StackExecution.push_state s count node depth) name = memory s name.
Proof.
  intros Hmeta Hframes. unfold StackExecution.push_state. rewrite store_meta_other by exact Hmeta.
  cbn [withMemory memory]. now rewrite InternTailExecution.modify_other,growArrays_other by exact Hframes.
Qed.
Lemma push_meta_length s count node depth :
  length (memory (StackExecution.push_state s count node depth) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof.
  unfold StackExecution.push_state. rewrite store_meta_length. cbn [withMemory memory].
  now rewrite InternTailExecution.modify_other,growArrays_other by discriminate.
Qed.
Lemma push_meta_other s count node depth i : i <> 10%nat ->
  meta_value (StackExecution.push_state s count node depth) i = meta_value s i.
Proof.
  intros Hi. unfold StackExecution.push_state. rewrite meta_store_other by exact Hi. unfold meta_value.
  cbn [withMemory memory]. now rewrite InternTailExecution.modify_other,growArrays_other by discriminate.
Qed.
Lemma push_projection s count node depth : FormulaProjection.storage s (StackExecution.push_state s count node depth).
Proof.
  split; [apply push_meta_length|]. split.
  - intros name Hneeded. apply push_other; unfold FormulaProjection.needed in Hneeded;
      destruct Hneeded as [-> | [-> | [-> | ->]]]; discriminate.
  - repeat split; apply push_meta_other; lia.
Qed.
Lemma push_arena s count node depth fs : NativeRepresentation.canonical_arena s fs ->
  NativeRepresentation.canonical_arena (StackExecution.push_state s count node depth) fs.
Proof. intros Harena. exact (FormulaProjection.storage_arena s _ fs (push_projection s count node depth) Harena). Qed.
End FrameReplace.
