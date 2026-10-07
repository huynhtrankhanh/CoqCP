From CoqCP Require Import Options Imperative Execution KoxiaArrays KoxiaArrayLoops KoxiaModular
  KoxiaTables KoxiaPolynomialBuffers KoxiaBufferSplit KoxiaArena KoxiaTreeBuffers KoxiaVisitSchedule
  KoxiaConvolution KoxiaConvolutionReady KoxiaMemoryPreservation KoxiaWorkspace KoxiaLeftExecution KoxiaFrameStores SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Logic.FunctionalExtensionality Lia.

Definition framesRepresent (frames : list (Z*Z*Z*Z*Z)) (stack : list AnnotatedFrame) :=
  exists tail, frames=encodeAnnotatedStack stack++tail.

Lemma encoded_stack_length stack : length (encodeAnnotatedStack stack)=length stack.
Proof. unfold encodeAnnotatedStack. rewrite length_map,length_rev. reflexivity. Qed.

Lemma framesRepresent_room frames stack : framesRepresent frames stack ->
  length stack<=length frames.
Proof. intros [tail ->]. rewrite length_app,encoded_stack_length. lia. Qed.

Lemma framesRepresent_top frames frame stack : framesRepresent frames (frame::stack) ->
  nth (length stack) frames (0%Z,0%Z,0%Z,0%Z,0%Z)=encodeAnnotatedFrame frame.
Proof.
  intros [tail ->]. rewrite encodeAnnotatedStack_cons,<-app_assoc.
  rewrite app_nth2 by (rewrite encoded_stack_length; lia).
  rewrite encoded_stack_length,Nat.sub_diag. reflexivity.
Qed.

Lemma framesRepresent_pop frames frame stack : framesRepresent frames (frame::stack) ->
  framesRepresent frames stack.
Proof.
  intros [tail ->]. exists (encodeAnnotatedFrame frame::tail).
  rewrite encodeAnnotatedStack_cons,<-app_assoc. reflexivity.
Qed.

Lemma framesRepresent_push frames old parent child stack :
  framesRepresent frames (old::stack) -> S (length stack)<length frames ->
  framesRepresent
    (<[S (length stack):=encodeAnnotatedFrame child]>
      (<[length stack:=encodeAnnotatedFrame parent]>frames)) (child::parent::stack).
Proof.
  intros [tail contents] room. rewrite contents,encodeAnnotatedStack_cons in room |- *.
  destruct tail as [|next rest].
  - rewrite !length_app,encoded_stack_length in room. cbn [length] in room. lia.
  - rewrite <-app_assoc. cbn [app].
    rewrite <-(encoded_stack_length stack),insert_two_at_end.
    exists rest. rewrite encode_two_cons,<-app_assoc. reflexivity.
Qed.

Definition arenaContains (arena : list Z) base (saved : list Z) :=
  forall index, index<length saved -> nth (base+index) arena 0%Z=nth index saved 0%Z.

Lemma arenaContains_transfer before after base saved bound :
  arenaContains before base saved -> base+length saved<=bound ->
  (forall index, index<bound -> nth index after 0%Z=nth index before 0%Z) ->
  arenaContains after base saved.
Proof. intros contains room same index range. rewrite same by lia. apply contains. exact range. Qed.

Lemma arenaContains_empty arena base : arenaContains arena base [].
Proof. intros index range. cbn [length] in range. lia. Qed.

Lemma arenaContains_saved state values len cut span base :
  (cut<len)%nat -> ConvolutionReady (withArray state arraydef_0__poly values) len cut span base ->
  arenaContains
    (memory (readyConvolutionFinal (withArray state arraydef_0__poly values) len cut span base)
      arraydef_0__arena) base (savedBuffer values len cut span).
Proof.
  intros present ready index range. rewrite savedBuffer_length in range.
  unfold savedLength in range. rewrite (proj2 (Nat.ltb_lt cut len) present) in range.
  rewrite ready_convolution_coefficients by assumption.
  rewrite tailCoefficient_shift by lia. rewrite withArray_preserve_same.
  rewrite savedBuffer_lookup.
  - reflexivity.
  - unfold savedLength. rewrite (proj2 (Nat.ltb_lt cut len) present). exact range.
Qed.

Lemma leftSavedState_contains state values len cut span base :
  ((cut<len)%nat -> ConvolutionReady (withArray state arraydef_0__poly values) len cut span base) ->
  arenaContains
    (memory (leftSavedState (withArray state arraydef_0__poly values) len cut span base)
      arraydef_0__arena) base (savedBuffer values len cut span).
Proof.
  intro ready. unfold leftSavedState. destruct (Nat.ltb cut len) eqn:present.
  - apply Nat.ltb_lt in present. apply arenaContains_saved; auto.
  - intros index range. rewrite savedBuffer_length in range. unfold savedLength in range.
    rewrite present in range. lia.
Qed.

Lemma leftSavedState_arena_prefix state len cut span base index :
  ((cut<len)%nat -> ConvolutionReady state len cut span base) -> index<base ->
  nth index (memory (leftSavedState state len cut span base) arraydef_0__arena) 0%Z=
  nth index (memory state arraydef_0__arena) 0%Z.
Proof.
  intros ready below. unfold leftSavedState. destruct (Nat.ltb cut len) eqn:present; [|reflexivity].
  apply readyConvolution_arena_prefix; [apply ready; apply Nat.ltb_lt; exact present|exact below].
Qed.

Lemma nth_skipn_Z (values : list Z) base index :
  nth index (skipn base values) 0%Z=nth (base+index) values 0%Z.
Proof.
  induction base as [|base IH] in values |- *; [reflexivity|].
  destruct values as [|value values]; [destruct index; reflexivity|].
  cbn [skipn Nat.add nth]. apply IH.
Qed.

Lemma arenaContains_active arena base saved j : arenaContains arena base saved ->
  activeCoefficient (skipn base arena) (length saved) j=activeCoefficient saved (length saved) j.
Proof.
  intro contains. unfold activeCoefficient. destruct (bool_decide (0<=j<Z.of_nat (length saved))%Z) eqn:inside;
    [|reflexivity]. apply bool_decide_eq_true_1 in inside.
  rewrite nth_skipn_Z. apply contains. lia.
Qed.

Lemma mergeBuffer_saved arena base saved values len : arenaContains arena base saved ->
  mergeBuffer values len (skipn base arena) (length saved)=mergeBuffer values len saved (length saved).
Proof.
  intro contains. unfold mergeBuffer. f_equal. apply functional_extensionality. intro index.
  unfold mergeValue. rewrite arenaContains_active by exact contains. reflexivity.
Qed.

Lemma leftSavedState_preserves state len cut span base name :
  name<>arraydef_0__work -> name<>arraydef_0__other -> name<>arraydef_0__result -> name<>arraydef_0__arena ->
  memory (leftSavedState state len cut span base) name=memory state name.
Proof.
  intros. unfold leftSavedState. destruct (Nat.ltb cut len); [apply readyConvolution_preserves; assumption|reflexivity].
Qed.

Lemma leftSavedState_lengths state len cut span base name :
  length (memory (leftSavedState state len cut span base) name)=length (memory state name).
Proof.
  unfold leftSavedState. destruct (Nat.ltb cut len); [unfold readyConvolutionFinal; apply convolutionFinal_lengths|reflexivity].
Qed.

Lemma workspace_leftSavedState state n stage len cut span base : SolverWorkspace state n stage ->
  ((cut<len)%nat -> ConvolutionReady state len cut span base) ->
  SolverWorkspace (leftSavedState state len cut span base) n stage.
Proof.
  intros workspace ready. unfold leftSavedState. destruct (Nat.ltb cut len) eqn:present; [|exact workspace].
  apply workspace_convolution; [exact workspace|apply ready; apply Nat.ltb_lt; exact present].
Qed.

Lemma workspace_storedChildFrames state n stage depth start span middle base saved :
  SolverWorkspace state n stage ->
  SolverWorkspace (storedChildFrames state depth start span middle base saved) n stage.
Proof. intro workspace. unfold storedChildFrames. apply workspace_frames; [exact workspace|rewrite !length_insert; reflexivity]. Qed.

Lemma storedChildFrames_preserves state depth start span middle base saved name : name<>arraydef_0__frames ->
  memory (storedChildFrames state depth start span middle base saved) name=memory state name.
Proof. intro different. unfold storedChildFrames. rewrite withArray_preserve_other by exact different. reflexivity. Qed.

Lemma storedChildFrames_before state depth start span middle base saved index :
  S depth<length (memory state arraydef_0__frames) -> index<depth ->
  nth index (memory (storedChildFrames state depth start span middle base saved) arraydef_0__frames)
    (0%Z,0%Z,0%Z,0%Z,0%Z)=
  nth index (memory state arraydef_0__frames) (0%Z,0%Z,0%Z,0%Z,0%Z).
Proof.
  intros room below. unfold storedChildFrames. rewrite withArray_preserve_same.
  rewrite !nthUpdateExcept by (rewrite ?length_insert; lia). reflexivity.
Qed.
