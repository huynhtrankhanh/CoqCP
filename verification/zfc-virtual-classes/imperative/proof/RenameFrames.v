From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash InternTail Stack FormulaEncoding Representation NameRepresentation HistoryStorage RenameStack Observation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameFrames.
Import IndexExecution SipHashExecution.
Definition entry fs (raw : Z*Z*Z*Z) task :=
  let '(root,depth,phase,left_id) := raw in word root /\ word depth /\
  match task with
  | RenameStack.visit p d => depth = Z.of_nat d /\ phase = 0 /\ nth_error fs (Z.to_nat root) = Some p
  | RenameStack.left_done p q d => depth = Z.of_nat d /\ phase = 1 /\ nth_error fs (Z.to_nat root) = Some (SetTheory.implies p q)
  | RenameStack.right_done p q d left_value => depth = Z.of_nat d /\ phase = 2 /\
      nth_error fs (Z.to_nat root) = Some (SetTheory.implies p q) /\ word left_id /\ nth_error fs (Z.to_nat left_id) = Some left_value
  | RenameStack.body_done p d => depth = Z.of_nat d /\ phase = 3 /\ nth_error fs (Z.to_nat root) = Some (SetTheory.all p)
  end.
Definition represents (s : Machine) fs stack :=
  meta_value s 10 = Z.of_nat (length stack) /\ Z.of_nat (length stack) <= maximum /\
  Forall2 (entry fs) (firstn (length stack) (memory s arraydef_0__frames)) (rev stack).
Lemma entry_extend fs extra raw task : entry fs raw task -> entry (fs ++ extra) raw task.
Proof.
  destruct raw as [[[root depth] phase] left_id]. destruct task; cbn [entry].
  all: intros [Hroot [Hdepth [Hd [Hp Hnode]]]]; split; [exact Hroot|]; split; [exact Hdepth|];
    split; [exact Hd|]; split; [exact Hp|]; try (now apply FormulaEncoding.nth_error_extend).
  destruct Hnode as [Hnode [Hleft Hvalue]]. split; [now apply FormulaEncoding.nth_error_extend|].
  split; [exact Hleft|now apply FormulaEncoding.nth_error_extend].
Qed.
Lemma capacity s fs stack : represents s fs stack -> (length stack <= length (memory s arraydef_0__frames))%nat.
Proof.
  intros [_ [_ Hframes]]. apply Forall2_length in Hframes. rewrite length_firstn,length_rev in Hframes. lia.
Qed.
Lemma empty s fs : meta_value s 10 = 0 -> represents s fs [].
Proof. intros Hcount. split; [exact Hcount|]. split; [unfold maximum; cbn; lia|constructor]. Qed.
Lemma transport s t fs stack : meta_value t 10 = meta_value s 10 -> memory t arraydef_0__frames = memory s arraydef_0__frames ->
  represents s fs stack -> represents t fs stack.
Proof. intros Hcount Hframes. unfold represents. now rewrite Hcount,Hframes. Qed.
Lemma extend s fs extra stack : represents s fs stack -> represents s (fs ++ extra) stack.
Proof. intros [Hcount [Hword Hframes]]. split; [exact Hcount|]. split; [exact Hword|].
  eapply Forall2_impl; [exact Hframes|]. intros raw task. now apply entry_extend. Qed.
Lemma firstn_related {A B} (R : A -> B -> Prop) xs ys count : Forall2 R xs ys -> Forall2 R (firstn count xs) (firstn count ys).
Proof. intros Hrel. induction Hrel in count |- *; destruct count; cbn; constructor; auto. Qed.
Lemma nth_error_prefix {A} (xs : list A) count index : (index < count)%nat ->
  nth_error (firstn count xs) index = nth_error xs index.
Proof. induction count as [|count IH] in xs,index |- *; [lia|]. destruct xs; destruct index; cbn; auto; intro; apply IH; lia. Qed.
Lemma top_entry s fs task stack : represents s fs (task :: stack) ->
  exists raw, nth_error (memory s arraydef_0__frames) (length stack) = Some raw /\ entry fs raw task /\
    (length stack < length (memory s arraydef_0__frames))%nat.
Proof.
  intros Hrep. pose proof Hrep as [_ [_ Hframes]].
  assert (Htop : nth_error (rev (task :: stack)) (length stack) = Some task).
  { cbn [rev]. rewrite nth_error_app2 by (rewrite length_rev; lia). rewrite length_rev. rewrite Nat.sub_diag. reflexivity. }
  destruct (NameRepresentation.related_lookup _ _ _ _ task Hframes Htop) as [raw [Hraw Hentry]].
  rewrite nth_error_prefix in Hraw by (cbn [length]; lia).
  exists raw. split; [exact Hraw|]. split; [exact Hentry|]. apply nth_error_Some.
  match goal with |- ?expression <> None =>
    assert (Hsame : expression = Some raw) by exact Hraw; rewrite Hsame; discriminate end.
Qed.
Lemma pop s fs task stack : (10 < length (memory s arraydef_0__meta))%nat -> represents s fs (task :: stack) ->
  represents (store_meta s 10 (Z.of_nat (length stack))) fs stack.
Proof.
  intros Hmeta [Hcount [Hword Hframes]]. split; [now apply meta_store_same|]. split; [cbn [length] in Hword; lia|].
  rewrite store_meta_other by discriminate.
  pose proof (firstn_related _ _ _ (length stack) Hframes) as Hprefix.
  rewrite firstn_firstn, Nat.min_l in Hprefix by (cbn [length]; lia).
  cbn [rev] in Hprefix. rewrite firstn_app,length_rev,Nat.sub_diag in Hprefix. cbn [firstn] in Hprefix.
  assert (Htake : firstn (length stack) (rev stack) = rev stack) by (apply firstn_all2; rewrite length_rev; lia).
  rewrite app_nil_r,Htake in Hprefix. exact Hprefix.
Qed.
Lemma push_frames s count node depth : memory (StackExecution.push_state s count node depth) arraydef_0__frames =
  <[count := (node,depth,0,0)]> (growList (memory s arraydef_0__frames) (S count) (0,0,0,0)).
Proof.
  unfold StackExecution.push_state. rewrite store_meta_other by discriminate. cbn [withMemory memory].
  now rewrite InternTailExecution.modify_same,growArrays_same.
Qed.
Lemma push_count s count node depth : (10 < length (memory s arraydef_0__meta))%nat ->
  meta_value (StackExecution.push_state s count node depth) 10 = Z.of_nat (S count).
Proof.
  intros Hmeta. unfold StackExecution.push_state. apply meta_store_same. cbn [withMemory memory].
  rewrite InternTailExecution.modify_other,growArrays_other by discriminate. exact Hmeta.
Qed.
Lemma push_visit s fs stack root depth p : (10 < length (memory s arraydef_0__meta))%nat ->
  represents s fs stack -> Z.of_nat (length stack) < maximum -> word root -> word (Z.of_nat depth) ->
  nth_error fs (Z.to_nat root) = Some p ->
  represents (StackExecution.push_state s (length stack) root (Z.of_nat depth)) fs (RenameStack.visit p depth :: stack).
Proof.
  intros Hmeta Hrep Hroom Hroot Hdepth Hlookup. pose proof (capacity s fs stack Hrep) as Hcapacity.
  destruct Hrep as [Hcount [Hword Hframes]]. split; [now apply push_count|]. split; [cbn [length]; lia|].
  cbn [length]. cbn [rev]. rewrite push_frames,HistoryStorage.write_prefix by exact Hcapacity.
  apply Forall2_app; [exact Hframes|]. constructor; [|constructor]. cbn [entry]. split; [exact Hroot|]. split; [exact Hdepth|]. repeat split; try reflexivity; assumption.
Qed.
Theorem generated_push_visit s bs ns fs stack root depth p observations :
  (10 < length (memory s arraydef_0__meta))%nat -> represents s fs stack -> Z.of_nat (length stack) < maximum ->
  ns vardef_0__push_node = root -> ns vardef_0__push_depth = Z.of_nat depth ->
  word root -> word (Z.of_nat depth) -> nth_error fs (Z.to_nat root) = Some p ->
  exists final, execObserved (funcdef_0__push bs ns) (s,observations) = Some (tt,(final,observations)) /\
    represents final fs (RenameStack.visit p depth :: stack).
Proof.
  intros Hmeta Hrep Hroom Hnode Hdepth Hroot Hdepthword Hlookup.
  exists (StackExecution.push_state s (length stack) root (Z.of_nat depth)). split.
  - apply observed_plain; [apply InternalObservation.push_nf|]. rewrite <-Hnode,<-Hdepth.
    apply StackExecution.generated_push; [exact Hmeta|exact (proj1 Hrep)|exact Hroom].
  - now apply push_visit.
Qed.
End RenameFrames.
