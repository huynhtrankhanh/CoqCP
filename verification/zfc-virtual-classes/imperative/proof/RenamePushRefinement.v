From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Stack Observation ObservedLocal RenameLeaf RenameStack RenameFrames RenameStructure FrameReplace RenamePush FormulaEncoding Representation HashTable RenameConfiguration.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenamePushRefinement.
Import IndexExecution SipHashExecution ObservedLocal RenameStructure.
Definition source tag p q := if Z.eq_dec tag 3 then SetTheory.implies p q else SetTheory.all p.
Definition waiting tag p q depth := if Z.eq_dec tag 3 then RenameStack.left_done p q depth else RenameStack.body_done p depth.
Definition next_depth tag depth := if Z.eq_dec tag 3 then depth else S depth.
Lemma decode_all fs raw p : FormulaEncoding.normal raw -> FormulaEncoding.decode fs raw = Some (SetTheory.all p) ->
  exists a, raw = (4,a,0) /\ word a /\ nth_error fs (Z.to_nat a) = Some p.
Proof.
  destruct raw as [[tag a] b]. unfold FormulaEncoding.normal.
  intros [[-> [-> ->]] | [[Htag [Ha Hb]] | [-> [Ha ->]]]] Hdecode.
  all: try (destruct Htag as [-> | [-> | ->]]).
  all: cbn [FormulaEncoding.decode] in Hdecode; try discriminate.
  - destruct (nth_error fs (Z.to_nat a)); [destruct (nth_error fs (Z.to_nat b))|]; discriminate.
  - destruct (nth_error fs (Z.to_nat a)) as [q|] eqn:Hlookup; [|discriminate].
    injection Hdecode as <-. exists a. split; [reflexivity|]. auto.
Qed.
Lemma source_fields s fs root tag p q : (tag = 3 \/ tag = 4) -> NativeRepresentation.canonical_arena s fs ->
  nth_error fs (Z.to_nat root) = Some (source tag p q) ->
  exists a b, (Z.to_nat root < length (memory s arraydef_0__formulas))%nat /\
    List.nth (Z.to_nat root) (memory s arraydef_0__formulas) (0,0,0) = (tag,a,b) /\ word a /\
    nth_error fs (Z.to_nat a) = Some p.
Proof.
  intros Htag [Htable [Hrep [Hunique Hnormal]]] Hlookup.
  assert (Hbound : (Z.to_nat root < length fs)%nat) by (apply nth_error_Some; congruence).
  assert (Hnative : (Z.to_nat root < length (memory s arraydef_0__formulas))%nat).
  { pose proof (proj1 Htable) as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
  pose proof (NativeRepresentation.represented_lookup s fs _ _ Hrep Hlookup) as Hdecode.
  destruct Htag as [Htag|Htag]; subst tag; cbn [source] in Hdecode.
  - destruct (FormulaEncoding.decode_implication fs _ p q (Hnormal _ Hbound) Hdecode)
      as [a [b [Hraw [Ha [Hb [Hp Hq]]]]]].
    exists a,b. split; [exact Hnative|]. split; [exact Hraw|]. auto.
  - destruct (decode_all fs _ p (Hnormal _ Hbound) Hdecode) as [a [Hraw [Ha Hp]]].
    exists a,0. split; [exact Hnative|]. split; [exact Hraw|]. auto.
Qed.
Lemma child_depth_value tag depth : (tag = 3 \/ tag = 4) -> (tag = 4 -> Z.of_nat depth < maximum) ->
  RenamePush.child_depth tag (Z.of_nat depth) = Z.of_nat (next_depth tag depth).
Proof.
  intros Htag Hsafe. destruct Htag as [Htag|Htag]; subst tag; cbn [RenamePush.child_depth next_depth]; [reflexivity|].
  change (coerceInt (Z.of_nat depth + 1) 64 = Z.of_nat (S depth)).
  replace (Z.of_nat depth + 1) with (Z.of_nat (S depth)) by lia. apply coerce_word. unfold word. pose proof (Hsafe eq_refl). lia.
Qed.
Lemma child_depth_word tag depth : (tag = 3 \/ tag = 4) -> word (Z.of_nat depth) ->
  (tag = 4 -> Z.of_nat depth < maximum) -> word (Z.of_nat (next_depth tag depth)).
Proof.
  intros Htag Hdepth Hsafe. destruct Htag as [Htag|Htag]; subst tag; cbn [next_depth]; [exact Hdepth|].
  change (word (Z.of_nat (S depth))). unfold word. pose proof (Hsafe eq_refl). lia.
Qed.
Theorem generated_fresh_refines (f : Frame) tag fs p q depth stack observations :
  (tag = 3 \/ tag = 4) -> (tag = 4 -> Z.of_nat depth < maximum) ->
  (10 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  Z.of_nat (S (length stack)) < maximum -> NativeRepresentation.canonical_arena (machine f) fs ->
  RenameFrames.represents (machine f) fs (RenameStack.visit (source tag p q) depth :: stack) ->
  exists final, execLocalObserved iteration (f,observations) = Some (KeepGoing,(final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) fs /\
    RenameFrames.represents (machine final) fs (RenameStack.visit p (next_depth tag depth) :: waiting tag p q depth :: stack) /\
    meta_value (machine final) 8 = 0 /\ RenameConfiguration.preserved f final.
Proof.
  intros Htag Hsafe Hmeta Herror Hroom Harena Hstack.
  destruct (RenameFrames.top_entry (machine f) fs _ stack Hstack) as [raw [Hraw [Hentry Hframes]]].
  destruct raw as [[[root raw_depth] phase] left_id]. cbn [RenameFrames.entry] in Hentry.
  destruct Hentry as [Hroot [Hdepth [Hdepth_eq [Hphase Hlookup]]]]; subst raw_depth phase.
  destruct (source_fields (machine f) fs root tag p q Htag Harena Hlookup) as [a [b [Hbound [Hformula [Ha Hchild]]]]].
  assert (Hnth : List.nth (length stack) (memory (machine f) arraydef_0__frames) (0,0,0,0) = (root,Z.of_nat depth,0,left_id))
    by exact (List.nth_error_nth _ _ (0,0,0,0) Hraw).
  set (parent := FrameReplace.write (machine f) (length stack) (root,Z.of_nat depth,RenamePush.parent_phase tag,0)).
  assert (Hparentmeta : (10 < length (memory parent arraydef_0__meta))%nat)
    by (unfold parent; now rewrite FrameReplace.write_other by discriminate).
  assert (Hparententry : RenameFrames.entry fs (root,Z.of_nat depth,RenamePush.parent_phase tag,0) (waiting tag p q depth)).
  { destruct Htag as [Htag|Htag]; subst tag.
    all: cbn [waiting RenamePush.parent_phase RenameFrames.entry];
      split; [exact Hroot|]; split; [exact Hdepth|]; split; [reflexivity|]; split; [reflexivity|exact Hlookup]. }
  assert (Hparentframes : RenameFrames.represents parent fs (waiting tag p q depth :: stack))
    by (eapply FrameReplace.replace_top; eassumption).
  pose proof (child_depth_word tag depth Htag Hdepth Hsafe) as Hchilddepth.
  set (pushed := StackExecution.push_state parent (S (length stack)) a (Z.of_nat (next_depth tag depth))).
  assert (Hresult : RenameFrames.represents pushed fs (RenameStack.visit p (next_depth tag depth) :: waiting tag p q depth :: stack)).
  { exact (RenameFrames.push_visit parent fs (waiting tag p q depth :: stack) a (next_depth tag depth) p Hparentmeta Hparentframes Hroom Ha Hchilddepth Hchild). }
  assert (Hpush : execObserved (funcdef_0__push (fun _ => false) (RenamePush.arguments a (Z.of_nat (next_depth tag depth))))
    (parent,observations) = Some (tt,(pushed,observations))).
  { apply observed_plain; [apply InternalObservation.push_nf|].
    apply StackExecution.generated_push; [exact Hparentmeta|exact (proj1 Hparentframes)|exact Hroom]. }
  rewrite <-(child_depth_value tag depth Htag Hsafe) in Hpush.
  pose proof Hstack as [Hcount [Hcountword Hentries]]. cbn [length] in Hcount,Hcountword.
  exists (RenamePush.result f pushed (length stack) root (Z.of_nat depth) left_id tag a b). split.
  - eapply RenamePush.generated_fresh; eassumption.
  - split.
    + apply FrameReplace.push_arena. apply FrameReplace.write_arena. exact Harena.
    + split; [exact Hresult|]. split.
      * change (meta_value pushed 8 = 0). unfold pushed,parent. rewrite FrameReplace.push_meta_other by lia.
        rewrite FrameReplace.write_meta. exact Herror.
      * apply RenameConfiguration.push.
Qed.
End RenamePushRefinement.
