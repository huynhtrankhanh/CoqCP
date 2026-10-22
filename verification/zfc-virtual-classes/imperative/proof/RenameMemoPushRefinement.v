From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Stack Observation ObservedLocal RenameMemoInit RenameMemoControl RenameMemoHit RenameStack RenameFrames RenameMemoInvariant RenameMemoLookup RenameMemoMeaning RenameMemoVisit RenameMemoStorage RenameMemoAccounting RenameMemoStack FrameReplace RenameMemoPush FormulaEncoding Representation HashTable.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameMemoPushRefinement.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInit RenameMemoControl.
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
  RenameMemoPush.child_depth tag (Z.of_nat depth) = Z.of_nat (next_depth tag depth).
Proof.
  intros Htag Hsafe. destruct Htag as [Htag|Htag]; subst tag; cbn [RenameMemoPush.child_depth next_depth]; [reflexivity|].
  change (coerceInt (Z.of_nat depth + 1) 64 = Z.of_nat (S depth)).
  replace (Z.of_nat depth + 1) with (Z.of_nat (S depth)) by lia. apply coerce_word. unfold word. pose proof (Hsafe eq_refl). lia.
Qed.
Lemma child_depth_word tag depth : (tag = 3 \/ tag = 4) -> word (Z.of_nat depth) ->
  (tag = 4 -> Z.of_nat depth < maximum) -> word (Z.of_nat (next_depth tag depth)).
Proof.
  intros Htag Hdepth Hsafe. destruct Htag as [Htag|Htag]; subst tag; cbn [next_depth]; [exact Hdepth|].
  change (word (Z.of_nat (S depth))). unfold word. pose proof (Hsafe eq_refl). lia.
Qed.
Theorem generated_fresh_miss (f : Frame) tag fs rho p q depth stack count root left_id observations :
  (tag = 3 \/ tag = 4) -> (tag = 4 -> Z.of_nat depth < maximum) ->
  RenameMemoInvariant.valid (machine f) count (RenameMemoMeaning.entry_meaning fs rho) ->
  Z.of_nat (S (length stack)) < maximum -> NativeRepresentation.canonical_arena (machine f) fs ->
  RenameFrames.represents (machine f) fs (RenameStack.visit (source tag p q) depth :: stack) ->
  RenameMemoVisit.view (machine f) fs (source tag p q) depth stack root left_id ->
  RenameMemoLookup.lookup (machine f) (root,Z.of_nat depth) count=None ->
  exists final, execLocalObserved iteration (f,observations) = Some (KeepGoing,(final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) fs /\
    RenameFrames.represents (machine final) fs (RenameStack.visit p (next_depth tag depth) :: waiting tag p q depth :: stack) /\
    RenameMemoInvariant.valid (machine final) count (RenameMemoMeaning.entry_meaning fs rho) /\ RenameMemoHit.parameters f final /\ RenameMemoAccounting.passive (machine f) (machine final).
Proof.
  intros Htag Hsafe Hvalid Hroom Harena Hstack Hview Hnone.
  pose proof Hvalid as [Hmeta Hsip Hpositive Herror Hcapacity Hmin HcapWord Hmemo Hlive Hload Hentries Hindexed].
  destruct Hview as [Hcount Hcountword Hroot Hdepth Hframes Hnth Hlookup Hnativebound].
  destruct (source_fields (machine f) fs root tag p q Htag Harena Hlookup) as [a [b [Hbound [Hformula [Ha Hchild]]]]].
  set (looked:=RenameMemoLookup.result_state (machine f) (root,Z.of_nat depth) count).
  assert (Hlookvalid : RenameMemoInvariant.valid looked count (RenameMemoMeaning.entry_meaning fs rho))
    by now apply RenameMemoInvariant.lookup_valid.
  pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hlookvalid) as Hlookmeta.
  assert (Hget : execObserved (funcdef_0__renameCacheGet (fun _=>false) (RenameMemoHit.arguments root (Z.of_nat depth)))
    (machine f,observations)=Some (tt,(looked,observations))).
  { pose proof (RenameMemoLookup.generated_lookup_exact (machine f) (fun _=>false) (RenameMemoHit.arguments root (Z.of_nat depth)) count observations
      Hmeta Hsip Hpositive Hcapacity ltac:(lia) HcapWord Hmemo) as Hrun.
    cbv beta iota zeta delta [RenameMemoHit.arguments] in Hrun.
    rewrite updated_same,updated_other,updated_same in Hrun by discriminate. exact Hrun. }
  assert (Hmiss : meta_value looked 31=maximum).
  { unfold looked. rewrite RenameMemoLookup.result_value,Hnone by exact Hmeta. reflexivity. }
  assert (Hlookarena : NativeRepresentation.canonical_arena looked fs).
  { apply RenameMemoStorage.canonical_arena with (s:=machine f); [apply RenameMemoInvariant.lookup_storage|exact Harena]. }
  assert (Hlookframes : RenameFrames.represents looked fs (RenameStack.visit (source tag p q) depth::stack)).
  { pose proof (RenameMemoLookup.result_frame (machine f) (root,Z.of_nat depth) count) as [Harrays [Hcells _]].
    apply RenameFrames.transport with (s:=machine f); [apply Hcells; lia|apply Harrays; discriminate|exact Hstack]. }
  assert (Hlookcapacity : (length stack<length (memory looked arraydef_0__frames))%nat).
  { pose proof (RenameMemoLookup.result_frame (machine f) (root,Z.of_nat depth) count) as [Harrays _].
    unfold looked. rewrite Harrays by discriminate. exact Hframes. }
  set (parent := FrameReplace.write looked (length stack) (root,Z.of_nat depth,RenameMemoPush.parent_phase tag,0)).
  assert (Hparentmeta : (10 < length (memory parent arraydef_0__meta))%nat)
    by (unfold parent; rewrite FrameReplace.write_other by discriminate; lia).
  assert (Hparententry : RenameFrames.entry fs (root,Z.of_nat depth,RenameMemoPush.parent_phase tag,0) (waiting tag p q depth)).
  { destruct Htag as [Htag|Htag]; subst tag.
    all: cbn [waiting RenameMemoPush.parent_phase RenameFrames.entry];
      split; [exact Hroot|]; split; [exact Hdepth|]; split; [reflexivity|]; split; [reflexivity|exact Hlookup]. }
  assert (Hparentframes : RenameFrames.represents parent fs (waiting tag p q depth :: stack))
    by (eapply FrameReplace.replace_top; [lia|exact Hlookframes|exact Hparententry]).
  pose proof (child_depth_word tag depth Htag Hdepth Hsafe) as Hchilddepth.
  set (pushed := StackExecution.push_state parent (S (length stack)) a (Z.of_nat (next_depth tag depth))).
  assert (Hresult : RenameFrames.represents pushed fs (RenameStack.visit p (next_depth tag depth) :: waiting tag p q depth :: stack)).
  { exact (RenameFrames.push_visit parent fs (waiting tag p q depth :: stack) a (next_depth tag depth) p Hparentmeta Hparentframes Hroom Ha Hchilddepth Hchild). }
  assert (Hpush : execObserved (funcdef_0__push (fun _ => false) (RenameMemoPush.arguments a (Z.of_nat (next_depth tag depth))))
    (parent,observations) = Some (tt,(pushed,observations))).
  { apply observed_plain; [apply InternalObservation.push_nf|].
    apply StackExecution.generated_push; [exact Hparentmeta|exact (proj1 Hparentframes)|exact Hroom]. }
  rewrite <-(child_depth_value tag depth Htag Hsafe) in Hpush.
  exists (RenameMemoPush.result f pushed (length stack) root (Z.of_nat depth) left_id tag a b). split.
  - eapply RenameMemoPush.generated_fresh_composition; eassumption.
  - split.
    + apply FrameReplace.push_arena. apply FrameReplace.write_arena. exact Hlookarena.
    + split; [exact Hresult|]. split.
      * apply RenameMemoStack.push_valid. now apply RenameMemoStack.write_valid.
      * split; [apply RenameMemoPush.parameters|].
        apply RenameMemoAccounting.passive_trans with (t:=parent).
        -- apply RenameMemoAccounting.passive_trans with (t:=looked); [apply RenameMemoAccounting.lookup|].
           apply RenameMemoAccounting.stack. apply RenameMemoStack.write_frame.
        -- apply RenameMemoAccounting.stack. apply RenameMemoStack.push_frame.
Qed.
End RenameMemoPushRefinement.
