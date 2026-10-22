From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Stack Observation ObservedLocal RenameStack RenameFrames RenameMemoInit RenameMemoControl RenameMemoHit RenameMemoInvariant RenameMemoAccounting RenameMemoStack RenameMemoMeaning FrameReplace RenameMemoNext FormulaEncoding Representation HashTable.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameMemoNextRefinement.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInit RenameMemoControl.
Theorem generated_next_refines (f : Frame) fs p q depth stack left_value current count rho observations :
  RenameMemoInvariant.valid (machine f) count (RenameMemoMeaning.entry_meaning fs rho) ->
  Z.of_nat (S (length stack)) < maximum -> NativeRepresentation.canonical_arena (machine f) fs ->
  RenameFrames.represents (machine f) fs (RenameStack.left_done p q depth :: stack) ->
  meta_value (machine f) 0 = current -> word current -> nth_error fs (Z.to_nat current) = Some left_value ->
  exists final, execLocalObserved iteration (f,observations) = Some (KeepGoing,(final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) fs /\
    RenameFrames.represents (machine final) fs (RenameStack.visit q depth :: RenameStack.right_done p q depth left_value :: stack) /\
    RenameMemoInvariant.valid (machine final) count (RenameMemoMeaning.entry_meaning fs rho) /\
    RenameMemoHit.parameters f final /\ RenameMemoAccounting.passive (machine f) (machine final).
Proof.
  intros Hvalid Hroom Harena Hstack Hcurrent Hcurrentword Hleft.
  pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hvalid) as Hready.
  assert (Hmeta : (10<length (memory (machine f) arraydef_0__meta))%nat) by lia.
  pose proof (RenameMemoInvariant.error_clear _ _ _ Hvalid) as Herror.
  destruct (RenameFrames.top_entry (machine f) fs _ stack Hstack) as [raw [Hraw [Hentry Hframes]]].
  destruct raw as [[[root raw_depth] phase] left_id]. cbn [RenameFrames.entry] in Hentry.
  destruct Hentry as [Hroot [Hdepth [Hdepth_eq [Hphase Hlookup]]]]; subst raw_depth phase.
  assert (Hbound : (Z.to_nat root < length fs)%nat) by (apply nth_error_Some; congruence).
  assert (Hnativebound : (Z.to_nat root < length (memory (machine f) arraydef_0__formulas))%nat).
  { pose proof (proj1 (proj1 Harena)) as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
  pose proof (NativeRepresentation.represented_lookup _ _ _ _ (proj1 (proj2 Harena)) Hlookup) as Hdecode.
  destruct (FormulaEncoding.decode_implication fs _ p q (proj2 (proj2 (proj2 Harena)) _ Hbound) Hdecode)
    as [a [b [Hformula [Ha [Hb [Hp Hq]]]]]].
  assert (Hnth : List.nth (length stack) (memory (machine f) arraydef_0__frames) (0,0,0,0) = (root,Z.of_nat depth,1,left_id))
    by exact (List.nth_error_nth _ _ (0,0,0,0) Hraw).
  set (parent := FrameReplace.write (machine f) (length stack) (root,Z.of_nat depth,2,current)).
  assert (Hparentmeta : (10 < length (memory parent arraydef_0__meta))%nat)
    by (unfold parent; now rewrite FrameReplace.write_other by discriminate).
  assert (Hparententry : RenameFrames.entry fs (root,Z.of_nat depth,2,current) (RenameStack.right_done p q depth left_value)).
  { cbn [RenameFrames.entry]. split; [exact Hroot|]. split; [exact Hdepth|]. split; [reflexivity|].
    split; [reflexivity|]. split; [exact Hlookup|]. auto. }
  assert (Hparentframes : RenameFrames.represents parent fs (RenameStack.right_done p q depth left_value :: stack))
    by (eapply FrameReplace.replace_top; eassumption).
  set (pushed := StackExecution.push_state parent (S (length stack)) b (Z.of_nat depth)).
  assert (Hresult : RenameFrames.represents pushed fs (RenameStack.visit q depth :: RenameStack.right_done p q depth left_value :: stack)).
  { exact (RenameFrames.push_visit parent fs (RenameStack.right_done p q depth left_value :: stack)
      b depth q Hparentmeta Hparentframes Hroom Hb Hdepth Hq). }
  assert (Hpush : execObserved (funcdef_0__push (fun _ => false) (RenameMemoNext.arguments b (Z.of_nat depth)))
    (parent,observations) = Some (tt,(pushed,observations))).
  { apply observed_plain; [apply InternalObservation.push_nf|].
    apply StackExecution.generated_push; [exact Hparentmeta|exact (proj1 Hparentframes)|exact Hroom]. }
  pose proof Hstack as [Hcount [Hcountword Hentries]]. cbn [length] in Hcount,Hcountword.
  exists (RenameMemoNext.result f pushed (length stack) root (Z.of_nat depth) left_id 3 a b). split.
  - eapply RenameMemoNext.generated_next; eassumption.
  - split.
    + apply FrameReplace.push_arena. apply FrameReplace.write_arena. exact Harena.
    + split; [exact Hresult|]. split.
      * apply RenameMemoStack.push_valid. now apply RenameMemoStack.write_valid.
      * split; [apply RenameMemoNext.parameters|].
        apply RenameMemoAccounting.passive_trans with (t:=parent).
        -- apply RenameMemoAccounting.stack. apply RenameMemoStack.write_frame.
        -- apply RenameMemoAccounting.stack. apply RenameMemoStack.push_frame.
Qed.
End RenameMemoNextRefinement.
