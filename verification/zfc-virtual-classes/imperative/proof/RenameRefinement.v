From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift Stack ObservedLocal ArenaFrame FrameReplace RenameStack RenameStructure RenameFrames RenameBudget RenameInvariant RenameStep Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameRefinement.
Import IndexExecution SipHashExecution IndexSemantics ObservedLocal RenameStructure RenameInvariant.
Lemma work_rename rho p : RenameStack.work (SetTheory.rename rho p) = RenameStack.work p.
Proof. induction p as [|i j|i j|p IHp q IHq|p IHp] in rho |- *; cbn [SetTheory.rename RenameStack.work]; congruence. Qed.
Definition initialized (f : Frame) := setMachine f (pushed f).
Lemma fits_depth rho depth p : fits rho depth p -> word (Z.of_nat depth).
Proof. destruct p; intros Hfits; exact (proj1 Hfits). Qed.
Lemma initial_invariant f fs p depth m shift arg :
  NativeRepresentation.canonical_arena (machine f) fs -> nth_error fs 0 = Some SetTheory.falsity ->
  meta_value (machine f) 8 = 0 -> parameters m shift arg f ->
  word (nums f vardef_0__rename_node) -> nth_error fs (Z.to_nat (nums f vardef_0__rename_node)) = Some p ->
  nums f vardef_0__rename_initialDepth = Z.of_nat depth -> fits (renaming m shift arg) depth p ->
  Z.of_nat (length fs + RenameStack.work p) <= resource_limit ->
  holds fs (SetTheory.rename (under_binders depth (renaming m shift arg)) p) m shift arg
    (initialized f) (Snapshot fs [RenameStack.visit p depth] SetTheory.falsity).
Proof.
  intros Harena Hfalse Herror Hparameters Hroot Hlookup Hdepth Hfits Hbudget.
  pose proof (proj1 (proj1 Harena)) as [Hmeta Hrest].
  assert (Hten : (10 < length (memory (machine f) arraydef_0__meta))%nat) by lia.
  set (cleared := store_meta (machine f) 10 0).
  assert (Hcleared : NativeRepresentation.canonical_arena cleared fs)
    by (apply (ArenaFrame.storage_arena (machine f)); [apply ArenaFrame.storage_meta; lia|exact Harena]).
  assert (Hclearedmeta : (10 < length (memory cleared arraydef_0__meta))%nat) by (unfold cleared; now rewrite store_meta_length).
  assert (Hempty : RenameFrames.represents cleared fs []).
  { apply RenameFrames.empty. unfold cleared. now apply meta_store_same. }
  constructor; cbn [formulas tasks answer].
  - unfold initialized,pushed. cbn [machine setMachine]. now apply FrameReplace.push_arena.
  - exact Hfalse.
  - unfold initialized,pushed. cbn [machine setMachine]. rewrite Hdepth.
    exact (RenameFrames.push_visit cleared fs [] (nums f vardef_0__rename_node) depth p Hclearedmeta Hempty
      ltac:(unfold maximum; cbn; lia) Hroot (fits_depth _ _ _ Hfits) Hlookup).
  - exact I.
  - constructor; [exact Hfits|constructor].
  - reflexivity.
  - exists []. now rewrite app_nil_r.
  - cbn [RenameStack.pending RenameStack.frame_work]. now rewrite Nat.add_0_r.
  - cbn [RenameStack.pending RenameStack.frame_work]. rewrite work_rename. lia.
  - exact Hparameters.
  - unfold initialized,pushed. cbn [machine setMachine]. rewrite FrameReplace.push_meta_other by discriminate.
    now rewrite meta_store_other by discriminate.
Qed.
Lemma sufficient_budget (fs : list SetTheory.formula) stack : Z.of_nat (length fs + RenameStack.pending stack) <= resource_limit ->
  (RenameStack.pending stack <= Nat.pow limit 8)%nat.
Proof.
  intros Hbudget. apply Nat2Z.inj_le. rewrite RenameBudget.actual_work_budget.
  rewrite Nat2Z.inj_add in Hbudget. unfold resource_limit in Hbudget. change (Z.of_nat (RenameStack.pending stack) <= 115792089237316195423570985008687907853269984665640564039457584007913129639936). lia.
Qed.
Theorem generated_local f fs p depth m shift arg observations :
  NativeRepresentation.canonical_arena (machine f) fs -> nth_error fs 0 = Some SetTheory.falsity ->
  meta_value (machine f) 8 = 0 -> parameters m shift arg f ->
  word (nums f vardef_0__rename_node) -> nth_error fs (Z.to_nat (nums f vardef_0__rename_node)) = Some p ->
  nums f vardef_0__rename_initialDepth = Z.of_nat depth -> fits (renaming m shift arg) depth p ->
  word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  Z.of_nat (length fs + RenameStack.work p) <= resource_limit ->
  exists final next index, execLocalObserved funcdef_0__rename_body (f,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) next /\
    meta_value (machine final) 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (SetTheory.rename (under_binders depth (renaming m shift arg)) p) /\
    (exists extra, next = fs ++ extra) /\ meta_value (machine final) 8 = 0 /\ meta_value (machine final) 10 = 0 /\ (length next <= length fs + RenameStack.work p)%nat.
Proof.
  intros Harena Hfalse Herror Hparameters Hroot Hlookup Hdepth Hfits Hshiftword Hargword Hbudget.
  set (target := SetTheory.rename (under_binders depth (renaming m shift arg)) p).
  set (first := Snapshot fs [RenameStack.visit p depth] SetTheory.falsity).
  pose proof (initial_invariant f fs p depth m shift arg Harena Hfalse Herror Hparameters Hroot Hlookup Hdepth Hfits Hbudget) as Hinitial.
  assert (Hwork : (RenameStack.pending (tasks first) <= Nat.pow limit 8)%nat).
  { apply (sufficient_budget fs). cbn [first tasks RenameStack.pending RenameStack.frame_work]. now rewrite Nat.add_0_r. }
  destruct (RenameBudget.traversal_complete ghost (holds fs target m shift arg) (fun g => RenameStack.pending (tasks g))
    (ready fs target m shift arg) (RenameStep.advance fs target m shift arg Hshiftword Hargword)
    (initialized f) first observations Hinitial Hwork)
    as [final [last [Htraversal [Hfinal [Hrank Hempty]]]]].
  assert (Htasks : tasks last = []) by (now apply pending_zero).
  pose proof (current_valid _ _ _ _ _ _ _ Hfinal) as Hcurrent. rewrite Htasks in Hcurrent.
  destruct Hcurrent as [Hindexword Hvalue].
  pose proof (meaning_valid _ _ _ _ _ _ _ Hfinal) as Hmeaning. rewrite Htasks in Hmeaning.
  cbn [RenameStack.meaning] in Hmeaning. rewrite Hmeaning in Hvalue.
  pose proof (arena_valid _ _ _ _ _ _ _ Hfinal) as Hnext.
  pose proof (proj1 (proj1 Hnext)) as [Hmeta_final Hrest_final].
  assert (Hten_final : (10 < length (memory (machine final) arraydef_0__meta))%nat) by lia.
  assert (Hrun : execLocalObserved funcdef_0__rename_body (f,observations) = Some (tt,(final,observations))).
  { rewrite actual_body. rewrite generated_prefix by (pose proof (proj1 (proj1 Harena)) as [Hmeta Hrest]; lia).
    rewrite local_bind. change (setMachine f (pushed f)) with (initialized f).
    match goal with |- optionBind ?expression _ = _ =>
      assert (Hactual : expression = Some (tt,(final,observations))) by exact Htraversal; rewrite Hactual end.
    cbn [optionBind fst snd]. now apply generated_finish_empty. }
  exists final,(formulas last),(Z.to_nat (meta_value (machine final) 0)).
  split; [exact Hrun|]. split; [exact Hnext|]. split.
  - rewrite Z2Nat.id by exact (proj1 Hindexword). reflexivity.
  - split; [now rewrite Z2Nat.id by exact (proj1 Hindexword)|]. split; [exact Hvalue|]. split.
    + exact (prefix_valid _ _ _ _ _ _ _ Hfinal).
    + split; [exact (error_clear _ _ _ _ _ _ _ Hfinal)|]. split; [exact Hempty|].
      pose proof (allocation_mass _ _ _ _ _ _ _ Hfinal) as Hmass. rewrite Htasks in Hmass.
      cbn [RenameStack.pending] in Hmass. unfold target in Hmass. rewrite work_rename in Hmass. lia.
Qed.
Theorem generated_rename s bs ns fs p depth m shift arg observations :
  NativeRepresentation.canonical_arena s fs -> nth_error fs 0 = Some SetTheory.falsity ->
  meta_value s 8 = 0 -> ns vardef_0__rename_mode = mode_number m ->
  ns vardef_0__rename_shift = Z.of_nat shift -> ns vardef_0__rename_arg = Z.of_nat arg ->
  word (ns vardef_0__rename_node) -> nth_error fs (Z.to_nat (ns vardef_0__rename_node)) = Some p ->
  ns vardef_0__rename_initialDepth = Z.of_nat depth -> fits (renaming m shift arg) depth p ->
  word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  Z.of_nat (length fs + RenameStack.work p) <= resource_limit ->
  exists final next index, execObserved (funcdef_0__rename bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (SetTheory.rename (under_binders depth (renaming m shift arg)) p) /\
    (exists extra, next = fs ++ extra) /\ meta_value final 8 = 0 /\ meta_value final 10 = 0 /\ (length next <= length fs + RenameStack.work p)%nat.
Proof.
  intros Harena Hfalse Herror Hmode Hshift Harg Hroot Hlookup Hdepth Hfits Hshiftword Hargword Hbudget.
  destruct (generated_local {|machine:=s;bools:=bs;nums:=ns|} fs p depth m shift arg observations Harena Hfalse Herror
    (conj Hmode (conj Hshift Harg)) Hroot Hlookup Hdepth Hfits Hshiftword Hargword Hbudget)
    as [final [next [index [Hrun Hpost]]]].
  exists (machine final),next,index. split; [|exact Hpost].
  pose proof (eliminate_correct funcdef_0__rename_body bs ns s observations) as Heliminate.
  rewrite Hrun in Heliminate. exact Heliminate.
Qed.
End RenameRefinement.
