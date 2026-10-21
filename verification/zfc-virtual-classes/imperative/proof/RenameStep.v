From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift ObservedLocal RenameStack RenameStructure RenameFrames RenameInvariant RenameConfiguration RenameFalsityRefinement RenameAtomRefinement RenamePushRefinement RenameNextRefinement RenameJoinRefinement Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameStep.
Import IndexExecution SipHashExecution IndexSemantics ObservedLocal RenameStructure RenameInvariant.
Section FixedInput.
Context (base : list SetTheory.formula) (target : SetTheory.formula) (m : mode) (shift arg : nat).
Hypothesis shift_word : word (Z.of_nat shift).
Hypothesis arg_word : word (Z.of_nat arg).
Let good := holds base target m shift arg.
Let mapping := renaming m shift arg.
Lemma finish f fs stack value final next new_stack new_value observations :
  good f (Snapshot fs stack value) -> stack <> [] ->
  RenameStack.tick mapping (stack,value) = (new_stack,new_value) ->
  execLocalObserved iteration (f,observations) = Some (KeepGoing,(final,observations)) ->
  NativeRepresentation.canonical_arena (machine final) next -> RenameFrames.represents (machine final) next new_stack ->
  current next new_stack new_value final -> (exists extra, next = fs ++ extra) ->
  (length next <= S (length fs))%nat -> meta_value (machine final) 8 = 0 -> RenameConfiguration.preserved f final ->
  exists final next_ghost, execLocalObserved iteration (f,observations) = Some (KeepGoing,(final,observations)) /\
    good final next_ghost /\ RenameStack.pending (tasks next_ghost) = (RenameStack.pending stack - 1)%nat.
Proof.
  intros Hgood Hnonempty Htick Hrun Harena Hframes Hcurrent Hextends Hgrowth Herror Hconfiguration.
  exists final,(Snapshot next new_stack new_value). split; [exact Hrun|]. split.
  - exact (adopt base target m shift arg f (Snapshot fs stack value) final next new_stack new_value Hgood Hnonempty Htick Harena Hframes Hcurrent Hextends Hgrowth Herror Hconfiguration).
  - destruct stack as [|head tail]; [contradiction|].
    pose proof (RenameStack.tick_decreases mapping head tail value) as Hdecrease. rewrite Htick in Hdecrease. cbn [tasks fst] in *. lia.
Qed.
Theorem advance f g observations : good f g -> (0 < RenameStack.pending (tasks g))%nat ->
  exists final next, execLocalObserved iteration (f,observations) = Some (KeepGoing,(final,observations)) /\
    good final next /\ RenameStack.pending (tasks next) = (RenameStack.pending (tasks g) - 1)%nat.
Proof.
  destruct g as [fs stack value]. intros Hgood Hpositive. cbn [tasks] in *.
  pose proof (arena_valid _ _ _ _ _ _ _ Hgood) as Harena.
  pose proof (frames_valid _ _ _ _ _ _ _ Hgood) as Hframes.
  pose proof (current_valid _ _ _ _ _ _ _ Hgood) as Hcurrent.
  pose proof (fits_valid _ _ _ _ _ _ _ Hgood) as Hfits.
  pose proof (falsity_valid _ _ _ _ _ _ _ Hgood) as Hfalse.
  pose proof (capacity _ _ _ _ _ _ _ Hgood) as Hcapacity.
  pose proof (stack_room _ _ _ _ _ _ _ Hgood) as Hroom.
  destruct (ready _ _ _ _ _ _ _ Hgood) as [Hmeta [Hempty Herror]].
  destruct (parameters_valid _ _ _ _ _ _ _ Hgood) as [Hmode [Hshift Harg]].
  cbn [formulas tasks answer] in Harena,Hframes,Hcurrent,Hfits,Hfalse,Hcapacity,Hroom.
  destruct stack as [|task stack]; [cbn [RenameStack.pending] in Hpositive; lia|].
  inversion Hfits as [|head tail Hhead Htail]; subst head tail.
  destruct task as [p depth|p q depth|p q depth left_value|p depth].
  - destruct p as [|i j|i j|p q|p].
    + destruct (RenameFalsityRefinement.generated_falsity_refines f fs depth stack observations Hmeta Herror Harena Hframes)
        as [final [Hrun [Hnext [Hstack [Hindex [Hflag Hconfiguration]]]]]].
      eapply finish with (final:=final) (next:=fs) (new_stack:=stack) (new_value:=SetTheory.falsity); try eassumption; try discriminate; try reflexivity.
      * eapply current_with_id with (index:=0%nat); eassumption.
      * exists []. now rewrite app_nil_r.
      * lia.
    + cbn [task_fits fits] in Hhead. destruct Hhead as [Hdepth [Hi [Hj [Hmapped_i Hmapped_j]]]].
      destruct (RenameAtomRefinement.generated_atom_refines f 1 fs i j depth stack m shift arg observations
        (or_introl eq_refl) Hmode Hshift Harg Hmeta Herror Hcapacity Harena Hframes Hi Hj shift_word arg_word Hmapped_i Hmapped_j)
        as [final [next [index [Hrun [Hnext [Hstack [Hindex [Hlookup [Hextends [Hflag [Hconfiguration Hgrowth]]]]]]]]]]].
      eapply finish with (final:=final) (next:=next) (new_stack:=stack) (new_value:=SetTheory.rename (under_binders depth mapping) (SetTheory.equal i j)); try eassumption; try discriminate; try reflexivity.
      eapply current_with_id; eassumption.
    + cbn [task_fits fits] in Hhead. destruct Hhead as [Hdepth [Hi [Hj [Hmapped_i Hmapped_j]]]].
      destruct (RenameAtomRefinement.generated_atom_refines f 2 fs i j depth stack m shift arg observations
        (or_intror eq_refl) Hmode Hshift Harg Hmeta Herror Hcapacity Harena Hframes Hi Hj shift_word arg_word Hmapped_i Hmapped_j)
        as [final [next [index [Hrun [Hnext [Hstack [Hindex [Hlookup [Hextends [Hflag [Hconfiguration Hgrowth]]]]]]]]]]].
      eapply finish with (final:=final) (next:=next) (new_stack:=stack) (new_value:=SetTheory.rename (under_binders depth mapping) (SetTheory.member i j)); try eassumption; try discriminate; try reflexivity.
      eapply current_with_id; eassumption.
    + destruct (RenamePushRefinement.generated_fresh_refines f 3 fs p q depth stack observations
        (or_introl eq_refl) ltac:(discriminate) Hmeta Herror Hroom Harena Hframes)
        as [final [Hrun [Hnext [Hstack [Hflag Hconfiguration]]]]].
      eapply finish with (final:=final) (next:=fs) (new_stack:=RenameStack.visit p depth :: RenameStack.left_done p q depth :: stack) (new_value:=value); try eassumption; try discriminate; try reflexivity.
      * exists []. now rewrite app_nil_r.
      * lia.
    + cbn [task_fits fits] in Hhead. destruct Hhead as [Hdepth [Hdepthbound Hbody]].
      destruct (RenamePushRefinement.generated_fresh_refines f 4 fs p SetTheory.falsity depth stack observations
        (or_intror eq_refl) ltac:(intros _; exact Hdepthbound) Hmeta Herror Hroom Harena Hframes)
        as [final [Hrun [Hnext [Hstack [Hflag Hconfiguration]]]]].
      eapply finish with (final:=final) (next:=fs) (new_stack:=RenameStack.visit p (S depth) :: RenameStack.body_done p depth :: stack) (new_value:=value); try eassumption; try discriminate; try reflexivity.
      * exists []. now rewrite app_nil_r.
      * lia.
  - destruct Hcurrent as [Hcurrentword Hlookup].
    destruct (RenameNextRefinement.generated_next_refines f fs p q depth stack value (meta_value (machine f) 0) observations
      Hmeta Herror Hroom Harena Hframes eq_refl Hcurrentword Hlookup)
      as [final [Hrun [Hnext [Hstack [Hflag Hconfiguration]]]]].
    eapply finish with (final:=final) (next:=fs) (new_stack:=RenameStack.visit q depth :: RenameStack.right_done p q depth value :: stack) (new_value:=value); try eassumption; try discriminate; try reflexivity.
    + exists []. now rewrite app_nil_r.
    + lia.
  - destruct Hcurrent as [Hcurrentword Hlookup].
    destruct (RenameJoinRefinement.generated_join_refines f 2 fs p q depth stack left_value value (meta_value (machine f) 0) observations
      (or_introl eq_refl) Hmeta Herror Hcapacity Harena Hframes eq_refl Hcurrentword Hlookup)
      as [final [next [index [Hrun [Hnext [Hstack [Hindex [Hlookupnext [Hextends [Hflag [Hconfiguration Hgrowth]]]]]]]]]]].
    eapply finish with (final:=final) (next:=next) (new_stack:=stack) (new_value:=SetTheory.implies left_value value); try eassumption; try discriminate; try reflexivity.
    eapply current_with_id; eassumption.
  - destruct Hcurrent as [Hcurrentword Hlookup].
    destruct (RenameJoinRefinement.generated_join_refines f 3 fs p SetTheory.falsity depth stack SetTheory.falsity value (meta_value (machine f) 0) observations
      (or_intror eq_refl) Hmeta Herror Hcapacity Harena Hframes eq_refl Hcurrentword Hlookup)
      as [final [next [index [Hrun [Hnext [Hstack [Hindex [Hlookupnext [Hextends [Hflag [Hconfiguration Hgrowth]]]]]]]]]]].
    eapply finish with (final:=final) (next:=next) (new_stack:=stack) (new_value:=SetTheory.all value); try eassumption; try discriminate; try reflexivity.
    eapply current_with_id; eassumption.
Qed.
End FixedInput.
End RenameStep.
