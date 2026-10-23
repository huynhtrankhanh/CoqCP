From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift ObservedLocal FormulaEncoding Representation FormulaTopology ArenaFrame
  Intern InternReserve FormulaCircuit FormulaCircuitProperties AxiomRefl AxiomK AxiomSRefinement AxiomStorage
  AxiomSeparationCircuits AxiomSeparationRaw RenameMemoRun RenameMemoBounds RenameMemoResourceBounds RenameMemoIndexBounds
  RenameMemoTransition RenameMemoCallers RenameMemoOutput RenameMemoLengths RenameMemoClassEqual RenameStack.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module AxiomSeparationRefinement.
Import IndexExecution SipHashExecution ObservedLocal IndexSemantics.
Local Opaque funcdef_0__intern funcdef_0__rename funcdef_0__axiom.
Lemma separation_result p : RenameStack.renamed (renaming separation_mode 0 0) 0 p=AxiomSeparationCircuits.renamed p.
Proof.
  unfold RenameStack.renamed,under_binders,AxiomSeparationCircuits.renamed.
  apply RenameMemoCallers.rename_extensional. intros [|i]; cbn [renaming SetTheory.sep_rename];lia.
Qed.
Theorem generated_refines s bs ns fs p root bound reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs root=Some p -> nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__axiom_tag=15 -> ns vardef_0__axiom_p=Z.of_nat root ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  RenameMemoIndexBounds.formula_bound bound p -> Z.of_nat bound+2<=maximum ->
  Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  Z.of_nat (length fs+S root*S root+14+reserve)<=9223372036854775807 ->
  exists built next,
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations)) /\
    NativeRepresentation.canonical_arena (AxiomRefl.finished built) next /\
    meta_value (AxiomRefl.finished built) 13=1 /\ meta_value (AxiomRefl.finished built) 8=0 /\
    word (meta_value (AxiomRefl.finished built) 0) /\
    nth_error next (Z.to_nat (meta_value (AxiomRefl.finished built) 0))=Some (SetTheory.separation p) /\
    SetTheory.derives (SetTheory.separation p) /\
    (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered (AxiomRefl.finished built) (length next) /\
    (length next<=length fs+S root*S root+14)%nat /\ AxiomStorage.logical_frame s (AxiomRefl.finished built).
Proof.
  intros Hmeta Hsip Harena Htopology Herror Hlookup Hfalse Htag Hroot Hfuel Hbound Hindices Hheight Hbudget.
  assert (Hrootword:word (Z.of_nat root)).
  { assert (Hlt:(root<length fs)%nat) by (apply nth_error_Some;congruence).
    apply Nat2Z.inj_lt in Hlt. unfold word,maximum. rewrite !Nat2Z.inj_add in Hbudget. lia. }
  pose proof (AxiomK.clearing_storage s) as Hclear.
  pose proof (ArenaFrame.storage_arena s (AxiomRefl.cleared s) fs Hclear Harena) as Hclear_arena.
  pose proof (AxiomK.storage_topology s (AxiomRefl.cleared s) (length fs) Hclear Htopology) as Hclear_topology.
  assert (Hclear_error:meta_value (AxiomRefl.cleared s) 8=0)
    by (unfold AxiomRefl.cleared;rewrite meta_store_other by lia;exact Herror).
  assert (Hrep:FormulaCircuit.represents fs [0] AxiomSeparationCircuits.initial).
  { constructor;[split;[unfold word,maximum;lia|exact Hfalse]|constructor]. }
  assert (Hprebudget:Z.of_nat (length fs+length AxiomSeparationCircuits.before+(S root*S root+12+reserve))<=9223372036854775807).
  { change (Z.of_nat (length fs+2+(S root*S root+12+reserve))<=9223372036854775807). lia. }
  destruct (FormulaCircuitProperties.complete AxiomSeparationCircuits.before (AxiomRefl.cleared s) fs
    [0] AxiomSeparationCircuits.initial AxiomSeparationCircuits.middle (S root*S root+12+reserve) observations
    Hclear_arena Hclear_topology Hclear_error Hrep AxiomSeparationCircuits.before_fits AxiomSeparationCircuits.before_inferred Hprebudget)
    as (prepared & pfs & pids & Hbefore & Hpframe & Hparena & Hperror & Hprep & Hpprefix & Hpreserve & Hptopology & Hpgrowth).
  pose proof (FormulaCircuitProperties.lengths _ _ _ _ _ _ Hbefore) as [Hpmeta Hpsip].
  assert (Hpmeta32:(31<length (memory prepared arraydef_0__meta))%nat)
    by (rewrite Hpmeta;unfold AxiomRefl.cleared;rewrite store_meta_length;exact Hmeta).
  assert (Hpsipready:(0<length (memory prepared arraydef_0__sipState))%nat)
    by (rewrite Hpsip;unfold AxiomRefl.cleared;rewrite store_meta_other by discriminate;exact Hsip).
  assert (Hplookup:nth_error pfs root=Some p) by (eapply InternReserve.lookup_preserved;eassumption).
  assert (Hpfalse:nth_error pfs 0=Some SetTheory.falsity) by (eapply InternReserve.lookup_preserved;eassumption).
  destruct (RenameMemoCallers.fixed_checks bound separation_mode (or_introl eq_refl) Hindices) as [Hzeroword Hindexroom].
  assert (Hroom:Z.of_nat (length pfs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit).
  { unfold RenameMemoResourceBounds.doubling_limit. rewrite !Nat2Z.inj_add in Hpreserve. lia. }
  destruct (RenameMemoRun.generated prepared (fun _=>false) (AxiomSeparationRaw.rename_arguments (Z.of_nat root))
    pfs p root 0 separation_mode 0 0 bound Hpmeta32 Hpsipready (RenameMemoClassEqual.arena_positive _ _ Hparena)
    Hperror Hparena Hptopology Hplookup Hpfalse eq_refl eq_refl eq_refl eq_refl eq_refl Hfuel Hroom
    Hzeroword Hzeroword Hbound Hindexroom Hheight observations)
    as (rframe & rfs & count & Hrename & Hrarena & Hcache & Hrword & Hrmeaning & Hrsource & Hrerror & Hempty & Hrgrowth & Hrtopology).
  rewrite separation_result in Hrmeaning.
  pose proof (RenameMemoOutput.source_extension pfs rfs Hrsource) as Hrprefix.
  assert (Hrrep:FormulaCircuit.represents rfs (pids++[meta_value (machine rframe) 0])
    (AxiomSeparationCircuits.middle++[AxiomSeparationCircuits.renamed p])).
  { apply Forall2_app;[eapply FormulaCircuit.extend;eassumption|]. constructor;[split;assumption|constructor]. }
  assert (Hremaining:Z.of_nat (length rfs+length AxiomSeparationCircuits.after+reserve)<=9223372036854775807).
  { change (Z.of_nat (length rfs+12+reserve)<=9223372036854775807). rewrite !Nat2Z.inj_add in Hpreserve. lia. }
  destruct (FormulaCircuitProperties.complete AxiomSeparationCircuits.after (machine rframe) rfs
    (pids++[meta_value (machine rframe) 0]) (AxiomSeparationCircuits.middle++[AxiomSeparationCircuits.renamed p])
    (AxiomSeparationCircuits.values p) reserve observations Hrarena Hrtopology Hrerror Hrrep
    AxiomSeparationCircuits.after_fits (AxiomSeparationCircuits.after_inferred p) Hremaining)
    as (built & next & ids & Htrace & Hbframe & Hbarena & Hberror & Hbrep & Hbprefix & Hbreserve & Hbtopology & Hbgrowth).
  assert (Hrun:execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations))).
  { apply (AxiomSeparationRaw.generated_helper s bs ns prepared pids (machine rframe) built ids (Z.of_nat root) observations).
    - lia.
    - exact Htag.
    - exact Hroot.
    - eapply AxiomSRefinement.source_reference;[exact Harena|exact Hrootword|now rewrite Nat2Z.id,Hlookup].
    - exact Hbefore.
    - exact Hrename.
    - exact Htrace. }
  assert (Hidlength:length (pids++[meta_value (machine rframe) 0])=4%nat).
  { pose proof (Forall2_length Hprep) as Hlength. change (length pids=3%nat) in Hlength. rewrite length_app. cbn [length]. lia. }
  destruct (AxiomSeparationCircuits.result observations (machine rframe) (pids++[meta_value (machine rframe) 0])
    built ids next p Hidlength Htrace Hbrep) as (Hbword & Hbmeaning & Hbderives).
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hbmeta.
  pose proof (proj1 (RenameMemoLengths.observed_lengths _ _ _ _ _ _ Hrename)) as Hrmeta.
  assert (Hbmeta13:(13<length (memory built arraydef_0__meta))%nat) by (rewrite Hbmeta,Hrmeta;lia).
  destruct (AxiomK.finishing_result built Hbmeta13) as (Hsuccess & Hfinalerror & Hfinalid).
  change (meta_value (AxiomRefl.finished built) 0=meta_value built 0) in Hfinalid.
  exists built,next. split;[exact Hrun|].
  split;[eapply ArenaFrame.storage_arena;[apply AxiomRefl.finished_storage|exact Hbarena]|].
  split;[exact Hsuccess|]. split;[unfold AxiomRefl.finished;rewrite !meta_store_other by lia;exact Hberror|].
  split;[now rewrite Hfinalid|]. split;[now rewrite Hfinalid|]. split;[exact Hbderives|].
  split;[eapply InternReserve.extends_trans;[exact Hpprefix|];eapply InternReserve.extends_trans;eassumption|].
  split;[exact Hbreserve|].
  split;[eapply AxiomK.storage_topology;[apply AxiomRefl.finished_storage|exact Hbtopology]|].
  split;[change (length next<=length rfs+12)%nat in Hbgrowth;change (length pfs<=length fs+2)%nat in Hpgrowth;lia|].
  eapply AxiomStorage.generated_frame;exact Hrun.
Qed.
End AxiomSeparationRefinement.
