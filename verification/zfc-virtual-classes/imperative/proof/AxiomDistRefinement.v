From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift ObservedLocal FormulaEncoding Representation FormulaTopology ArenaFrame
  Intern InternReserve FormulaCircuit FormulaCircuitProperties AxiomRefl AxiomK AxiomSRefinement AxiomStorage AxiomDistRaw
  RenameMemoRun RenameMemoBounds RenameMemoResourceBounds RenameMemoIndexBounds RenameMemoTransition RenameMemoCallers
  RenameMemoOutput RenameMemoLengths RenameMemoClassEqual RenameStack.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module AxiomDistRefinement.
Import IndexExecution SipHashExecution ObservedLocal IndexSemantics.
Local Opaque funcdef_0__intern funcdef_0__rename funcdef_0__axiom.
Definition values p q := [p;q;SetTheory.shift p;SetTheory.implies (SetTheory.shift p) q;
  SetTheory.all (SetTheory.implies (SetTheory.shift p) q);SetTheory.all q;
  SetTheory.implies p (SetTheory.all q);SetTheory.axiom_formula (SetTheory.Dist p q)].
Lemma infer p q : FormulaCircuit.infer AxiomDistRaw.plan [p;q;SetTheory.shift p]=Some (values p q).
Proof. reflexivity. Qed.
Lemma fits : Forall FormulaCircuit.fits AxiomDistRaw.plan.
Proof. repeat constructor. Qed.
Lemma shift_result p : RenameStack.renamed (renaming shift_mode 1 0) 0 p=SetTheory.shift p.
Proof.
  unfold RenameStack.renamed,under_binders,SetTheory.shift. apply RenameMemoCallers.rename_extensional.
  intro i. cbn [renaming]. lia.
Qed.
Lemma result observations s p_id q_id shifted final ids next p q :
  FormulaCircuit.executes observations AxiomDistRaw.plan s [p_id;q_id;shifted] final ids ->
  FormulaCircuit.represents next ids (values p q) ->
  word (meta_value final 0) /\
  nth_error next (Z.to_nat (meta_value final 0))=Some (SetTheory.axiom_formula (SetTheory.Dist p q)) /\
  SetTheory.derives (SetTheory.axiom_formula (SetTheory.Dist p q)).
Proof.
  intros Htrace Hrep.
  pose proof (FormulaCircuit.wire next ids (values p q) 7
    (SetTheory.axiom_formula (SetTheory.Dist p q)) Hrep eq_refl) as Hwire.
  unfold AxiomDistRaw.plan in Htrace.
  repeat match goal with H:FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H;clear H;subst end.
  match goal with H:FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H;clear H;subst end.
  cbn [List.nth app] in Hwire. destruct Hwire as [Hword Hmeaning].
  split;[exact Hword|]. split;[exact Hmeaning|apply SetTheory.d_dist].
Qed.
Theorem generated_refines s bs ns fs p q root other bound reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs root=Some p -> nth_error fs other=Some q -> nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__axiom_tag=4 -> ns vardef_0__axiom_p=Z.of_nat root -> ns vardef_0__axiom_q=Z.of_nat other ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  RenameMemoIndexBounds.formula_bound bound p -> Z.of_nat bound+1<=maximum ->
  Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  Z.of_nat (length fs+S root*S root+5+reserve)<=9223372036854775807 ->
  exists built next,
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations)) /\
    NativeRepresentation.canonical_arena (AxiomRefl.finished built) next /\
    meta_value (AxiomRefl.finished built) 13=1 /\ meta_value (AxiomRefl.finished built) 8=0 /\
    word (meta_value (AxiomRefl.finished built) 0) /\
    nth_error next (Z.to_nat (meta_value (AxiomRefl.finished built) 0))=Some (SetTheory.axiom_formula (SetTheory.Dist p q)) /\
    SetTheory.derives (SetTheory.axiom_formula (SetTheory.Dist p q)) /\
    (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered (AxiomRefl.finished built) (length next) /\
    (length next<=length fs+S root*S root+5)%nat /\ AxiomStorage.logical_frame s (AxiomRefl.finished built).
Proof.
  intros Hmeta Hsip Harena Htopology Herror Hlookup Hother Hfalse Htag Hroot Hq Hfuel Hbound Hindices Hheight Hbudget.
  assert (Hrootword:word (Z.of_nat root)).
  { assert (Hlt:(root<length fs)%nat) by (apply nth_error_Some;congruence).
    apply Nat2Z.inj_lt in Hlt. unfold word,maximum. rewrite !Nat2Z.inj_add in Hbudget. lia. }
  assert (Hotherword:word (Z.of_nat other)).
  { assert (Hlt:(other<length fs)%nat) by (apply nth_error_Some;congruence).
    apply Nat2Z.inj_lt in Hlt. unfold word,maximum. rewrite !Nat2Z.inj_add in Hbudget. lia. }
  pose proof (AxiomK.clearing_storage s) as Hclear.
  pose proof (ArenaFrame.storage_arena s (AxiomRefl.cleared s) fs Hclear Harena) as Hclear_arena.
  pose proof (AxiomK.storage_topology s (AxiomRefl.cleared s) (length fs) Hclear Htopology) as Hclear_topology.
  assert (Hclear_meta:(31<length (memory (AxiomRefl.cleared s) arraydef_0__meta))%nat)
    by (unfold AxiomRefl.cleared;rewrite store_meta_length;exact Hmeta).
  assert (Hclear_sip:(0<length (memory (AxiomRefl.cleared s) arraydef_0__sipState))%nat)
    by (unfold AxiomRefl.cleared;rewrite store_meta_other by discriminate;exact Hsip).
  assert (Hclear_error:meta_value (AxiomRefl.cleared s) 8=0)
    by (unfold AxiomRefl.cleared;rewrite meta_store_other by lia;exact Herror).
  destruct (RenameMemoCallers.shift_checks bound 1 Hindices) as (Hshiftword & Hargword & Hindexroom).
  assert (Hroom:Z.of_nat (length fs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit).
  { unfold RenameMemoResourceBounds.doubling_limit. rewrite !Nat2Z.inj_add in Hbudget. lia. }
  destruct (RenameMemoRun.generated (AxiomRefl.cleared s) (fun _=>false) (AxiomDistRaw.rename_arguments (Z.of_nat root))
    fs p root 0 shift_mode 1 0 bound Hclear_meta Hclear_sip (RenameMemoClassEqual.arena_positive _ _ Hclear_arena)
    Hclear_error Hclear_arena Hclear_topology Hlookup Hfalse eq_refl eq_refl eq_refl eq_refl eq_refl Hfuel Hroom
    Hshiftword Hargword Hbound Hindexroom Hheight observations)
    as (rframe & rfs & count & Hrename & Hrarena & Hcache & Hrword & Hrmeaning & Hrsource & Hrerror & Hempty & Hrgrowth & Hrtopology).
  rewrite shift_result in Hrmeaning.
  pose proof (RenameMemoOutput.source_extension fs rfs Hrsource) as Hrprefix.
  assert (Hrp:nth_error rfs root=Some p) by (eapply InternReserve.lookup_preserved;eassumption).
  assert (Hrq:nth_error rfs other=Some q) by (eapply InternReserve.lookup_preserved;eassumption).
  assert (Hrep:FormulaCircuit.represents rfs [Z.of_nat root;Z.of_nat other;meta_value (machine rframe) 0]
    [p;q;SetTheory.shift p]).
  { constructor;[split;[exact Hrootword|now rewrite Nat2Z.id]|].
    constructor;[split;[exact Hotherword|now rewrite Nat2Z.id]|]. constructor;[split;assumption|constructor]. }
  assert (Hremaining:Z.of_nat (length rfs+length AxiomDistRaw.plan+reserve)<=9223372036854775807).
  { change (Z.of_nat (length rfs+5+reserve)<=9223372036854775807). lia. }
  destruct (FormulaCircuitProperties.complete AxiomDistRaw.plan (machine rframe) rfs
    [Z.of_nat root;Z.of_nat other;meta_value (machine rframe) 0] [p;q;SetTheory.shift p] (values p q) reserve observations
    Hrarena Hrtopology Hrerror Hrep fits (infer p q) Hremaining)
    as (built & next & ids & Htrace & Hbframe & Hbarena & Hberror & Hbrep & Hbprefix & Hbreserve & Hbtopology & Hbgrowth).
  assert (Hrun:execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations))).
  { apply (AxiomDistRaw.generated_helper s bs ns (machine rframe) built ids (Z.of_nat root) (Z.of_nat other) observations).
    - lia.
    - exact Htag.
    - exact Hroot.
    - exact Hq.
    - eapply AxiomSRefinement.source_reference;[exact Harena|exact Hrootword|now rewrite Nat2Z.id,Hlookup].
    - eapply AxiomSRefinement.source_reference;[exact Harena|exact Hotherword|now rewrite Nat2Z.id,Hother].
    - exact Hrename.
    - exact Htrace. }
  destruct (result observations (machine rframe) (Z.of_nat root) (Z.of_nat other)
    (meta_value (machine rframe) 0) built ids next p q Htrace Hbrep) as (Hbword & Hbmeaning & Hbderives).
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hbmeta.
  pose proof (proj1 (RenameMemoLengths.observed_lengths _ _ _ _ _ _ Hrename)) as Hrmeta.
  assert (Hbmeta13:(13<length (memory built arraydef_0__meta))%nat)
    by (rewrite Hbmeta,Hrmeta;unfold AxiomRefl.cleared;rewrite store_meta_length;lia).
  destruct (AxiomK.finishing_result built Hbmeta13) as (Hsuccess & Hfinalerror & Hfinalid).
  change (meta_value (AxiomRefl.finished built) 0=meta_value built 0) in Hfinalid.
  exists built,next. split;[exact Hrun|].
  split;[eapply ArenaFrame.storage_arena;[apply AxiomRefl.finished_storage|exact Hbarena]|].
  split;[exact Hsuccess|]. split;[unfold AxiomRefl.finished;rewrite !meta_store_other by lia;exact Hberror|].
  split;[now rewrite Hfinalid|]. split;[now rewrite Hfinalid|]. split;[exact Hbderives|].
  split;[eapply InternReserve.extends_trans;eassumption|]. split;[exact Hbreserve|].
  split;[eapply AxiomK.storage_topology;[apply AxiomRefl.finished_storage|exact Hbtopology]|].
  split;[change (length next<=length fs+S root*S root+5)%nat;change (length next<=length rfs+5)%nat in Hbgrowth;lia|].
  eapply AxiomStorage.generated_frame;exact Hrun.
Qed.
End AxiomDistRefinement.
