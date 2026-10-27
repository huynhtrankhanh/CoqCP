From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift ObservedLocal FormulaEncoding Representation FormulaTopology ArenaFrame Intern InternReserve InternGrowth InternLengths FormulaCircuit AxiomRefl AxiomK AxiomSRefinement AxiomStorage AxiomInstRaw RenameMemoRun RenameMemoBounds RenameMemoResourceBounds RenameMemoIndexBounds RenameMemoTransition RenameMemoCallers RenameMemoOutput RenameMemoLengths RenameMemoTopology RenameMemoClassEqual RenameStack FormulaCircuitProperties AxiomDistRaw AxiomSeparationCircuits AxiomSeparationRaw AxiomInstRefinement AxiomDistRefinement AxiomSeparationRefinement SchemaEvaluationIndexBounds SchemaEvaluationIndexCircuit SchemaEvaluationIndexCircuitTrace SchemaEvaluationIndexAxiomCircuits RenameMemoIndexRun RenameMemoInput.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaEvaluationIndexAxiomRenaming.
Import IndexExecution SipHashExecution ObservedLocal IndexSemantics SchemaEvaluationIndexAxiomCircuits.
Module Instantiation.
Import AxiomInstRefinement.
Theorem generated_refines s bs ns fs p root arg bound reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs root=Some p -> nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__axiom_tag=3 -> ns vardef_0__axiom_p=Z.of_nat root -> ns vardef_0__axiom_q=Z.of_nat arg ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  RenameMemoIndexBounds.formula_bound bound p -> Z.of_nat bound+Z.of_nat arg<=maximum ->
  Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  Z.of_nat (length fs+S root*S root+2+reserve)<=9223372036854775807 ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  exists final next index, SchemaEvaluationIndexBounds.raw_arena final (length next) (bound+arg) /\
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (SetTheory.axiom_formula (SetTheory.Inst p arg)) /\
    SetTheory.derives (SetTheory.axiom_formula (SetTheory.Inst p arg)) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ meta_value final 13=1 /\
    AxiomStorage.logical_frame s final /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered final (length next) /\ (length next<=length fs+S root*S root+2)%nat.
Proof.
  intros Hmeta Hsip Harena Htopology Herror Hlookup Hfalse Htag Hroot Harg Hfuel Hbound Hindices Hheight Hbudget HrawInitial.
  assert (Hrootword:word (Z.of_nat root)).
  { assert (Hlt:(root<length fs)%nat) by (apply nth_error_Some;congruence).
    apply Nat2Z.inj_lt in Hlt. unfold word,maximum. rewrite !Nat2Z.inj_add in Hbudget. lia. }
  assert (Hclear_arena:NativeRepresentation.canonical_arena (AxiomInstRaw.cleared s) fs).
  { apply (ArenaFrame.storage_arena s);[apply AxiomK.clearing_storage|exact Harena]. }
  assert (Hclear_error:meta_value (AxiomInstRaw.cleared s) 8=0).
  { unfold AxiomInstRaw.cleared. rewrite meta_store_other by lia. exact Herror. }
  assert (Hnormal:FormulaEncoding.normal (4,Z.of_nat root,0)) by
    (right;right;split;[reflexivity|];split;[exact Hrootword|reflexivity]).
  assert (Hdecode:FormulaEncoding.decode fs (4,Z.of_nat root,0)=Some (SetTheory.all p)).
  { cbn [FormulaEncoding.decode]. now rewrite Nat2Z.id,Hlookup. }
  assert (Hfirstbudget:Z.of_nat (length fs+S (S root*S root+1+reserve))<=9223372036854775807).
  { replace (length fs+S (S root*S root+1+reserve))%nat with (length fs+S root*S root+2+reserve)%nat by lia. exact Hbudget. }
  destruct (InternReserve.generated_refines (AxiomInstRaw.cleared s) (fun _=>false) (FormulaCircuit.arguments 4 (Z.of_nat root) 0)
    fs (SetTheory.all p) (S root*S root+1+reserve) observations Hclear_arena Hclear_error Hfirstbudget Hnormal Hdecode)
    as (quantified & qfs & qid & Hall & Hqframe & Hqarena & Hqerror & Hqid & Hqidword & Hqmeaning & Hqprefix & Hqreserve).
  pose proof (InternLengths.observed_lengths _ _ _ _ _ _ Hall) as [Hqmeta Hqsip].
  assert (Hqmeta32:(31<length (memory quantified arraydef_0__meta))%nat)
    by (rewrite Hqmeta;unfold AxiomInstRaw.cleared;rewrite store_meta_length;exact Hmeta).
  assert (Hqsipready:(0<length (memory quantified arraydef_0__sipState))%nat)
    by (rewrite Hqsip;unfold AxiomInstRaw.cleared;rewrite store_meta_other by discriminate;exact Hsip).
  assert (Hplain_all:exec (funcdef_0__intern (fun _=>false) (FormulaCircuit.arguments 4 (Z.of_nat root) 0))
    (AxiomInstRaw.cleared s)=Some (tt,quantified)).
  { pose proof (f_equal (fun response=>option_map (fun r=>(fst r,fst (snd r))) response) Hall) as Hplain.
    rewrite execObserved_erases in Hplain. exact Hplain. }
  assert (Hcapacity:Z.of_nat (length fs)<=9223372036854775807) by (rewrite !Nat2Z.inj_add in Hbudget;lia).
  pose proof (InternGrowth.at_most_one _ _ _ _ fs qfs Hclear_arena Hclear_error Hcapacity Hplain_all Hqarena) as Hqgrowth.
  pose proof (AxiomK.storage_topology s (AxiomInstRaw.cleared s) (length fs) (AxiomK.clearing_storage s) Htopology) as Hclear_topology.
  pose proof (RenameMemoTopology.preserves _ _ fs qfs Hclear_arena Hqarena Hqprefix Hqgrowth Hclear_topology) as Hqtopology.
  assert (Hlookup_q:nth_error qfs root=Some p) by (eapply InternReserve.lookup_preserved;eassumption).
  assert (Hfalse_q:nth_error qfs 0=Some SetTheory.falsity) by (eapply InternReserve.lookup_preserved;eassumption).
  destruct (RenameMemoCallers.instantiate_checks bound arg Hindices) as (Hzero & Hargword & Hindexroom).
  assert (Hrenroom:Z.of_nat (length qfs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit).
  { rewrite !Nat2Z.inj_add in Hqreserve. unfold RenameMemoResourceBounds.doubling_limit. lia. }
  assert (HquantifiedRaw:SchemaEvaluationIndexBounds.raw_arena quantified (length qfs) bound).
  { eapply SchemaEvaluationIndexBounds.observed_intern;[exact Hclear_arena|exact Hclear_error|exact Hcapacity| | |exact Hall|exact Hqarena].
    - exact (storage_raw s (AxiomInstRaw.cleared s) (length fs) bound (AxiomK.clearing_storage s) HrawInitial).
    - change (RenameMemoInput.raw_bound bound (4,Z.of_nat root,0)). unfold RenameMemoInput.raw_bound;intros [H|H];discriminate. }
  destruct (RenameMemoIndexRun.generated_bounded quantified (fun _=>false) (AxiomInstRaw.rename_arguments (Z.of_nat root) (Z.of_nat arg))
    qfs p root 0 instantiate_mode 0 arg bound Hqmeta32 Hqsipready (RenameMemoClassEqual.arena_positive _ _ Hqarena)
    Hqerror Hqarena Hqtopology Hlookup_q Hfalse_q eq_refl eq_refl eq_refl eq_refl eq_refl Hfuel Hrenroom
    Hzero Hargword HquantifiedRaw Hindexroom Hheight observations)
    as (rframe & rfs & count & Hrename & Hrarena & Hcache & Hrword & Hrmeaning & Hrsource & Hrerror & Hempty & Hrgrowth & Hrtopology & Hrraw).
  pose proof (RenameMemoOutput.source_extension qfs rfs Hrsource) as Hrprefix.
  assert (Hqmeaning_r:nth_error rfs qid=Some (SetTheory.all p)) by (eapply InternReserve.lookup_preserved;eassumption).
  assert (Hrnormal:FormulaEncoding.normal (3,meta_value quantified 0,meta_value (machine rframe) 0)).
  { right;left. split;[right;right;reflexivity|]. split;[now rewrite Hqid|exact Hrword]. }
  assert (Hrdecode:FormulaEncoding.decode rfs (3,meta_value quantified 0,meta_value (machine rframe) 0)=
    Some (SetTheory.axiom_formula (SetTheory.Inst p arg))).
  { cbn [FormulaEncoding.decode]. rewrite Hqid,Nat2Z.id,Hqmeaning_r,Hrmeaning. reflexivity. }
  assert (Hlastbudget:Z.of_nat (length rfs+S reserve)<=9223372036854775807).
  { rewrite !Nat2Z.inj_add in Hqreserve. lia. }
  destruct (InternReserve.generated_refines (machine rframe) (fun _=>false)
    (FormulaCircuit.arguments 3 (meta_value quantified 0) (meta_value (machine rframe) 0))
    rfs (SetTheory.axiom_formula (SetTheory.Inst p arg)) reserve observations Hrarena Hrerror Hlastbudget Hrnormal Hrdecode)
    as (built & next & index & Hlast & Hbframe & Hbarena & Hberror & Hbindex & Hbword & Hbmeaning & Hbprefix & Hbreserve).
  assert (Hrun:execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations))).
  { apply (generated_helper s bs ns quantified (machine rframe) built (Z.of_nat root) (Z.of_nat arg) observations).
    - lia.
    - exact Htag.
    - exact Hroot.
    - exact Harg.
    - eapply AxiomSRefinement.source_reference;[exact Harena|exact Hrootword|now rewrite Nat2Z.id,Hlookup].
    - exact Hall.
    - exact Hrename.
    - exact Hlast. }
  pose proof (InternLengths.observed_lengths _ _ _ _ _ _ Hlast) as [Hbmeta Hbsip].
  pose proof (RenameMemoLengths.observed_lengths _ _ _ _ _ _ Hrename) as [Hrmeta Hrsip].
  assert (Hbmeta13:(13<length (memory built arraydef_0__meta))%nat) by (rewrite Hbmeta,Hrmeta;lia).
  pose proof (AxiomK.finishing_result built Hbmeta13) as (Hsuccess & Hfinalerror & Hfinalid).
  change (meta_value (AxiomRefl.finished built) 0=meta_value built 0) in Hfinalid.
  assert (Hlastplain:exec (funcdef_0__intern (fun _=>false)
    (FormulaCircuit.arguments 3 (meta_value quantified 0) (meta_value (machine rframe) 0))) (machine rframe)=Some (tt,built)).
  { pose proof (f_equal (fun response=>option_map (fun r=>(fst r,fst (snd r))) response) Hlast) as Hplain.
    rewrite execObserved_erases in Hplain. exact Hplain. }
  assert (Hrcapacity:Z.of_nat (length rfs)<=9223372036854775807) by (rewrite Nat2Z.inj_add in Hlastbudget;lia).
  pose proof (InternGrowth.at_most_one _ _ _ _ rfs next Hrarena Hrerror Hrcapacity Hlastplain Hbarena) as Hbgrowth.
  pose proof (RenameMemoTopology.preserves _ _ rfs next Hrarena Hbarena Hbprefix Hbgrowth Hrtopology) as Hbtopology.
  assert (HrawBuilt:SchemaEvaluationIndexBounds.raw_arena built (length next) (bound+arg)).
  { eapply SchemaEvaluationIndexBounds.observed_intern;[exact Hrarena|exact Hrerror|exact Hrcapacity|exact Hrraw| |exact Hlast|exact Hbarena].
    change (RenameMemoInput.raw_bound (bound+arg) (3,meta_value quantified 0,meta_value (machine rframe) 0)).
    unfold RenameMemoInput.raw_bound;intros [H|H];discriminate. }
  exists (AxiomRefl.finished built),next,index. split;[exact (storage_raw built (AxiomRefl.finished built) (length next) _ (AxiomRefl.finished_storage built) HrawBuilt)|]. split;[exact Hrun|].
  split;[eapply ArenaFrame.storage_arena;[apply AxiomRefl.finished_storage|exact Hbarena]|].
  split;[now rewrite Hfinalid|]. split;[exact Hbword|]. split;[exact Hbmeaning|].
  split;[apply SetTheory.d_inst|]. split.
  - eapply InternReserve.extends_trans;[exact Hqprefix|]. eapply InternReserve.extends_trans;eassumption.
  - split;[unfold AxiomRefl.finished;rewrite !meta_store_other by lia;exact Hberror|].
    split;[exact Hsuccess|]. split;[eapply AxiomStorage.generated_frame;exact Hrun|].
    split;[exact Hbreserve|]. split;[eapply AxiomK.storage_topology;[apply AxiomRefl.finished_storage|exact Hbtopology]|]. lia.
Qed.
End Instantiation.
Module Distribution.
Import AxiomDistRefinement.
Theorem generated_refines s bs ns fs p q root other bound reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs root=Some p -> nth_error fs other=Some q -> nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__axiom_tag=4 -> ns vardef_0__axiom_p=Z.of_nat root -> ns vardef_0__axiom_q=Z.of_nat other ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  RenameMemoIndexBounds.formula_bound bound p -> Z.of_nat bound+1<=maximum ->
  Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  Z.of_nat (length fs+S root*S root+5+reserve)<=9223372036854775807 ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  exists built next, SchemaEvaluationIndexBounds.raw_arena (AxiomRefl.finished built) (length next) (bound+1) /\
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
  intros Hmeta Hsip Harena Htopology Herror Hlookup Hother Hfalse Htag Hroot Hq Hfuel Hbound Hindices Hheight Hbudget HrawInitial.
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
  destruct (RenameMemoIndexRun.generated_bounded (AxiomRefl.cleared s) (fun _=>false) (AxiomDistRaw.rename_arguments (Z.of_nat root))
    fs p root 0 shift_mode 1 0 bound Hclear_meta Hclear_sip (RenameMemoClassEqual.arena_positive _ _ Hclear_arena)
    Hclear_error Hclear_arena Hclear_topology Hlookup Hfalse eq_refl eq_refl eq_refl eq_refl eq_refl Hfuel Hroom
    Hshiftword Hargword (storage_raw s (AxiomRefl.cleared s) (length fs) bound (AxiomK.clearing_storage s) HrawInitial) Hindexroom Hheight observations)
    as (rframe & rfs & count & Hrename & Hrarena & Hcache & Hrword & Hrmeaning & Hrsource & Hrerror & Hempty & Hrgrowth & Hrtopology & Hrraw).
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
  assert (HrawBuilt:SchemaEvaluationIndexBounds.raw_arena built (length next) (bound+1)).
  { eapply SchemaEvaluationIndexCircuitTrace.trace_arena;[exact Htrace|exact Hrarena|exact Hrerror|exact Hrraw| | |exact Hbarena].
    - repeat rewrite Nat2Z.inj_add in Hremaining;lia.
    - unfold AxiomDistRaw.plan. repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];lia. }
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
  exists built,next. split;[exact (storage_raw built (AxiomRefl.finished built) (length next) _ (AxiomRefl.finished_storage built) HrawBuilt)|]. split;[exact Hrun|].
  split;[eapply ArenaFrame.storage_arena;[apply AxiomRefl.finished_storage|exact Hbarena]|].
  split;[exact Hsuccess|]. split;[unfold AxiomRefl.finished;rewrite !meta_store_other by lia;exact Hberror|].
  split;[now rewrite Hfinalid|]. split;[now rewrite Hfinalid|]. split;[exact Hbderives|].
  split;[eapply InternReserve.extends_trans;eassumption|]. split;[exact Hbreserve|].
  split;[eapply AxiomK.storage_topology;[apply AxiomRefl.finished_storage|exact Hbtopology]|].
  split;[change (length next<=length fs+S root*S root+5)%nat;change (length next<=length rfs+5)%nat in Hbgrowth;lia|].
  eapply AxiomStorage.generated_frame;exact Hrun.
Qed.
End Distribution.
Module Separation.
Import AxiomSeparationRefinement.
Theorem generated_refines s bs ns fs p root bound reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs root=Some p -> nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__axiom_tag=15 -> ns vardef_0__axiom_p=Z.of_nat root ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  RenameMemoIndexBounds.formula_bound bound p -> Z.of_nat bound+2<=maximum ->
  Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  Z.of_nat (length fs+S root*S root+14+reserve)<=9223372036854775807 ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  exists built next, SchemaEvaluationIndexBounds.raw_arena (AxiomRefl.finished built) (length next) (bound+2) /\
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
  intros Hmeta Hsip Harena Htopology Herror Hlookup Hfalse Htag Hroot Hfuel Hbound Hindices Hheight Hbudget HrawInitial.
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
  assert (HpreparedRaw:SchemaEvaluationIndexBounds.raw_arena prepared (length pfs) (bound+2)).
  { eapply SchemaEvaluationIndexCircuitTrace.trace_arena;[exact Hbefore|exact Hclear_arena|exact Hclear_error| | | |exact Hparena].
    - apply (SchemaEvaluationIndexBounds.raw_arena_mono (AxiomRefl.cleared s) (length fs) bound (bound+2) ltac:(lia)).
      exact (storage_raw s (AxiomRefl.cleared s) (length fs) bound (AxiomK.clearing_storage s) HrawInitial).
    - cbn [AxiomSeparationCircuits.before length] in *;repeat rewrite Nat2Z.inj_add in Hprebudget;lia.
    - unfold AxiomSeparationCircuits.before. repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];lia. }
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
  destruct (RenameMemoIndexRun.generated (bound+2)%nat prepared (fun _=>false) (AxiomSeparationRaw.rename_arguments (Z.of_nat root))
    pfs p root 0 separation_mode 0 0 bound Hpmeta32 Hpsipready (RenameMemoClassEqual.arena_positive _ _ Hparena)
    Hperror Hparena Hptopology Hplookup Hpfalse eq_refl eq_refl eq_refl eq_refl eq_refl Hfuel Hroom
    Hzeroword Hzeroword Hbound Hindexroom Hheight HpreparedRaw ltac:(cbn [RenameMemoIndexBounds.increment];lia) observations)
    as (rframe & rfs & count & Hrename & Hrarena & Hcache & Hrword & Hrmeaning & Hrsource & Hrerror & Hempty & Hrgrowth & Hrtopology & Hrraw).
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
  assert (HrawBuilt:SchemaEvaluationIndexBounds.raw_arena built (length next) (bound+2)).
  { eapply SchemaEvaluationIndexCircuitTrace.trace_arena;[exact Htrace|exact Hrarena|exact Hrerror|exact Hrraw| | |exact Hbarena].
    - repeat rewrite Nat2Z.inj_add in Hremaining;lia.
    - unfold AxiomSeparationCircuits.after. repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];lia. }
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
  exists built,next. split;[exact (storage_raw built (AxiomRefl.finished built) (length next) _ (AxiomRefl.finished_storage built) HrawBuilt)|]. split;[exact Hrun|].
  split;[eapply ArenaFrame.storage_arena;[apply AxiomRefl.finished_storage|exact Hbarena]|].
  split;[exact Hsuccess|]. split;[unfold AxiomRefl.finished;rewrite !meta_store_other by lia;exact Hberror|].
  split;[now rewrite Hfinalid|]. split;[now rewrite Hfinalid|]. split;[exact Hbderives|].
  split;[eapply InternReserve.extends_trans;[exact Hpprefix|];eapply InternReserve.extends_trans;eassumption|].
  split;[exact Hbreserve|].
  split;[eapply AxiomK.storage_topology;[apply AxiomRefl.finished_storage|exact Hbtopology]|].
  split;[change (length next<=length rfs+12)%nat in Hbgrowth;change (length pfs<=length fs+2)%nat in Hpgrowth;lia|].
  eapply AxiomStorage.generated_frame;exact Hrun.
Qed.
End Separation.
End SchemaEvaluationIndexAxiomRenaming.
