From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift ObservedLocal FormulaEncoding Representation FormulaTopology ArenaFrame
  Intern InternReserve InternGrowth InternLengths FormulaCircuit AxiomRefl AxiomK AxiomSRefinement AxiomStorage AxiomInstRaw
  RenameMemoRun RenameMemoBounds RenameMemoResourceBounds RenameMemoIndexBounds RenameMemoTransition RenameMemoCallers
  RenameMemoOutput RenameMemoLengths RenameMemoTopology RenameMemoClassEqual RenameStack.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module AxiomInstRefinement.
Local Opaque funcdef_0__intern funcdef_0__rename.
Import IndexExecution SipHashExecution ObservedLocal IndexSemantics.
Theorem generated_helper s bs ns quantified renamed built root arg observations :
  (13<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag=3 -> ns vardef_0__axiom_p=root -> ns vardef_0__axiom_q=arg -> root<meta_value s 1 ->
  execObserved (funcdef_0__intern (fun _=>false) (FormulaCircuit.arguments 4 root 0))
    (AxiomInstRaw.cleared s,observations)=Some (tt,(quantified,observations)) ->
  execObserved (funcdef_0__rename (fun _=>false) (AxiomInstRaw.rename_arguments root arg))
    (quantified,observations)=Some (tt,(renamed,observations)) ->
  execObserved (funcdef_0__intern (fun _=>false) (FormulaCircuit.arguments 3 (meta_value quantified 0) (meta_value renamed 0)))
    (renamed,observations)=Some (tt,(built,observations)) ->
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations)).
Proof.
  intros Hmeta Htag Hroot Harg Hbound Hall Hrename Hlast.
  pose proof (AxiomInstRaw.generated_body {|machine:=s;bools:=bs;nums:=ns|} quantified renamed built root arg observations
    Hmeta Htag Hroot Harg Hbound Hall Hrename Hlast) as Hbody.
  unfold funcdef_0__axiom. rewrite eliminate_correct. exact Hbody.
Qed.
Local Opaque funcdef_0__axiom.
Theorem generated_refines s bs ns fs p root arg bound reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs root=Some p -> nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__axiom_tag=3 -> ns vardef_0__axiom_p=Z.of_nat root -> ns vardef_0__axiom_q=Z.of_nat arg ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  RenameMemoIndexBounds.formula_bound bound p -> Z.of_nat bound+Z.of_nat arg<=maximum ->
  Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  Z.of_nat (length fs+S root*S root+2+reserve)<=9223372036854775807 ->
  exists final next index,
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (SetTheory.axiom_formula (SetTheory.Inst p arg)) /\
    SetTheory.derives (SetTheory.axiom_formula (SetTheory.Inst p arg)) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ meta_value final 13=1 /\
    AxiomStorage.logical_frame s final /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered final (length next) /\ (length next<=length fs+S root*S root+2)%nat.
Proof.
  intros Hmeta Hsip Harena Htopology Herror Hlookup Hfalse Htag Hroot Harg Hfuel Hbound Hindices Hheight Hbudget.
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
  destruct (RenameMemoRun.generated quantified (fun _=>false) (AxiomInstRaw.rename_arguments (Z.of_nat root) (Z.of_nat arg))
    qfs p root 0 instantiate_mode 0 arg bound Hqmeta32 Hqsipready (RenameMemoClassEqual.arena_positive _ _ Hqarena)
    Hqerror Hqarena Hqtopology Hlookup_q Hfalse_q eq_refl eq_refl eq_refl eq_refl eq_refl Hfuel Hrenroom
    Hzero Hargword Hbound Hindexroom Hheight observations)
    as (rframe & rfs & count & Hrename & Hrarena & Hcache & Hrword & Hrmeaning & Hrsource & Hrerror & Hempty & Hrgrowth & Hrtopology).
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
  exists (AxiomRefl.finished built),next,index. split;[exact Hrun|].
  split;[eapply ArenaFrame.storage_arena;[apply AxiomRefl.finished_storage|exact Hbarena]|].
  split;[now rewrite Hfinalid|]. split;[exact Hbword|]. split;[exact Hbmeaning|].
  split;[apply SetTheory.d_inst|]. split.
  - eapply InternReserve.extends_trans;[exact Hqprefix|]. eapply InternReserve.extends_trans;eassumption.
  - split;[unfold AxiomRefl.finished;rewrite !meta_store_other by lia;exact Hberror|].
    split;[exact Hsuccess|]. split;[eapply AxiomStorage.generated_frame;exact Hrun|].
    split;[exact Hbreserve|]. split;[eapply AxiomK.storage_topology;[apply AxiomRefl.finished_storage|exact Hbtopology]|]. lia.
Qed.
End AxiomInstRefinement.
