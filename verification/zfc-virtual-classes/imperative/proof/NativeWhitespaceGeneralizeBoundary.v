From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeStateFrames NativeProtocolLift NativeTheoremBoundary
 ReadOne TokenByte InternBounded Intern InternGrowth Observation FormulaEncoding Representation ArenaFrame ClassStorage
 HistoryRefinement HistoryLookup HistoryStorage LogicalHistory SemanticFrames Generalize GeneralizeRefinement GeneralizeTotal
 CommandGeneralize ReplyOK ReplyNO NativeArgumentReads.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceGeneralizeBoundary.
Import IndexExecution SipHashExecution NativeTheoremBoundary GeneralizeRefinement.
Lemma flow_weaken small large before after reply tail : (small<=large)%nat ->
 flow small before after reply tail -> flow large before after reply tail.
Proof.
 intros Hle (Hin & Hout & Herror & Hstop & Hformula & Hclasses & Hhistory).
 apply Nat2Z.inj_le in Hle. unfold flow. split;[exact Hin|]. split;[exact Hout|]. split;[exact Herror|].
 split;[exact Hstop|]. split;[lia|]. split;assumption.
Qed.
Lemma intern_history_flow before parsed built fs next count fid tail :
 frame before parsed tail -> InternExecution.logical_frame parsed built ->
 NativeRepresentation.canonical_arena parsed fs -> NativeRepresentation.canonical_arena built next ->
 (length next<=S (length fs))%nat -> meta_value built 8=0 ->
 (3<length (memory built arraydef_0__meta))%nat -> meta_value built 3=Z.of_nat count ->
 flow 1 before (HistoryStorage.result built count fid) (Protocol.OK count) tail.
Proof.
 intros [Hin [Hout Hparse]] [Harrays [Hcells [Hinput Houtput]]] Harena Hnext Hgrowth Herror Hmeta Hcount.
 assert (H1:meta_value parsed 1=meta_value before 1) by (apply Hparse;lia).
 assert (H2:meta_value built 2=meta_value before 2).
 { etransitivity;[apply Hcells;lia|apply Hparse;lia]. }
 assert (H3:meta_value built 3=meta_value before 3).
 { etransitivity;[apply Hcells;lia|apply Hparse;lia]. }
 assert (H9:meta_value built 9=meta_value before 9).
 { etransitivity;[apply Hcells;lia|apply Hparse;lia]. }
 pose proof (proj1 (proj2 (proj1 Harena))) as HbeforeCount.
 pose proof (proj1 (proj2 (proj1 Hnext))) as HnextCount.
 change (meta_value parsed 1=Z.of_nat (length fs)) in HbeforeCount.
 change (meta_value built 1=Z.of_nat (length next)) in HnextCount.
 assert (Hformula:meta_value built 1<=meta_value before 1+1).
 { apply Nat2Z.inj_le in Hgrowth. rewrite Nat2Z.inj_succ in Hgrowth. lia. }
 unfold flow. split.
 - change (stdin (ReplyOKExecution.reply_state (HistoryStorage.written built count fid) count)=tail).
   exact (eq_trans (ReplyOKExecution.reply_input (HistoryStorage.written built count fid) count) (eq_trans Hinput Hin)).
 - split.
   + change (stdout (ReplyOKExecution.reply_state (HistoryStorage.written built count fid) count)=stdout before++Protocol.reply_bytes (Protocol.OK count)).
     exact (eq_trans (ReplyOKExecution.reply_output (HistoryStorage.written built count fid) count)
       (f_equal (fun bytes=>bytes++Protocol.reply_bytes (Protocol.OK count)) (eq_trans Houtput Hout))).
   + split;[rewrite HistoryStorage.result_meta_other by lia;exact Herror|].
     split;[rewrite HistoryStorage.result_meta_other by lia;exact H9|].
     split;[rewrite HistoryStorage.result_meta_other by lia;exact Hformula|].
     split;[rewrite HistoryStorage.result_meta_other by lia;exact H2|].
     rewrite HistoryStorage.result_count by exact Hmeta. rewrite Nat2Z.inj_succ;lia.
Qed.
Theorem generated_protocol s logical bs ns value p first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> Z.of_nat value <= maximum ->
  Protocol.theorem_at logical value = Some p ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = 51 :: first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 13 [value] []) (Protocol.OK (length (Protocol.history logical))) (logical_after logical fs index) /\
    NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs (Protocol.classes logical) /\
    HistoryRefinement.represents final (logical_after logical fs index) /\ flow 1 s final (Protocol.OK (length (Protocol.history logical))) tail.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hhistorybound Hvalue Hlookup Harena Hclasses Hhistory Hsep1 Hsep2 Hspaces Hin.
  assert (Hopword : Z.of_nat 13 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReads.generated_reads s (fun _ => false) (fun _ => 0) 13 49 [51] value first_separator spaces last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hvalue Hsep1 Hsep2 Hspaces Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  set (arg := argument_state s value last_separator tail).
  change (17 < length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadOne.argument_storage s 49 [51] value last_separator tail Hmeta) Harena). }
  assert (Harg_history : HistoryRefinement.represents arg logical) by now apply argument_history.
  destruct (HistoryLookup.theorem_lookup arg logical value p Harg_history Hlookup) as [fid [Hentry [Hformula [Hnative Hnth]]]].
  destruct (HistoryLookup.formula_reference arg _ fid p Harg_arena Hformula) as [_ [Hfidword _]].
  assert (Hreference : Z.of_nat value < meta_value arg 3).
  { rewrite (proj1 Harg_history). assert (value < length (Protocol.history logical))%nat by (apply nth_error_Some; congruence). lia. }
  assert (Hnormal : FormulaEncoding.normal (4,Z.of_nat fid,0)) by (right; right; split; [reflexivity|]; split; [exact Hfidword|reflexivity]).
  assert (Hdecode : FormulaEncoding.decode (Protocol.formulas logical) (4,Z.of_nat fid,0) = Some (SetTheory.all p)).
  { change (option_map SetTheory.all (nth_error (Protocol.formulas logical) (Z.to_nat (Z.of_nat fid))) = Some (SetTheory.all p)).
    unfold Protocol.formula_at in Hformula. now rewrite Nat2Z.id, Hformula. }
  destruct (InternBounded.generated_refines arg (fun _ => false) (GeneralizeExecution.arguments (Z.of_nat fid))
    (Protocol.formulas logical) (SetTheory.all p) Harg_arena Hargerror Hbound Hnormal Hdecode)
    as [internstate [fs [index [Hintern [Hframe [Hflag [Hresult [Hword [Hnext [Hformula_result Hextends]]]]]]]]]].
  assert (Hobserved : execObserved (funcdef_0__intern (fun _ => false) (GeneralizeExecution.arguments (Z.of_nat fid)))
    (arg,observations) = Some (tt,(internstate,observations))).
  { apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern]. }
  pose proof (InternGrowth.at_most_one arg internstate (fun _=>false) (GeneralizeExecution.arguments (Z.of_nat fid))
    (Protocol.formulas logical) fs Harg_arena Hargerror Hbound Hintern Hnext) as Hgrowth.
  pose proof Hframe as [Harrays [Hcells [Hintern_input Hintern_output]]].
  assert (Hpostmeta : (17 < length (memory internstate arraydef_0__meta))%nat).
  { pose proof (proj1 (proj1 (proj1 Hnext))) as Hcapacity. lia. }
  assert (Hpostbuffer : (20 <= length (memory internstate arraydef_0__printBuffer))%nat).
  { rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). exact Hargbuffer. }
  assert (Hintern_history : HistoryRefinement.represents internstate logical) by (eapply SemanticFrames.intern_history; eassumption).
  set (final := HistoryStorage.result internstate (length (Protocol.history logical)) (Z.of_nat index)).
  pose proof (GeneralizeExecution.generated_generalize arg (fun _ => false) (CommandGeneralizeExecution.arguments (Z.of_nat value)) internstate
    (length (Protocol.history logical)) value (Z.of_nat fid) index observations Hnative Hnth eq_refl Hobserved
    ltac:(lia) Hpostbuffer Hflag (proj1 Hintern_history) Hhistorybound Hresult) as Hgen.
  assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (unfold final; rewrite HistoryStorage.result_meta_length; lia).
  assert (Hfinalerror : meta_value final 8 = 0) by (unfold final; rewrite HistoryStorage.result_meta_other by lia; exact Hflag).
  pose proof (CommandGeneralizeExecution.generated_command s bs ns _ arg final (Z.of_nat value) observations _
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference Hgen Hfinalmeta Hfinalerror) as Hrun.
  rewrite Hintern_input, Hintern_output, Hinput, Houtput in Hrun.
  exists final,index,fs. split; [exact Hrun|].
  assert (Hunique : NoDup fs) by (now apply (SemanticFrames.arena_NoDup internstate)).
  split.
  - eapply Protocol.step_accept with (t := logical_after logical fs index).
    + unfold logical_after, logical_before_append. cbn [Protocol.with_history Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
      eapply (Protocol.accept_proof logical (Protocol.Req 13 [value] []) (SetTheory.all p) fs (Protocol.classes logical) index).
      * now apply (Protocol.req_gen logical value p).
      * split; [exact Hextends|]. split; [exact Hunique|]. split; [exact Hformula_result|]. exists []; now rewrite app_nil_r.
    + now apply HistoryRefinement.retained_refl.
  - split; [now apply HistoryStorage.result_arena|]. split.
    + apply HistoryStorage.result_classes. destruct Hextends as [extra ->].
      apply (SemanticFrames.intern_classes arg internstate); [exact Hframe|]. now apply argument_classes.
    + split;[exact (HistoryStorage.append_represents internstate (logical_before_append logical fs) index ltac:(lia) Hintern_history)|].
      exact (intern_history_flow s arg internstate (Protocol.formulas logical) fs (length (Protocol.history logical)) (Z.of_nat index) tail
       (read_one_frame s 49 [51] value last_separator tail Hmeta Hinput Houtput) Hframe Harg_arena Hnext Hgrowth Hflag ltac:(lia) (proj1 Hintern_history)).
Qed.
Theorem generated_rejected_protocol s logical bs ns value first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> nth_error (Protocol.history logical) value = None ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = 51 :: first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 13 [value] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\ HistoryRefinement.represents final logical /\ flow 1 s final Protocol.NO tail.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Harena Hclasses Hhistory Hsep1 Hsep2 Hspaces Hin.
  assert (Hopword : Z.of_nat 13 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReads.generated_reads s (fun _ => false) (fun _ => 0) 13 49 [51] value first_separator spaces last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hvalue Hsep1 Hsep2 Hspaces Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  set (arg := argument_state s value last_separator tail).
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_history : HistoryRefinement.represents arg logical) by now apply argument_history.
  assert (Hreference : meta_value arg 3 <= Z.of_nat value).
  { rewrite (proj1 Harg_history). apply nth_error_None in Hlookup. lia. }
  pose proof (CommandGeneralizeExecution.generated_rejected_command s bs ns _ arg (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference) as Hrun.
  rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state arg). split; [exact Hrun|].
  split; [apply GeneralizeTotal.logical_rejected; [exact Hlookup|now apply (SemanticFrames.arena_NoDup s)]|].
  split.
  - eapply ArenaFrame.storage_arena; [|exact Harena]. eapply ArenaFrame.storage_trans;
      [exact (ReadOne.argument_storage s 49 [51] value last_separator tail Hmeta)|apply ArenaFrame.storage_output].
  - split;[now apply argument_classes|]. split;[exact Harg_history|].
    apply (flow_weaken 0 1 s _ Protocol.NO tail ltac:(lia)).
    apply no_flow;[exact (read_one_frame s 49 [51] value last_separator tail Hmeta Hinput Houtput)|exact Herror].
Qed.
Theorem generated_total_protocol s logical bs ns value first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> Z.of_nat value <= maximum -> LogicalHistory.valid logical ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = 51 :: first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 13 [value] []) reply next /\
    NativeRepresentation.canonical_arena final (Protocol.formulas next) /\
    ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) /\ HistoryRefinement.represents final next /\ LogicalHistory.valid next /\ flow 1 s final reply tail.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hhistorybound Hvalue Hvalid Harena Hclasses Hhistory Hsep1 Hsep2 Hspaces Hin.
  destruct (nth_error (Protocol.history logical) value) as [fid|] eqn:Hlookup.
  - destruct (Hvalid value fid Hlookup) as [p Hp].
    assert (Htheorem : Protocol.theorem_at logical value = Some p) by (unfold Protocol.theorem_at; rewrite Hlookup; exact Hp).
    destruct (generated_protocol s logical bs ns value p first_separator spaces last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hbound Hhistorybound Hvalue Htheorem Harena Hclasses Hhistory Hsep1 Hsep2 Hspaces Hin)
      as [final [index [fs [Hrun [Hstep [Ha [Hc [Hh Hflow]]]]]]]].
    exists final,(Protocol.OK (length (Protocol.history logical))),(logical_after logical fs index).
    split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split; [exact Hc|]. split; [exact Hh|].
    split;[eapply LogicalHistory.step_valid;eassumption|exact Hflow].
  - destruct (generated_rejected_protocol s logical bs ns value first_separator spaces last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Harena Hclasses Hhistory Hsep1 Hsep2 Hspaces Hin)
      as [final [Hrun [Hstep [Ha [Hc [Hh Hflow]]]]]].
    exists final,Protocol.NO,logical. split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split;[exact Hc|]. split;[exact Hh|]. split;assumption.
Qed.
Theorem generated_generalize s logical bs ns value first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> Z.of_nat value <= maximum -> LogicalHistory.valid logical ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = 51 :: first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 13 [value] []) reply next /\
    NativeState.represents final next /\ LogicalHistory.valid next /\ (Guarantees.safe logical -> Guarantees.safe next) /\ boundary 1 s logical final reply next tail.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hbound HhistoryBound Hvalue Hvalid Hstate Hfirst Hlast Hspaces Hinput.
 destruct (generated_total_protocol s logical bs ns value first_separator spaces last_separator tail observations
   Hmeta Htoken Hprint Hpending Herror Hbound HhistoryBound Hvalue Hvalid (NativeState.formula_representation _ _ Hstate)
   (NativeState.class_representation _ _ Hstate) (NativeState.history_representation _ _ Hstate) Hfirst Hlast Hspaces Hinput)
 as (final & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory & HnextValid & Hflow).
 assert (Hnext:NativeState.represents final next).
 { exact (NativeProtocolLift.canonical 13 49 [51] s bs ns first_separator (spaces++decimalBytes value++last_separator::tail)
   observations final _ logical (Protocol.Req 13 [value] []) reply next ltac:(lia) ltac:(lia)
   ltac:(unfold NativeStateFrames.nonbinding;repeat split;lia) eq_refl eq_refl Hmeta Htoken Hpending Herror Hfirst Hinput
   Hrun Hstate Hstep Harena Hclasses Hhistory). }
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hnext|]. split;[exact HnextValid|]. split.
 - intro Hsafe. eapply Guarantees.step_safe;eassumption.
 - exact (boundary_from_flow 1 s final bs ns logical next reply tail observations _ Hstate Hnext Htoken Hprint Hrun Hflow).
Qed.
End NativeWhitespaceGeneralizeBoundary.
