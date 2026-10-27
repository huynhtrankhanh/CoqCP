From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeTheoremCommands NativeCommandBoundary NativeCommandLengths
 ReadOne ReadTwo ParsedState TokenByte FormulaEncoding Representation ArenaFrame FormulaProjection ClassStorage HistoryRefinement
 HistoryLookup HistoryStorage LogicalHistory SemanticFrames CommandInspect CommandRestate CommandRestateReject
 InspectRefinement ModusPonens ModusPonensRefinement ModusPonensRejection CommandMP CommandMPReject ReplyOK ReplyNO NativeProtocolLift NativeStateFrames.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeTheoremBoundary.
Import IndexExecution SipHashExecution.
Definition frame before parsed tail := stdin parsed=tail /\ stdout parsed=stdout before /\
 forall cell,cell<>6%nat -> cell<>11%nat -> cell<>14%nat -> cell<>15%nat -> cell<>17%nat ->
 meta_value parsed cell=meta_value before cell.
Definition flow allowance before after reply tail := stdin after=tail /\
 stdout after=stdout before++Protocol.reply_bytes reply /\ meta_value after 8=0 /\ meta_value after 9=meta_value before 9 /\
 meta_value after 1<=meta_value before 1+Z.of_nat allowance /\
 meta_value after 2=meta_value before 2 /\ meta_value after 3<=meta_value before 3+1.
Definition boundary allowance before logical after reply next tail := NativeCommandBoundary.io before after reply tail /\
 (length (Protocol.formulas next)<=length (Protocol.formulas logical)+allowance)%nat /\
 length (Protocol.classes next)=length (Protocol.classes logical) /\
 (length (Protocol.history next)<=S (length (Protocol.history logical)))%nat.
Lemma read_one_frame native ch chars value sep tail :
 (17<length (memory native arraydef_0__meta))%nat ->
 stdin (ReadOne.argument_state native ch chars value sep tail)=tail ->
 stdout (ReadOne.argument_state native ch chars value sep tail)=stdout native ->
 frame native (ReadOne.argument_state native ch chars value sep tail) tail.
Proof. intros Hmeta Hin Hout. split;[exact Hin|]. split;[exact Hout|]. intros;apply ReadOne.argument_meta_other;assumption. Qed.
Lemma read_two_frame native ch chars a middle b last tail :
 (17<length (memory native arraydef_0__meta))%nat ->
 stdin (ReadTwo.second_state native ch chars a middle b last tail)=tail ->
 stdout (ReadTwo.second_state native ch chars a middle b last tail)=stdout native ->
 frame native (ReadTwo.second_state native ch chars a middle b last tail) tail.
Proof. intros Hmeta Hin Hout. split;[exact Hin|]. split;[exact Hout|]. intros;apply ReadTwo.second_meta_other;assumption. Qed.
Lemma no_flow before parsed tail : frame before parsed tail -> meta_value before 8=0 ->
 flow 0 before (ReplyNOExecution.reply_state parsed) Protocol.NO tail.
Proof.
 intros [Hin [Hout Hcells]] Herror. unfold flow. split;[exact Hin|]. split.
 - change (stdout parsed++Protocol.reply_bytes Protocol.NO=stdout before++Protocol.reply_bytes Protocol.NO). exact (f_equal (fun bytes=>bytes++Protocol.reply_bytes Protocol.NO) Hout).
 - change (meta_value parsed 8=0 /\ meta_value parsed 9=meta_value before 9 /\
     meta_value parsed 1<=meta_value before 1+0 /\ meta_value parsed 2=meta_value before 2 /\
     meta_value parsed 3<=meta_value before 3+1).
   assert (H1:meta_value parsed 1=meta_value before 1) by (apply Hcells;lia).
   assert (H2:meta_value parsed 2=meta_value before 2) by (apply Hcells;lia).
   assert (H3:meta_value parsed 3=meta_value before 3) by (apply Hcells;lia).
   assert (H8:meta_value parsed 8=meta_value before 8) by (apply Hcells;lia).
   assert (H9:meta_value parsed 9=meta_value before 9) by (apply Hcells;lia).
   repeat split;congruence || lia.
Qed.
Lemma ok_flow before parsed value tail : frame before parsed tail -> meta_value before 8=0 ->
 flow 0 before (ReplyOKExecution.reply_state parsed value) (Protocol.OK value) tail.
Proof.
 intros [Hin [Hout Hcells]] Herror. unfold flow. split.
 - rewrite ReplyOKExecution.reply_input;exact Hin.
 - split.
   + exact (eq_trans (ReplyOKExecution.reply_output parsed value) (f_equal (fun bytes=>bytes++Protocol.reply_bytes (Protocol.OK value)) Hout)).
   + assert (Hsame:forall cell,meta_value (ReplyOKExecution.reply_state parsed value) cell=meta_value parsed cell).
     { intro cell. unfold meta_value. rewrite ReplyOKExecution.reply_other by discriminate;reflexivity. }
     split;[rewrite Hsame,Hcells by lia;exact Herror|]. split;[rewrite Hsame;apply Hcells;lia|].
     split;[rewrite Hsame,Hcells by lia;cbn;lia|]. split;[rewrite Hsame;apply Hcells;lia|]. rewrite Hsame,Hcells by lia;lia.
Qed.
Lemma history_flow before parsed count fid tail :
 frame before parsed tail -> meta_value before 8=0 ->
 (3<length (memory parsed arraydef_0__meta))%nat -> meta_value parsed 3=Z.of_nat count ->
 flow 0 before (HistoryStorage.result parsed count fid) (Protocol.OK count) tail.
Proof.
 intros [Hin [Hout Hcells]] Herror Hmeta Hcount. unfold flow. split.
 - change (stdin (ReplyOKExecution.reply_state (HistoryStorage.written parsed count fid) count)=tail).
   exact (eq_trans (ReplyOKExecution.reply_input (HistoryStorage.written parsed count fid) count) Hin).
 - split.
   + change (stdout (ReplyOKExecution.reply_state (HistoryStorage.written parsed count fid) count)=stdout before++Protocol.reply_bytes (Protocol.OK count)).
     exact (eq_trans (ReplyOKExecution.reply_output (HistoryStorage.written parsed count fid) count)
       (f_equal (fun bytes=>bytes++Protocol.reply_bytes (Protocol.OK count)) Hout)).
   + split;[rewrite HistoryStorage.result_meta_other,Hcells by lia;exact Herror|].
     split;[rewrite HistoryStorage.result_meta_other by lia;apply Hcells;lia|].
     split;[rewrite HistoryStorage.result_meta_other,Hcells by lia;cbn;lia|].
     split;[rewrite HistoryStorage.result_meta_other by lia;apply Hcells;lia|].
     rewrite HistoryStorage.result_count by exact Hmeta. rewrite Hcells in Hcount by lia.
     rewrite Nat2Z.inj_succ;lia.
Qed.
Lemma boundary_from_flow allowance before after bs ns logical next reply tail observations trace :
 NativeState.represents before logical -> NativeState.represents after next ->
 (1024<=length (memory before arraydef_0__token))%nat -> (20<=length (memory before arraydef_0__printBuffer))%nat ->
 execObserved (funcdef_0__command bs ns) (before,observations)=Some(tt,(after,trace)) ->
 flow allowance before after reply tail -> boundary allowance before logical after reply next tail.
Proof.
 intros Hstate Hnext Htoken Hprint Hrun [Hin [Hout [Herror [Hstop [Hformulas [Hclasses Hhistory]]]]]].
 unfold boundary. split.
 - unfold NativeCommandBoundary.io. split;[exact Hin|]. split;[exact Hout|]. split.
   + rewrite (NativeCommandLengths.generated arraydef_0__token before bs ns after observations trace NativeCommandLengths.token_protected Hrun);exact Htoken.
   + split.
     * rewrite (NativeCommandLengths.generated arraydef_0__printBuffer before bs ns after observations trace NativeCommandLengths.printBuffer_protected Hrun);exact Hprint.
     * split;assumption.
 - pose proof (proj1 (proj2 (proj1 (NativeState.formula_representation _ _ Hstate)))) as Hcount.
   pose proof (proj1 (proj2 (proj1 (NativeState.formula_representation _ _ Hnext)))) as HcountNext.
   change (meta_value before 1=Z.of_nat (length (Protocol.formulas logical))) in Hcount.
   change (meta_value after 1=Z.of_nat (length (Protocol.formulas next))) in HcountNext.
   rewrite Hcount,HcountNext in Hformulas. split.
   + apply Nat2Z.inj_le. rewrite Nat2Z.inj_add;exact Hformulas.
   + rewrite (proj1 (NativeState.class_representation _ _ Hstate)),(proj1 (NativeState.class_representation _ _ Hnext)) in Hclasses.
     split;[lia|].
     rewrite (proj1 (NativeState.history_representation _ _ Hstate)),(proj1 (NativeState.history_representation _ _ Hnext)) in Hhistory.
     apply Nat2Z.inj_le. rewrite Nat2Z.inj_succ;exact Hhistory.
Qed.
Theorem inspect_control s logical bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> LogicalHistory.valid logical ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 57 :: first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final reply,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 19 [value] []) reply logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\ HistoryRefinement.represents final logical /\ flow 0 s final reply tail.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hvalid Harena Hclasses Hhistory Hsep1 Hsep2 Hin.
  assert (Hopword : Z.of_nat 19 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadOne.generated_reads s (fun _ => false) (fun _ => 0) 19 49 [57] value first_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hvalue Hsep1 Hsep2 Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  set (arg := ReadOne.argument_state s 49 [57] value last_separator tail).
  change (17 < length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadOne.argument_storage s 49 [57] value last_separator tail Hmeta) Harena). }
  pose proof (ParsedState.one_history s logical 49 [57] value last_separator tail Hmeta Hhistory) as Harg_history.
  pose proof (ParsedState.one_classes s _ _ 49 [57] value last_separator tail Hmeta Hclasses) as Harg_classes.
  change (HistoryRefinement.represents arg logical) in Harg_history.
  change (ClassStorage.represents arg (Protocol.formulas logical) (Protocol.classes logical)) in Harg_classes.
  assert (Hunique : NoDup (Protocol.formulas logical)) by now apply (SemanticFrames.arena_NoDup s).
  destruct (nth_error (Protocol.history logical) value) as [fid|] eqn:Hlookup.
  - destruct (Hvalid value fid Hlookup) as [p Hp].
    destruct (HistoryLookup.native_lookup arg logical value fid Harg_history Hlookup) as [Hnative Hnth].
    pose proof (proj1 (proj2 (HistoryLookup.formula_reference s _ fid p Harena Hp))) as Hword.
    assert (Hreference : Z.of_nat value < meta_value arg 3).
    { rewrite (proj1 Harg_history). assert (value < length (Protocol.history logical))%nat by (apply nth_error_Some; congruence). lia. }
    pose proof (CommandInspectExecution.generated_command s bs ns _ arg fid (Z.of_nat value) observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference
      ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) Hargbuffer (proj2 Hword)) as Hrun.
    rewrite Hinput,Houtput in Hrun. exists (ReplyOKExecution.reply_state arg fid),(Protocol.OK fid). split; [exact Hrun|].
    split.
    + eapply Protocol.step_accept; [apply Protocol.accept_inspect; exact Hlookup|now apply HistoryRefinement.retained_refl].
    + split; [exact (FormulaProjection.storage_arena arg _ _ (FormulaProjection.reply_storage arg fid) Harg_arena)|].
      split; [now apply SemanticFrames.reply_classes|]. split;[now apply SemanticFrames.reply_history|].
      apply ok_flow;[exact (read_one_frame s 49 [57] value last_separator tail Hmeta Hinput Houtput)|exact Herror].
  - assert (Hreference : meta_value arg 3 <= Z.of_nat value).
    { rewrite (proj1 Harg_history). apply nth_error_None in Hlookup. lia. }
    pose proof (CommandInspectExecution.generated_rejected_command s bs ns _ arg (Z.of_nat value) observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference) as Hrun.
    rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state arg),Protocol.NO. split; [exact Hrun|].
    split; [now apply InspectRefinement.logical_rejected|]. split.
    + eapply ArenaFrame.storage_arena; [|exact Harg_arena]. apply ArenaFrame.storage_output.
    + split;[exact Harg_classes|]. split;[exact Harg_history|].
      apply no_flow;[exact (read_one_frame s 49 [57] value last_separator tail Hmeta Hinput Houtput)|exact Herror].
Qed.
Theorem generated_inspect s logical bs ns value first_separator last_separator tail observations :
 (17<length (memory s arraydef_0__meta))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15=50 -> meta_value s 8=0 ->
 Z.of_nat value<=maximum -> LogicalHistory.valid logical -> NativeState.represents s logical ->
 TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
 stdin s=57::first_separator::decimalBytes value++last_separator::tail ->
 exists final reply,
 execObserved (funcdef_0__command bs ns) (s,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 19 [value] []) reply logical /\ NativeState.represents final logical /\
 boundary 0 s logical final reply logical tail.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hvalue Hvalid Hstate Hfirst Hlast Hinput.
 destruct (inspect_control s logical bs ns value first_separator last_separator tail observations
   Hmeta Htoken Hprint Hpending Herror Hvalue Hvalid (NativeState.formula_representation _ _ Hstate)
   (NativeState.class_representation _ _ Hstate) (NativeState.history_representation _ _ Hstate) Hfirst Hlast Hinput)
 as (final & reply & Hrun & Hstep & Harena & Hclasses & Hhistory & Hflow).
 assert (Hnext:NativeState.represents final logical).
 { exact (NativeProtocolLift.canonical 19 49 [57] s bs ns first_separator (decimalBytes value++last_separator::tail)
   observations final _ logical (Protocol.Req 19 [value] []) reply logical ltac:(lia) ltac:(lia)
   ltac:(unfold NativeStateFrames.nonbinding;repeat split;lia) eq_refl eq_refl Hmeta Htoken Hpending Herror Hfirst Hinput
   Hrun Hstate Hstep Harena Hclasses Hhistory). }
 exists final,reply. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hnext|].
 exact (boundary_from_flow 0 s final bs ns logical logical reply tail observations _ Hstate Hnext Htoken Hprint Hrun Hflow).
Qed.
End NativeTheoremBoundary.
