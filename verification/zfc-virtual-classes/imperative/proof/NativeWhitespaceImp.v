From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash DecimalInput CommandArgs CommandInput ReadOne ReadTwo TokenByte InternBounded Intern Observation
 FormulaEncoding Representation ArenaFrame FormulaProjection ClassStorage HistoryRefinement SemanticFrames
 FormulaAtoms FormulaImp FormulaAll ReplyOK ReplyNO NativeState NativeStateFrames.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From NativeProof Require Import NativeArgumentReadsTwoFull NativeSimpleCommands.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeWhitespaceImp.
Import IndexExecution SipHashExecution NativeSimpleCommands NativeSimpleCommands.Imp.
Theorem generated_protocol ch chars s logical bs ns a b p q first_separator prefix1 middle prefix2 last tail observations :
  decimalBytes 3%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  Protocol.formula_at logical a = Some p -> Protocol.formula_at logical b = Some q ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = chars ++ first_separator :: prefix1 ++ decimalBytes a ++ middle :: prefix2 ++ decimalBytes b ++ last :: tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 3 [a;b] []) (Protocol.OK index) (logical_after logical fs) /\
    NativeState.represents final (logical_after logical fs) /\
    boundary s logical final (Protocol.OK index) (logical_after logical fs) tail.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb HlookupA HlookupB Hnative Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  assert (Hcode : Z.of_nat 3 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReadsTwoFull.generated_reads s (fun _ => false) (fun _ => 0) 3 ch chars a b first_separator prefix1 middle prefix2 last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin) as Hread.
  destruct Hread as [Hopcode [HreadA [HreadB [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer [Hsecondnumber [Hsecondvalid [Hseconderror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := ReadTwo.second_state s ch chars a middle b last tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) Harena). }
  assert (Hnormal : FormulaEncoding.normal (3,Z.of_nat a,Z.of_nat b)).
  { right. left. split; [right; right; reflexivity|]. unfold word. split; lia. }
  assert (HreferenceA : Z.of_nat a < meta_value arg 1) by (eapply reference; eassumption).
  assert (HreferenceB : Z.of_nat b < meta_value arg 1) by (eapply reference; eassumption).
  destruct (InternBounded.generated_refines arg (fun _ => false) (FormulaImpExecution.arguments (Z.of_nat a) (Z.of_nat b))
    (Protocol.formulas logical) (SetTheory.implies p q) Harg_arena Hseconderror Hbound Hnormal (decoded _ _ _ _ _ HlookupA HlookupB))
    as [internstate [fs [index [Hintern [Hframe [Hflag [Hresult [Hword [Hnext [Hformula Hextends]]]]]]]]]].
  assert (Hobserved : execObserved (funcdef_0__intern (fun _ => false) (FormulaImpExecution.arguments (Z.of_nat a) (Z.of_nat b)))
    (arg,observations) = Some (tt,(internstate,observations))).
  { apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern]. }
  pose proof Hframe as [Harrays [Hcells [Hintern_input Hintern_output]]].
  assert (Hpostmeta : (17 < length (memory internstate arraydef_0__meta))%nat).
  { pose proof (proj1 (proj1 (proj1 Hnext))) as Hcapacity. lia. }
  assert (Hpostbuffer : (20 <= length (memory internstate arraydef_0__printBuffer))%nat).
  { rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
    exact Hsecondbuffer. }
  pose proof (FormulaImpExecution.generated_command s bs ns _ _ arg internstate index (Z.of_nat a) (Z.of_nat b) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror
    HreferenceA HreferenceB Hobserved Hpostmeta Hpostbuffer Hflag Hresult Hword) as Hrun.
  assert (Htail : stdin internstate = tail) by (rewrite Hintern_input; exact Hinput).
  assert (Hstdout : stdout internstate = stdout s) by (rewrite Hintern_output; exact Houtput).
  rewrite Htail, Hstdout in Hrun.
  assert (Hregistries : NativeStateFrames.registries s (ReplyOKExecution.reply_state internstate index)).
  { eapply NativeStateFrames.trans.
    - exact (NativeStateFrames.read_two s ch chars a middle b last tail Hmeta).
    - eapply NativeStateFrames.trans;[exact (NativeStateFrames.intern _ _ Hframe)|apply NativeStateFrames.reply_ok]. }
  exists (ReplyOKExecution.reply_state internstate index),index,fs. split; [exact Hrun|].
  assert (Hpartial :
    Protocol.step logical (Protocol.Req 3 [a;b] []) (Protocol.OK index) (logical_after logical fs) /\
    NativeRepresentation.canonical_arena (ReplyOKExecution.reply_state internstate index) fs /\
    ClassStorage.represents (ReplyOKExecution.reply_state internstate index) fs (Protocol.classes logical) /\
    HistoryRefinement.represents (ReplyOKExecution.reply_state internstate index) (logical_after logical fs)).
  {
  assert (Hunique : NoDup fs) by (now apply (SemanticFrames.arena_NoDup internstate)).
  destruct Hextends as [extra Hextends]. split.
  - eapply Protocol.step_accept with (t := logical_after logical fs).
    + eapply Protocol.accept_formula with (p := SetTheory.implies p q).
      * eapply requested; eassumption.
      * split; [now exists extra|]. split; [exact Hunique|]. split; [exact Hformula|]. exists []; now rewrite app_nil_r.
    + apply HistoryRefinement.retained_refl. exact Hunique.
  - split; [exact (FormulaProjection.storage_arena internstate _ fs (FormulaProjection.reply_storage internstate index) Hnext)|].
    split.
    + apply SemanticFrames.reply_classes. rewrite Hextends. apply (SemanticFrames.intern_classes arg internstate); [exact Hframe|].
      destruct Hclasses as [Hcount Hclassarray]. split.
      * unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hcount.
      * unfold arg. rewrite ReadTwo.second_other by discriminate. exact Hclassarray.
    + apply SemanticFrames.reply_history. apply (SemanticFrames.intern_history arg internstate); [exact Hframe|].
      destruct Hhistory as [Hcount Hprefix]. split.
      * unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hcount.
      * unfold arg. rewrite ReadTwo.second_other by discriminate. exact Hprefix.
  }
  destruct Hpartial as [Hstep [Hformulas [HclassesFinal HhistoryFinal]]].
  split;[exact Hstep|].
  split.
  { eapply NativeStateFrames.finish;[exact Hnative|exact Hregistries|exact Hstep|discriminate|reflexivity|
    exact Hformulas|exact HclassesFinal|exact HhistoryFinal]. }
  { eapply reply_ok_boundary;[exact Htail|exact Hstdout| |exact Hpostbuffer|exact Hflag| |].
    + rewrite (Harrays arraydef_0__token ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
      unfold arg. rewrite read_two_token_length. exact Htoken.
    + rewrite Hcells by lia. unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta;lia). reflexivity.
    + exact (intern_growth arg internstate _ _ _ fs Harg_arena Hseconderror Hbound Hintern Hnext).
  }
Qed.
Theorem logical_rejected logical a b :
  (Protocol.formula_at logical a = None \/ Protocol.formula_at logical b = None) ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 3 [a;b] []) Protocol.NO logical.
Proof.
  intros Hbad Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H; subst; destruct Hbad; congruence end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end].
Qed.
Theorem generated_rejected_protocol ch chars s logical bs ns a b first_separator prefix1 middle prefix2 last tail observations :
  decimalBytes 3%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  (Protocol.formula_at logical a = None \/ Protocol.formula_at logical b = None) ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = chars ++ first_separator :: prefix1 ++ decimalBytes a ++ middle :: prefix2 ++ decimalBytes b ++ last :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 3 [a;b] []) Protocol.NO logical /\
    NativeState.represents final logical /\
    boundary s logical final Protocol.NO logical tail.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb Hbad Hnative Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  assert (Hcode : Z.of_nat 3 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReadsTwoFull.generated_reads s (fun _ => false) (fun _ => 0) 3 ch chars a b first_separator prefix1 middle prefix2 last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin) as Hread.
  destruct Hread as [Hopcode [HreadA [HreadB [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer [Hsecondnumber [Hsecondvalid [Hseconderror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := ReadTwo.second_state s ch chars a middle b last tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) Harena). }
  assert (Hbadrefs : meta_value arg 1 <= Z.of_nat a \/ meta_value arg 1 <= Z.of_nat b).
  { pose proof (proj1 (proj2 (proj1 Harg_arena))) as Hcount.
    change (meta_value arg 1 = Z.of_nat (length (Protocol.formulas logical))) in Hcount.
    rewrite Hcount. destruct Hbad as [Hbad|Hbad]; unfold Protocol.formula_at in Hbad; apply nth_error_None in Hbad; lia. }
  pose proof (FormulaImpExecution.generated_rejected_command s bs ns _ _ arg (Z.of_nat a) (Z.of_nat b) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror Hbadrefs) as Hrun.
  assert (Htail : stdin arg = tail) by exact Hinput.
  assert (Hstdout : stdout arg = stdout s) by exact Houtput.
  rewrite Htail, Hstdout in Hrun.
  assert (Hregistries : NativeStateFrames.registries s (ReplyNOExecution.reply_state arg)).
  { eapply NativeStateFrames.trans;[exact (NativeStateFrames.read_two s ch chars a middle b last tail Hmeta)|apply NativeStateFrames.reply_no]. }
  exists (ReplyNOExecution.reply_state arg). split; [exact Hrun|].
  assert (Hpartial :
    Protocol.step logical (Protocol.Req 3 [a;b] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena (ReplyNOExecution.reply_state arg) (Protocol.formulas logical) /\
    ClassStorage.represents (ReplyNOExecution.reply_state arg) (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents (ReplyNOExecution.reply_state arg) logical).
  {
  split; [apply logical_rejected; [exact Hbad|now apply (SemanticFrames.arena_NoDup s)]|].
  split.
  - exact (ArenaFrame.storage_arena arg _ (Protocol.formulas logical) (ArenaFrame.storage_output _ _) Harg_arena).
  - destruct Hclasses as [Hcount Hclassarray]. split.
    + split.
      * change (meta_value arg 2 = Z.of_nat (length (Protocol.classes logical))).
        unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hcount.
      * change (Forall2 (fun entry cls => ClassStorage.decode (Protocol.formulas logical) entry = Some cls)
          (memory arg arraydef_0__classes) (Protocol.classes logical)).
        unfold arg. rewrite ReadTwo.second_other by discriminate. exact Hclassarray.
    + destruct Hhistory as [Hnumber Hprefix]. split.
      * change (meta_value arg 3 = Z.of_nat (length (Protocol.history logical))).
        unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hnumber.
      * change (firstn (length (Protocol.history logical)) (memory arg arraydef_0__theorems) = map Z.of_nat (Protocol.history logical)).
        unfold arg. rewrite ReadTwo.second_other by discriminate. exact Hprefix.
  }
  destruct Hpartial as [Hstep [Hformulas [HclassesFinal HhistoryFinal]]].
  split;[exact Hstep|].
  split.
  { eapply NativeStateFrames.finish;[exact Hnative|exact Hregistries|exact Hstep|discriminate|reflexivity|
    exact Hformulas|exact HclassesFinal|exact HhistoryFinal]. }
  { eapply reply_no_boundary;[exact Hinput|exact Houtput| |exact Hsecondbuffer|exact Hseconderror|].
    + unfold arg. rewrite read_two_token_length. exact Htoken.
    + unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta;lia). reflexivity.
  }
Qed.
Theorem generated_total_protocol ch chars s logical bs ns a b first_separator prefix1 middle prefix2 last tail observations :
  decimalBytes 3%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = chars ++ first_separator :: prefix1 ++ decimalBytes a ++ middle :: prefix2 ++ decimalBytes b ++ last :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 3 [a;b] []) reply next /\
    NativeState.represents final next /\
    boundary s logical final reply next tail.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb Hnative Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  destruct (Protocol.formula_at logical a) as [p|] eqn:HlookupA.
  - destruct (Protocol.formula_at logical b) as [q|] eqn:HlookupB.
    + destruct (generated_protocol ch chars s logical bs ns a b p q first_separator prefix1 middle prefix2 last tail observations
        Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb HlookupA HlookupB Hnative Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
        as [final [index [fs Hrun]]].
      exists final,(Protocol.OK index),(logical_after logical fs). exact Hrun.
    + destruct (generated_rejected_protocol ch chars s logical bs ns a b first_separator prefix1 middle prefix2 last tail observations
        Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb (or_intror HlookupB) Hnative Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin) as [final Hrun].
      exists final,Protocol.NO,logical. exact Hrun.
  - destruct (generated_rejected_protocol ch chars s logical bs ns a b first_separator prefix1 middle prefix2 last tail observations
      Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb (or_introl HlookupA) Hnative Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin) as [final Hrun].
    exists final,Protocol.NO,logical. exact Hrun.
Qed.
End NativeWhitespaceImp.
