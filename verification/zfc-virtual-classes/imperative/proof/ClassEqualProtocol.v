From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash ReadTwo TokenByte ClassEqualCommand ClassEqualRefinement ClassLookup ClassStorage HistoryRefinement RenameStorage RenameInvariant SemanticFrames FormulaEncoding Representation ArenaFrame FormulaProjection ReplyOK ReplyNO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ClassEqualProtocol.
Import IndexExecution SipHashExecution.
Definition logical_after logical fs := Protocol.State fs (Protocol.classes logical) (Protocol.history logical)
  (Protocol.bindings logical) (Protocol.expressions logical).
Lemma argument_classes s logical ch chars a middle b last tail : (17 < length (memory s arraydef_0__meta))%nat ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) ->
  ClassStorage.represents (ReadTwo.second_state s ch chars a middle b last tail) (Protocol.formulas logical) (Protocol.classes logical).
Proof.
  intros Hmeta [Hcount Hclasses]. split; [rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia); exact Hcount|].
  now rewrite ReadTwo.second_other by discriminate.
Qed.
Lemma argument_history s logical ch chars a middle b last tail : (17 < length (memory s arraydef_0__meta))%nat ->
  HistoryRefinement.represents s logical -> HistoryRefinement.represents (ReadTwo.second_state s ch chars a middle b last tail) logical.
Proof.
  intros Hmeta [Hcount Hhistory]. split; [rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia); exact Hcount|].
  now rewrite ReadTwo.second_other by discriminate.
Qed.
Lemma reference s fs classes value cls : ClassStorage.represents s fs classes -> nth_error classes value = Some cls -> Z.of_nat value < meta_value s 2.
Proof. intros [Hcount Hclasses] Hlookup. rewrite Hcount. assert (Hbound : (value < length classes)%nat) by (apply nth_error_Some; congruence). lia. Qed.
Theorem generated_protocol ch chars s logical bs ns a b cls_a cls_b first_separator middle last tail observations :
  decimalBytes 7%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  nth_error (Protocol.formulas logical) 0 = Some SetTheory.falsity ->
  ClassEqualRefinement.ready cls_a cls_b ->
  Z.of_nat (length (Protocol.formulas logical) + ClassEqualRefinement.work cls_a cls_b) <= RenameInvariant.resource_limit ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  Protocol.class_at logical a = Some cls_a -> Protocol.class_at logical b = Some cls_b ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 7 [a;b] []) (Protocol.OK index) (logical_after logical fs) /\
    NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs (Protocol.classes logical) /\
    HistoryRefinement.represents final (logical_after logical fs).
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Hfalse Hready Hbudget Ha Hb Hlookup_a Hlookup_b Harena Hclasses Hwellformed Hhistory Hsep1 Hsep2 Hsep3 Hin.
  assert (Hcode : Z.of_nat 7 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _=>false) (fun _=>0) 7 ch chars a b first_separator middle last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin) as Hread.
  destruct Hread as [Hopcode [HreadA [HreadB [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer [Hsecondnumber [Hsecondvalid [Hseconderror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := ReadTwo.second_state s ch chars a middle b last tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical))
    by (exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) Harena)).
  pose proof (argument_classes s logical ch chars a middle b last tail Hmeta Hclasses) as Harg_classes.
  pose proof (argument_history s logical ch chars a middle b last tail Hmeta Hhistory) as Harg_history.
  assert (Harg_wellformed : ClassLookup.wellformed arg).
  { apply (ClassLookup.transport s); [unfold arg; now rewrite ReadTwo.second_other by discriminate|exact Hwellformed]. }
  assert (Href_a : Z.of_nat a < meta_value arg 2) by (eapply reference; eassumption).
  assert (Href_b : Z.of_nat b < meta_value arg 2) by (eapply reference; eassumption).
  destruct (ClassEqualRefinement.generated_refines arg (fun _=>false) (ClassEqualCommand.arguments (Z.of_nat a) (Z.of_nat b))
    (Protocol.formulas logical) (Protocol.classes logical) a b cls_a cls_b observations
    Harg_arena Hfalse Hseconderror Harg_classes Harg_wellformed Hlookup_a Hlookup_b eq_refl eq_refl Hready Hbudget)
    as [built [fs [index [Hhelper [Hnext [Hindex [Hword [Hformula [Hprefix [Hflag [Hframe [Hbuilt_classes Hbuilt_wellformed]]]]]]]]]]]].
  pose proof Hframe as [Harrays [Hcells [Hinput_helper Houtput_helper]]].
  assert (Hpostmeta : (17 < length (memory built arraydef_0__meta))%nat) by (pose proof (proj1 (proj1 Hnext)) as [Hcapacity Hrest]; lia).
  assert (Hpostbuffer : (20 <= length (memory built arraydef_0__printBuffer))%nat).
  { rewrite Harrays by (repeat split; discriminate). exact Hsecondbuffer. }
  pose proof (ClassEqualCommand.generated_command s bs ns _ _ arg built index (Z.of_nat a) (Z.of_nat b) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror
    Href_a Href_b Hhelper Hpostmeta Hpostbuffer Hflag Hindex (proj2 Hword)) as Hrun.
  assert (Htail : stdin built = tail) by (rewrite Hinput_helper; exact Hinput).
  assert (Hstdout : stdout built = stdout s) by (rewrite Houtput_helper; exact Houtput).
  rewrite Htail,Hstdout in Hrun.
  exists (ReplyOKExecution.reply_state built index),index,fs. split; [exact Hrun|].
  assert (Hunique : NoDup fs) by (now apply (SemanticFrames.arena_NoDup built)). split.
  - eapply Protocol.step_accept with (t:=logical_after logical fs).
    + eapply Protocol.accept_formula with (p:=VirtualClasses.erase (VirtualClasses.class_equal cls_a cls_b)).
      * eapply Protocol.req_class_equal; eassumption.
      * split; [exact Hprefix|]. split; [exact Hunique|]. split; [exact Hformula|]. exists []; now rewrite app_nil_r.
    + apply HistoryRefinement.retained_refl. exact Hunique.
  - split; [exact (FormulaProjection.storage_arena built _ fs (FormulaProjection.reply_storage built index) Hnext)|].
    split; [now apply SemanticFrames.reply_classes|]. apply SemanticFrames.reply_history.
    exact (RenameStorage.history_transport arg built logical Hframe Harg_history).
Qed.
Theorem logical_rejected logical a b :
  (Protocol.class_at logical a = None \/ Protocol.class_at logical b = None) ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 7 [a;b] []) Protocol.NO logical.
Proof.
  intros Hbad Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H; subst; destruct Hbad; congruence end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end].
Qed.
Theorem generated_rejected_protocol ch chars s logical bs ns a b first_separator middle last tail observations :
  decimalBytes 7%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  (Protocol.class_at logical a = None \/ Protocol.class_at logical b = None) ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 7 [a;b] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final logical.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb Hbad Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hin.
  assert (Hcode : Z.of_nat 7 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _ => false) (fun _ => 0) 7 ch chars a b first_separator middle last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin) as Hread.
  destruct Hread as [Hopcode [HreadA [HreadB [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer [Hsecondnumber [Hsecondvalid [Hseconderror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := ReadTwo.second_state s ch chars a middle b last tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) Harena). }
  assert (Hbadrefs : meta_value arg 2 <= Z.of_nat a \/ meta_value arg 2 <= Z.of_nat b).
  { pose proof (proj1 Hclasses) as Hcount.
    assert (Hargcount : meta_value arg 2 = Z.of_nat (length (Protocol.classes logical))).
    { unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hcount. }
    rewrite Hargcount. destruct Hbad as [Hbad|Hbad]; unfold Protocol.class_at in Hbad; apply nth_error_None in Hbad; lia. }
  pose proof (ClassEqualCommand.generated_rejected_command s bs ns _ _ arg (Z.of_nat a) (Z.of_nat b) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror Hbadrefs) as Hrun.
  assert (Htail : stdin arg = tail) by exact Hinput.
  assert (Hstdout : stdout arg = stdout s) by exact Houtput.
  rewrite Htail, Hstdout in Hrun.
  exists (ReplyNOExecution.reply_state arg). split; [exact Hrun|].
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
Qed.
Theorem generated_total_protocol ch chars s logical bs ns a b first_separator middle last tail observations :
  decimalBytes 7%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  nth_error (Protocol.formulas logical) 0 = Some SetTheory.falsity ->
  (forall cls_a cls_b, Protocol.class_at logical a = Some cls_a -> Protocol.class_at logical b = Some cls_b ->
    ClassEqualRefinement.ready cls_a cls_b /\
    Z.of_nat (length (Protocol.formulas logical) + ClassEqualRefinement.work cls_a cls_b) <= RenameInvariant.resource_limit) ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 7 [a;b] []) reply next /\
    NativeRepresentation.canonical_arena final (Protocol.formulas next) /\
    ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) /\ HistoryRefinement.represents final next.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Hfalse Hdomain Ha Hb Harena Hclasses Hwellformed Hhistory Hsep1 Hsep2 Hsep3 Hin.
  destruct (Protocol.class_at logical a) as [cls_a|] eqn:Hlookup_a.
  - destruct (Protocol.class_at logical b) as [cls_b|] eqn:Hlookup_b.
    + destruct (Hdomain cls_a cls_b eq_refl eq_refl) as [Hready Hbudget].
      destruct (generated_protocol ch chars s logical bs ns a b cls_a cls_b first_separator middle last tail observations
        Hencoding Hmeta Htoken Hbuffer Hpending Herror Hfalse Hready Hbudget Ha Hb Hlookup_a Hlookup_b Harena Hclasses Hwellformed Hhistory Hsep1 Hsep2 Hsep3 Hin)
        as [final [index [fs Hpost]]]. exists final,(Protocol.OK index),(logical_after logical fs). exact Hpost.
    + destruct (generated_rejected_protocol ch chars s logical bs ns a b first_separator middle last tail observations
        Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb (or_intror Hlookup_b) Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hin) as [final Hpost].
      exists final,Protocol.NO,logical. exact Hpost.
  - destruct (generated_rejected_protocol ch chars s logical bs ns a b first_separator middle last tail observations
      Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb (or_introl Hlookup_a) Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hin) as [final Hpost].
    exists final,Protocol.NO,logical. exact Hpost.
Qed.
End ClassEqualProtocol.
