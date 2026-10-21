From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash ReadTwo TokenByte InternBounded Intern Observation FormulaEncoding Representation ArenaFrame FormulaProjection ClassStorage HistoryRefinement SemanticFrames FormulaAtoms ReplyOK.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module FormulaAtomsRefinement.
Import IndexExecution SipHashExecution.
Definition atom (opcode a b : nat) := if Nat.eq_dec opcode 1%nat then SetTheory.equal a b else SetTheory.member a b.
Definition logical_after logical fs := Protocol.State fs (Protocol.classes logical) (Protocol.history logical)
  (Protocol.bindings logical) (Protocol.expressions logical).
Lemma decoded meaning opcode a b : (opcode = 1%nat \/ opcode = 2%nat) ->
  FormulaEncoding.decode meaning (Z.of_nat opcode,Z.of_nat a,Z.of_nat b) = Some (atom opcode a b).
Proof. intros [Hcase|Hcase]; subst opcode; unfold atom, FormulaEncoding.decode; now rewrite !Nat2Z.id. Qed.
Lemma requested logical opcode a b : (opcode = 1%nat \/ opcode = 2%nat) ->
  Protocol.formula_request logical (Protocol.Req opcode [a;b] []) (atom opcode a b).
Proof. intros [Hcase|Hcase]; subst opcode; cbn [atom]; constructor. Qed.
Theorem generated_protocol opcode ch chars s logical bs ns a b first_separator middle last tail observations :
  (opcode = 1%nat \/ opcode = 2%nat) -> decimalBytes opcode = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req opcode [a;b] []) (Protocol.OK index) (logical_after logical fs) /\
    NativeRepresentation.canonical_arena final fs /\
    ClassStorage.represents final fs (Protocol.classes logical) /\
    HistoryRefinement.represents final (logical_after logical fs).
Proof.
  intros Hcase Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hin.
  assert (Hcode : Z.of_nat opcode <= maximum) by (unfold maximum; destruct Hcase; subst opcode; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _ => false) (fun _ => 0) opcode ch chars a b first_separator middle last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin) as Hread.
  destruct Hread as [Hopcode [HreadA [HreadB [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer [Hsecondnumber [Hsecondvalid [Hseconderror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := ReadTwo.second_state s ch chars a middle b last tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) Harena). }
  assert (Hnormal : FormulaEncoding.normal (Z.of_nat opcode,Z.of_nat a,Z.of_nat b)).
  { right. left. split; [destruct Hcase; subst opcode; cbn; tauto|]. unfold word. split; lia. }
  destruct (InternBounded.generated_refines arg (fun _ => false) (FormulaAtomsExecution.arguments (Z.of_nat opcode) (Z.of_nat a) (Z.of_nat b))
    (Protocol.formulas logical) (atom opcode a b) Harg_arena Hseconderror Hbound Hnormal (decoded _ _ _ _ Hcase))
    as [internstate [fs [index [Hintern [Hframe [Hflag [Hresult [Hword [Hnext [Hformula Hextends]]]]]]]]]].
  assert (Hobserved : execObserved (funcdef_0__intern (fun _ => false) (FormulaAtomsExecution.arguments (Z.of_nat opcode) (Z.of_nat a) (Z.of_nat b)))
    (arg,observations) = Some (tt,(internstate,observations))).
  { apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern]. }
  pose proof Hframe as [Harrays [Hcells [Hintern_input Hintern_output]]].
  assert (Hpostmeta : (17 < length (memory internstate arraydef_0__meta))%nat).
  { pose proof (proj1 (proj1 (proj1 Hnext))) as Hcapacity. lia. }
  assert (Hpostbuffer : (20 <= length (memory internstate arraydef_0__printBuffer))%nat).
  { rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
    exact Hsecondbuffer. }
  assert (Htag : Z.of_nat opcode = 1 \/ Z.of_nat opcode = 2) by (destruct Hcase; subst opcode; cbn; auto).
  pose proof (FormulaAtomsExecution.generated_command (Z.of_nat opcode) s bs ns _ _ arg internstate index (Z.of_nat a) (Z.of_nat b) observations
    Htag Hopcode Hopmeta Hopnumber Hopvalid Hoperror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror
    Hobserved Hpostmeta Hpostbuffer Hflag Hresult Hword) as Hrun.
  assert (Htail : stdin internstate = tail) by (rewrite Hintern_input; exact Hinput).
  assert (Hstdout : stdout internstate = stdout s) by (rewrite Hintern_output; exact Houtput).
  rewrite Htail, Hstdout in Hrun.
  exists (ReplyOKExecution.reply_state internstate index),index,fs. split; [exact Hrun|].
  assert (Hunique : NoDup fs) by (now apply (SemanticFrames.arena_NoDup internstate)).
  destruct Hextends as [extra Hextends]. split.
  - eapply Protocol.step_accept with (t := logical_after logical fs).
    + eapply Protocol.accept_formula with (p := atom opcode a b).
      * now apply requested.
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
Qed.
End FormulaAtomsRefinement.
