From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash DecimalInput CommandArgs CommandInput ReadOne ReadTwo TokenByte InternBounded Intern Observation
 FormulaEncoding Representation ArenaFrame FormulaProjection ClassStorage HistoryRefinement SemanticFrames
 FormulaAtoms FormulaImp FormulaAll ReplyOK ReplyNO NativeState NativeStateFrames.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

(** Canonical complete native command runs, with all five protocol-state
    representations retained. No execution witness is an input premise. *)
Module NativeSimpleCommands.
Import IndexExecution SipHashExecution.
Definition boundary s logical final reply next tail :=
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes reply /\
 (1024<=length(memory final arraydef_0__token))%nat /\
 (20<=length(memory final arraydef_0__printBuffer))%nat /\
 meta_value final 8=0 /\ meta_value final 9=meta_value s 9 /\
 (length(Protocol.formulas next)<=S(length(Protocol.formulas logical)))%nat.
Lemma read_one_token_length s ch chars value sep tail :
 length(memory (ReadOne.argument_state s ch chars value sep tail) arraydef_0__token)=length(memory s arraydef_0__token).
Proof. unfold ReadOne.argument_state,ReadOne.opcode_state.
 now rewrite DecimalInput.encoded_token_length,CommandArgs.pending_token_length. Qed.
Lemma read_two_token_length s ch chars a middle b last tail :
 length(memory (ReadTwo.second_state s ch chars a middle b last tail) arraydef_0__token)=length(memory s arraydef_0__token).
Proof. unfold ReadTwo.second_state,ReadTwo.first_state.
 now rewrite DecimalInput.encoded_token_length,read_one_token_length. Qed.
Lemma intern_growth s final bs ns meaning next :
 NativeRepresentation.canonical_arena s meaning -> meta_value s 8=0 ->
 Z.of_nat(length meaning)<=9223372036854775807 ->
 exec (funcdef_0__intern bs ns) s=Some(tt,final) ->
 NativeRepresentation.canonical_arena final next -> (length next<=S(length meaning))%nat.
Proof.
 intros Hsource Herror Hbound Hrun Hnext.
 destruct (InternBounded.generated_intern_bounded s bs ns (length meaning) (proj1 Hsource) Herror Hbound)
   as [witness [Hwitness [_ [_ [count [index [Hcount [Htable Hrest]]]]]]]].
 rewrite Hrun in Hwitness. injection Hwitness as Hsame. subst witness.
 pose proof (proj1(proj2 Htable)) as HcountValue.
 pose proof (proj1(proj2(proj1 Hnext))) as HnextValue.
 change (meta_value final 1=Z.of_nat(length next)) in HnextValue.
 rewrite HcountValue in HnextValue. apply Nat2Z.inj in HnextValue.
 destruct Hcount as [Hequal|[Hequal Hindex]];lia.
Qed.
Lemma reply_ok_boundary s logical current next index tail :
 stdin current=tail -> stdout current=stdout s ->
 (1024<=length(memory current arraydef_0__token))%nat ->
 (20<=length(memory current arraydef_0__printBuffer))%nat ->
 meta_value current 8=0 -> meta_value current 9=meta_value s 9 ->
 (length(Protocol.formulas next)<=S(length(Protocol.formulas logical)))%nat ->
 boundary s logical (ReplyOKExecution.reply_state current index) (Protocol.OK index) next tail.
Proof.
 intros Hin Hout Htoken Hprint Herror Hstop Hgrowth. unfold boundary.
 split;[now rewrite ReplyOKExecution.reply_input|].
 split;[now rewrite ReplyOKExecution.reply_output,Hout|].
 split;[now rewrite ReplyOKExecution.reply_other by discriminate|].
 split;[now rewrite ReplyOKExecution.reply_buffer_length|].
 split;[unfold meta_value;now rewrite ReplyOKExecution.reply_other by discriminate|].
 split;[unfold meta_value;now rewrite ReplyOKExecution.reply_other by discriminate|exact Hgrowth].
Qed.
Lemma reply_no_boundary s logical current tail :
 stdin current=tail -> stdout current=stdout s ->
 (1024<=length(memory current arraydef_0__token))%nat ->
 (20<=length(memory current arraydef_0__printBuffer))%nat ->
 meta_value current 8=0 -> meta_value current 9=meta_value s 9 ->
 boundary s logical (ReplyNOExecution.reply_state current) Protocol.NO logical tail.
Proof.
 intros Hin Hout Htoken Hprint Herror Hstop. unfold boundary.
 split;[exact Hin|]. split;[now rewrite ReplyNOExecution.reply_output,Hout|].
 split;[exact Htoken|]. split;[exact Hprint|]. split;[exact Herror|]. split;[exact Hstop|lia].
Qed.

Module Atoms.
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
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req opcode [a;b] []) (Protocol.OK index) (logical_after logical fs) /\
    NativeState.represents final (logical_after logical fs) /\
    boundary s logical final (Protocol.OK index) (logical_after logical fs) tail.
Proof.
  intros Hcase Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb Hnative Hsep1 Hsep2 Hsep3 Hin.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
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
  assert (Hregistries : NativeStateFrames.registries s (ReplyOKExecution.reply_state internstate index)).
  { eapply NativeStateFrames.trans.
    - exact (NativeStateFrames.read_two s ch chars a middle b last tail Hmeta).
    - eapply NativeStateFrames.trans;[exact (NativeStateFrames.intern _ _ Hframe)|apply NativeStateFrames.reply_ok]. }
  exists (ReplyOKExecution.reply_state internstate index),index,fs. split; [exact Hrun|].
  assert (Hpartial :
    Protocol.step logical (Protocol.Req opcode [a;b] []) (Protocol.OK index) (logical_after logical fs) /\
    NativeRepresentation.canonical_arena (ReplyOKExecution.reply_state internstate index) fs /\
    ClassStorage.represents (ReplyOKExecution.reply_state internstate index) fs (Protocol.classes logical) /\
    HistoryRefinement.represents (ReplyOKExecution.reply_state internstate index) (logical_after logical fs)).
  {
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
  }
  destruct Hpartial as [Hstep [Hformulas [HclassesFinal HhistoryFinal]]].
  split;[exact Hstep|].
  split.
  { eapply NativeStateFrames.finish;[exact Hnative|exact Hregistries|exact Hstep|cbn [Protocol.opcode];destruct Hcase;lia|reflexivity|
    exact Hformulas|exact HclassesFinal|exact HhistoryFinal]. }
  { eapply reply_ok_boundary;[exact Htail|exact Hstdout| |exact Hpostbuffer|exact Hflag| |].
    + rewrite (Harrays arraydef_0__token ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
      unfold arg. rewrite read_two_token_length. exact Htoken.
    + rewrite Hcells by lia. unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta;lia). reflexivity.
    + exact (intern_growth arg internstate _ _ _ fs Harg_arena Hseconderror Hbound Hintern Hnext).
  }
Qed.
End Atoms.


Module Imp.
Import IndexExecution SipHashExecution.
Definition logical_after logical fs := Protocol.State fs (Protocol.classes logical) (Protocol.history logical)
  (Protocol.bindings logical) (Protocol.expressions logical).
Lemma decoded meaning a b p q : nth_error meaning a = Some p -> nth_error meaning b = Some q ->
  FormulaEncoding.decode meaning (3,Z.of_nat a,Z.of_nat b) = Some (SetTheory.implies p q).
Proof. intros Ha Hb. unfold FormulaEncoding.decode. now rewrite !Nat2Z.id, Ha, Hb. Qed.
Lemma reference s meaning value p : NativeRepresentation.canonical_arena s meaning -> nth_error meaning value = Some p ->
  Z.of_nat value < meta_value s 1.
Proof.
  intros Harena Hlookup. pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
  change (meta_value s 1 = Z.of_nat (length meaning)) in Hcount.
  assert (Hindex : (value < length meaning)%nat) by (apply nth_error_Some; congruence).
  rewrite Hcount. lia.
Qed.
Lemma requested logical a b p q : Protocol.formula_at logical a = Some p -> Protocol.formula_at logical b = Some q ->
  Protocol.formula_request logical (Protocol.Req 3 [a;b] []) (SetTheory.implies p q).
Proof. intros Ha Hb. now apply Protocol.req_imp with (p := p) (q := q). Qed.
Theorem generated_protocol ch chars s logical bs ns a b p q first_separator middle last tail observations :
  decimalBytes 3%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  Protocol.formula_at logical a = Some p -> Protocol.formula_at logical b = Some q ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 3 [a;b] []) (Protocol.OK index) (logical_after logical fs) /\
    NativeState.represents final (logical_after logical fs) /\
    boundary s logical final (Protocol.OK index) (logical_after logical fs) tail.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb HlookupA HlookupB Hnative Hsep1 Hsep2 Hsep3 Hin.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  assert (Hcode : Z.of_nat 3 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _ => false) (fun _ => 0) 3 ch chars a b first_separator middle last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin) as Hread.
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
Theorem generated_rejected_protocol ch chars s logical bs ns a b first_separator middle last tail observations :
  decimalBytes 3%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  (Protocol.formula_at logical a = None \/ Protocol.formula_at logical b = None) ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 3 [a;b] []) Protocol.NO logical /\
    NativeState.represents final logical /\
    boundary s logical final Protocol.NO logical tail.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb Hbad Hnative Hsep1 Hsep2 Hsep3 Hin.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  assert (Hcode : Z.of_nat 3 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _ => false) (fun _ => 0) 3 ch chars a b first_separator middle last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin) as Hread.
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
Theorem generated_total_protocol ch chars s logical bs ns a b first_separator middle last tail observations :
  decimalBytes 3%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 3 [a;b] []) reply next /\
    NativeState.represents final next /\
    boundary s logical final reply next tail.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb Hnative Hsep1 Hsep2 Hsep3 Hin.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  destruct (Protocol.formula_at logical a) as [p|] eqn:HlookupA.
  - destruct (Protocol.formula_at logical b) as [q|] eqn:HlookupB.
    + destruct (generated_protocol ch chars s logical bs ns a b p q first_separator middle last tail observations
        Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb HlookupA HlookupB Hnative Hsep1 Hsep2 Hsep3 Hin)
        as [final [index [fs Hrun]]].
      exists final,(Protocol.OK index),(logical_after logical fs). exact Hrun.
    + destruct (generated_rejected_protocol ch chars s logical bs ns a b first_separator middle last tail observations
        Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb (or_intror HlookupB) Hnative Hsep1 Hsep2 Hsep3 Hin) as [final Hrun].
      exists final,Protocol.NO,logical. exact Hrun.
  - destruct (generated_rejected_protocol ch chars s logical bs ns a b first_separator middle last tail observations
      Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb (or_introl HlookupA) Hnative Hsep1 Hsep2 Hsep3 Hin) as [final Hrun].
    exists final,Protocol.NO,logical. exact Hrun.
Qed.
End Imp.


Module All.
Import IndexExecution SipHashExecution.
Definition logical_after logical fs := Protocol.State fs (Protocol.classes logical) (Protocol.history logical)
  (Protocol.bindings logical) (Protocol.expressions logical).
Definition argument_state s value sep tail := ReadOne.argument_state s 52 [] value sep tail.
Theorem generated_protocol s logical bs ns value p first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 53 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 -> Z.of_nat value <= maximum ->
  Protocol.formula_at logical value = Some p ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 4 [value] []) (Protocol.OK index) (logical_after logical fs) /\
    NativeState.represents final (logical_after logical fs) /\
    boundary s logical final (Protocol.OK index) (logical_after logical fs) tail.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hvalue Hlookup Hnative Hsep1 Hsep2 Hin.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  assert (Hfour : Z.of_nat 4 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadOne.generated_reads s (fun _ => false) (fun _ => 0) 4 52 [] value first_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hfour eq_refl Hvalue Hsep1 Hsep2 Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  set (arg := argument_state s value last_separator tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadOne.argument_storage s 52 [] value last_separator tail Hmeta) Harena). }
  assert (Hreference : Z.of_nat value < meta_value arg 1).
  { pose proof (proj1 (proj2 (proj1 Harg_arena))) as Hcount.
    change (meta_value arg 1 = Z.of_nat (length (Protocol.formulas logical))) in Hcount.
    assert (Hindex : (value < length (Protocol.formulas logical))%nat).
    { apply nth_error_Some. unfold Protocol.formula_at in Hlookup. congruence. }
    rewrite Hcount. lia. }
  assert (Hnormal : FormulaEncoding.normal (4,Z.of_nat value,0)).
  { right. right. repeat split; try reflexivity; try unfold word; lia. }
  assert (Hdecode : FormulaEncoding.decode (Protocol.formulas logical) (4,Z.of_nat value,0) = Some (SetTheory.all p)).
  { change (option_map SetTheory.all (nth_error (Protocol.formulas logical) (Z.to_nat (Z.of_nat value))) = Some (SetTheory.all p)).
    unfold Protocol.formula_at in Hlookup. now rewrite Nat2Z.id, Hlookup. }
  destruct (InternBounded.generated_refines arg (fun _ => false) (FormulaAllExecution.arguments (Z.of_nat value))
    (Protocol.formulas logical) (SetTheory.all p) Harg_arena Hargerror Hbound Hnormal Hdecode)
    as [internstate [fs [index [Hintern [Hframe [Hflag [Hresult [Hword [Hnext [Hformula Hextends]]]]]]]]]].
  assert (Hobserved : execObserved (funcdef_0__intern (fun _ => false) (FormulaAllExecution.arguments (Z.of_nat value)))
    (arg,observations) = Some (tt,(internstate,observations))).
  { apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern]. }
  pose proof Hframe as [Harrays [Hcells [Hintern_input Hintern_output]]].
  assert (Hpostmeta : (17 < length (memory internstate arraydef_0__meta))%nat).
  { pose proof (proj1 (proj1 (proj1 Hnext))) as Hcapacity. lia. }
  assert (Hpostbuffer : (20 <= length (memory internstate arraydef_0__printBuffer))%nat).
  { rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
    exact Hargbuffer. }
  pose proof (FormulaAllExecution.generated_command s bs ns _ arg internstate index (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference Hobserved Hpostmeta Hpostbuffer Hflag Hresult Hword) as Hrun.
  assert (Htail : stdin internstate = tail) by (rewrite Hintern_input; exact Hinput).
  assert (Hstdout : stdout internstate = stdout s) by (rewrite Hintern_output; exact Houtput).
  rewrite Htail, Hstdout in Hrun.
  assert (Hregistries : NativeStateFrames.registries s (ReplyOKExecution.reply_state internstate index)).
  { eapply NativeStateFrames.trans.
    - exact (NativeStateFrames.read_one s 52 [] value last_separator tail Hmeta).
    - eapply NativeStateFrames.trans;[exact (NativeStateFrames.intern _ _ Hframe)|apply NativeStateFrames.reply_ok]. }
  exists (ReplyOKExecution.reply_state internstate index),index,fs. split; [exact Hrun|].
  assert (Hpartial :
    Protocol.step logical (Protocol.Req 4 [value] []) (Protocol.OK index) (logical_after logical fs) /\
    NativeRepresentation.canonical_arena (ReplyOKExecution.reply_state internstate index) fs /\
    ClassStorage.represents (ReplyOKExecution.reply_state internstate index) fs (Protocol.classes logical) /\
    HistoryRefinement.represents (ReplyOKExecution.reply_state internstate index) (logical_after logical fs)).
  {
  assert (Hunique : NoDup fs) by (now apply (SemanticFrames.arena_NoDup internstate)).
  destruct Hextends as [extra Hextends]. split.
  - eapply Protocol.step_accept with (t := logical_after logical fs).
    + eapply Protocol.accept_formula with (p := SetTheory.all p).
      * apply Protocol.req_all with (p := p). exact Hlookup.
      * split; [now exists extra|]. split; [exact Hunique|]. split; [exact Hformula|]. exists []; now rewrite app_nil_r.
    + apply HistoryRefinement.retained_refl. exact Hunique.
  - split; [exact (FormulaProjection.storage_arena internstate _ fs (FormulaProjection.reply_storage internstate index) Hnext)|].
    split.
    + apply SemanticFrames.reply_classes. rewrite Hextends. apply (SemanticFrames.intern_classes arg internstate); [exact Hframe|].
      destruct Hclasses as [Hcount Hclassarray]. split.
      * unfold arg, argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount.
      * unfold arg, argument_state. rewrite ReadOne.argument_other by discriminate. exact Hclassarray.
    + apply SemanticFrames.reply_history. apply (SemanticFrames.intern_history arg internstate); [exact Hframe|].
      destruct Hhistory as [Hcount Hprefix]. split.
      * unfold arg, argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount.
      * unfold arg, argument_state. rewrite ReadOne.argument_other by discriminate. exact Hprefix.
  }
  destruct Hpartial as [Hstep [Hformulas [HclassesFinal HhistoryFinal]]].
  split;[exact Hstep|].
  split.
  { eapply NativeStateFrames.finish;[exact Hnative|exact Hregistries|exact Hstep|discriminate|reflexivity|
    exact Hformulas|exact HclassesFinal|exact HhistoryFinal]. }
  { eapply reply_ok_boundary;[exact Htail|exact Hstdout| |exact Hpostbuffer|exact Hflag| |].
    + rewrite (Harrays arraydef_0__token ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
      unfold arg, argument_state. rewrite read_one_token_length. exact Htoken.
    + rewrite Hcells by lia. unfold arg, argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta;lia). reflexivity.
    + exact (intern_growth arg internstate _ _ _ fs Harg_arena Hargerror Hbound Hintern Hnext).
  }
Qed.
Definition rejected s value sep tail := ReplyNOExecution.reply_state (argument_state s value sep tail).
Theorem generated_rejected s bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 53 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> meta_value s 1 <= Z.of_nat value ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(rejected s value last_separator tail,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hreference Hsep1 Hsep2 Hin.
  assert (Hsix : Z.of_nat 4 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadOne.generated_reads s (fun _ => false) (fun _ => 0) 4 52 [] value first_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hsix eq_refl Hvalue Hsep1 Hsep2 Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  assert (Hargreference : meta_value (argument_state s value last_separator tail) 1 <= Z.of_nat value).
  { unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hreference. }
  pose proof (FormulaAllExecution.generated_rejected_command s bs ns _ _ (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hargreference) as Hrun.
  rewrite Hinput, Houtput in Hrun. exact Hrun.
Qed.
Lemma argument_represents s meaning classes value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> ClassStorage.represents s meaning classes ->
  ClassStorage.represents (argument_state s value sep tail) meaning classes.
Proof.
  intros Hmeta [Hcount Hclasses]. split.
  - unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount.
  - unfold argument_state. rewrite ReadOne.argument_other by discriminate. exact Hclasses.
Qed.
Lemma rejected_represents s meaning classes value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> ClassStorage.represents s meaning classes ->
  ClassStorage.represents (rejected s value sep tail) meaning classes.
Proof. exact (argument_represents s meaning classes value sep tail). Qed.
Lemma rejected_arena s meaning value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> NativeRepresentation.canonical_arena s meaning ->
  NativeRepresentation.canonical_arena (rejected s value sep tail) meaning.
Proof.
  intros Hmeta Harena. apply (ArenaFrame.storage_arena s (rejected s value sep tail) meaning); [|exact Harena].
  exact (ArenaFrame.storage_trans s (argument_state s value sep tail) _
    (ReadOne.argument_storage s 52 [] value sep tail Hmeta) (ArenaFrame.storage_output _ _)).
Qed.
Theorem logical_rejected logical value : Protocol.formula_at logical value = None ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 4 [value] []) Protocol.NO logical.
Proof.
  intros Hlookup Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H; subst; congruence end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.formula_at logical value = Some _ |- _ => congruence end].
Qed.
Lemma rejected_history s logical value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> HistoryRefinement.represents s logical ->
  HistoryRefinement.represents (rejected s value sep tail) logical.
Proof.
  intros Hmeta [Hcount Hprefix]. split.
  - change (meta_value (ReadOne.argument_state s 52 [] value sep tail) 3 = Z.of_nat (length (Protocol.history logical))).
    rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount.
  - change (firstn (length (Protocol.history logical))
      (memory (ReadOne.argument_state s 52 [] value sep tail) arraydef_0__theorems) = map Z.of_nat (Protocol.history logical)).
    rewrite ReadOne.argument_other by discriminate. exact Hprefix.
Qed.
Theorem generated_rejected_protocol s logical bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 53 -> meta_value s 8 = 0 -> Z.of_nat value <= maximum ->
  Protocol.formula_at logical value = None -> NoDup (Protocol.formulas logical) ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 4 [value] []) Protocol.NO logical /\
    NativeState.represents final logical /\
    boundary s logical final Protocol.NO logical tail.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Hunique Hnative Hsep1 Hsep2 Hin.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  assert (Hreference : meta_value s 1 <= Z.of_nat value).
  { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
    change (meta_value s 1 = Z.of_nat (length (Protocol.formulas logical))) in Hcount.
    pose proof Hlookup as Hindex. unfold Protocol.formula_at in Hindex. apply nth_error_None in Hindex.
    rewrite Hcount. lia. }
  assert (Hregistries : NativeStateFrames.registries s (rejected s value last_separator tail)).
  { eapply NativeStateFrames.trans;[exact (NativeStateFrames.read_one s 52 [] value last_separator tail Hmeta)|apply NativeStateFrames.reply_no]. }
  exists (rejected s value last_separator tail). split.
  - exact (generated_rejected s bs ns value first_separator last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hvalue Hreference Hsep1 Hsep2 Hin).
  - 
  assert (Hpartial :
    Protocol.step logical (Protocol.Req 4 [value] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena (rejected s value last_separator tail) (Protocol.formulas logical) /\
    ClassStorage.represents (rejected s value last_separator tail) (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents (rejected s value last_separator tail) logical).
  {split; [now apply logical_rejected|]. split; [now apply rejected_arena|].
    split; [now apply rejected_represents|now apply rejected_history].
  }
  destruct Hpartial as [Hstep [Hformulas [HclassesFinal HhistoryFinal]]].
  split;[exact Hstep|].
  split.
  { eapply NativeStateFrames.finish;[exact Hnative|exact Hregistries|exact Hstep|discriminate|reflexivity|
    exact Hformulas|exact HclassesFinal|exact HhistoryFinal]. }
  { unfold rejected. eapply reply_no_boundary.
    + reflexivity.
    + unfold argument_state,ReadOne.argument_state.
      rewrite (proj2 (proj2 (DecimalInput.encoded_result_correct _ value tail ltac:(rewrite ReadOne.opcode_meta_length;exact Hmeta) Hvalue))).
      unfold ReadOne.opcode_state. apply CommandInput.parsed_output.
    + unfold argument_state. rewrite read_one_token_length. exact Htoken.
    + unfold argument_state. rewrite ReadOne.argument_other by discriminate. exact Hbuffer.
    + unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta;lia). exact Herror.
    + unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta;lia). reflexivity.
  }
Qed.
Theorem generated_total_protocol s logical bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 53 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 -> Z.of_nat value <= maximum ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 4 [value] []) reply next /\
    NativeState.represents final next /\
    boundary s logical final reply next tail.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hvalue Hnative Hsep1 Hsep2 Hin.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  destruct (Protocol.formula_at logical value) as [p|] eqn:Hlookup.
  - destruct (generated_protocol s logical bs ns value p first_separator last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hbound Hvalue Hlookup Hnative Hsep1 Hsep2 Hin)
      as [final [index [fs Hrun]]].
    exists final,(Protocol.OK index),(logical_after logical fs). exact Hrun.
  - pose proof (SemanticFrames.arena_NoDup s (Protocol.formulas logical) Harena) as Hunique.
    destruct (generated_rejected_protocol s logical bs ns value first_separator last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Hunique Hnative Hsep1 Hsep2 Hin)
      as [final Hrun].
    exists final,Protocol.NO,logical. exact Hrun.
Qed.
End All.

Import IndexExecution SipHashExecution.
(** The common session-facing interface uses any separator accepted by the
    parser and one or two unsigned decimal arguments, according to the opcode. *)
Definition simple_request opcode (values:list nat) :=
 ((opcode=1%nat \/ opcode=2%nat \/ opcode=3%nat) /\ exists a b,values=[a;b]) \/
 (opcode=4%nat /\ exists value,values=[value]).
Fixpoint argument_bytes (values:list nat) (separator:Z) (tail:list Z) := match values with
 | []=>tail
 | value::rest=>decimalBytes value++separator::argument_bytes rest separator tail
 end.
Definition argument_input values middle last tail := match values with
 | [a;b]=>decimalBytes a++middle::decimalBytes b++last::tail
 | [value]=>decimalBytes value++last::tail
 | _=>tail end.
Theorem generated_boundary opcode values ch chars s logical bs ns first_separator middle last tail observations :
 simple_request opcode values -> decimalBytes opcode=ch::chars ->
 (17<length(memory s arraydef_0__meta))%nat ->
 (1024<=length(memory s arraydef_0__token))%nat ->
 (20<=length(memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 ->
 Z.of_nat(length(Protocol.formulas logical))<=9223372036854775807 ->
 Forall (fun value=>Z.of_nat value<=maximum) values ->
 NativeState.represents s logical -> TokenByteExecution.separator first_separator ->
 TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
 stdin s=chars++first_separator::argument_input values middle last tail ->
 exists final reply next,
  execObserved (funcdef_0__command bs ns) (s,observations)=Some(tt,(final,
   observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
  Protocol.step logical (Protocol.Req opcode values []) reply next /\
  NativeState.represents final next /\ boundary s logical final reply next tail.
Proof.
 intros Hshape Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Hvalues Hnative Hsep1 Hsep2 Hsep3 Hin.
 destruct Hshape as [[Htag [a [b Hargs]]]|[Htag [value Hargs]]];subst values.
 - inversion Hvalues as [|a' rest Ha Hrest];subst.
   inversion Hrest as [|b' rest' Hb Hnil];subst.
   destruct Htag as [Hone|[Htwo|Hthree]].
   + destruct (Atoms.generated_protocol opcode ch chars s logical bs ns a b first_separator middle last tail observations
       (or_introl Hone) Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb Hnative Hsep1 Hsep2 Hsep3 Hin)
       as [final [index [fs Hrun]]].
     exists final,(Protocol.OK index),(Atoms.logical_after logical fs). exact Hrun.
   + destruct (Atoms.generated_protocol opcode ch chars s logical bs ns a b first_separator middle last tail observations
       (or_intror Htwo) Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb Hnative Hsep1 Hsep2 Hsep3 Hin)
       as [final [index [fs Hrun]]].
     exists final,(Protocol.OK index),(Atoms.logical_after logical fs). exact Hrun.
   + subst opcode. exact (Imp.generated_total_protocol ch chars s logical bs ns a b first_separator middle last tail observations
       Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb Hnative Hsep1 Hsep2 Hsep3 Hin).
 - subst opcode. inversion Hvalues as [|value' rest Hvalue Hnil];subst.
   change (52::[]=ch::chars) in Hencoding. injection Hencoding as Hch Hchars.
   rewrite <-Hch in Hpending. rewrite <-Hchars in Hin.
   exact (All.generated_total_protocol s logical bs ns value first_separator last tail observations
     Hmeta Htoken Hbuffer Hpending Herror Hbound Hvalue Hnative Hsep1 Hsep3 Hin).
Qed.
Theorem generated_protocol opcode values ch chars s logical bs ns separator tail observations :
 simple_request opcode values -> decimalBytes opcode=ch::chars ->
 (17<length(memory s arraydef_0__meta))%nat ->
 (1024<=length(memory s arraydef_0__token))%nat ->
 (20<=length(memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 ->
 Z.of_nat(length(Protocol.formulas logical))<=9223372036854775807 ->
 Forall (fun value=>Z.of_nat value<=maximum) values ->
 NativeState.represents s logical -> TokenByteExecution.separator separator ->
 stdin s=chars++separator::argument_bytes values separator tail ->
 exists final reply next,
  execObserved (funcdef_0__command bs ns) (s,observations)=Some(tt,(final,
   observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
  Protocol.step logical (Protocol.Req opcode values []) reply next /\
  NativeState.represents final next.
Proof.
 intros Hshape Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Hvalues Hnative Hseparator Hin.
 assert (Hinput:stdin s=chars++separator::argument_input values separator separator tail).
 { destruct Hshape as [[Htag [a [b Hargs]]]|[Htag [value Hargs]]];subst values;exact Hin. }
 destruct (generated_boundary opcode values ch chars s logical bs ns separator separator separator tail observations
   Hshape Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Hvalues Hnative Hseparator Hseparator Hseparator Hinput)
   as [final [reply [next [Hrun [Hstep [Hrep Hboundary]]]]]].
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|exact Hrep].
Qed.
End NativeSimpleCommands.
