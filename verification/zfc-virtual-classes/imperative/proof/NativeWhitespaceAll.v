From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash DecimalInput CommandArgs CommandInput ReadOne ReadTwo TokenByte InternBounded Intern Observation
 FormulaEncoding Representation ArenaFrame FormulaProjection ClassStorage HistoryRefinement SemanticFrames
 FormulaAtoms FormulaImp FormulaAll ReplyOK ReplyNO NativeState NativeStateFrames.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From NativeProof Require Import NativeArgumentReads NativeSimpleCommands.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeWhitespaceAll.
Import IndexExecution SipHashExecution NativeSimpleCommands NativeSimpleCommands.All.
Theorem generated_protocol s logical bs ns value p first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 53 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 -> Z.of_nat value <= maximum ->
  Protocol.formula_at logical value = Some p ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 4 [value] []) (Protocol.OK index) (logical_after logical fs) /\
    NativeState.represents final (logical_after logical fs) /\
    boundary s logical final (Protocol.OK index) (logical_after logical fs) tail.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hvalue Hlookup Hnative Hsep1 Hsep2 Hspaces Hin.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  assert (Hfour : Z.of_nat 4 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReads.generated_reads s (fun _ => false) (fun _ => 0) 4 52 [] value first_separator spaces last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hfour eq_refl Hvalue Hsep1 Hsep2 Hspaces Hin) as Hread.
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
Theorem generated_rejected s bs ns value first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 53 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> meta_value s 1 <= Z.of_nat value ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(rejected s value last_separator tail,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hreference Hsep1 Hsep2 Hspaces Hin.
  assert (Hsix : Z.of_nat 4 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReads.generated_reads s (fun _ => false) (fun _ => 0) 4 52 [] value first_separator spaces last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hsix eq_refl Hvalue Hsep1 Hsep2 Hspaces Hin) as Hread.
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
Theorem generated_rejected_protocol s logical bs ns value first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 53 -> meta_value s 8 = 0 -> Z.of_nat value <= maximum ->
  Protocol.formula_at logical value = None -> NoDup (Protocol.formulas logical) ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 4 [value] []) Protocol.NO logical /\
    NativeState.represents final logical /\
    boundary s logical final Protocol.NO logical tail.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Hunique Hnative Hsep1 Hsep2 Hspaces Hin.
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
  - exact (generated_rejected s bs ns value first_separator spaces last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hvalue Hreference Hsep1 Hsep2 Hspaces Hin).
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
Theorem generated_total_protocol s logical bs ns value first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 53 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 -> Z.of_nat value <= maximum ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 4 [value] []) reply next /\
    NativeState.represents final next /\
    boundary s logical final reply next tail.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hvalue Hnative Hsep1 Hsep2 Hspaces Hin.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  destruct (Protocol.formula_at logical value) as [p|] eqn:Hlookup.
  - destruct (generated_protocol s logical bs ns value p first_separator spaces last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hbound Hvalue Hlookup Hnative Hsep1 Hsep2 Hspaces Hin)
      as [final [index [fs Hrun]]].
    exists final,(Protocol.OK index),(logical_after logical fs). exact Hrun.
  - pose proof (SemanticFrames.arena_NoDup s (Protocol.formulas logical) Harena) as Hunique.
    destruct (generated_rejected_protocol s logical bs ns value first_separator spaces last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Hunique Hnative Hsep1 Hsep2 Hspaces Hin)
      as [final Hrun].
    exists final,Protocol.NO,logical. exact Hrun.
Qed.
End NativeWhitespaceAll.
