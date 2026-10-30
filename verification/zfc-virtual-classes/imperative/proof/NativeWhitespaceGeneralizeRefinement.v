From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash ReadOne TokenByte InternBounded Intern Observation FormulaEncoding Representation ArenaFrame ClassStorage HistoryRefinement HistoryLookup HistoryStorage LogicalHistory SemanticFrames Generalize CommandGeneralize ReplyNO.
From NativeProof Require Import NativeArgumentReads.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeWhitespaceGeneralizeRefinement.
Import IndexExecution SipHashExecution.
Definition logical_before_append logical fs := Protocol.State fs (Protocol.classes logical) (Protocol.history logical)
  (Protocol.bindings logical) (Protocol.expressions logical).
Definition logical_after logical fs index := Protocol.with_history (logical_before_append logical fs) (Protocol.history logical ++ [index]).
Definition argument_state s value sep tail := ReadOne.argument_state s 49 [51] value sep tail.
Lemma argument_history s logical value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> HistoryRefinement.represents s logical ->
  HistoryRefinement.represents (argument_state s value sep tail) logical.
Proof.
  intros Hmeta [Hcount Hprefix]. split.
  - unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount.
  - unfold argument_state. rewrite ReadOne.argument_other by discriminate. exact Hprefix.
Qed.
Lemma argument_classes s fs cs value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> ClassStorage.represents s fs cs ->
  ClassStorage.represents (argument_state s value sep tail) fs cs.
Proof.
  intros Hmeta [Hcount Hclasses]. split.
  - unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount.
  - unfold argument_state. rewrite ReadOne.argument_other by discriminate. exact Hclasses.
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
    HistoryRefinement.represents final (logical_after logical fs index).
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
    + exact (HistoryStorage.append_represents internstate (logical_before_append logical fs) index ltac:(lia) Hintern_history).
Qed.
End NativeWhitespaceGeneralizeRefinement.
