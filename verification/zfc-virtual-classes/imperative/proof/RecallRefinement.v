From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadName NameQueryState TypedNameLookup NameRepresentation BindNameRefinement NameSearch ArenaFrame FormulaProjection Representation ClassStorage HistoryRefinement SemanticFrames CommandRecall LogicalNames LogicalHistory.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RecallRefinement.
Import IndexExecution SipHashExecution.
Definition answer logical meaning := match meaning with Some (Protocol.theorem_binding _) => Protocol.OK (length (Protocol.history logical)) | _ => Protocol.NO end.
Definition after logical meaning := match meaning with Some (Protocol.theorem_binding fid) => Protocol.with_history logical (Protocol.history logical ++ [fid]) | _ => logical end.
Lemma reply_typed logical meaning : CommandRecallExecution.reply true (TypedNameLookup.binding_kind meaning) (length (Protocol.history logical)) = answer logical (Some meaning).
Proof. destruct meaning; reflexivity. Qed.
Lemma after_typed logical meaning : CommandRecallExecution.history_after logical true (TypedNameLookup.binding_kind meaning) (TypedNameLookup.binding_value meaning) = after logical (Some meaning).
Proof. destruct meaning; reflexivity. Qed.
Lemma logical_rejected logical name :
  (forall id, Protocol.lookup name (Protocol.bindings logical) <> Some (Protocol.theorem_binding id)) ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 21 [] name) Protocol.NO logical.
Proof.
  intros Hmissing Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H; subst end].
  eapply Hmissing; eassumption.
Qed.
Lemma logical_total logical name : LogicalNames.valid logical -> NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req 21 [] name) (answer logical (Protocol.lookup name (Protocol.bindings logical)))
    (after logical (Protocol.lookup name (Protocol.bindings logical))).
Proof.
  intros Hvalid Hunique. unfold answer,after. destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hlookup;
    [destruct meaning as [id flag|id|root]|].
  - apply logical_rejected; [intros; congruence|exact Hunique].
  - destruct (LogicalNames.lookup_valid logical name _ Hvalid Hlookup) as [p Hp].
    eapply Protocol.step_accept with (t := Protocol.with_history logical (Protocol.history logical ++ [id])).
    + eapply Protocol.accept_proof with (p := p).
      * now apply (Protocol.req_recall logical name id p).
      * split; [exists []; now rewrite app_nil_r|]. split; [exact Hunique|]. split; [exact Hp|]. exists []; now rewrite app_nil_r.
    + apply HistoryRefinement.retained_refl. exact Hunique.
  - apply logical_rejected; [intros; congruence|exact Hunique].
  - apply logical_rejected; [intros; congruence|exact Hunique].
Qed.
Theorem generated_total_protocol s logical bs ns name first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 51 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> LogicalNames.valid logical -> LogicalHistory.valid logical ->
  Protocol.valid_name name -> NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  NameRepresentation.represents s (Protocol.bindings logical) ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 49 :: first_separator :: name ++ last_separator :: tail ->
  exists final, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (answer logical (Protocol.lookup name (Protocol.bindings logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 21 [] name) (answer logical (Protocol.lookup name (Protocol.bindings logical))) (after logical (Protocol.lookup name (Protocol.bindings logical))) /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final (after logical (Protocol.lookup name (Protocol.bindings logical))) /\ NameRepresentation.represents final (Protocol.bindings logical).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hhistoryroom Hnamesvalid Hhistoryvalid Hvalid Harena Hclasses Hhistory Hbindings Hsep1 Hsep2 Hin.
  destruct (ReadName.generated_reads s 21 50 [49] name first_separator last_separator tail observations Hmeta Htoken Hpending Herror
    ltac:(unfold maximum; lia) eq_refl Hvalid Hsep1 Hsep2 Hin)
    as [Hopcode [Hread [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hnamedmeta [Hnamevalid [Hnameerror [Hnametoken [Hinput Houtput]]]]]]]]]]].
  set (op := ReadName.opcode_state s 50 [49] name last_separator tail).
  set (parsed := ReadName.name_state s 50 [49] name last_separator tail).
  change (17 < length (memory parsed arraydef_0__meta))%nat in Hnamedmeta.
  change (NameRepresentation.token_rep parsed name) in Hnametoken.
  change (meta_value parsed 8 = 0) in Hnameerror.
  change (stdin parsed = tail) in Hinput. change (stdout parsed = stdout s) in Houtput.
  pose proof (NameQueryState.bindings s 50 [49] name last_separator tail _ Hmeta Hbindings) as Hparsedbindings.
  assert (Hparsedarena : NativeRepresentation.canonical_arena parsed (Protocol.formulas logical))
    by exact (ArenaFrame.storage_arena s parsed _ (NameQueryState.storage s 50 [49] name last_separator tail Hmeta) Harena).
  pose proof (NameQueryState.classes s 50 [49] name last_separator tail _ _ Hmeta Hclasses) as Hparsedclasses.
  pose proof (NameQueryState.history s 50 [49] name last_separator tail logical Hmeta Hhistory) as Hparsedhistory.
  destruct (TypedNameLookup.generated parsed (fun _ => false) (fun _ => 0) (Protocol.bindings logical) name observations
    ltac:(lia) Hparsedbindings Hnametoken) as [looked [Hlookup [Hlookbindings [Hlength [Hframe Houtcome]]]]].
  pose proof Hframe as [Harrays [Hcells [Hlookinput Hlookoutput]]].
  assert (Hlookmeta : (17 < length (memory looked arraydef_0__meta))%nat) by (now rewrite Hlength).
  assert (Hlookerror : meta_value looked 8 = 0) by (rewrite Hcells by lia; exact Hnameerror).
  assert (Hlookbuffer : (20 <= length (memory looked arraydef_0__printBuffer))%nat).
  { rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate)). unfold parsed. now rewrite ReadName.name_other by discriminate. }
  assert (Hlookarena : NativeRepresentation.canonical_arena looked (Protocol.formulas logical))
    by exact (FormulaProjection.storage_arena parsed looked _ (BindNameRefinement.lookup_projection parsed looked Hframe Hlength) Hparsedarena).
  pose proof (BindNameRefinement.lookup_classes parsed looked _ _ Hframe Hparsedclasses) as Hlookclasses.
  pose proof (BindNameRefinement.lookup_history parsed looked logical Hframe Hparsedhistory) as Hlookhistory.
  assert (Hlookcount : meta_value looked 3 = Z.of_nat (length (Protocol.history logical))) by exact (proj1 Hlookhistory).
  pose proof (logical_total logical name Hnamesvalid (SemanticFrames.arena_NoDup s _ Harena)) as Hlogical.
  unfold TypedNameLookup.outcome in Houtcome.
  destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hmeaning.
  - destruct Houtcome as [index [raw [Hresult [Hindex [Hbound [Hnth Hrecord]]]]]].
    destruct raw as [[[[offset size] value] flag] kind].
    destruct Hrecord as [Hsize [Hoffset [Hoffsetword [Hword [Hflag [Hspan [Hbytes [Hdecode Hvalidname]]]]]]]].
    pose proof (TypedNameLookup.decode_kind value flag kind meaning Hdecode) as Hkind.
    pose proof (TypedNameLookup.decode_value value flag kind meaning Hword Hdecode) as Hvalue.
    subst kind value.
    pose proof (CommandRecallExecution.generated_command s bs ns op parsed looked true index offset size
      (length (Protocol.history logical)) (TypedNameLookup.binding_value meaning) flag (TypedNameLookup.binding_kind meaning) observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hnamevalid Hnameerror Hlookup Hlookmeta Hresult Hindex
      (fun _ => Hbound) (fun _ => Hnth) Hlookbuffer (proj2 Hword) Hlookcount Hhistoryroom Hlookerror) as Hrun.
    rewrite (reply_typed logical meaning),Hlookinput,Hlookoutput,Hinput,Houtput in Hrun.
    exists (CommandRecallExecution.result looked true (TypedNameLookup.binding_kind meaning) (length (Protocol.history logical)) (TypedNameLookup.binding_value meaning)).
    split; [exact Hrun|]. split; [exact Hlogical|]. split.
    + exact (FormulaProjection.storage_arena looked _ _ (CommandRecallExecution.result_projection looked true _ _ _) Hlookarena).
    + split; [now apply CommandRecallExecution.result_classes|]. split.
      * rewrite <-(after_typed logical meaning). apply CommandRecallExecution.result_history; [lia|exact Hlookhistory].
      *
      now apply CommandRecallExecution.result_bindings.
  - pose proof (CommandRecallExecution.generated_command s bs ns op parsed looked false 0 0 0 (length (Protocol.history logical)) 0 0 0 observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hnamevalid Hnameerror Hlookup Hlookmeta Houtcome
      ltac:(unfold maximum; lia) ltac:(discriminate) ltac:(discriminate) Hlookbuffer ltac:(unfold maximum; lia) Hlookcount Hhistoryroom Hlookerror) as Hrun.
    rewrite Hlookinput,Hlookoutput,Hinput,Houtput in Hrun.
    exists (CommandRecallExecution.result looked false 0 (length (Protocol.history logical)) 0). split; [exact Hrun|]. split; [exact Hlogical|]. split.
    + exact (FormulaProjection.storage_arena looked _ _ (CommandRecallExecution.result_projection looked false 0 (length (Protocol.history logical)) 0) Hlookarena).
    + split; [now apply CommandRecallExecution.result_classes|]. split.
      * exact Hlookhistory.
      * now apply CommandRecallExecution.result_bindings.
Qed.
End RecallRefinement.
