From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadName NameQueryState TypedNameLookup NameRepresentation BindNameRefinement NameSearch ArenaFrame FormulaProjection Representation ClassStorage HistoryRefinement SemanticFrames CommandLookupClass.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module LookupClassRefinement.
Import IndexExecution SipHashExecution.
Definition answer meaning := match meaning with Some (Protocol.class_binding id _) => Protocol.OK id | _ => Protocol.NO end.
Lemma reply_typed meaning : CommandLookupClassExecution.reply true (TypedNameLookup.binding_kind meaning) (TypedNameLookup.binding_value meaning) = answer (Some meaning).
Proof. destruct meaning; reflexivity. Qed.
Lemma logical_rejected logical name :
  (forall id flag, Protocol.lookup name (Protocol.bindings logical) <> Some (Protocol.class_binding id flag)) ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 10 [] name) Protocol.NO logical.
Proof.
  intros Hmissing Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end
      |eapply Hmissing; eassumption].
Qed.
Lemma logical_total logical name : NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req 10 [] name) (answer (Protocol.lookup name (Protocol.bindings logical))) logical.
Proof.
  intro Hunique. unfold answer. destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hlookup;
    [destruct meaning as [id flag|id|root]|].
  - eapply Protocol.step_accept; [eapply Protocol.accept_lookup; exact Hlookup|now apply HistoryRefinement.retained_refl].
  - apply logical_rejected; [intros; congruence|exact Hunique].
  - apply logical_rejected; [intros; congruence|exact Hunique].
  - apply logical_rejected; [intros; congruence|exact Hunique].
Qed.
Theorem generated_total_protocol s logical bs ns name first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Protocol.valid_name name -> NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  NameRepresentation.represents s (Protocol.bindings logical) ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 48 :: first_separator :: name ++ last_separator :: tail ->
  exists final, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (answer (Protocol.lookup name (Protocol.bindings logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 10 [] name) (answer (Protocol.lookup name (Protocol.bindings logical))) logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final logical /\ NameRepresentation.represents final (Protocol.bindings logical).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalid Harena Hclasses Hhistory Hbindings Hsep1 Hsep2 Hin.
  destruct (ReadName.generated_reads s 10 49 [48] name first_separator last_separator tail observations Hmeta Htoken Hpending Herror
    ltac:(unfold maximum; lia) eq_refl Hvalid Hsep1 Hsep2 Hin)
    as [Hopcode [Hread [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hnamedmeta [Hnamevalid [Hnameerror [Hnametoken [Hinput Houtput]]]]]]]]]]].
  set (op := ReadName.opcode_state s 49 [48] name last_separator tail).
  set (parsed := ReadName.name_state s 49 [48] name last_separator tail).
  change (17 < length (memory parsed arraydef_0__meta))%nat in Hnamedmeta.
  change (NameRepresentation.token_rep parsed name) in Hnametoken.
  change (meta_value parsed 8 = 0) in Hnameerror.
  change (stdin parsed = tail) in Hinput. change (stdout parsed = stdout s) in Houtput.
  pose proof (NameQueryState.bindings s 49 [48] name last_separator tail _ Hmeta Hbindings) as Hparsedbindings.
  assert (Hparsedarena : NativeRepresentation.canonical_arena parsed (Protocol.formulas logical))
    by exact (ArenaFrame.storage_arena s parsed _ (NameQueryState.storage s 49 [48] name last_separator tail Hmeta) Harena).
  pose proof (NameQueryState.classes s 49 [48] name last_separator tail _ _ Hmeta Hclasses) as Hparsedclasses.
  pose proof (NameQueryState.history s 49 [48] name last_separator tail logical Hmeta Hhistory) as Hparsedhistory.
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
  pose proof (logical_total logical name (SemanticFrames.arena_NoDup s _ Harena)) as Hlogical.
  unfold TypedNameLookup.outcome in Houtcome.
  destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hmeaning.
  - destruct Houtcome as [index [raw [Hresult [Hindex [Hbound [Hnth Hrecord]]]]]].
    destruct raw as [[[[offset size] value] flag] kind].
    destruct Hrecord as [Hsize [Hoffset [Hoffsetword [Hword [Hflag [Hspan [Hbytes [Hdecode Hvalidname]]]]]]]].
    pose proof (TypedNameLookup.decode_kind value flag kind meaning Hdecode) as Hkind.
    pose proof (TypedNameLookup.decode_value value flag kind meaning Hword Hdecode) as Hvalue.
    subst kind value.
    pose proof (CommandLookupClassExecution.generated_command s bs ns op parsed looked true index offset size
      (TypedNameLookup.binding_value meaning) flag (TypedNameLookup.binding_kind meaning) observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hnamevalid Hnameerror Hlookup Hlookmeta Hresult Hindex
      (fun _ => Hbound) (fun _ => Hnth) Hlookbuffer (proj2 Hword) Hlookerror) as Hrun.
    rewrite reply_typed,Hlookinput,Hlookoutput,Hinput,Houtput in Hrun.
    exists (CommandLookupClassExecution.result looked true (TypedNameLookup.binding_kind meaning) (TypedNameLookup.binding_value meaning)).
    split; [exact Hrun|]. split; [exact Hlogical|]. split.
    + exact (FormulaProjection.storage_arena looked _ _ (CommandLookupClassExecution.result_projection looked true _ _) Hlookarena).
    + split; [now apply CommandLookupClassExecution.result_classes|]. split; [now apply CommandLookupClassExecution.result_history|].
      now apply CommandLookupClassExecution.result_bindings.
  - pose proof (CommandLookupClassExecution.generated_command s bs ns op parsed looked false 0 0 0 0 0 0 observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hnamevalid Hnameerror Hlookup Hlookmeta Houtcome
      ltac:(unfold maximum; lia) ltac:(discriminate) ltac:(discriminate) Hlookbuffer ltac:(unfold maximum; lia) Hlookerror) as Hrun.
    rewrite Hlookinput,Hlookoutput,Hinput,Houtput in Hrun.
    exists (CommandLookupClassExecution.result looked false 0 0). split; [exact Hrun|]. split; [exact Hlogical|]. split.
    + exact (FormulaProjection.storage_arena looked _ _ (CommandLookupClassExecution.result_projection looked false 0 0) Hlookarena).
    + split; [now apply CommandLookupClassExecution.result_classes|]. split; [now apply CommandLookupClassExecution.result_history|].
      now apply CommandLookupClassExecution.result_bindings.
Qed.
End LookupClassRefinement.
