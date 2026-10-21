From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Schemata.
From NativeProof Require Import Index SipHash TokenByte ReadName NameQueryState TypedNameLookup NameRepresentation BindNameRefinement NameSearch ArenaFrame FormulaProjection Representation ClassStorage HistoryRefinement SemanticFrames CommandArity LogicalNames SchemaMetadata.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ArityRefinement.
Import IndexExecution SipHashExecution.
Definition answer logical meaning := match meaning with Some (Protocol.schema_binding root) =>
  match Protocol.pf logical root with Some cert => Protocol.OK (Schemata.proof_arity cert) | None => Protocol.NO end | _ => Protocol.NO end.
Lemma logical_rejected logical name :
  (forall id, Protocol.lookup name (Protocol.bindings logical) <> Some (Protocol.schema_binding id)) ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 26 [] name) Protocol.NO logical.
Proof.
  intros Hmissing Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end
      |eapply Hmissing; eassumption].
Qed.
Lemma logical_total logical name : LogicalNames.valid logical -> NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req 26 [] name) (answer logical (Protocol.lookup name (Protocol.bindings logical))) logical.
Proof.
  intros Hvalid Hunique. unfold answer. destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hlookup;
    [destruct meaning as [id flag|id|root]|].
  - apply logical_rejected; [intros; congruence|exact Hunique].
  - apply logical_rejected; [intros; congruence|exact Hunique].
  - destruct (LogicalNames.lookup_valid logical name _ Hvalid Hlookup) as [cert Hcert]. rewrite Hcert.
    eapply Protocol.step_accept; [eapply Protocol.accept_arity; eassumption|now apply HistoryRefinement.retained_refl].
  - apply logical_rejected; [intros; congruence|exact Hunique].
Qed.
Lemma native_arguments native logical name meaning : LogicalNames.valid logical -> SchemaMetadata.represents native (Protocol.expressions logical) ->
  Protocol.lookup name (Protocol.bindings logical) = Some meaning ->
  exists width, Z.of_nat width <= maximum /\
    (TypedNameLookup.binding_kind meaning = 2%Z -> TypedNameLookup.binding_value meaning < length (memory native arraydef_0__schemaNodes))%nat /\
    (TypedNameLookup.binding_kind meaning = 2 -> snd (SchemaMetadata.node_at native (TypedNameLookup.binding_value meaning)) = Z.of_nat width) /\
    CommandArityExecution.reply true (TypedNameLookup.binding_kind meaning) width = answer logical (Some meaning).
Proof.
  intros Hvalid Hrep Hlookup. destruct meaning as [id flag|id|root].
  - exists 0%nat. split; [unfold maximum; cbn; lia|]. split; [discriminate|]. split; [discriminate|reflexivity].
  - exists 0%nat. split; [unfold maximum; cbn; lia|]. split; [discriminate|]. split; [discriminate|reflexivity].
  - destruct (LogicalNames.lookup_valid logical name _ Hvalid Hlookup) as [cert Hcert].
    destruct (SchemaMetadata.proof_fields native logical root cert Hrep Hcert) as [Hbound [Htype [Hwidth Hword]]].
    exists (Schemata.proof_arity cert). split; [exact Hword|]. split; [intros _; exact Hbound|]. split; [intros _; exact Hwidth|].
    unfold answer. rewrite Hcert. reflexivity.
Qed.
Lemma result_schemas native found kind width expressions :
  SchemaMetadata.represents native expressions ->
  SchemaMetadata.represents (CommandArityExecution.result native found kind width) expressions.
Proof.
  intros Hrep. eapply SchemaMetadata.transport; [apply CommandArityExecution.result_meta| |exact Hrep].
  apply CommandArityExecution.result_other. discriminate.
Qed.
Theorem generated_total_protocol s logical bs ns name first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 51 -> meta_value s 8 = 0 ->
  LogicalNames.valid logical -> SchemaMetadata.represents s (Protocol.expressions logical) ->
  Protocol.valid_name name -> NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  NameRepresentation.represents s (Protocol.bindings logical) ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 54 :: first_separator :: name ++ last_separator :: tail ->
  exists final, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (answer logical (Protocol.lookup name (Protocol.bindings logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 26 [] name) (answer logical (Protocol.lookup name (Protocol.bindings logical))) logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final logical /\ NameRepresentation.represents final (Protocol.bindings logical) /\
    SchemaMetadata.represents final (Protocol.expressions logical).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hnamesvalid Hschemas Hvalid Harena Hclasses Hhistory Hbindings Hsep1 Hsep2 Hin.
  destruct (ReadName.generated_reads s 26 50 [54] name first_separator last_separator tail observations Hmeta Htoken Hpending Herror
    ltac:(unfold maximum; lia) eq_refl Hvalid Hsep1 Hsep2 Hin)
    as [Hopcode [Hread [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hnamedmeta [Hnamevalid [Hnameerror [Hnametoken [Hinput Houtput]]]]]]]]]]].
  set (op := ReadName.opcode_state s 50 [54] name last_separator tail).
  set (parsed := ReadName.name_state s 50 [54] name last_separator tail).
  change (17 < length (memory parsed arraydef_0__meta))%nat in Hnamedmeta.
  change (NameRepresentation.token_rep parsed name) in Hnametoken.
  change (meta_value parsed 8 = 0) in Hnameerror.
  change (stdin parsed = tail) in Hinput. change (stdout parsed = stdout s) in Houtput.
  pose proof (NameQueryState.bindings s 50 [54] name last_separator tail _ Hmeta Hbindings) as Hparsedbindings.
  assert (Hparsedarena : NativeRepresentation.canonical_arena parsed (Protocol.formulas logical))
    by exact (ArenaFrame.storage_arena s parsed _ (NameQueryState.storage s 50 [54] name last_separator tail Hmeta) Harena).
  pose proof (NameQueryState.classes s 50 [54] name last_separator tail _ _ Hmeta Hclasses) as Hparsedclasses.
  pose proof (NameQueryState.history s 50 [54] name last_separator tail logical Hmeta Hhistory) as Hparsedhistory.
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
  assert (Hparsedschemas : SchemaMetadata.represents parsed (Protocol.expressions logical)).
  { eapply SchemaMetadata.transport; [| |exact Hschemas].
    - unfold parsed. apply ReadName.name_meta_other; try exact Hmeta; lia.
    - unfold parsed. apply ReadName.name_other; discriminate. }
  assert (Hlookschemas : SchemaMetadata.represents looked (Protocol.expressions logical)).
  { eapply SchemaMetadata.transport; [apply Hcells; lia|apply Harrays; discriminate|exact Hparsedschemas]. }
  pose proof (logical_total logical name Hnamesvalid (SemanticFrames.arena_NoDup s _ Harena)) as Hlogical.
  unfold TypedNameLookup.outcome in Houtcome.
  destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hmeaning.
  - destruct Houtcome as [index [raw [Hresult [Hindex [Hbound [Hnth Hrecord]]]]]].
    destruct raw as [[[[offset size] value] flag] kind].
    destruct Hrecord as [Hsize [Hoffset [Hoffsetword [Hword [Hflag [Hspan [Hbytes [Hdecode Hvalidname]]]]]]]].
    pose proof (TypedNameLookup.decode_kind value flag kind meaning Hdecode) as Hkind.
    pose proof (TypedNameLookup.decode_value value flag kind meaning Hword Hdecode) as Hvalue.
    subst kind value.
    destruct (native_arguments looked logical name meaning Hnamesvalid Hlookschemas Hmeaning)
      as [width [Hwidthword [Hschemaindex [Hschemawidth Hreply]]]].
    pose proof (CommandArityExecution.generated_command s bs ns op parsed looked true index offset size
      (TypedNameLookup.binding_value meaning) flag (TypedNameLookup.binding_kind meaning) width observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hnamevalid Hnameerror Hlookup Hlookmeta Hresult Hindex
      (fun _ => Hbound) (fun _ => Hnth) (fun _ => Hschemaindex) (fun _ => Hschemawidth) Hlookbuffer Hwidthword Hlookerror) as Hrun.
    rewrite Hreply,Hlookinput,Hlookoutput,Hinput,Houtput in Hrun.
    exists (CommandArityExecution.result looked true (TypedNameLookup.binding_kind meaning) width).
    split; [exact Hrun|]. split; [exact Hlogical|]. split.
    + exact (FormulaProjection.storage_arena looked _ _ (CommandArityExecution.result_projection looked true _ _) Hlookarena).
    + split; [now apply CommandArityExecution.result_classes|]. split; [now apply CommandArityExecution.result_history|].
      split; [now apply CommandArityExecution.result_bindings|now apply result_schemas].
  - pose proof (CommandArityExecution.generated_command s bs ns op parsed looked false 0 0 0 0 0 0 0 observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hnamevalid Hnameerror Hlookup Hlookmeta Houtcome
      ltac:(unfold maximum; lia) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hlookbuffer ltac:(unfold maximum; lia) Hlookerror) as Hrun.
    rewrite Hlookinput,Hlookoutput,Hinput,Houtput in Hrun.
    exists (CommandArityExecution.result looked false 0 0). split; [exact Hrun|]. split; [exact Hlogical|]. split.
    + exact (FormulaProjection.storage_arena looked _ _ (CommandArityExecution.result_projection looked false 0 0) Hlookarena).
    + split; [now apply CommandArityExecution.result_classes|]. split; [now apply CommandArityExecution.result_history|].
      split; [now apply CommandArityExecution.result_bindings|now apply result_schemas].
Qed.
End ArityRefinement.
