From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte ReadName ReadToken CommandInput NameQueryState TypedNameLookup
 NameRepresentation BindNameRefinement NameSearch ArenaFrame FormulaProjection Representation ClassStorage HistoryRefinement SemanticFrames
 CommandLookupClass CommandNameQuery CommandRecall CommandArity LookupClassRefinement NameQueryRefinement RecallRefinement ArityRefinement
 LogicalNames LogicalHistory SchemaMetadata SchemaRepresentation HistoryStorage ReplyOK ReplyNO NativeState NativeSchemaLift NativeCommandLengths.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeQueryCommands.
Import IndexExecution SipHashExecution.
Definition prefix before looked tail := stdin looked=tail /\ stdout looked=stdout before /\
 meta_value looked 8=meta_value before 8 /\ meta_value looked 9=meta_value before 9.
Definition control before after reply tail := stdin after=tail /\
 stdout after=stdout before++Protocol.reply_bytes reply /\
 meta_value after 8=meta_value before 8 /\ meta_value after 9=meta_value before 9.
Definition boundary before after reply tail := stdin after=tail /\
 stdout after=stdout before++Protocol.reply_bytes reply /\
 (1024<=length (memory after arraydef_0__token))%nat /\ (20<=length (memory after arraydef_0__printBuffer))%nat /\
 meta_value after 8=0 /\ meta_value after 9=meta_value before 9.
Lemma lookup_prefix before ch chars name sep tail looked :
 (17<length (memory before arraydef_0__meta))%nat ->
 NameSearchExecution.storage_frame (ReadName.name_state before ch chars name sep tail) looked -> prefix before looked tail.
Proof.
 intros Hmeta [Harrays [Hcells [Hin Hout]]]. split;[exact Hin|]. split.
 - etransitivity;[exact Hout|]. unfold ReadName.name_state.
   rewrite ReadTokenExecution.result_output. apply CommandInput.parsed_output.
 - split;rewrite Hcells by lia;apply ReadName.name_meta_other;try exact Hmeta;lia.
Qed.
Lemma ok_control before looked id tail : prefix before looked tail ->
 control before (ReplyOKExecution.reply_state looked id) (Protocol.OK id) tail.
Proof.
 intros [Hin [Hout [Herror Hstop]]]. unfold control. split;[now rewrite ReplyOKExecution.reply_input|].
 split;[exact (eq_trans (ReplyOKExecution.reply_output looked id) (f_equal (fun bytes=>bytes++Protocol.reply_bytes (Protocol.OK id)) Hout))|].
 unfold meta_value. rewrite ReplyOKExecution.reply_other by discriminate. split;assumption.
Qed.
Lemma no_control before looked tail : prefix before looked tail ->
 control before (ReplyNOExecution.reply_state looked) Protocol.NO tail.
Proof.
 intros [Hin [Hout [Herror Hstop]]]. unfold control. split;[exact Hin|].
 split;[exact (f_equal (fun bytes=>bytes++Protocol.reply_bytes Protocol.NO) Hout)|]. split;assumption.
Qed.
Lemma history_control before looked count id tail : prefix before looked tail ->
 control before (HistoryStorage.result looked count (Z.of_nat id)) (Protocol.OK count) tail.
Proof.
 intros [Hin [Hout [Herror Hstop]]]. unfold control. split.
 - unfold HistoryStorage.result. change (stdin (ReplyOKExecution.reply_state (HistoryStorage.written looked count (Z.of_nat id)) count)=tail).
   rewrite ReplyOKExecution.reply_input. exact Hin.
 - split.
   + unfold HistoryStorage.result. change (stdout (ReplyOKExecution.reply_state (HistoryStorage.written looked count (Z.of_nat id)) count)=stdout before++Protocol.reply_bytes (Protocol.OK count)).
     etransitivity;[apply ReplyOKExecution.reply_output|]. exact (f_equal (fun bytes=>bytes++Protocol.reply_bytes (Protocol.OK count)) Hout).
   + split;rewrite HistoryStorage.result_meta_other by lia;assumption.
Qed.
Lemma lookup_control before looked found kind id tail : prefix before looked tail ->
 control before (CommandLookupClassExecution.result looked found kind id) (CommandLookupClassExecution.reply found kind id) tail.
Proof.
 intro Hprefix. destruct found;cbn [CommandLookupClassExecution.result CommandLookupClassExecution.reply];[destruct (Z.eq_dec kind 0)|];
 first [now apply ok_control|now apply no_control].
Qed.
Lemma query_control before looked q found kind flag tail : prefix before looked tail ->
 control before (CommandNameQueryExecution.result looked q found kind flag) (CommandNameQueryExecution.reply q found kind flag) tail.
Proof.
 intros [Hin [Hout [Herror Hstop]]]. unfold control,CommandNameQueryExecution.result.
 split;[exact Hin|]. split;[exact (f_equal (fun bytes=>bytes++Protocol.reply_bytes (CommandNameQueryExecution.reply q found kind flag)) Hout)|].
 split;assumption.
Qed.
Lemma recall_control before looked found kind count id tail : prefix before looked tail ->
 control before (CommandRecallExecution.result looked found kind count id) (CommandRecallExecution.reply found kind count) tail.
Proof.
 intro Hprefix. destruct found;cbn [CommandRecallExecution.result CommandRecallExecution.reply];[destruct (Z.eq_dec kind 1)|];
 first [now apply history_control|now apply no_control].
Qed.
Lemma arity_control before looked found kind width tail : prefix before looked tail ->
 control before (CommandArityExecution.result looked found kind width) (CommandArityExecution.reply found kind width) tail.
Proof.
 intro Hprefix. destruct found;cbn [CommandArityExecution.result CommandArityExecution.reply];[destruct (Z.eq_dec kind 2)|];
 first [now apply ok_control|now apply no_control].
Qed.
Lemma observed_boundary before bs ns final observations trace reply tail :
 (1024<=length (memory before arraydef_0__token))%nat -> (20<=length (memory before arraydef_0__printBuffer))%nat ->
 meta_value before 8=0 -> control before final reply tail ->
 execObserved (funcdef_0__command bs ns) (before,observations)=Some(tt,(final,trace)) -> boundary before final reply tail.
Proof.
 intros Htoken Hprint Herror [Hin [Hout [Hclear Hstop]]] Hrun. unfold boundary.
 split;[exact Hin|]. split;[exact Hout|]. split.
 - rewrite (NativeCommandLengths.generated arraydef_0__token before bs ns final observations trace NativeCommandLengths.token_protected Hrun). exact Htoken.
 - split.
   + rewrite (NativeCommandLengths.generated arraydef_0__printBuffer before bs ns final observations trace NativeCommandLengths.printBuffer_protected Hrun). exact Hprint.
   + split;congruence.
Qed.
Module Lookup.
Import LookupClassRefinement.
Theorem generated_control s logical bs ns name first_separator last_separator tail observations :
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
    HistoryRefinement.represents final logical /\ NameRepresentation.represents final (Protocol.bindings logical) /\ control s final (answer (Protocol.lookup name (Protocol.bindings logical))) tail.
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
  pose proof (lookup_prefix s 49 [48] name last_separator tail looked Hmeta Hframe) as Hprefix.
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
      split;[now apply CommandLookupClassExecution.result_bindings|].
      rewrite <-reply_typed. now apply lookup_control.
  - pose proof (CommandLookupClassExecution.generated_command s bs ns op parsed looked false 0 0 0 0 0 0 observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hnamevalid Hnameerror Hlookup Hlookmeta Houtcome
      ltac:(unfold maximum; lia) ltac:(discriminate) ltac:(discriminate) Hlookbuffer ltac:(unfold maximum; lia) Hlookerror) as Hrun.
    rewrite Hlookinput,Hlookoutput,Hinput,Houtput in Hrun.
    exists (CommandLookupClassExecution.result looked false 0 0). split; [exact Hrun|]. split; [exact Hlogical|]. split.
    + exact (FormulaProjection.storage_arena looked _ _ (CommandLookupClassExecution.result_projection looked false 0 0) Hlookarena).
    + split; [now apply CommandLookupClassExecution.result_classes|]. split; [now apply CommandLookupClassExecution.result_history|].
      split;[now apply CommandLookupClassExecution.result_bindings|].
      now apply lookup_control.
Qed.
Theorem generated_total_protocol s logical bs ns name first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Protocol.valid_name name -> NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 48 :: first_separator :: name ++ last_separator :: tail ->
  exists final, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (answer (Protocol.lookup name (Protocol.bindings logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 10 [] name) (answer (Protocol.lookup name (Protocol.bindings logical))) logical /\
    NativeState.represents final logical /\ boundary s final (answer (Protocol.lookup name (Protocol.bindings logical))) tail /\
    (Guarantees.safe logical -> Guarantees.safe logical).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hvalid Hstate Hsep1 Hsep2 Hin.
 destruct (generated_control s logical bs ns name first_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hvalid
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate) Hsep1 Hsep2 Hin)
 as (final & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hcontrol).
 exists final. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeSchemaLift.canonical 10 49 [48] s bs ns first_separator
     (name++last_separator::tail) observations final _ logical (Protocol.Req 10 [] name) (answer (Protocol.lookup name (Protocol.bindings logical))) logical
     _ _ eq_refl _ Hmeta Htoken Hpending Herror Hsep1 Hin Hrun Hstate Hstep _ _ Hhistory _).
   + lia.
   + lia.
   + reflexivity.
   + exact Harena.
   + exact Hclasses.
   + exact Hnames.
 - split.
   + exact (observed_boundary s bs ns final observations _ _ tail Htoken Hbuffer Herror Hcontrol Hrun).
   + intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.

End Lookup.
Module Query.
Import NameQueryRefinement.
Theorem generated_control q s logical bs ns name first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = first_byte q + 1 -> meta_value s 8 = 0 ->
  Protocol.valid_name name -> NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  NameRepresentation.represents s (Protocol.bindings logical) ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 53 :: first_separator :: name ++ last_separator :: tail ->
  exists final, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (answer q (Protocol.lookup name (Protocol.bindings logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req (number q) [] name) (answer q (Protocol.lookup name (Protocol.bindings logical))) logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final logical /\ NameRepresentation.represents final (Protocol.bindings logical) /\ control s final (answer q (Protocol.lookup name (Protocol.bindings logical))) tail.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalid Harena Hclasses Hhistory Hbindings Hsep1 Hsep2 Hin.
  destruct (ReadName.generated_reads s (number q) (first_byte q) [53] name first_separator last_separator tail observations Hmeta Htoken Hpending Herror
    ltac:(destruct q; cbn [number]; unfold maximum; lia) ltac:(destruct q; reflexivity) Hvalid Hsep1 Hsep2 Hin)
    as [Hopcode [Hread [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hnamedmeta [Hnamevalid [Hnameerror [Hnametoken [Hinput Houtput]]]]]]]]]]].
  rewrite number_opcode in Hopnumber.
  set (op := ReadName.opcode_state s (first_byte q) [53] name last_separator tail).
  set (parsed := ReadName.name_state s (first_byte q) [53] name last_separator tail).
  change (17 < length (memory parsed arraydef_0__meta))%nat in Hnamedmeta.
  change (NameRepresentation.token_rep parsed name) in Hnametoken.
  change (meta_value parsed 8 = 0) in Hnameerror.
  change (stdin parsed = tail) in Hinput. change (stdout parsed = stdout s) in Houtput.
  pose proof (NameQueryState.bindings s (first_byte q) [53] name last_separator tail _ Hmeta Hbindings) as Hparsedbindings.
  assert (Hparsedarena : NativeRepresentation.canonical_arena parsed (Protocol.formulas logical))
    by exact (ArenaFrame.storage_arena s parsed _ (NameQueryState.storage s (first_byte q) [53] name last_separator tail Hmeta) Harena).
  pose proof (NameQueryState.classes s (first_byte q) [53] name last_separator tail _ _ Hmeta Hclasses) as Hparsedclasses.
  pose proof (NameQueryState.history s (first_byte q) [53] name last_separator tail logical Hmeta Hhistory) as Hparsedhistory.
  destruct (TypedNameLookup.generated parsed (fun _ => false) (fun _ => 0) (Protocol.bindings logical) name observations
    ltac:(lia) Hparsedbindings Hnametoken) as [looked [Hlookup [Hlookbindings [Hlength [Hframe Houtcome]]]]].
  pose proof Hframe as [Harrays [Hcells [Hlookinput Hlookoutput]]].
  pose proof (lookup_prefix s (first_byte q) [53] name last_separator tail looked Hmeta Hframe) as Hprefix.
  assert (Hlookmeta : (17 < length (memory looked arraydef_0__meta))%nat) by (now rewrite Hlength).
  assert (Hlookerror : meta_value looked 8 = 0) by (rewrite Hcells by lia; exact Hnameerror).
  assert (Hlookbuffer : (20 <= length (memory looked arraydef_0__printBuffer))%nat).
  { rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate)). unfold parsed. now rewrite ReadName.name_other by discriminate. }
  assert (Hlookarena : NativeRepresentation.canonical_arena looked (Protocol.formulas logical))
    by exact (FormulaProjection.storage_arena parsed looked _ (BindNameRefinement.lookup_projection parsed looked Hframe Hlength) Hparsedarena).
  pose proof (BindNameRefinement.lookup_classes parsed looked _ _ Hframe Hparsedclasses) as Hlookclasses.
  pose proof (BindNameRefinement.lookup_history parsed looked logical Hframe Hparsedhistory) as Hlookhistory.
  pose proof (logical_total q logical name (SemanticFrames.arena_NoDup s _ Harena)) as Hlogical.
  unfold TypedNameLookup.outcome in Houtcome.
  destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hmeaning.
  - destruct Houtcome as [index [raw [Hresult [Hindex [Hbound [Hnth Hrecord]]]]]].
    destruct raw as [[[[offset size] value] flag] kind].
    destruct Hrecord as [Hsize [Hoffset [Hoffsetword [Hword [Hflag [Hspan [Hbytes [Hdecode Hvalidname]]]]]]]].
    pose proof (TypedNameLookup.decode_kind value flag kind meaning Hdecode) as Hkind.
    pose proof (TypedNameLookup.decode_value value flag kind meaning Hword Hdecode) as Hvalue.
    subst kind value.
    pose proof (CommandNameQueryExecution.generated_command q s bs ns op parsed looked true index offset size
      (TypedNameLookup.binding_value meaning) flag (TypedNameLookup.binding_kind meaning) observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hnamevalid Hnameerror Hlookup Hlookmeta Hresult Hindex
      (fun _ => Hbound) (fun _ => Hnth) Hlookbuffer (proj2 Hword) (kind_range meaning) Hlookerror) as Hrun.
    rewrite (reply_typed q _ _ _ meaning Hflag Hdecode),Hlookinput,Hlookoutput,Hinput,Houtput in Hrun.
    exists (CommandNameQueryExecution.result looked q true (TypedNameLookup.binding_kind meaning) flag).
    split; [exact Hrun|]. split; [exact Hlogical|]. split.
    + exact (FormulaProjection.storage_arena looked _ _ (CommandNameQueryExecution.result_projection looked q true _ _) Hlookarena).
    + split; [now apply CommandNameQueryExecution.result_classes|]. split; [now apply CommandNameQueryExecution.result_history|].
      split;[now apply CommandNameQueryExecution.result_bindings|].
      rewrite <-(reply_typed q _ _ _ meaning Hflag Hdecode). now apply query_control.
  - rewrite answer_missing in Hlogical |- *.
    pose proof (CommandNameQueryExecution.generated_command q s bs ns op parsed looked false 0 0 0 0 0 0 observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hnamevalid Hnameerror Hlookup Hlookmeta Houtcome
      ltac:(unfold maximum; lia) ltac:(discriminate) ltac:(discriminate) Hlookbuffer ltac:(unfold maximum; lia) ltac:(now left) Hlookerror) as Hrun.
    rewrite Hlookinput,Hlookoutput,Hinput,Houtput in Hrun.
    exists (CommandNameQueryExecution.result looked q false 0 0). split; [exact Hrun|]. split; [exact Hlogical|]. split.
    + exact (FormulaProjection.storage_arena looked _ _ (CommandNameQueryExecution.result_projection looked q false 0 0) Hlookarena).
    + split; [now apply CommandNameQueryExecution.result_classes|]. split; [now apply CommandNameQueryExecution.result_history|].
      split;[now apply CommandNameQueryExecution.result_bindings|].
      now apply query_control.
Qed.
Theorem generated_total_protocol q s logical bs ns name first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = first_byte q + 1 -> meta_value s 8 = 0 ->
  Protocol.valid_name name -> NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 53 :: first_separator :: name ++ last_separator :: tail ->
  exists final, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (answer q (Protocol.lookup name (Protocol.bindings logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req (number q) [] name) (answer q (Protocol.lookup name (Protocol.bindings logical))) logical /\
    NativeState.represents final logical /\ boundary s final (answer q (Protocol.lookup name (Protocol.bindings logical))) tail /\
    (Guarantees.safe logical -> Guarantees.safe logical).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hvalid Hstate Hsep1 Hsep2 Hin.
 destruct (generated_control q s logical bs ns name first_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hvalid
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate) Hsep1 Hsep2 Hin)
 as (final & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hcontrol).
 exists final. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeSchemaLift.canonical (number q) (first_byte q) [53] s bs ns first_separator
     (name++last_separator::tail) observations final _ logical (Protocol.Req (number q) [] name) (answer q (Protocol.lookup name (Protocol.bindings logical))) logical
     _ _ eq_refl _ Hmeta Htoken Hpending Herror Hsep1 Hin Hrun Hstate Hstep _ _ Hhistory _).
   + destruct q;cbn [number];lia.
   + destruct q;cbn [number];lia.
   + destruct q;reflexivity.
   + exact Harena.
   + exact Hclasses.
   + exact Hnames.
 - split.
   + exact (observed_boundary s bs ns final observations _ _ tail Htoken Hbuffer Herror Hcontrol Hrun).
   + intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.

End Query.
Module Recall.
Import RecallRefinement.
Theorem generated_control s logical bs ns name first_separator last_separator tail observations :
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
    HistoryRefinement.represents final (after logical (Protocol.lookup name (Protocol.bindings logical))) /\ NameRepresentation.represents final (Protocol.bindings logical) /\ control s final (answer logical (Protocol.lookup name (Protocol.bindings logical))) tail.
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
  pose proof (lookup_prefix s 50 [49] name last_separator tail looked Hmeta Hframe) as Hprefix.
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
      split;[now apply CommandRecallExecution.result_bindings|].
      rewrite <-reply_typed. now apply recall_control.
  - pose proof (CommandRecallExecution.generated_command s bs ns op parsed looked false 0 0 0 (length (Protocol.history logical)) 0 0 0 observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hnamevalid Hnameerror Hlookup Hlookmeta Houtcome
      ltac:(unfold maximum; lia) ltac:(discriminate) ltac:(discriminate) Hlookbuffer ltac:(unfold maximum; lia) Hlookcount Hhistoryroom Hlookerror) as Hrun.
    rewrite Hlookinput,Hlookoutput,Hinput,Houtput in Hrun.
    exists (CommandRecallExecution.result looked false 0 (length (Protocol.history logical)) 0). split; [exact Hrun|]. split; [exact Hlogical|]. split.
    + exact (FormulaProjection.storage_arena looked _ _ (CommandRecallExecution.result_projection looked false 0 (length (Protocol.history logical)) 0) Hlookarena).
    + split; [now apply CommandRecallExecution.result_classes|]. split.
      * exact Hlookhistory.
      * split;[now apply CommandRecallExecution.result_bindings|]. now apply recall_control.
Qed.
Theorem generated_total_protocol s logical bs ns name first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 51 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> LogicalNames.valid logical -> LogicalHistory.valid logical ->
  Protocol.valid_name name -> NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 49 :: first_separator :: name ++ last_separator :: tail ->
  exists final, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (answer logical (Protocol.lookup name (Protocol.bindings logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 21 [] name) (answer logical (Protocol.lookup name (Protocol.bindings logical))) (after logical (Protocol.lookup name (Protocol.bindings logical))) /\
    NativeState.represents final (after logical (Protocol.lookup name (Protocol.bindings logical))) /\ boundary s final (answer logical (Protocol.lookup name (Protocol.bindings logical))) tail /\
    (Guarantees.safe logical -> Guarantees.safe (after logical (Protocol.lookup name (Protocol.bindings logical)))).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hhistoryroom Hnamesvalid Hhistoryvalid Hvalid Hstate Hsep1 Hsep2 Hin.
 destruct (generated_control s logical bs ns name first_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hhistoryroom Hnamesvalid Hhistoryvalid Hvalid
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate) Hsep1 Hsep2 Hin)
 as (final & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hcontrol).
 exists final. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - assert (Hformulas:Protocol.formulas (after logical (Protocol.lookup name (Protocol.bindings logical)))=Protocol.formulas logical).
   { unfold after. destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|];[destruct meaning|];reflexivity. }
   assert (HclassesSame:Protocol.classes (after logical (Protocol.lookup name (Protocol.bindings logical)))=Protocol.classes logical).
   { unfold after. destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|];[destruct meaning|];reflexivity. }
   assert (Hbindings:Protocol.bindings (after logical (Protocol.lookup name (Protocol.bindings logical)))=Protocol.bindings logical).
   { unfold after. destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|];[destruct meaning|];reflexivity. }
   refine (NativeSchemaLift.canonical 21 50 [49] s bs ns first_separator
     (name++last_separator::tail) observations final _ logical (Protocol.Req 21 [] name) (answer logical (Protocol.lookup name (Protocol.bindings logical))) (after logical (Protocol.lookup name (Protocol.bindings logical)))
     _ _ eq_refl _ Hmeta Htoken Hpending Herror Hsep1 Hin Hrun Hstate Hstep _ _ Hhistory _).
   + lia.
   + lia.
   + reflexivity.
   + now rewrite Hformulas.
   + now rewrite Hformulas,HclassesSame.
   + now rewrite Hbindings.
 - split.
   + exact (observed_boundary s bs ns final observations _ _ tail Htoken Hbuffer Herror Hcontrol Hrun).
   + intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.

End Recall.
Module Arity.
Import ArityRefinement.
Theorem generated_control s logical bs ns name first_separator last_separator tail observations :
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
    SchemaMetadata.represents final (Protocol.expressions logical) /\ control s final (answer logical (Protocol.lookup name (Protocol.bindings logical))) tail.
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
  pose proof (lookup_prefix s 50 [54] name last_separator tail looked Hmeta Hframe) as Hprefix.
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
      split;[now apply CommandArityExecution.result_bindings|]. split;[now apply result_schemas|].
      rewrite <-Hreply. now apply arity_control.
  - pose proof (CommandArityExecution.generated_command s bs ns op parsed looked false 0 0 0 0 0 0 0 observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hnamevalid Hnameerror Hlookup Hlookmeta Houtcome
      ltac:(unfold maximum; lia) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hlookbuffer ltac:(unfold maximum; lia) Hlookerror) as Hrun.
    rewrite Hlookinput,Hlookoutput,Hinput,Houtput in Hrun.
    exists (CommandArityExecution.result looked false 0 0). split; [exact Hrun|]. split; [exact Hlogical|]. split.
    + exact (FormulaProjection.storage_arena looked _ _ (CommandArityExecution.result_projection looked false 0 0) Hlookarena).
    + split; [now apply CommandArityExecution.result_classes|]. split; [now apply CommandArityExecution.result_history|].
      split;[now apply CommandArityExecution.result_bindings|]. split;[now apply result_schemas|].
      now apply arity_control.
Qed.
Theorem generated_total_protocol s logical bs ns name first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 51 -> meta_value s 8 = 0 ->
  LogicalNames.valid logical ->
  Protocol.valid_name name -> NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 54 :: first_separator :: name ++ last_separator :: tail ->
  exists final, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (answer logical (Protocol.lookup name (Protocol.bindings logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 26 [] name) (answer logical (Protocol.lookup name (Protocol.bindings logical))) logical /\
    NativeState.represents final logical /\ boundary s final (answer logical (Protocol.lookup name (Protocol.bindings logical))) tail /\
    (Guarantees.safe logical -> Guarantees.safe logical).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hnamesvalid Hvalid Hstate Hsep1 Hsep2 Hin.
 destruct (generated_control s logical bs ns name first_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hnamesvalid (SchemaRepresentation.metadata _ _ (NativeState.schema_representation _ _ Hstate)) Hvalid
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate) Hsep1 Hsep2 Hin)
 as (final & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & HfinalSchemas & Hcontrol).
 exists final. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeSchemaLift.canonical 26 50 [54] s bs ns first_separator
     (name++last_separator::tail) observations final _ logical (Protocol.Req 26 [] name) (answer logical (Protocol.lookup name (Protocol.bindings logical))) logical
     _ _ eq_refl _ Hmeta Htoken Hpending Herror Hsep1 Hin Hrun Hstate Hstep _ _ Hhistory _).
   + lia.
   + lia.
   + reflexivity.
   + exact Harena.
   + exact Hclasses.
   + exact Hnames.
 - split.
   + exact (observed_boundary s bs ns final observations _ _ tail Htoken Hbuffer Herror Hcontrol Hrun).
   + intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.

End Arity.
End NativeQueryCommands.
