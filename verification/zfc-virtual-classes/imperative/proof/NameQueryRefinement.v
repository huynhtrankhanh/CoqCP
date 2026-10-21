From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadName NameQueryState TypedNameLookup NameRepresentation BindNameRefinement NameSearch ArenaFrame FormulaProjection Representation ClassStorage HistoryRefinement SemanticFrames CommandNameQuery.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NameQueryRefinement.
Import IndexExecution SipHashExecution CommandNameQueryExecution.
Definition number q : nat := match q with Setness => 15 | Kind => 25 end.
Definition first_byte q : Z := match q with Setness => 49 | Kind => 50 end.
Lemma number_opcode q : Z.of_nat (number q) = opcode q.
Proof. destruct q; reflexivity. Qed.
Definition answer q meaning := match q with
| Setness => match meaning with Some (Protocol.class_binding _ flag) => if flag then Protocol.SET else Protocol.CLASS | _ => Protocol.NO end
| Kind => match meaning with Some (Protocol.class_binding _ _) => Protocol.CLASS | Some (Protocol.theorem_binding _) => Protocol.THEOREM | Some (Protocol.schema_binding _) => Protocol.SCHEMA | None => Protocol.NO end end.
Lemma answer_missing q : answer q None = Protocol.NO.
Proof. destruct q; reflexivity. Qed.
Lemma kind_range meaning : TypedNameLookup.binding_kind meaning = 0 \/ TypedNameLookup.binding_kind meaning = 1 \/ TypedNameLookup.binding_kind meaning = 2.
Proof. destruct meaning; cbn [TypedNameLookup.binding_kind]; tauto. Qed.
Lemma reply_typed q value flag kind meaning : (flag = 0 \/ flag = 1) -> NameRepresentation.decode value flag kind = Some meaning ->
  reply q true kind flag = answer q (Some meaning).
Proof.
  intros Hflag Hdecode. pose proof (TypedNameLookup.decode_kind value flag kind meaning Hdecode) as Hkind. subst kind.
  destruct meaning as [id certified|id|id].
  - pose proof (TypedNameLookup.decode_flag value flag _ id certified Hflag Hdecode) as Hcert. subst flag. destruct q,certified; reflexivity.
  - destruct q; reflexivity.
  - destruct q; reflexivity.
Qed.
Lemma logical_rejected q logical name : answer q (Protocol.lookup name (Protocol.bindings logical)) = Protocol.NO ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req (number q) [] name) Protocol.NO logical.
Proof.
  intros Hanswer Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. destruct q; cbn [number] in Haccept; inversion Haccept; subst;
    try solve [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end];
    try solve [match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end].
  all: match goal with H : Protocol.lookup _ _ = Some _ |- _ => rewrite H in Hanswer end;
    cbn [answer] in Hanswer; try discriminate.
  all: match goal with flag : bool |- _ => destruct flag; discriminate end.
Qed.
Lemma logical_total q logical name : NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req (number q) [] name) (answer q (Protocol.lookup name (Protocol.bindings logical))) logical.
Proof.
  intro Hunique. destruct q; destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hlookup;
    [destruct meaning as [id flag|id|root]| |destruct meaning as [id flag|id|root]|]; cbn [number answer].
  - eapply Protocol.step_accept; [eapply Protocol.accept_query; exact Hlookup|now apply HistoryRefinement.retained_refl].
  - apply (logical_rejected Setness); [rewrite Hlookup; reflexivity|exact Hunique].
  - apply (logical_rejected Setness); [rewrite Hlookup; reflexivity|exact Hunique].
  - apply (logical_rejected Setness); [rewrite Hlookup; reflexivity|exact Hunique].
  - eapply Protocol.step_accept; [eapply Protocol.accept_kind_class; exact Hlookup|now apply HistoryRefinement.retained_refl].
  - eapply Protocol.step_accept; [eapply Protocol.accept_kind_theorem; exact Hlookup|now apply HistoryRefinement.retained_refl].
  - eapply Protocol.step_accept; [eapply Protocol.accept_kind_schema; exact Hlookup|now apply HistoryRefinement.retained_refl].
  - apply (logical_rejected Kind); [rewrite Hlookup; reflexivity|exact Hunique].
Qed.
Theorem generated_total_protocol q s logical bs ns name first_separator last_separator tail observations :
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
    HistoryRefinement.represents final logical /\ NameRepresentation.represents final (Protocol.bindings logical).
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
      now apply CommandNameQueryExecution.result_bindings.
  - rewrite answer_missing in Hlogical |- *.
    pose proof (CommandNameQueryExecution.generated_command q s bs ns op parsed looked false 0 0 0 0 0 0 observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread Hnamedmeta Hnamevalid Hnameerror Hlookup Hlookmeta Houtcome
      ltac:(unfold maximum; lia) ltac:(discriminate) ltac:(discriminate) Hlookbuffer ltac:(unfold maximum; lia) ltac:(now left) Hlookerror) as Hrun.
    rewrite Hlookinput,Hlookoutput,Hinput,Houtput in Hrun.
    exists (CommandNameQueryExecution.result looked q false 0 0). split; [exact Hrun|]. split; [exact Hlogical|]. split.
    + exact (FormulaProjection.storage_arena looked _ _ (CommandNameQueryExecution.result_projection looked q false 0 0) Hlookarena).
    + split; [now apply CommandNameQueryExecution.result_classes|]. split; [now apply CommandNameQueryExecution.result_history|].
      now apply CommandNameQueryExecution.result_bindings.
Qed.
End NameQueryRefinement.
