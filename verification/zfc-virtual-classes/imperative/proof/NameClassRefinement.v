From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ReadName ReadNameOne ReadToken TokenByte Representation ArenaFrame FormulaProjection ClassStorage HistoryRefinement SemanticFrames NameRepresentation BindNameRefinement CommandNameClass ReplyNO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NameClassRefinement.
Import IndexExecution SipHashExecution.
Definition named logical name value := Protocol.State (Protocol.formulas logical) (Protocol.classes logical) (Protocol.history logical)
  (Protocol.bindings logical ++ [(name,Protocol.class_binding value false)]) (Protocol.expressions logical).
Lemma logical_success logical name value cls : nth_error (Protocol.classes logical) value = Some cls ->
  Protocol.lookup name (Protocol.bindings logical) = None -> NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req 9 [value] name) (Protocol.OK value) (named logical name value).
Proof.
  intros Hclass Hfresh Hunique. eapply Protocol.step_accept.
  - apply Protocol.accept_name_class with (c := cls); assumption.
  - apply HistoryRefinement.retained_refl. exact Hunique.
Qed.
Lemma logical_rejected logical name value :
  (nth_error (Protocol.classes logical) value = None \/ Protocol.lookup name (Protocol.bindings logical) <> None) ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 9 [value] name) Protocol.NO logical.
Proof.
  intros Hinvalid Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end
      |destruct Hinvalid; unfold Protocol.class_at in *; congruence].
Qed.
Theorem generated_total_protocol s logical bs ns value name first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 58 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> Protocol.valid_name name ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  NameRepresentation.represents s (Protocol.bindings logical) ->
  Z.of_nat (length (Protocol.bindings logical)) < maximum ->
  Z.of_nat (length (memory s arraydef_0__names) + length name) <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ middle_separator :: name ++ last_separator :: tail ->
  exists final reply target, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 9 [value] name) reply target /\
    NativeRepresentation.canonical_arena final (Protocol.formulas target) /\
    ClassStorage.represents final (Protocol.formulas target) (Protocol.classes target) /\
    HistoryRefinement.represents final target /\ NameRepresentation.represents final (Protocol.bindings target).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hvalid Harena Hclasses Hhistory Hbindings Hbindingroom Hbytesroom Hsep1 Hsep2 Hsep3 Hin.
  destruct (ReadNameOne.generated_reads s 9 57 [] value name first_separator middle_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror ltac:(unfold maximum; lia) eq_refl Hvalue Hvalid Hsep1 Hsep2 Hsep3 Hin)
    as [Hopcode [Hargument [Hreadname [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargnumber [Hargvalid [Hargerror
      [Hnamemeta [Hnamevalid [Hnameerror [Hnametoken [Hinput Houtput]]]]]]]]]]]]]]]].
  set (op := ReadNameOne.opcode_state s 57 [] value middle_separator name last_separator tail).
  set (arg := ReadNameOne.argument_state s 57 [] value middle_separator name last_separator tail).
  set (parsed := ReadNameOne.name_state s 57 [] value middle_separator name last_separator tail).
  change (17 < length (memory parsed arraydef_0__meta))%nat in Hnamemeta.
  change (stdin parsed = tail) in Hinput. change (stdout parsed = stdout s) in Houtput.
  pose proof (ReadNameOne.name_storage s 57 [] value middle_separator name last_separator tail Hmeta) as Hstorage.
  assert (Hparsedarena : NativeRepresentation.canonical_arena parsed (Protocol.formulas logical))
    by exact (ArenaFrame.storage_arena s parsed _ Hstorage Harena).
  pose proof (ReadNameOne.name_classes s 57 [] value middle_separator name last_separator tail _ _ Hmeta Hclasses) as Hparsedclasses.
  pose proof (ReadNameOne.name_history s 57 [] value middle_separator name last_separator tail logical Hmeta Hhistory) as Hparsedhistory.
  pose proof (ReadNameOne.name_bindings s 57 [] value middle_separator name last_separator tail _ Hmeta Hbindings) as Hparsedbindings.
  change (ClassStorage.represents parsed (Protocol.formulas logical) (Protocol.classes logical)) in Hparsedclasses.
  change (HistoryRefinement.represents parsed logical) in Hparsedhistory.
  change (NameRepresentation.represents parsed (Protocol.bindings logical)) in Hparsedbindings.
  change (NameRepresentation.token_rep parsed name) in Hnametoken.
  change (meta_value parsed 14 = 1) in Hnamevalid.
  change (meta_value parsed 8 = 0) in Hnameerror.
  assert (Hparsedbuffer : (20 <= length (memory parsed arraydef_0__printBuffer))%nat)
    by (unfold parsed; rewrite ReadNameOne.name_other by discriminate; exact Hbuffer).
  assert (Hparsedroom : Z.of_nat (length (memory parsed arraydef_0__names) + length name) <= maximum)
    by (unfold parsed; rewrite ReadNameOne.name_other by discriminate; exact Hbytesroom).
  assert (Hunique : NoDup (Protocol.formulas logical)) by exact (SemanticFrames.arena_NoDup s _ Harena).
  destruct (nth_error (Protocol.classes logical) value) as [cls|] eqn:Hentry.
  - assert (Hreference : Z.of_nat value < meta_value parsed 2).
    { rewrite (proj1 Hparsedclasses). assert (value < length (Protocol.classes logical))%nat by (apply nth_error_Some; congruence). lia. }
    destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hlookup.
    + destruct (BindNameRefinement.generated_duplicate parsed (fun _ => false)
        (CommandNameClassExecution.binding_arguments (Z.of_nat value)) (Protocol.bindings logical) name meaning observations
        ltac:(lia) Hparsedbindings Hnametoken Hlookup)
        as [final [Hbind [Hfinalbindings [Hprojection [Hfinalclasses [Hfinalhistory Hfinalerror]]]]]].
      assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (rewrite (proj1 Hprojection); lia).
      assert (Hfinalclear : meta_value final 8 = 0) by (rewrite Hfinalerror; exact Hnameerror).
      pose proof (CommandNameClassExecution.generated_command s bs ns op arg parsed final (Z.of_nat value) observations
        _ Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
        Hnamemeta Hnamevalid Hnameerror Hreference Hbind Hfinalmeta Hfinalclear) as Hrun.
      rewrite Hinput,Houtput in Hrun. exists final,Protocol.NO,logical. split; [exact Hrun|]. split.
      * apply logical_rejected; [right; congruence|exact Hunique].
      * split; [exact (FormulaProjection.storage_arena parsed final _ Hprojection Hparsedarena)|].
        split; [exact (Hfinalclasses _ _ Hparsedclasses)|]. split; [exact (Hfinalhistory logical Hparsedhistory)|exact Hfinalbindings].
    + assert (Hdecode : NameRepresentation.decode (Z.of_nat value) 0 0 = Some (Protocol.class_binding value false)).
      { unfold NameRepresentation.decode. cbn. now rewrite Nat2Z.id. }
      destruct (BindNameRefinement.generated_fresh parsed (fun _ => false)
        (CommandNameClassExecution.binding_arguments (Z.of_nat value)) (Protocol.bindings logical) name value 0 (Protocol.class_binding value false) observations
        ltac:(lia) Hparsedbuffer Hparsedbindings Hnametoken Hvalid Hlookup Hbindingroom Hparsedroom Hvalue Hdecode eq_refl eq_refl)
        as [final [Hbind [Hfinalbindings [Hprojection [Hfinalclasses [Hfinalhistory Hfinalerror]]]]]].
      assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (rewrite (proj1 Hprojection); lia).
      assert (Hfinalclear : meta_value final 8 = 0) by (rewrite Hfinalerror; exact Hnameerror).
      pose proof (CommandNameClassExecution.generated_command s bs ns op arg parsed final (Z.of_nat value) observations
        _ Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
        Hnamemeta Hnamevalid Hnameerror Hreference Hbind Hfinalmeta Hfinalclear) as Hrun.
      rewrite Hinput,Houtput in Hrun. exists final,(Protocol.OK value),(named logical name value). split; [exact Hrun|]. split.
      * eapply logical_success; eassumption.
      * split; [exact (FormulaProjection.storage_arena parsed final _ Hprojection Hparsedarena)|].
        split; [exact (Hfinalclasses _ _ Hparsedclasses)|]. split; [exact (Hfinalhistory logical Hparsedhistory)|exact Hfinalbindings].
  - assert (Hreference : meta_value parsed 2 <= Z.of_nat value).
    { rewrite (proj1 Hparsedclasses). apply nth_error_None in Hentry. lia. }
    pose proof (CommandNameClassExecution.generated_rejected_command s bs ns op arg parsed (Z.of_nat value) observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
      Hnamemeta Hnamevalid Hnameerror Hreference) as Hrun.
    rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state parsed),Protocol.NO,logical. split; [exact Hrun|]. split.
    + apply logical_rejected; [now left|exact Hunique].
    + split.
      * eapply ArenaFrame.storage_arena; [apply ArenaFrame.storage_output|exact Hparsedarena].
      * split; [exact Hparsedclasses|]. split; [exact Hparsedhistory|exact Hparsedbindings].
Qed.
End NameClassRefinement.
