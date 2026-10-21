From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash ReadName ReadNameOne ReadToken TokenByte Representation ArenaFrame FormulaProjection ClassStorage HistoryRefinement HistoryLookup LogicalHistory SemanticFrames NameRepresentation BindNameRefinement CommandNameTheorem ReplyNO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NameTheoremRefinement.
Import IndexExecution SipHashExecution.
Definition named logical name fid := Protocol.State (Protocol.formulas logical) (Protocol.classes logical) (Protocol.history logical)
  (Protocol.bindings logical ++ [(name,Protocol.theorem_binding fid)]) (Protocol.expressions logical).
Lemma logical_success logical name value fid : nth_error (Protocol.history logical) value = Some fid ->
  Protocol.lookup name (Protocol.bindings logical) = None -> NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req 20 [value] name) (Protocol.OK fid) (named logical name fid).
Proof.
  intros Hhistory Hfresh Hunique. eapply Protocol.step_accept.
  - apply Protocol.accept_name_theorem; assumption.
  - apply HistoryRefinement.retained_refl. exact Hunique.
Qed.
Lemma logical_rejected logical name value :
  (nth_error (Protocol.history logical) value = None \/ Protocol.lookup name (Protocol.bindings logical) <> None) ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 20 [value] name) Protocol.NO logical.
Proof.
  intros Hinvalid Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end
      |destruct Hinvalid; congruence].
Qed.
Theorem generated_total_protocol s logical bs ns value name first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 51 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> Protocol.valid_name name -> LogicalHistory.valid logical ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  NameRepresentation.represents s (Protocol.bindings logical) ->
  Z.of_nat (length (Protocol.bindings logical)) < maximum ->
  Z.of_nat (length (memory s arraydef_0__names) + length name) <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 48 :: first_separator :: decimalBytes value ++ middle_separator :: name ++ last_separator :: tail ->
  exists final reply target, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 20 [value] name) reply target /\
    NativeRepresentation.canonical_arena final (Protocol.formulas target) /\
    ClassStorage.represents final (Protocol.formulas target) (Protocol.classes target) /\
    HistoryRefinement.represents final target /\ NameRepresentation.represents final (Protocol.bindings target).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hvalid Hhistoryvalid Harena Hclasses Hhistory Hbindings Hbindingroom Hbytesroom Hsep1 Hsep2 Hsep3 Hin.
  destruct (ReadNameOne.generated_reads s 20 50 [48] value name first_separator middle_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror ltac:(unfold maximum; lia) eq_refl Hvalue Hvalid Hsep1 Hsep2 Hsep3 Hin)
    as [Hopcode [Hargument [Hreadname [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargnumber [Hargvalid [Hargerror
      [Hnamemeta [Hnamevalid [Hnameerror [Hnametoken [Hinput Houtput]]]]]]]]]]]]]]]].
  set (op := ReadNameOne.opcode_state s 50 [48] value middle_separator name last_separator tail).
  set (arg := ReadNameOne.argument_state s 50 [48] value middle_separator name last_separator tail).
  set (parsed := ReadNameOne.name_state s 50 [48] value middle_separator name last_separator tail).
  change (17 < length (memory parsed arraydef_0__meta))%nat in Hnamemeta.
  change (stdin parsed = tail) in Hinput. change (stdout parsed = stdout s) in Houtput.
  pose proof (ReadNameOne.name_storage s 50 [48] value middle_separator name last_separator tail Hmeta) as Hstorage.
  assert (Hparsedarena : NativeRepresentation.canonical_arena parsed (Protocol.formulas logical))
    by exact (ArenaFrame.storage_arena s parsed _ Hstorage Harena).
  pose proof (ReadNameOne.name_classes s 50 [48] value middle_separator name last_separator tail _ _ Hmeta Hclasses) as Hparsedclasses.
  pose proof (ReadNameOne.name_history s 50 [48] value middle_separator name last_separator tail logical Hmeta Hhistory) as Hparsedhistory.
  pose proof (ReadNameOne.name_bindings s 50 [48] value middle_separator name last_separator tail _ Hmeta Hbindings) as Hparsedbindings.
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
  destruct (nth_error (Protocol.history logical) value) as [fid|] eqn:Hentry.
  - destruct (Hhistoryvalid value fid Hentry) as [p Hp].
    pose proof (proj2 (proj1 (proj2 (HistoryLookup.formula_reference s _ fid p Harena Hp)))) as Hfidword.
    destruct (HistoryLookup.native_lookup parsed logical value fid Hparsedhistory Hentry) as [Hnative Hnth].
    assert (Hreference : Z.of_nat value < meta_value parsed 3).
    { rewrite (proj1 Hparsedhistory). assert (value < length (Protocol.history logical))%nat by (apply nth_error_Some; congruence). lia. }
    destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hlookup.
    + destruct (BindNameRefinement.generated_duplicate parsed (fun _ => false)
        (CommandNameTheoremExecution.binding_arguments (Z.of_nat fid)) (Protocol.bindings logical) name meaning observations
        ltac:(lia) Hparsedbindings Hnametoken Hlookup)
        as [final [Hbind [Hfinalbindings [Hprojection [Hfinalclasses [Hfinalhistory Hfinalerror]]]]]].
      assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (rewrite (proj1 Hprojection); lia).
      assert (Hfinalclear : meta_value final 8 = 0) by (rewrite Hfinalerror; exact Hnameerror).
      pose proof (CommandNameTheoremExecution.generated_command s bs ns op arg parsed final (Z.of_nat value) (Z.of_nat fid) observations
        _ Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
        Hnamemeta Hnamevalid Hnameerror Hreference ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) Hbind Hfinalmeta Hfinalclear) as Hrun.
      rewrite Hinput,Houtput in Hrun. exists final,Protocol.NO,logical. split; [exact Hrun|]. split.
      * apply logical_rejected; [right; congruence|exact Hunique].
      * split; [exact (FormulaProjection.storage_arena parsed final _ Hprojection Hparsedarena)|].
        split; [exact (Hfinalclasses _ _ Hparsedclasses)|]. split; [exact (Hfinalhistory logical Hparsedhistory)|exact Hfinalbindings].
    + assert (Hdecode : NameRepresentation.decode (Z.of_nat fid) 0 1 = Some (Protocol.theorem_binding fid)).
      { unfold NameRepresentation.decode. cbn. now rewrite Nat2Z.id. }
      destruct (BindNameRefinement.generated_fresh parsed (fun _ => false)
        (CommandNameTheoremExecution.binding_arguments (Z.of_nat fid)) (Protocol.bindings logical) name fid 1 (Protocol.theorem_binding fid) observations
        ltac:(lia) Hparsedbuffer Hparsedbindings Hnametoken Hvalid Hlookup Hbindingroom Hparsedroom Hfidword Hdecode eq_refl eq_refl)
        as [final [Hbind [Hfinalbindings [Hprojection [Hfinalclasses [Hfinalhistory Hfinalerror]]]]]].
      assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (rewrite (proj1 Hprojection); lia).
      assert (Hfinalclear : meta_value final 8 = 0) by (rewrite Hfinalerror; exact Hnameerror).
      pose proof (CommandNameTheoremExecution.generated_command s bs ns op arg parsed final (Z.of_nat value) (Z.of_nat fid) observations
        _ Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
        Hnamemeta Hnamevalid Hnameerror Hreference ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) Hbind Hfinalmeta Hfinalclear) as Hrun.
      rewrite Hinput,Houtput in Hrun. exists final,(Protocol.OK fid),(named logical name fid). split; [exact Hrun|]. split.
      * now apply logical_success.
      * split; [exact (FormulaProjection.storage_arena parsed final _ Hprojection Hparsedarena)|].
        split; [exact (Hfinalclasses _ _ Hparsedclasses)|]. split; [exact (Hfinalhistory logical Hparsedhistory)|exact Hfinalbindings].
  - assert (Hreference : meta_value parsed 3 <= Z.of_nat value).
    { rewrite (proj1 Hparsedhistory). apply nth_error_None in Hentry. lia. }
    pose proof (CommandNameTheoremExecution.generated_rejected_command s bs ns op arg parsed (Z.of_nat value) observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
      Hnamemeta Hnamevalid Hnameerror Hreference) as Hrun.
    rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state parsed),Protocol.NO,logical. split; [exact Hrun|]. split.
    + apply logical_rejected; [now left|exact Hunique].
    + split.
      * eapply ArenaFrame.storage_arena; [apply ArenaFrame.storage_output|exact Hparsedarena].
      * split; [exact Hparsedclasses|]. split; [exact Hparsedhistory|exact Hparsedbindings].
Qed.
End NameTheoremRefinement.
