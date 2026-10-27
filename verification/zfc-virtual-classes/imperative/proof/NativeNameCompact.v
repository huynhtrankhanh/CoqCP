From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash ReadOne ReadName ReadNameOne ReadToken ReadNat DecimalInput CommandInput TokenByte
 Representation ArenaFrame FormulaProjection ClassStorage HistoryRefinement HistoryLookup LogicalHistory LogicalNames SemanticFrames
 NameRepresentation BindNameRefinement BindName BindingStorage NameSearch NameLookup NameCopy
 CommandNameClass CommandNameTheorem CommandNameSchema ReplyNO ReplyOK SchemaMetadata SchemaRepresentation SchemaFrame
 NativeState NativeSchemaLift NativeNamedCommands NativeQueryCommands.
From NativeProof Require Import NativeNamedBoundary.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeNameCompact.
Import IndexExecution SipHashExecution NativeQueryCommands NativeNamedBoundary.
Definition boundary := NativeNamedBoundary.boundary.
Fixpoint name_bytes (bindings:list (Protocol.name*Protocol.binding)) : nat :=
 match bindings with []=>0 |(name,meaning)::rest=>length name+name_bytes rest end.
Definition compact_bindings (native:Machine) bindings := length (memory native arraydef_0__names)=name_bytes bindings.
Definition bytes logical := name_bytes (Protocol.bindings logical).
Definition compact native logical := compact_bindings native (Protocol.bindings logical).
Lemma name_bytes_app bindings extra : name_bytes (bindings++extra)=(name_bytes bindings+name_bytes extra)%nat.
Proof. induction bindings as [|[name meaning] rest IH];cbn [List.app name_bytes];[reflexivity|rewrite IH;lia]. Qed.
Lemma compact_same before after bindings : memory after arraydef_0__names=memory before arraydef_0__names ->
 compact_bindings before bindings -> compact_bindings after bindings.
Proof. unfold compact_bindings;intros -> H;exact H. Qed.
Lemma compact_append before after bindings name meaning :
 length (memory after arraydef_0__names)=(length (memory before arraydef_0__names)+length name)%nat ->
 compact_bindings before bindings -> compact_bindings after (bindings++[(name,meaning)]).
Proof. unfold compact_bindings;intros Hlength Hbefore. rewrite Hlength,name_bytes_app,Hbefore. cbn [name_bytes];lia. Qed.
Lemma parsed_compact before ch chars value middle name last tail bindings : compact_bindings before bindings ->
 compact_bindings (ReadNameOne.name_state before ch chars value middle name last tail) bindings.
Proof. apply compact_same. apply ReadNameOne.name_other;discriminate. Qed.
Module Binding.
Import BindNameRefinement NameSearchExecution NameLookupExecution.
Theorem generated_fresh s bs ns bindings name value kind meaning observations :
  (8 < length (memory s arraydef_0__meta))%nat -> (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  NameRepresentation.represents s bindings -> NameRepresentation.token_rep s name -> Protocol.valid_name name ->
  Protocol.lookup name bindings = None -> Z.of_nat (length bindings) < maximum ->
  Z.of_nat (length (memory s arraydef_0__names) + length name) <= maximum -> Z.of_nat value <= maximum ->
  NameRepresentation.decode (Z.of_nat value) 0 kind = Some meaning ->
  ns vardef_0__bindName_value = Z.of_nat value -> ns vardef_0__bindName_kind = kind ->
  exists final, execObserved (funcdef_0__bindName bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK value); unreadInput := stdin s|}])) /\
    NameRepresentation.represents final (bindings ++ [(name,meaning)]) /\ FormulaProjection.storage s final /\
    (forall fs classes, ClassStorage.represents s fs classes -> ClassStorage.represents final fs classes) /\
    (forall logical, HistoryRefinement.represents s logical -> HistoryRefinement.represents final logical) /\
    meta_value final 8 = meta_value s 8 /\ control s final (Protocol.OK value) (stdin s) /\
    (length (memory final arraydef_0__names)<=length (memory s arraydef_0__names)+length name)%nat /\
    (compact_bindings s bindings -> compact_bindings final (bindings++[(name,meaning)])).
Proof.
  intros Hmeta Hbuffer Hrep Htoken Hvalid Hfresh Hcountword Hbytesword Hvalueword Hdecode Hvalue Hkind.
  assert (Hfind : find_native s (length bindings) (length name) (length bindings) = None).
  { pose proof (NameRepresentation.lookup_correspondence s bindings name Hrep Htoken) as Hmeaning.
    destruct (find_native s (length bindings) (length name) (length bindings)); [|reflexivity].
    destruct Hmeaning as [meaning' [Hentry Hlookup]]. congruence. }
  destruct (generated_lookup_with_capacity s (fun _ => false) (fun _ => 0) (length bindings) (length name) observations
    ltac:(lia) (proj1 Hrep) (proj1 Htoken) (proj1 (proj2 Htoken)) (NameRepresentation.valid_storage s bindings Hrep))
    as [looked [Hlookup [Hcorrect Hlength]]].
  rewrite Hfind in Hcorrect. destruct Hcorrect as [Hmissing Hframe].
  pose proof (NameRepresentation.storage_transport s looked bindings Hframe Hrep) as Hrep'.
  pose proof (token_transport s looked name Hframe Htoken) as Htoken'.
  pose proof Hframe as [Harrays [Hcells [Hinput Houtput]]].
  assert (Hmeta' : (8 < length (memory looked arraydef_0__meta))%nat) by (now rewrite Hlength).
  assert (Hbuffer' : (20 <= length (memory looked arraydef_0__printBuffer))%nat)
    by (now rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate))).
  assert (Hbytesword' : Z.of_nat (length (memory looked arraydef_0__names) + length name) <= maximum)
    by (now rewrite (Harrays arraydef_0__names ltac:(discriminate))).
  set (final := BindingStorage.result looked (length bindings) (length (memory looked arraydef_0__names)) (length name) value kind).
  exists final. split.
  - pose proof (BindNameExecution.generated_bind s bs ns looked (length bindings) (length (memory looked arraydef_0__names))
      (length name) value kind observations Hlookup Hmeta' Hbuffer' Hmissing (proj1 Hrep') (proj1 (proj2 Hrep'))
      (proj1 Htoken') Hcountword Hbytesword' Hvalueword Hvalue Hkind (proj1 (proj2 Htoken'))) as Hrun.
    rewrite Hinput,Houtput in Hrun. exact Hrun.
  - split.
    + exact (BindingStorage.append_represents looked bindings name value kind meaning ltac:(lia)
        Hrep' Htoken' Hcountword Hbytesword' Hvalueword Hdecode Hvalid).
    + split.
      * eapply FormulaProjection.storage_trans; [exact (lookup_projection s looked Hframe Hlength)|apply BindingStorage.result_projection].
      * split.
        -- intros fs classes Hclasses. apply BindingStorage.result_classes. exact (lookup_classes s looked fs classes Hframe Hclasses).
        -- split.
           ++ intros logical Hhistory. apply BindingStorage.result_history. exact (lookup_history s looked logical Hframe Hhistory).
           ++ split;[unfold final;rewrite BindingStorage.result_meta_other by lia;apply Hcells;lia|].
              split.
              ** unfold final. apply binding_control. now apply lookup_self_prefix.
              ** split.
                 --- unfold final. rewrite BindingStorage.result_names_length by reflexivity.
                     rewrite Harrays by discriminate. lia.
                 --- intro Hcompact. apply (compact_append s final bindings name meaning);[|exact Hcompact].
                     unfold final. rewrite BindingStorage.result_names_length by reflexivity. now rewrite Harrays by discriminate.
Qed.
Theorem generated_duplicate s bs ns bindings name meaning observations :
  (6 < length (memory s arraydef_0__meta))%nat ->
  NameRepresentation.represents s bindings -> NameRepresentation.token_rep s name ->
  Protocol.lookup name bindings = Some meaning ->
  exists final, execObserved (funcdef_0__bindName bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin s|}])) /\
    NameRepresentation.represents final bindings /\ FormulaProjection.storage s final /\
    (forall fs classes, ClassStorage.represents s fs classes -> ClassStorage.represents final fs classes) /\
    (forall logical, HistoryRefinement.represents s logical -> HistoryRefinement.represents final logical) /\
    meta_value final 8 = meta_value s 8 /\ control s final Protocol.NO (stdin s) /\
    (length (memory final arraydef_0__names)<=length (memory s arraydef_0__names)+length name)%nat /\
    (compact_bindings s bindings -> compact_bindings final bindings).
Proof.
  intros Hmeta Hrep Htoken Hpresent.
  assert (Hfind : exists index, find_native s (length bindings) (length name) (length bindings) = Some index).
  { pose proof (NameRepresentation.lookup_correspondence s bindings name Hrep Htoken) as Hmeaning.
    destruct (find_native s (length bindings) (length name) (length bindings)) as [index|]; [now exists index|congruence]. }
  destruct Hfind as [index Hfind].
  destruct (generated_lookup_with_capacity s (fun _ => false) (fun _ => 0) (length bindings) (length name) observations
    Hmeta (proj1 Hrep) (proj1 Htoken) (proj1 (proj2 Htoken)) (NameRepresentation.valid_storage s bindings Hrep))
    as [looked [Hlookup [Hcorrect Hlength]]].
  rewrite Hfind in Hcorrect. destruct Hcorrect as [Hfound Hframe].
  pose proof (found_below_sentinel s (length bindings) (length name) index (proj1 (proj2 (proj2 Hrep))) Hfind) as Hindex.
  pose proof (NameRepresentation.storage_transport s looked bindings Hframe Hrep) as Hrep'.
  pose proof Hframe as [Harrays [Hcells [Hinput Houtput]]].
  exists (ReplyNOExecution.reply_state looked). split.
  - pose proof (BindNameExecution.generated_duplicate s bs ns looked observations Hlookup ltac:(rewrite Hlength; lia) ltac:(lia)) as Hrun.
    rewrite Hinput,Houtput in Hrun. exact Hrun.
  - split.
    + change (NameRepresentation.represents looked bindings). exact Hrep'.
    + split.
      * change (FormulaProjection.storage s looked). exact (lookup_projection s looked Hframe Hlength).
      * split.
        -- intros fs classes Hclasses. change (ClassStorage.represents looked fs classes). exact (lookup_classes s looked fs classes Hframe Hclasses).
        -- split.
           ++ intros logical Hhistory. change (HistoryRefinement.represents looked logical). exact (lookup_history s looked logical Hframe Hhistory).
           ++ split;[change (meta_value looked 8 = meta_value s 8);apply Hcells;lia|].
              split.
              ** apply NativeQueryCommands.no_control. now apply lookup_self_prefix.
              ** split.
                 --- rewrite ReplyNOExecution.reply_memory,Harrays by discriminate. lia.
                 --- apply compact_same. rewrite ReplyNOExecution.reply_memory. apply Harrays;discriminate.
Qed.
End Binding.
Module Class.
Import NameClassRefinement.NameClassRefinement.
Theorem generated_control s logical bs ns value name first_separator middle_separator last_separator tail observations :
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
    HistoryRefinement.represents final target /\ NameRepresentation.represents final (Protocol.bindings target) /\ control s final reply tail /\
    (length (memory final arraydef_0__names)<=length (memory s arraydef_0__names)+length name)%nat /\
    (compact s logical -> compact final target).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hvalid Harena Hclasses Hhistory Hbindings Hbindingroom Hbytesroom Hsep1 Hsep2 Hsep3 Hin.
  destruct (ReadNameOne.generated_reads s 9 57 [] value name first_separator middle_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror ltac:(unfold maximum; lia) eq_refl Hvalue Hvalid Hsep1 Hsep2 Hsep3 Hin)
    as [Hopcode [Hargument [Hreadname [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargnumber [Hargvalid [Hargerror
      [Hnamemeta [Hnamevalid [Hnameerror [Hnametoken [Hinput Houtput]]]]]]]]]]]]]]]].
  set (op := ReadNameOne.opcode_state s 57 [] value middle_separator name last_separator tail).
  set (arg := ReadNameOne.argument_state s 57 [] value middle_separator name last_separator tail).
  set (parsed := ReadNameOne.name_state s 57 [] value middle_separator name last_separator tail).
  pose proof (parsed_prefix s 57 [] value middle_separator name last_separator tail Hmeta) as HparsedPrefix.
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
    + destruct (Binding.generated_duplicate parsed (fun _ => false)
        (CommandNameClassExecution.binding_arguments (Z.of_nat value)) (Protocol.bindings logical) name meaning observations
        ltac:(lia) Hparsedbindings Hnametoken Hlookup)
        as (final & Hbind & Hfinalbindings & Hprojection & Hfinalclasses & Hfinalhistory & Hfinalerror & Hbindcontrol & Hgrowth & Hcompact).
      assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (rewrite (proj1 Hprojection); lia).
      assert (Hfinalclear : meta_value final 8 = 0) by (rewrite Hfinalerror; exact Hnameerror).
      pose proof (CommandNameClassExecution.generated_command s bs ns op arg parsed final (Z.of_nat value) observations
        _ Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
        Hnamemeta Hnamevalid Hnameerror Hreference Hbind Hfinalmeta Hfinalclear) as Hrun.
      rewrite Hinput,Houtput in Hrun. exists final,Protocol.NO,logical. split; [exact Hrun|]. split.
      * apply logical_rejected; [right; congruence|exact Hunique].
      * split; [exact (FormulaProjection.storage_arena parsed final _ Hprojection Hparsedarena)|].
        split; [exact (Hfinalclasses _ _ Hparsedclasses)|]. split;[exact (Hfinalhistory logical Hparsedhistory)|]. split;[exact Hfinalbindings|].
        split;[exact (control_prefix s parsed final _ tail HparsedPrefix Hbindcontrol)|].
        split.
        -- unfold parsed in Hgrowth. rewrite ReadNameOne.name_other in Hgrowth by discriminate. exact Hgrowth.
        -- intro Hsource. apply Hcompact. unfold compact_bindings in *. unfold parsed. rewrite ReadNameOne.name_other by discriminate. exact Hsource.
    + assert (Hdecode : NameRepresentation.decode (Z.of_nat value) 0 0 = Some (Protocol.class_binding value false)).
      { unfold NameRepresentation.decode. cbn. now rewrite Nat2Z.id. }
      destruct (Binding.generated_fresh parsed (fun _ => false)
        (CommandNameClassExecution.binding_arguments (Z.of_nat value)) (Protocol.bindings logical) name value 0 (Protocol.class_binding value false) observations
        ltac:(lia) Hparsedbuffer Hparsedbindings Hnametoken Hvalid Hlookup Hbindingroom Hparsedroom Hvalue Hdecode eq_refl eq_refl)
        as (final & Hbind & Hfinalbindings & Hprojection & Hfinalclasses & Hfinalhistory & Hfinalerror & Hbindcontrol & Hgrowth & Hcompact).
      assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (rewrite (proj1 Hprojection); lia).
      assert (Hfinalclear : meta_value final 8 = 0) by (rewrite Hfinalerror; exact Hnameerror).
      pose proof (CommandNameClassExecution.generated_command s bs ns op arg parsed final (Z.of_nat value) observations
        _ Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
        Hnamemeta Hnamevalid Hnameerror Hreference Hbind Hfinalmeta Hfinalclear) as Hrun.
      rewrite Hinput,Houtput in Hrun. exists final,(Protocol.OK value),(named logical name value). split; [exact Hrun|]. split.
      * eapply logical_success; eassumption.
      * split; [exact (FormulaProjection.storage_arena parsed final _ Hprojection Hparsedarena)|].
        split; [exact (Hfinalclasses _ _ Hparsedclasses)|]. split;[exact (Hfinalhistory logical Hparsedhistory)|]. split;[exact Hfinalbindings|].
        split;[exact (control_prefix s parsed final _ tail HparsedPrefix Hbindcontrol)|].
        split.
        -- unfold parsed in Hgrowth. rewrite ReadNameOne.name_other in Hgrowth by discriminate. exact Hgrowth.
        -- intro Hsource. apply Hcompact. unfold compact_bindings in *. unfold parsed. rewrite ReadNameOne.name_other by discriminate. exact Hsource.
  - assert (Hreference : meta_value parsed 2 <= Z.of_nat value).
    { rewrite (proj1 Hparsedclasses). apply nth_error_None in Hentry. lia. }
    pose proof (CommandNameClassExecution.generated_rejected_command s bs ns op arg parsed (Z.of_nat value) observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
      Hnamemeta Hnamevalid Hnameerror Hreference) as Hrun.
    rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state parsed),Protocol.NO,logical. split; [exact Hrun|]. split.
    + apply logical_rejected; [now left|exact Hunique].
    + split.
      * eapply ArenaFrame.storage_arena; [apply ArenaFrame.storage_output|exact Hparsedarena].
      * split; [exact Hparsedclasses|]. split;[exact Hparsedhistory|]. split;[exact Hparsedbindings|]. split;[now apply NativeQueryCommands.no_control|].
        split.
        -- rewrite ReplyNOExecution.reply_memory. unfold parsed. rewrite ReadNameOne.name_other by discriminate. lia.
        -- apply compact_same. rewrite ReplyNOExecution.reply_memory. unfold parsed. apply ReadNameOne.name_other;discriminate.
Qed.
Theorem generated_total_protocol s logical bs ns value name first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 58 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> Protocol.valid_name name ->
  NativeState.represents s logical ->
  Z.of_nat (length (Protocol.bindings logical)) < maximum ->
  Z.of_nat (length (memory s arraydef_0__names) + length name) <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ middle_separator :: name ++ last_separator :: tail ->
  exists final reply target, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 9 [value] name) reply target /\
    NativeState.represents final target /\ boundary s final reply tail /\ (Guarantees.safe logical -> Guarantees.safe target) /\
    (length (memory final arraydef_0__names)<=length (memory s arraydef_0__names)+length name)%nat /\
    (compact s logical -> compact final target).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hword Hname Hstate HbindingRoom HnameRoom Hfirst Hmiddle Hlast Hinput.
 destruct (generated_control s logical bs ns value name first_separator middle_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hword Hname
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate)
   HbindingRoom HnameRoom Hfirst Hmiddle Hlast Hinput)
 as (final & reply & target & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hcontrol & Hgrowth & Hcompact).
 exists final,reply,target. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - exact (NativeSchemaLift.canonical 9 57 [] s bs ns first_separator
    (decimalBytes value++middle_separator::name++last_separator::tail) observations final _ logical (Protocol.Req 9 [value] name) reply target
    ltac:(lia) ltac:(lia) eq_refl eq_refl Hmeta Htoken Hpending Herror Hfirst Hinput Hrun Hstate Hstep Harena Hclasses Hhistory Hnames).
 - split.
   + exact (NativeQueryCommands.observed_boundary s bs ns final observations _ reply tail Htoken Hbuffer Herror Hcontrol Hrun).
   + split;[intro Hsafe;eapply Guarantees.step_safe;eassumption|]. split;assumption.
Qed.
End Class.
Module TheoremName.
Import NameTheoremRefinement.NameTheoremRefinement.
Theorem generated_control s logical bs ns value name first_separator middle_separator last_separator tail observations :
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
    HistoryRefinement.represents final target /\ NameRepresentation.represents final (Protocol.bindings target) /\ control s final reply tail /\
    (length (memory final arraydef_0__names)<=length (memory s arraydef_0__names)+length name)%nat /\
    (compact s logical -> compact final target).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hvalid Hhistoryvalid Harena Hclasses Hhistory Hbindings Hbindingroom Hbytesroom Hsep1 Hsep2 Hsep3 Hin.
  destruct (ReadNameOne.generated_reads s 20 50 [48] value name first_separator middle_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror ltac:(unfold maximum; lia) eq_refl Hvalue Hvalid Hsep1 Hsep2 Hsep3 Hin)
    as [Hopcode [Hargument [Hreadname [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargnumber [Hargvalid [Hargerror
      [Hnamemeta [Hnamevalid [Hnameerror [Hnametoken [Hinput Houtput]]]]]]]]]]]]]]]].
  set (op := ReadNameOne.opcode_state s 50 [48] value middle_separator name last_separator tail).
  set (arg := ReadNameOne.argument_state s 50 [48] value middle_separator name last_separator tail).
  set (parsed := ReadNameOne.name_state s 50 [48] value middle_separator name last_separator tail).
  pose proof (parsed_prefix s 50 [48] value middle_separator name last_separator tail Hmeta) as HparsedPrefix.
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
    + destruct (Binding.generated_duplicate parsed (fun _ => false)
        (CommandNameTheoremExecution.binding_arguments (Z.of_nat fid)) (Protocol.bindings logical) name meaning observations
        ltac:(lia) Hparsedbindings Hnametoken Hlookup)
        as (final & Hbind & Hfinalbindings & Hprojection & Hfinalclasses & Hfinalhistory & Hfinalerror & Hbindcontrol & Hgrowth & Hcompact).
      assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (rewrite (proj1 Hprojection); lia).
      assert (Hfinalclear : meta_value final 8 = 0) by (rewrite Hfinalerror; exact Hnameerror).
      pose proof (CommandNameTheoremExecution.generated_command s bs ns op arg parsed final (Z.of_nat value) (Z.of_nat fid) observations
        _ Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
        Hnamemeta Hnamevalid Hnameerror Hreference ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) Hbind Hfinalmeta Hfinalclear) as Hrun.
      rewrite Hinput,Houtput in Hrun. exists final,Protocol.NO,logical. split; [exact Hrun|]. split.
      * apply logical_rejected; [right; congruence|exact Hunique].
      * split; [exact (FormulaProjection.storage_arena parsed final _ Hprojection Hparsedarena)|].
        split; [exact (Hfinalclasses _ _ Hparsedclasses)|]. split;[exact (Hfinalhistory logical Hparsedhistory)|]. split;[exact Hfinalbindings|].
        split;[exact (control_prefix s parsed final _ tail HparsedPrefix Hbindcontrol)|].
        split.
        -- unfold parsed in Hgrowth. rewrite ReadNameOne.name_other in Hgrowth by discriminate. exact Hgrowth.
        -- intro Hsource. apply Hcompact. unfold compact_bindings in *. unfold parsed. rewrite ReadNameOne.name_other by discriminate. exact Hsource.
    + assert (Hdecode : NameRepresentation.decode (Z.of_nat fid) 0 1 = Some (Protocol.theorem_binding fid)).
      { unfold NameRepresentation.decode. cbn. now rewrite Nat2Z.id. }
      destruct (Binding.generated_fresh parsed (fun _ => false)
        (CommandNameTheoremExecution.binding_arguments (Z.of_nat fid)) (Protocol.bindings logical) name fid 1 (Protocol.theorem_binding fid) observations
        ltac:(lia) Hparsedbuffer Hparsedbindings Hnametoken Hvalid Hlookup Hbindingroom Hparsedroom Hfidword Hdecode eq_refl eq_refl)
        as (final & Hbind & Hfinalbindings & Hprojection & Hfinalclasses & Hfinalhistory & Hfinalerror & Hbindcontrol & Hgrowth & Hcompact).
      assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (rewrite (proj1 Hprojection); lia).
      assert (Hfinalclear : meta_value final 8 = 0) by (rewrite Hfinalerror; exact Hnameerror).
      pose proof (CommandNameTheoremExecution.generated_command s bs ns op arg parsed final (Z.of_nat value) (Z.of_nat fid) observations
        _ Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
        Hnamemeta Hnamevalid Hnameerror Hreference ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) Hbind Hfinalmeta Hfinalclear) as Hrun.
      rewrite Hinput,Houtput in Hrun. exists final,(Protocol.OK fid),(named logical name fid). split; [exact Hrun|]. split.
      * now apply logical_success.
      * split; [exact (FormulaProjection.storage_arena parsed final _ Hprojection Hparsedarena)|].
        split; [exact (Hfinalclasses _ _ Hparsedclasses)|]. split;[exact (Hfinalhistory logical Hparsedhistory)|]. split;[exact Hfinalbindings|].
        split;[exact (control_prefix s parsed final _ tail HparsedPrefix Hbindcontrol)|].
        split.
        -- unfold parsed in Hgrowth. rewrite ReadNameOne.name_other in Hgrowth by discriminate. exact Hgrowth.
        -- intro Hsource. apply Hcompact. unfold compact_bindings in *. unfold parsed. rewrite ReadNameOne.name_other by discriminate. exact Hsource.
  - assert (Hreference : meta_value parsed 3 <= Z.of_nat value).
    { rewrite (proj1 Hparsedhistory). apply nth_error_None in Hentry. lia. }
    pose proof (CommandNameTheoremExecution.generated_rejected_command s bs ns op arg parsed (Z.of_nat value) observations
      Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
      Hnamemeta Hnamevalid Hnameerror Hreference) as Hrun.
    rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state parsed),Protocol.NO,logical. split; [exact Hrun|]. split.
    + apply logical_rejected; [now left|exact Hunique].
    + split.
      * eapply ArenaFrame.storage_arena; [apply ArenaFrame.storage_output|exact Hparsedarena].
      * split; [exact Hparsedclasses|]. split;[exact Hparsedhistory|]. split;[exact Hparsedbindings|]. split;[now apply NativeQueryCommands.no_control|].
        split.
        -- rewrite ReplyNOExecution.reply_memory. unfold parsed. rewrite ReadNameOne.name_other by discriminate. lia.
        -- apply compact_same. rewrite ReplyNOExecution.reply_memory. unfold parsed. apply ReadNameOne.name_other;discriminate.
Qed.
Theorem generated_total_protocol s logical bs ns value name first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 51 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> Protocol.valid_name name -> LogicalHistory.valid logical ->
  NativeState.represents s logical ->
  Z.of_nat (length (Protocol.bindings logical)) < maximum ->
  Z.of_nat (length (memory s arraydef_0__names) + length name) <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 48 :: first_separator :: decimalBytes value ++ middle_separator :: name ++ last_separator :: tail ->
  exists final reply target, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 20 [value] name) reply target /\
    NativeState.represents final target /\ boundary s final reply tail /\ (Guarantees.safe logical -> Guarantees.safe target) /\
    (length (memory final arraydef_0__names)<=length (memory s arraydef_0__names)+length name)%nat /\
    (compact s logical -> compact final target).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hword Hname Hvalid Hstate HbindingRoom HnameRoom Hfirst Hmiddle Hlast Hinput.
 destruct (generated_control s logical bs ns value name first_separator middle_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hword Hname Hvalid
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate)
   HbindingRoom HnameRoom Hfirst Hmiddle Hlast Hinput)
 as (final & reply & target & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hcontrol & Hgrowth & Hcompact).
 exists final,reply,target. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - exact (NativeSchemaLift.canonical 20 50 [48] s bs ns first_separator
    (decimalBytes value++middle_separator::name++last_separator::tail) observations final _ logical (Protocol.Req 20 [value] name) reply target
    ltac:(lia) ltac:(lia) eq_refl eq_refl Hmeta Htoken Hpending Herror Hfirst Hinput Hrun Hstate Hstep Harena Hclasses Hhistory Hnames).
 - split.
   + exact (NativeQueryCommands.observed_boundary s bs ns final observations _ reply tail Htoken Hbuffer Herror Hcontrol Hrun).
   + split;[intro Hsafe;eapply Guarantees.step_safe;eassumption|]. split;assumption.
Qed.
End TheoremName.
Module Schema.
Import NameSchemaRefinement.NameSchemaRefinement.
Theorem generated_control s logical bs ns value name first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 51 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> Protocol.valid_name name ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  NameRepresentation.represents s (Protocol.bindings logical) ->
  SchemaMetadata.represents s (Protocol.expressions logical) ->
  Z.of_nat (length (Protocol.bindings logical)) < maximum ->
  Z.of_nat (length (memory s arraydef_0__names) + length name) <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 51 :: first_separator :: decimalBytes value ++ middle_separator :: name ++ last_separator :: tail ->
  exists final reply target, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 23 [value] name) reply target /\
    NativeRepresentation.canonical_arena final (Protocol.formulas target) /\
    ClassStorage.represents final (Protocol.formulas target) (Protocol.classes target) /\
    HistoryRefinement.represents final target /\ NameRepresentation.represents final (Protocol.bindings target) /\
    SchemaMetadata.represents final (Protocol.expressions target) /\ control s final reply tail /\
    (length (memory final arraydef_0__names)<=length (memory s arraydef_0__names)+length name)%nat /\
    (compact s logical -> compact final target).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hvalid Harena Hclasses Hhistory Hbindings Hschemas Hbindingroom Hbytesroom Hsep1 Hsep2 Hsep3 Hin.
  destruct (ReadNameOne.generated_reads s 23 50 [51] value name first_separator middle_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror ltac:(unfold maximum; lia) eq_refl Hvalue Hvalid Hsep1 Hsep2 Hsep3 Hin)
    as [Hopcode [Hargument [Hreadname [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargnumber [Hargvalid [Hargerror
      [Hnamemeta [Hnamevalid [Hnameerror [Hnametoken [Hinput Houtput]]]]]]]]]]]]]]]].
  set (op := ReadNameOne.opcode_state s 50 [51] value middle_separator name last_separator tail).
  set (arg := ReadNameOne.argument_state s 50 [51] value middle_separator name last_separator tail).
  set (parsed := ReadNameOne.name_state s 50 [51] value middle_separator name last_separator tail).
  pose proof (parsed_prefix s 50 [51] value middle_separator name last_separator tail Hmeta) as HparsedPrefix.
  change (17 < length (memory parsed arraydef_0__meta))%nat in Hnamemeta.
  change (stdin parsed = tail) in Hinput. change (stdout parsed = stdout s) in Houtput.
  pose proof (ReadNameOne.name_storage s 50 [51] value middle_separator name last_separator tail Hmeta) as Hstorage.
  assert (Hparsedarena : NativeRepresentation.canonical_arena parsed (Protocol.formulas logical))
    by exact (ArenaFrame.storage_arena s parsed _ Hstorage Harena).
  pose proof (ReadNameOne.name_classes s 50 [51] value middle_separator name last_separator tail _ _ Hmeta Hclasses) as Hparsedclasses.
  pose proof (ReadNameOne.name_history s 50 [51] value middle_separator name last_separator tail logical Hmeta Hhistory) as Hparsedhistory.
  pose proof (ReadNameOne.name_bindings s 50 [51] value middle_separator name last_separator tail _ Hmeta Hbindings) as Hparsedbindings.
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
  assert (Hparsedschemas : SchemaMetadata.represents parsed (Protocol.expressions logical)).
  { eapply SchemaFrame.readToken_preserves; [exact Hreadname|].
    eapply SchemaFrame.readNat_preserves; [exact Hargument|].
    eapply SchemaFrame.readNat_preserves; [exact Hopcode|exact Hschemas]. }
  destruct (Protocol.pf logical value) as [cls|] eqn:Hentry.
  - assert (Hreference : Z.of_nat value < meta_value parsed 16).
    { rewrite (proj1 Hparsedschemas).
      unfold Protocol.pf in Hentry.
      destruct (nth_error (Protocol.expressions logical) value) as [expr|] eqn:Hexpr; [|discriminate].
      assert (value < length (Protocol.expressions logical))%nat by (apply nth_error_Some; congruence). lia. }
    destruct (SchemaMetadata.proof_fields parsed logical value cls Hparsedschemas Hentry)
      as [Hnodebound [Htype Hwidth]].
    assert (HnodeboundZ : (Z.to_nat (Z.of_nat value) < length (memory parsed arraydef_0__schemaNodes))%nat)
      by now rewrite Nat2Z.id.
    assert (HtypeZ : snd (fst (SchemaMetadata.node_at parsed (Z.to_nat (Z.of_nat value)))) = 2)
      by now rewrite Nat2Z.id.
    destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hlookup.
    + destruct (Binding.generated_duplicate parsed (fun _ => false)
        (CommandNameSchemaExecution.binding_arguments (Z.of_nat value)) (Protocol.bindings logical) name meaning observations
        ltac:(lia) Hparsedbindings Hnametoken Hlookup)
        as (final & Hbind & Hfinalbindings & Hprojection & Hfinalclasses & Hfinalhistory & Hfinalerror & Hbindcontrol & Hgrowth & Hcompact).
      assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (rewrite (proj1 Hprojection); lia).
      assert (Hfinalclear : meta_value final 8 = 0) by (rewrite Hfinalerror; exact Hnameerror).
      pose proof (CommandNameSchemaExecution.generated_command s bs ns op arg parsed final (Z.of_nat value) observations
        _ Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
        Hnamemeta Hnamevalid Hnameerror Hreference HnodeboundZ HtypeZ Hbind Hfinalmeta Hfinalclear) as Hrun.
      rewrite Hinput,Houtput in Hrun. exists final,Protocol.NO,logical. split; [exact Hrun|]. split.
      * apply logical_rejected; [right; congruence|exact Hunique].
      * split; [exact (FormulaProjection.storage_arena parsed final _ Hprojection Hparsedarena)|].
        split; [exact (Hfinalclasses _ _ Hparsedclasses)|]. split;[exact (Hfinalhistory logical Hparsedhistory)|]. split;[exact Hfinalbindings|].
        split;[exact (SchemaFrame.bindName_preserves _ _ _ _ _ _ _ Hbind Hparsedschemas)|].
        split;[exact (control_prefix s parsed final _ tail HparsedPrefix Hbindcontrol)|].
        split.
        -- unfold parsed in Hgrowth. rewrite ReadNameOne.name_other in Hgrowth by discriminate. exact Hgrowth.
        -- intro Hsource. apply Hcompact. unfold compact_bindings in *. unfold parsed. rewrite ReadNameOne.name_other by discriminate. exact Hsource.
    + assert (Hdecode : NameRepresentation.decode (Z.of_nat value) 0 2 = Some (Protocol.schema_binding value)).
      { unfold NameRepresentation.decode. cbn. now rewrite Nat2Z.id. }
      destruct (Binding.generated_fresh parsed (fun _ => false)
        (CommandNameSchemaExecution.binding_arguments (Z.of_nat value)) (Protocol.bindings logical) name value 2 (Protocol.schema_binding value) observations
        ltac:(lia) Hparsedbuffer Hparsedbindings Hnametoken Hvalid Hlookup Hbindingroom Hparsedroom Hvalue Hdecode eq_refl eq_refl)
        as (final & Hbind & Hfinalbindings & Hprojection & Hfinalclasses & Hfinalhistory & Hfinalerror & Hbindcontrol & Hgrowth & Hcompact).
      assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (rewrite (proj1 Hprojection); lia).
      assert (Hfinalclear : meta_value final 8 = 0) by (rewrite Hfinalerror; exact Hnameerror).
      pose proof (CommandNameSchemaExecution.generated_command s bs ns op arg parsed final (Z.of_nat value) observations
        _ Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreadname
        Hnamemeta Hnamevalid Hnameerror Hreference HnodeboundZ HtypeZ Hbind Hfinalmeta Hfinalclear) as Hrun.
      rewrite Hinput,Houtput in Hrun. exists final,(Protocol.OK value),(named logical name value). split; [exact Hrun|]. split.
      * eapply logical_success; eassumption.
      * split; [exact (FormulaProjection.storage_arena parsed final _ Hprojection Hparsedarena)|].
        split; [exact (Hfinalclasses _ _ Hparsedclasses)|]. split;[exact (Hfinalhistory logical Hparsedhistory)|]. split;[exact Hfinalbindings|].
        split;[exact (SchemaFrame.bindName_preserves _ _ _ _ _ _ _ Hbind Hparsedschemas)|].
        split;[exact (control_prefix s parsed final _ tail HparsedPrefix Hbindcontrol)|].
        split.
        -- unfold parsed in Hgrowth. rewrite ReadNameOne.name_other in Hgrowth by discriminate. exact Hgrowth.
        -- intro Hsource. apply Hcompact. unfold compact_bindings in *. unfold parsed. rewrite ReadNameOne.name_other by discriminate. exact Hsource.
  - assert (Hreject : execObserved (funcdef_0__command bs ns) (s,observations) =
      Some (tt,(ReplyNOExecution.reply_state parsed,
        observations ++ [{|flushedOutput := stdout parsed ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin parsed|}]))).
    { unfold Protocol.pf in Hentry.
      destruct (nth_error (Protocol.expressions logical) value) as [expr|] eqn:Hexpr.
      - destruct (SchemaMetadata.fields parsed _ value expr Hparsedschemas Hexpr) as [Hbound [Htype Hwidth]].
        assert (Hreference : Z.of_nat value < meta_value parsed 16).
        { rewrite (proj1 Hparsedschemas). assert (value < length (Protocol.expressions logical))%nat by (apply nth_error_Some; congruence). lia. }
        assert (HboundZ : (Z.to_nat (Z.of_nat value) < length (memory parsed arraydef_0__schemaNodes))%nat)
          by now rewrite Nat2Z.id.
        destruct expr; try discriminate;
          eapply (CommandNameSchemaExecution.generated_wrong_type_command s bs ns op arg parsed (Z.of_nat value));
          try eassumption; [rewrite Nat2Z.id; exact Htype|discriminate|rewrite Nat2Z.id; exact Htype|discriminate].
      - assert (Hreference : meta_value parsed 16 <= Z.of_nat value).
        { rewrite (proj1 Hparsedschemas). apply nth_error_None in Hexpr. lia. }
        eapply CommandNameSchemaExecution.generated_rejected_command; eassumption. }
    rewrite Hinput,Houtput in Hreject. exists (ReplyNOExecution.reply_state parsed),Protocol.NO,logical.
    split; [exact Hreject|]. split.
    + apply logical_rejected; [now left|exact Hunique].
    + split.
      * eapply ArenaFrame.storage_arena; [apply ArenaFrame.storage_output|exact Hparsedarena].
      * split; [exact Hparsedclasses|]. split; [exact Hparsedhistory|]. split;[exact Hparsedbindings|]. split;[exact Hparsedschemas|]. split;[now apply NativeQueryCommands.no_control|].
        split.
        -- rewrite ReplyNOExecution.reply_memory. unfold parsed. rewrite ReadNameOne.name_other by discriminate. lia.
        -- apply compact_same. rewrite ReplyNOExecution.reply_memory. unfold parsed. apply ReadNameOne.name_other;discriminate.
Qed.
Theorem generated_total_protocol s logical bs ns value name first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 51 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> Protocol.valid_name name ->
  NativeState.represents s logical ->
  Z.of_nat (length (Protocol.bindings logical)) < maximum ->
  Z.of_nat (length (memory s arraydef_0__names) + length name) <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 51 :: first_separator :: decimalBytes value ++ middle_separator :: name ++ last_separator :: tail ->
  exists final reply target, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 23 [value] name) reply target /\
    NativeState.represents final target /\ boundary s final reply tail /\ (Guarantees.safe logical -> Guarantees.safe target) /\
    (length (memory final arraydef_0__names)<=length (memory s arraydef_0__names)+length name)%nat /\
    (compact s logical -> compact final target).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hword Hname Hstate HbindingRoom HnameRoom Hfirst Hmiddle Hlast Hinput.
 destruct (generated_control s logical bs ns value name first_separator middle_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hword Hname
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate) (SchemaRepresentation.metadata _ _ (NativeState.schema_representation _ _ Hstate))
   HbindingRoom HnameRoom Hfirst Hmiddle Hlast Hinput)
 as (final & reply & target & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hmetadata & Hcontrol & Hgrowth & Hcompact).
 exists final,reply,target. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - exact (NativeSchemaLift.canonical 23 50 [51] s bs ns first_separator
    (decimalBytes value++middle_separator::name++last_separator::tail) observations final _ logical (Protocol.Req 23 [value] name) reply target
    ltac:(lia) ltac:(lia) eq_refl eq_refl Hmeta Htoken Hpending Herror Hfirst Hinput Hrun Hstate Hstep Harena Hclasses Hhistory Hnames).
 - split.
   + exact (NativeQueryCommands.observed_boundary s bs ns final observations _ reply tail Htoken Hbuffer Herror Hcontrol Hrun).
   + split;[intro Hsafe;eapply Guarantees.step_safe;eassumption|]. split;assumption.
Qed.
End Schema.
Lemma name_bytes_fold bindings : name_bytes bindings=fold_right (fun item total=>length (fst item)+total)%nat 0%nat bindings.
Proof. induction bindings as [|[name meaning] rest IH];cbn [name_bytes fold_right fst];[reflexivity|now rewrite IH]. Qed.
Lemma bytes_append before after name meaning : Protocol.bindings after=Protocol.bindings before++[(name,meaning)] ->
 bytes after=(bytes before+length name)%nat.
Proof. unfold bytes;intro H;rewrite H,name_bytes_app;cbn [name_bytes];lia. Qed.
Lemma marked_bytes bindings name cls :
 name_bytes (map (fun item=>if Protocol.name_eq_dec name (fst item) then (name,Protocol.class_binding cls true) else item) bindings)=name_bytes bindings.
Proof.
 induction bindings as [|[key meaning] rest IH];[reflexivity|]. cbn [map fst].
 destruct (Protocol.name_eq_dec name key) as [->|Hdifferent];cbn [name_bytes];now rewrite IH.
Qed.
Lemma accepted_bytes_bound source request reply after : Protocol.accepted source request reply after ->
 (bytes after<=bytes source+length (Protocol.object_name request))%nat.
Proof.
 intro Haccepted. destruct Haccepted;unfold bytes;
 cbn [Protocol.bindings Protocol.with_history Protocol.object_name];try lia;
 rewrite ?name_bytes_app;cbn [name_bytes];try lia.
 rewrite marked_bytes;lia.
Qed.
Theorem step_bytes_bound source request reply after : Protocol.step source request reply after ->
 (bytes after<=bytes source+length (Protocol.object_name request))%nat.
Proof.
 intro Hstep. destruct Hstep as [reply middle after Haccepted Hretained|after Hnone Hretained];
 destruct Hretained as [Hprefix [Hdistinct [Hclasses [Hhistory [Hbindings Hexpressions]]]]];
 unfold bytes;rewrite Hbindings.
 - exact (accepted_bytes_bound _ _ _ _ Haccepted).
 - lia.
Qed.
Lemma accepted_bytes_unchanged source request reply after :
 Protocol.opcode request<>9%nat -> Protocol.opcode request<>20%nat -> Protocol.opcode request<>23%nat ->
 Protocol.accepted source request reply after -> bytes after=bytes source.
Proof.
 intros H9 H20 H23 Haccepted. destruct Haccepted;
 cbn [Protocol.opcode] in H9,H20,H23;try congruence;
 unfold bytes;cbn [Protocol.bindings Protocol.with_history];try reflexivity.
 apply marked_bytes.
Qed.
Theorem step_bytes_unchanged source request reply after :
 Protocol.opcode request<>9%nat -> Protocol.opcode request<>20%nat -> Protocol.opcode request<>23%nat ->
 Protocol.step source request reply after -> bytes after=bytes source.
Proof.
 intros H9 H20 H23 Hstep. destruct Hstep as [reply middle after Haccepted Hretained|after Hnone Hretained];
 destruct Hretained as [Hprefix [Hdistinct [Hclasses [Hhistory [Hbindings Hexpressions]]]]];
 unfold bytes;rewrite Hbindings.
 - exact (accepted_bytes_unchanged _ _ _ _ H9 H20 H23 Haccepted).
 - reflexivity.
Qed.
Lemma bytes_initial : bytes Protocol.initial=0%nat.
Proof. reflexivity. Qed.
Lemma initial_compact native : memory native arraydef_0__names=[] -> compact native Protocol.initial.
Proof. unfold compact,compact_bindings;intro H;rewrite H;reflexivity. Qed.
End NativeNameCompact.
