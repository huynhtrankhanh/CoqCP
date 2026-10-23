From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash ReadToken ReadNat ReadName TokenByte DecimalInput CommandArgs NameQueryState
  NameSearch TypedNameLookup NameRepresentation ClassCertifyState ClassCertifyCommand RenameMemoClassSetness
  RenameMemoLengths RenameMemoParseDomain RenameMemoResourceBounds RenameStorage ArenaFrame FormulaProjection
  FormulaTopology FormulaEncoding Representation ClassStorage ClassLookup HistoryRefinement HistoryLookup SemanticFrames
  SchemaMetadata InternReserve.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ClassCertifyProtocol.
Import IndexExecution SipHashExecution ClassCertifyState.
Definition target logical next name cls (matches : bool) := Protocol.State next (Protocol.classes logical) (Protocol.history logical)
  (if matches then map (mark name cls) (Protocol.bindings logical) else Protocol.bindings logical) (Protocol.expressions logical).
Lemma logical_step logical next name cls c flag tid p matches :
  Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.class_binding cls flag) ->
  Protocol.class_at logical cls=Some c -> Protocol.theorem_at logical tid=Some p ->
  (matches=true <-> p=Protocol.class_setness c) ->
  (exists extra,next=Protocol.formulas logical++extra) -> NoDup next ->
  Protocol.step logical (Protocol.Req 14 [tid] name) (ClassCertifyCommand.reply cls matches)
    (target logical next name cls matches).
Proof.
  intros Hlookup Hclass Htheorem Hmatches Hprefix Hunique. destruct matches.
  - assert (Hp : p=Protocol.class_setness c) by (apply Hmatches; reflexivity). subst p.
    eapply Protocol.step_accept; [eapply Protocol.accept_certify; eassumption|].
    unfold Protocol.retained_storage,target. cbn [Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
    split; [exact Hprefix|]. split; [exact Hunique|]. split; [exists []; now rewrite app_nil_r|].
    repeat split; reflexivity.
  - apply Protocol.step_reject.
    + assert (Hbad : p<>Protocol.class_setness c).
      { intro Heq. pose proof ((proj2 Hmatches) Heq). discriminate. }
      intros reply after Haccepted. inversion Haccepted; subst;
        try solve [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end];
        try solve [match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end].
      congruence.
    + unfold Protocol.retained_storage,target. cbn [Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
      split; [exact Hprefix|]. split; [exact Hunique|]. split; [exists []; now rewrite app_nil_r|].
      repeat split; reflexivity.
Qed.
Theorem generated_named_protocol s logical bs ns name cls c flag tid p first middle last tail reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  (1024<=length (memory s arraydef_0__token))%nat -> (20<=length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15=50 -> meta_value s 8=0 -> Protocol.valid_name name -> Z.of_nat tid<=maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) -> FormulaTopology.ordered s (length (Protocol.formulas logical)) ->
  nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s ->
  HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
  SchemaMetadata.represents s (Protocol.expressions logical) -> NoDup (map fst (Protocol.bindings logical)) ->
  Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.class_binding cls flag) ->
  Protocol.class_at logical cls=Some c -> Protocol.theorem_at logical tid=Some p ->
  RenameMemoClassSetness.ready s (Protocol.formulas logical) cls c ->
  Z.of_nat (length (Protocol.formulas logical)+RenameMemoClassSetness.work s cls c+reserve)<=RenameMemoResourceBounds.doubling_limit ->
  TokenByteExecution.separator first -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s=52::first::name++middle::decimalBytes tid++last::tail ->
  exists final next matches,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (ClassCertifyCommand.reply cls matches);unreadInput:=tail|}])) /\
    (matches=true <-> p=Protocol.class_setness c) /\
    Protocol.step logical (Protocol.Req 14 [tid] name) (ClassCertifyCommand.reply cls matches) (target logical next name cls matches) /\
    NativeRepresentation.canonical_arena final next /\
    ClassStorage.represents final next (Protocol.classes logical) /\
    HistoryRefinement.represents final (target logical next name cls matches) /\
    NameRepresentation.represents final (Protocol.bindings (target logical next name cls matches)) /\
    SchemaMetadata.represents final (Protocol.expressions logical) /\
    (exists extra,next=Protocol.formulas logical++extra) /\
    Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit.
Proof.
  intros Hmeta Hsip Htoken Hbuffer Hpending Herror Hvalid Htidword Harena Htopology Hfalse Hclasses Hwellformed
    Hhistory Hnames Hschemas Hnamesunique Hlookup Hclass Htheorem Hready Hbudget Hsep1 Hsep2 Hsep3 Hin.
  destruct (ReadName.generated_reads s 14 49 [52] name first middle (decimalBytes tid++last::tail) observations
    ltac:(lia) Htoken Hpending Herror ltac:(unfold maximum; lia) eq_refl Hvalid Hsep1 Hsep2 Hin)
    as [Hopcode [Hreadname [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hnamemeta [Hnamevalid [Hnameerror [Hnametoken [Hnameinput Hnameoutput]]]]]]]]]]].
  set (op:=ReadName.opcode_state s 49 [52] name middle (decimalBytes tid++last::tail)).
  set (named:=ReadName.name_state s 49 [52] name middle (decimalBytes tid++last::tail)).
  fold op named in Hopcode,Hreadname,Hopmeta,Hopnumber,Hopvalid,Hoperror,Hnamemeta,Hnamevalid,Hnameerror,Hnametoken,Hnameinput,Hnameoutput.
  change (NameRepresentation.token_rep named name) in Hnametoken.
  pose proof (named_frame s 49 [52] name middle (decimalBytes tid++last::tail) ltac:(lia)) as Hnamedframe.
  change (frame s named) in Hnamedframe.
  pose proof (names s named _ Hnamedframe Hnames) as Hnamednames.
  destruct (lookup_present named (fun _=>false) (fun _=>0) (Protocol.bindings logical) name
    (Protocol.class_binding cls flag) observations ltac:(lia) Hnamednames Hnametoken Hlookup)
    as (looked & binding & raw & Hlookrun & Hlookframe & Hlookstorage & Hlookinput & Hlookoutput & Hbinding & Hsentinel & Hentry & Hraw & Hrecord).
  destruct raw as [[[[offset size] value] rawflag] kind].
  destruct Hrecord as [Hsize [Hoffset [Hoffsetword [Hvalueword [Hrawflag [Hspan [Hbytes [Hdecode Hvalidname]]]]]]]].
  pose proof (TypedNameLookup.decode_kind value rawflag kind _ Hdecode) as Hkind.
  pose proof (TypedNameLookup.decode_value value rawflag kind _ Hvalueword Hdecode) as Hvalue.
  change (kind=0) in Hkind. change (value=Z.of_nat cls) in Hvalue. subst kind value.
  assert (Hlookmeta : (31<length (memory looked arraydef_0__meta))%nat).
  { rewrite (proj1 Hlookframe),(proj1 Hnamedframe). exact Hmeta. }
  assert (Hlookerror : meta_value looked 8=0).
  { rewrite (proj2 (proj2 Hlookframe)) by lia. exact Hnameerror. }
  assert (Hlooktoken : (1024<=length (memory looked arraydef_0__token))%nat).
  { rewrite (proj1 Hlookstorage arraydef_0__token ltac:(discriminate)).
    unfold named,ReadName.name_state. rewrite ReadName.token_length.
    unfold ReadName.opcode_state. now rewrite CommandArgs.pending_token_length. }
  assert (Hlookclear : meta_value looked 15=0).
  { rewrite (proj1 (proj2 Hlookstorage)) by lia.
    unfold named,ReadName.name_state. rewrite ReadTokenExecution.result_meta_other by (try rewrite ReadName.opcode_meta_length; lia).
    apply CommandArgs.pending_cleared. lia. }
  set (parsed:=DecimalInput.encoded_result looked tid tail).
  pose proof (DecimalInput.generated_readNat_encoded_observed looked (fun _=>false) (fun _=>0) tid last tail observations
    ltac:(lia) Hlooktoken Hlookclear Hlookerror Htidword Hsep3 ltac:(rewrite Hlookinput; exact Hnameinput)) as Hreadtid.
  pose proof (number_frame looked tid tail ltac:(lia)) as Hnumberframe.
  change (frame looked parsed) in Hnumberframe.
  assert (Hparsedframe : frame s parsed) by (eapply frame_trans; [exact Hnamedframe|eapply frame_trans; eassumption]).
  pose proof (arena_frame s parsed Hparsedframe) as Hparsedstorage.
  assert (Hparsedmeta : (31<length (memory parsed arraydef_0__meta))%nat) by (rewrite (proj1 Hparsedframe); exact Hmeta).
  assert (Hparsederror : meta_value parsed 8=0) by (rewrite (proj2 (proj2 Hparsedframe)) by lia; exact Herror).
  pose proof (classes s parsed _ _ Hparsedframe Hclasses) as Hparsedclasses.
  pose proof (history s parsed logical Hparsedframe Hhistory) as Hparsedhistory.
  pose proof (names s parsed _ Hparsedframe Hnames) as Hparsednames.
  pose proof (schemas s parsed _ Hparsedframe Hschemas) as Hparsedschemas.
  assert (Hparsedarena : NativeRepresentation.canonical_arena parsed (Protocol.formulas logical))
    by (eapply ArenaFrame.storage_arena; eassumption).
  assert (Hparsedwellformed : ClassLookup.wellformed parsed)
    by (eapply ClassLookup.transport; [apply (proj1 (proj2 Hparsedframe)); discriminate|exact Hwellformed]).
  assert (Hparsedready : RenameMemoClassSetness.ready parsed (Protocol.formulas logical) cls c)
    by (eapply ready; eassumption).
  assert (Hparsedbudget : Z.of_nat (length (Protocol.formulas logical)+RenameMemoClassSetness.work parsed cls c+reserve)<=RenameMemoResourceBounds.doubling_limit)
    by (now rewrite (work s parsed cls c Hparsedframe)).
  destruct (RenameMemoClassSetness.generated_refines parsed (fun _=>false) (ClassCertifyCommand.arguments (Z.of_nat cls))
    (Protocol.formulas logical) (Protocol.classes logical) cls c reserve observations Hparsedmeta
    ltac:(rewrite (proj1 (proj2 Hparsedframe)) by discriminate; exact Hsip) Hparsedarena
    (RenameMemoParseDomain.topology s parsed _ Hparsedstorage Htopology) Hfalse Hparsederror Hparsedclasses Hparsedwellformed
    Hclass eq_refl Hparsedready Hparsedbudget)
    as (built & next & index & Hsetness & Harena_next & Hindex & Hindexword & Hmeaning & Hprefix & Hbuilterror & Hbuildframe
      & Hbuiltclasses & Hbuiltwellformed & Hremaining & Hbuiltordered & Hgrowth).
  pose proof (RenameStorage.history_transport parsed built logical Hbuildframe Hparsedhistory) as Hbuilthistory.
  pose proof (RenameStorage.names_transport parsed built _ Hbuildframe Hparsednames) as Hbuiltnames.
  pose proof (RenameStorage.schemas_transport parsed built _ Hbuildframe Hparsedschemas) as Hbuiltchemas.
  destruct (HistoryLookup.theorem_lookup built logical tid p Hbuilthistory Htheorem)
    as (fid & Hfid & Hformula & Htidbound & Htheoremnth).
  assert (Hformulanext : nth_error next fid=Some p) by (eapply InternReserve.lookup_preserved; eassumption).
  assert (Hbuiltmeta : (17<length (memory built arraydef_0__meta))%nat).
  { pose proof (proj1 (proj1 Harena_next)) as [Hm Hrest]. lia. }
  assert (Hbuiltbuffer : (20<=length (memory built arraydef_0__printBuffer))%nat).
  { rewrite (proj1 Hbuildframe arraydef_0__printBuffer ltac:(repeat split; discriminate)).
    rewrite (proj1 (proj2 Hparsedframe)) by discriminate. exact Hbuffer. }
  assert (Hparsedrecord : nth_error (memory parsed arraydef_0__bindings) binding=Some (offset,size,Z.of_nat cls,rawflag,0)).
  { unfold parsed. rewrite DecimalInput.encoded_other by discriminate. exact Hraw. }
  assert (Hbuiltrecord : nth_error (memory built arraydef_0__bindings) binding=Some (offset,size,Z.of_nat cls,rawflag,0)).
  { rewrite (proj1 Hbuildframe arraydef_0__bindings ltac:(repeat split; discriminate)). exact Hparsedrecord. }
  assert (Hparsedbound : (binding<length (memory parsed arraydef_0__bindings))%nat) by (apply nth_error_Some; congruence).
  assert (Hbuiltbound : (binding<length (memory built arraydef_0__bindings))%nat) by (apply nth_error_Some; congruence).
  assert (Htidcount : Z.of_nat tid<meta_value parsed 3).
  { rewrite (proj1 Hparsedhistory). assert (tid<length (Protocol.history logical))%nat by (apply nth_error_Some; congruence). lia. }
  assert (Hparsednumber : meta_value parsed 11=Z.of_nat tid) by (apply (proj1 (DecimalInput.encoded_result_correct looked tid tail ltac:(lia) Htidword))).
  assert (Hparsedvalid : meta_value parsed 14=1).
  { unfold parsed,DecimalInput.encoded_result,ReadNatExecution.token_number. rewrite meta_store_other by discriminate. apply ReadTokenExecution.result_valid. lia. }
  assert (Htheoremrecord : nth_error (memory built arraydef_0__theorems) tid=Some (Z.of_nat fid))
    by (apply nth_error_nth' with (d:=0) in Htidbound; rewrite Htidbound; f_equal; exact Htheoremnth).
  assert (Hclsword : Z.of_nat cls<=maximum) by exact (proj2 Hvalueword).
  assert (Hbuiltinput : stdin built=tail).
  { rewrite (proj1 (proj2 (proj2 Hbuildframe))). reflexivity. }
  assert (Hbuiltoutput : stdout built=stdout s).
  { transitivity (stdout parsed); [exact (proj2 (proj2 (proj2 Hbuildframe)))|].
    transitivity (stdout looked); [exact (proj2 (proj2 (DecimalInput.encoded_result_correct looked tid tail ltac:(lia) Htidword)))|].
    transitivity (stdout named); assumption. }
  set (matches:=if Nat.eq_dec index fid then true else false).
  assert (Hmatches : matches=true <-> p=Protocol.class_setness c).
  { unfold matches. destruct (Nat.eq_dec index fid) as [Heq|Hne].
    - subst index. split; intro H; [congruence|reflexivity].
    - split; [discriminate|]. intro Hsame. exfalso. apply Hne. subst p.
      exact ((proj1 (proj2 (proj2 Harena_next))) index fid _ Hmeaning Hformulanext). }
  assert (Hyes : matches=true -> meta_value built 0=Z.of_nat fid) by (unfold matches; destruct (Nat.eq_dec index fid); intros; congruence).
  assert (Hno : matches=false -> meta_value built 0<>Z.of_nat fid) by
    (unfold matches; destruct (Nat.eq_dec index fid); intros; [discriminate|rewrite Hindex;lia]).
  pose proof (ClassCertifyCommand.generated_command s bs ns op named looked parsed built binding tid cls offset size rawflag
    (Z.of_nat fid) matches observations Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hreadname Hnamemeta Hnamevalid Hnameerror
    Hlookrun ltac:(lia) Hbinding Hlookerror Hreadtid ltac:(lia) Hparsednumber Hparsedvalid Hparsederror ltac:(unfold maximum in Hsentinel;lia)
    Hparsedbound Hparsedrecord Htidcount Hsetness ltac:(lia) Hbuilterror Htidbound Htheoremrecord Hbuiltbound Hbuiltrecord Hyes Hno Hbuiltbuffer Hclsword) as Hrun.
  rewrite Hbuiltinput,Hbuiltoutput in Hrun.
  exists (ClassCertifyCommand.result built binding offset size cls matches),next,matches; split; [exact Hrun|].
  split; [exact Hmatches|].
  split; [eapply logical_step; [exact Hlookup|exact Hclass|exact Htheorem|exact Hmatches|exact Hprefix|now apply (SemanticFrames.arena_NoDup built)]|].
  split; [eapply FormulaProjection.storage_arena; [apply result_projection|exact Harena_next]|].
  split; [now apply result_classes|].
  split; [apply result_history; exact Hbuilthistory|].
  split; [eapply result_names; eassumption|].
  split; [now apply result_schemas|].
  split; assumption.
Qed.
End ClassCertifyProtocol.
