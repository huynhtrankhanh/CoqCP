From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Guarantees.
From NativeProof Require Import Index SipHash ReadToken ReadNat ReadName TokenByte DecimalInput CommandArgs NameQueryState
  NameSearch TypedNameLookup NameRepresentation ClassCertifyState ClassCertifyCommand RenameMemoClassSetness
  RenameMemoLengths RenameMemoParseDomain RenameMemoResourceBounds RenameStorage ArenaFrame FormulaProjection
  FormulaTopology FormulaEncoding Representation ClassStorage ClassLookup HistoryRefinement HistoryLookup SemanticFrames
  SchemaMetadata InternReserve ClassCertifyProtocol ClassCertifyRejection ClassCertifyTotal ClassCertifyLengths
  LogicalNames LogicalHistory ReplyOK ReplyNO HashTable ClassCertifyRejectedCommand.
From NativeProof Require Import ClassCertifyInvariant NativeState NativeSchemaLift NativeCommandStop NativeCommandBoundary.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeClassCertifyBoundary.
Import IndexExecution SipHashExecution ClassCertifyState ClassCertifyProtocol ClassCertifyInvariant.
Theorem named_control s logical bs ns name cls c flag tid p first middle last tail reserve observations :
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
    Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\
    machine_invariant s final next /\ stdin final=tail /\
    stdout final=stdout s++Protocol.reply_bytes (ClassCertifyCommand.reply cls matches).
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
  split; [eapply ClassCertifyProtocol.logical_step; [exact Hlookup|exact Hclass|exact Htheorem|exact Hmatches|exact Hprefix|now apply (SemanticFrames.arena_NoDup built)]|].
  split; [eapply FormulaProjection.storage_arena; [apply result_projection|exact Harena_next]|].
  split; [now apply result_classes|].
  split; [apply result_history; exact Hbuilthistory|].
  split; [eapply result_names; eassumption|].
  split; [now apply result_schemas|].
  split; [exact Hprefix|]. split; [exact Hremaining|].
  split.
  - apply result_machine; [|exact Hbuilterror|exact Hbuiltordered|exact Hbuiltwellformed].
    eapply lengths_trans; [apply named_lengths|].
    eapply lengths_trans; [eapply looked_lengths; [exact Hlookstorage|exact (proj1 Hlookframe)]|].
    eapply lengths_trans; [apply parsed_lengths|]. eapply built_lengths; exact Hsetness.
  - destruct matches;cbn [ClassCertifyCommand.result ClassCertifyCommand.reply].
    + rewrite ReplyOKExecution.reply_input,ReplyOKExecution.reply_output.
      change (stdin built=tail /\ stdout built++Protocol.reply_bytes (Protocol.OK cls)=stdout s++Protocol.reply_bytes (Protocol.OK cls)).
      rewrite Hbuiltinput,Hbuiltoutput. split;reflexivity.
    + rewrite ReplyNOExecution.reply_input,ReplyNOExecution.reply_output,Hbuiltinput,Hbuiltoutput. split;reflexivity.
Qed.
Theorem rejected_control s logical bs ns name tid first middle last tail observations :
  (17<length (memory s arraydef_0__meta))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
  meta_value s 15=50 -> meta_value s 8=0 -> Protocol.valid_name name -> Z.of_nat tid<=maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) ->
  HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
  SchemaMetadata.represents s (Protocol.expressions logical) ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) -> ClassLookup.wellformed s ->
  ClassCertifyRejection.invalid logical name tid ->
  TokenByteExecution.separator first -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s=52::first::name++middle::decimalBytes tid++last::tail ->
  exists final, execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
    observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.NO;unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 14 [tid] name) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final logical /\ NameRepresentation.represents final (Protocol.bindings logical) /\
    SchemaMetadata.represents final (Protocol.expressions logical) /\
    machine_invariant s final (Protocol.formulas logical) /\ stdin final=tail /\
    stdout final=stdout s++Protocol.reply_bytes Protocol.NO.
Proof.
  intros Hmeta Htoken Hpending Herror Hvalid Htidword Harena Hclasses Hhistory Hnames Hschemas Htopology Hwellformed Hinvalid Hsep1 Hsep2 Hsep3 Hin.
  destruct (ReadName.generated_reads s 14 49 [52] name first middle (decimalBytes tid++last::tail) observations
    Hmeta Htoken Hpending Herror ltac:(unfold maximum; lia) eq_refl Hvalid Hsep1 Hsep2 Hin)
    as [Hopcode [Hreadname [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hnamemeta [Hnamevalid [Hnameerror [Hnametoken [Hnameinput Hnameoutput]]]]]]]]]]].
  set (op:=ReadName.opcode_state s 49 [52] name middle (decimalBytes tid++last::tail)).
  set (named:=ReadName.name_state s 49 [52] name middle (decimalBytes tid++last::tail)).
  fold op named in Hopcode,Hreadname,Hopmeta,Hopnumber,Hopvalid,Hoperror,Hnamemeta,Hnamevalid,Hnameerror,Hnametoken,Hnameinput,Hnameoutput.
  pose proof (named_frame s 49 [52] name middle (decimalBytes tid++last::tail) Hmeta) as Hnamedframe.
  change (frame s named) in Hnamedframe.
  pose proof (names s named _ Hnamedframe Hnames) as Hnamednames.
  destruct (TypedNameLookup.generated named (fun _=>false) (fun _=>0) (Protocol.bindings logical) name observations
    ltac:(lia) Hnamednames Hnametoken)
    as (looked & Hlookrun & Hlooknames & Hlooklength & Hlookstorage & Houtcome).
  pose proof (looked_frame named looked Hlookstorage Hlooklength) as Hlookframe.
  assert (Hlookmeta : (17<length (memory looked arraydef_0__meta))%nat) by (rewrite Hlooklength; exact Hnamemeta).
  assert (Hlookerror : meta_value looked 8=0) by (rewrite (proj1 (proj2 Hlookstorage)) by lia; exact Hnameerror).
  assert (Hlooktoken : (1024<=length (memory looked arraydef_0__token))%nat).
  { rewrite (proj1 Hlookstorage arraydef_0__token ltac:(discriminate)).
    unfold named,ReadName.name_state. rewrite ReadName.token_length.
    unfold ReadName.opcode_state. now rewrite CommandArgs.pending_token_length. }
  assert (Hlookclear : meta_value looked 15=0).
  { rewrite (proj1 (proj2 Hlookstorage)) by lia.
    unfold named,ReadName.name_state. rewrite ReadTokenExecution.result_meta_other by (try rewrite ReadName.opcode_meta_length; lia).
    apply CommandArgs.pending_cleared. exact Hmeta. }
  set (parsed:=DecimalInput.encoded_result looked tid tail).
  pose proof (DecimalInput.generated_readNat_encoded_observed looked (fun _=>false) (fun _=>0) tid last tail observations
    Hlookmeta Hlooktoken Hlookclear Hlookerror Htidword Hsep3
    ltac:(rewrite (proj1 (proj2 (proj2 Hlookstorage)));exact Hnameinput)) as Hreadtid.
  pose proof (number_frame looked tid tail Hlookmeta) as Hnumberframe.
  change (frame looked parsed) in Hnumberframe.
  assert (Hparsedframe : frame s parsed) by (eapply frame_trans; [exact Hnamedframe|eapply frame_trans; eassumption]).
  assert (Hparsedmeta : (17<length (memory parsed arraydef_0__meta))%nat) by (rewrite (proj1 Hparsedframe); exact Hmeta).
  assert (Hparsederror : meta_value parsed 8=0) by (rewrite (proj2 (proj2 Hparsedframe)) by lia; exact Herror).
  pose proof (history s parsed logical Hparsedframe Hhistory) as Hparsedhistory.
  assert (Hparsednumber : meta_value parsed 11=Z.of_nat tid)
    by exact (proj1 (DecimalInput.encoded_result_correct looked tid tail Hlookmeta Htidword)).
  assert (Hparsedvalid : meta_value parsed 14=1).
  { unfold parsed,DecimalInput.encoded_result,ReadNatExecution.token_number. rewrite meta_store_other by discriminate.
    apply ReadTokenExecution.result_valid. exact Hlookmeta. }
  assert (Hparsedoutput : stdout parsed=stdout s).
  { transitivity (stdout looked); [exact (proj2 (proj2 (DecimalInput.encoded_result_correct looked tid tail Hlookmeta Htidword)))|].
    transitivity (stdout named); [exact (proj2 (proj2 (proj2 Hlookstorage)))|exact Hnameoutput]. }
  assert (Hrawguards : exists (found : bool) binding offset size value flag kind,
    meta_value looked 0=(if found then Z.of_nat binding else maximum) /\
    (found=true -> Z.of_nat binding<>maximum) /\
    (found=true -> binding<length (memory parsed arraydef_0__bindings))%nat /\
    (found=true -> nth_error (memory parsed arraydef_0__bindings) binding=Some (offset,size,value,flag,kind)) /\
    (found=false \/ kind<>0 \/ meta_value parsed 3<=Z.of_nat tid)).
  { unfold TypedNameLookup.outcome in Houtcome.
    destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hlookup.
    - destruct Houtcome as (binding & raw & Hbinding & Hsentinel & Hbound & Hraw & Hrecord).
      destruct raw as [[[[offset size] value] flag] kind].
      destruct Hrecord as (Hsize & Hoff & Hoffword & Hword & Hflag & Hspan & Hbytes & Hdecode & Hvalidname).
      pose proof (TypedNameLookup.decode_kind value flag kind meaning Hdecode) as Hkind.
      assert (Hparsedraw : nth_error (memory parsed arraydef_0__bindings) binding=Some (offset,size,value,flag,kind)).
      { unfold parsed. rewrite DecimalInput.encoded_other by discriminate.
        apply nth_error_nth' with (d:=(0,0,0,0,0)) in Hbound. rewrite Hbound. now f_equal. }
      exists true,binding,offset,size,value,flag,kind. split; [exact Hbinding|].
      split; [intros; lia|]. split; [intros; apply nth_error_Some; congruence|]. split; [intros; exact Hparsedraw|].
      destruct meaning as [cls certified|theorem|root]; [right;right|right;left|right;left];
        cbn [TypedNameLookup.binding_kind] in Hkind; try lia.
      specialize (Hinvalid cls certified Hlookup). rewrite (proj1 Hparsedhistory).
      apply nth_error_None in Hinvalid. lia.
    - exists false,0%nat,0,0,0,0,0. split; [exact Houtcome|]. split; [discriminate|].
      split; [discriminate|]. split; [discriminate|]. now left. }
  destruct Hrawguards as (found & binding & offset & size & value & flag & kind & Hbinding & Hsentinel & Hbound & Hraw & Hbad).
  pose proof (ClassCertifyRejectedCommand.generated_command s bs ns op named looked parsed found binding tid offset size value flag kind
    observations Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hreadname Hnamemeta Hnamevalid Hnameerror Hlookrun Hlookmeta Hbinding
    Hlookerror Hreadtid Hparsedmeta Hparsednumber Hparsedvalid Hparsederror Hsentinel Hbound Hraw Hbad) as Hrun.
  rewrite Hparsedoutput in Hrun. change (stdin parsed) with tail in Hrun.
  exists (ReplyNOExecution.reply_state parsed). split; [exact Hrun|].
  split; [apply ClassCertifyRejection.logical_rejected; [exact Hinvalid|now apply (SemanticFrames.arena_NoDup s)]|].
  split; [eapply ArenaFrame.storage_arena; [apply arena_frame;exact Hparsedframe|exact Harena]|].
  split; [eapply classes; eassumption|]. split; [exact Hparsedhistory|].
  split; [eapply names; eassumption|]. split; [eapply schemas; eassumption|].
  split.
  - split.
    + intros array Harray. rewrite ReplyNOExecution.reply_memory.
      eapply lengths_trans; [apply named_lengths| |exact Harray].
      eapply lengths_trans; [eapply looked_lengths; [exact Hlookstorage|exact Hlooklength]|apply parsed_lengths].
    + split; [exact Hparsederror|]. split.
      * eapply RenameMemoParseDomain.topology; [apply arena_frame; exact Hparsedframe|exact Htopology].
      * eapply ClassLookup.transport; [apply (proj1 (proj2 Hparsedframe)); discriminate|exact Hwellformed].
  - rewrite ReplyNOExecution.reply_input,ReplyNOExecution.reply_output,Hparsedoutput. split;reflexivity.
Qed.
Theorem total_control s logical bs ns name tid first middle last tail reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  (1024<=length (memory s arraydef_0__token))%nat -> (20<=length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15=50 -> meta_value s 8=0 -> Protocol.valid_name name -> Z.of_nat tid<=maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) -> FormulaTopology.ordered s (length (Protocol.formulas logical)) ->
  nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s ->
  HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
  SchemaMetadata.represents s (Protocol.expressions logical) -> NoDup (map fst (Protocol.bindings logical)) ->
  LogicalNames.valid logical -> LogicalHistory.valid logical -> ClassCertifyTotal.capacity s logical name tid reserve ->
  TokenByteExecution.separator first -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s=52::first::name++middle::decimalBytes tid++last::tail ->
  exists final reply after,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 14 [tid] name) reply after /\
    NativeRepresentation.canonical_arena final (Protocol.formulas after) /\
    ClassStorage.represents final (Protocol.formulas after) (Protocol.classes after) /\
    HistoryRefinement.represents final after /\ NameRepresentation.represents final (Protocol.bindings after) /\
    SchemaMetadata.represents final (Protocol.expressions after) /\
    machine_invariant s final (Protocol.formulas after) /\
    LogicalNames.valid after /\ LogicalHistory.valid after /\
    NoDup (map fst (Protocol.bindings after)) /\
    Protocol.classes after=Protocol.classes logical /\
    Protocol.history after=Protocol.history logical /\
    Protocol.expressions after=Protocol.expressions logical /\
    (exists extra,Protocol.formulas after=Protocol.formulas logical++extra) /\
    stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes reply.
Proof.
  intros Hmeta Hsip Htoken Hbuffer Hpending Herror Hvalid Htidword Harena Htopology Hfalse Hclasses Hwellformed Hhistory
    Hnames Hschemas Hunique Hvalidnames Hvalidhistory Hcapacity Hsep1 Hsep2 Hsep3 Hin.
  destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hlookup.
  - destruct meaning as [cls flag|formula|root].
    + destruct (LogicalNames.lookup_valid logical name _ Hvalidnames Hlookup) as [c Hclass].
      destruct (nth_error (Protocol.history logical) tid) as [fid|] eqn:Hhistoryentry.
      * destruct (Hvalidhistory tid fid Hhistoryentry) as [p Hformula].
        assert (Htheorem : Protocol.theorem_at logical tid=Some p).
        { unfold Protocol.theorem_at. now rewrite Hhistoryentry. }
        destruct (Hcapacity cls flag c p Hlookup Hclass Htheorem) as [Hready Hbudget].
        destruct (named_control s logical bs ns name cls c flag tid p first middle last tail reserve observations
          Hmeta Hsip Htoken Hbuffer Hpending Herror Hvalid Htidword Harena Htopology Hfalse Hclasses Hwellformed Hhistory Hnames Hschemas Hunique
          Hlookup Hclass Htheorem Hready Hbudget Hsep1 Hsep2 Hsep3 Hin)
          as (final & next & matches & Hrun & Hmatches & Hstep & Harena_next & Hclasses_next & Hhistory_next & Hnames_next & Hschemas_next & Hprefix & Hremaining & Hmachine & Hfinalin & Hfinalout).
        pose proof (LogicalNames.step_valid _ _ _ _ Hstep Hvalidnames Hvalidhistory) as Hvalidnames_next.
        pose proof (LogicalHistory.step_valid _ _ _ _ Hstep Hvalidhistory) as Hvalidhistory_next.
        assert (Hunique_next : NoDup (map fst (Protocol.bindings (target logical next name cls matches)))).
        { rewrite target_keys. exact Hunique. }
        exists final,(ClassCertifyCommand.reply cls matches),(target logical next name cls matches).
        repeat first [assumption|split|reflexivity].
      * assert (Hinvalid : ClassCertifyRejection.invalid logical name tid).
        { intros other cert Hbinding. exact Hhistoryentry. }
        destruct (rejected_control s logical bs ns name tid first middle last tail observations
          ltac:(lia) Htoken Hpending Herror Hvalid Htidword Harena Hclasses Hhistory Hnames Hschemas Htopology Hwellformed Hinvalid Hsep1 Hsep2 Hsep3 Hin)
          as (final & Hrun & Hstep & Harena_next & Hclasses_next & Hhistory_next & Hnames_next & Hschemas_next & Hmachine & Hfinalin & Hfinalout).
        assert (Hprefix : exists extra,Protocol.formulas logical=Protocol.formulas logical++extra)
          by (exists []; now rewrite app_nil_r).
        exists final,Protocol.NO,logical. repeat first [assumption|split|reflexivity].
    + assert (Hinvalid : ClassCertifyRejection.invalid logical name tid) by (intros other cert Hbinding; congruence).
      destruct (rejected_control s logical bs ns name tid first middle last tail observations
        ltac:(lia) Htoken Hpending Herror Hvalid Htidword Harena Hclasses Hhistory Hnames Hschemas Htopology Hwellformed Hinvalid Hsep1 Hsep2 Hsep3 Hin)
        as (final & Hrun & Hstep & Harena_next & Hclasses_next & Hhistory_next & Hnames_next & Hschemas_next & Hmachine & Hfinalin & Hfinalout).
      assert (Hprefix : exists extra,Protocol.formulas logical=Protocol.formulas logical++extra)
          by (exists []; now rewrite app_nil_r).
        exists final,Protocol.NO,logical. repeat first [assumption|split|reflexivity].
    + assert (Hinvalid : ClassCertifyRejection.invalid logical name tid) by (intros other cert Hbinding; congruence).
      destruct (rejected_control s logical bs ns name tid first middle last tail observations
        ltac:(lia) Htoken Hpending Herror Hvalid Htidword Harena Hclasses Hhistory Hnames Hschemas Htopology Hwellformed Hinvalid Hsep1 Hsep2 Hsep3 Hin)
        as (final & Hrun & Hstep & Harena_next & Hclasses_next & Hhistory_next & Hnames_next & Hschemas_next & Hmachine & Hfinalin & Hfinalout).
      assert (Hprefix : exists extra,Protocol.formulas logical=Protocol.formulas logical++extra)
          by (exists []; now rewrite app_nil_r).
        exists final,Protocol.NO,logical. repeat first [assumption|split|reflexivity].
  - assert (Hinvalid : ClassCertifyRejection.invalid logical name tid) by (intros other cert Hbinding; congruence).
    destruct (rejected_control s logical bs ns name tid first middle last tail observations
      ltac:(lia) Htoken Hpending Herror Hvalid Htidword Harena Hclasses Hhistory Hnames Hschemas Htopology Hwellformed Hinvalid Hsep1 Hsep2 Hsep3 Hin)
      as (final & Hrun & Hstep & Harena_next & Hclasses_next & Hhistory_next & Hnames_next & Hschemas_next & Hmachine & Hfinalin & Hfinalout).
    assert (Hprefix : exists extra,Protocol.formulas logical=Protocol.formulas logical++extra)
          by (exists []; now rewrite app_nil_r).
        exists final,Protocol.NO,logical. repeat first [assumption|split|reflexivity].
Qed.

Definition complete s logical bs ns name tid tail observations final reply after :=
 execObserved (funcdef_0__command bs ns) (s,observations)=Some(tt,(final,
   observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 14 [tid] name) reply after /\
 NativeState.represents final after /\ NativeCommandBoundary.io s final reply tail /\
 machine_invariant s final (Protocol.formulas after) /\
 LogicalNames.valid after /\ LogicalHistory.valid after /\ NoDup (map fst (Protocol.bindings after)) /\
 Protocol.classes after=Protocol.classes logical /\ Protocol.history after=Protocol.history logical /\
 Protocol.expressions after=Protocol.expressions logical /\
 (exists extra,Protocol.formulas after=Protocol.formulas logical++extra) /\
 (Guarantees.safe logical -> Guarantees.safe after).

Theorem generated_total s logical bs ns name tid first middle last tail reserve observations :
 (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat -> (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=50 -> meta_value s 8=0 -> Protocol.valid_name name -> Z.of_nat tid<=maximum ->
 NativeState.represents s logical -> FormulaTopology.ordered s (length (Protocol.formulas logical)) ->
 nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity -> ClassLookup.wellformed s ->
 NoDup (map fst (Protocol.bindings logical)) -> LogicalNames.valid logical -> LogicalHistory.valid logical ->
 ClassCertifyTotal.capacity s logical name tid reserve ->
 TokenByteExecution.separator first -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
 stdin s=52::first::name++middle::decimalBytes tid++last::tail ->
 exists final reply after, complete s logical bs ns name tid tail observations final reply after.
Proof.
 intros Hmeta Hsip Htoken Hprint Hpending Herror Hvalid Htidword Hstate Htop Hfalse Hwellformed
   Hunique Hvalidnames Hvalidhistory Hcapacity Hfirst Hmiddle Hlast Hinput.
 destruct (total_control s logical bs ns name tid first middle last tail reserve observations
   Hmeta Hsip Htoken Hprint Hpending Herror Hvalid Htidword
   (NativeState.formula_representation _ _ Hstate) Htop Hfalse (NativeState.class_representation _ _ Hstate) Hwellformed
   (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate)
   (proj1 (NativeState.schema_representation _ _ Hstate)) Hunique Hvalidnames Hvalidhistory Hcapacity Hfirst Hmiddle Hlast Hinput)
   as (final & reply & after & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hschemas & Hmachine &
     Hvalidnames' & Hvalidhistory' & Hunique' & Hclasses' & Hhistory' & Hschemas' & Hprefix & Hin & Hout).
 assert (Hstate':NativeState.represents final after).
 { exact (NativeSchemaLift.canonical 14 49 [52] s bs ns first (name++middle::decimalBytes tid++last::tail)
     observations final _ logical (Protocol.Req 14 [tid] name) reply after ltac:(lia) ltac:(lia) eq_refl eq_refl
     ltac:(lia) Htoken Hpending Herror Hfirst Hinput Hrun Hstate Hstep Harena Hclasses Hhistory Hnames). }
 assert (Herror':meta_value final 8=0) by exact (proj1 (proj2 Hmachine)).
 assert (Hstop:meta_value final 9=meta_value s 9).
 { exact (NativeCommandStop.canonical 14 49 [52] s bs ns first (name++middle::decimalBytes tid++last::tail)
     observations final _ ltac:(lia) eq_refl ltac:(lia) Htoken Hpending Herror Hfirst Hinput Hrun Herror'). }
 destruct (ClassCertifyInvariant.invariant_lengths s final _ Hmachine) as (Hm & Hsip' & Htoken' & Hprint').
 exists final,reply,after. unfold complete. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hstate'|]. split.
 - unfold NativeCommandBoundary.io. rewrite Htoken',Hprint'. repeat split;assumption.
 - split;[exact Hmachine|]. split;[exact Hvalidnames'|]. split;[exact Hvalidhistory'|].
   split;[exact Hunique'|]. split;[exact Hclasses'|]. split;[exact Hhistory'|].
   split;[exact Hschemas'|]. split;[exact Hprefix|]. exact (Guarantees.step_safe _ _ _ _ Hstep).
Qed.
End NativeClassCertifyBoundary.
