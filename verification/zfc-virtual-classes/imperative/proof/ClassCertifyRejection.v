From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ReadToken ReadNat ReadName TokenByte DecimalInput CommandArgs NameSearch
  TypedNameLookup NameRepresentation ClassCertifyState ClassCertifyRejectedCommand ArenaFrame Representation
  ClassStorage HistoryRefinement SemanticFrames SchemaMetadata ReplyNO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ClassCertifyRejection.
Import IndexExecution SipHashExecution ClassCertifyState.
Definition invalid logical name tid := forall cls flag,
  Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.class_binding cls flag) ->
  nth_error (Protocol.history logical) tid=None.
Lemma logical_rejected logical name tid : invalid logical name tid -> NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req 14 [tid] name) Protocol.NO logical.
Proof.
  intros Hinvalid Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros reply after Haccepted. inversion Haccepted; subst;
    try solve [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end];
    try solve [match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H end].
  match goal with H : Protocol.lookup name _=Some (Protocol.class_binding ?cls ?flag) |- _ =>
    specialize (Hinvalid cls flag H) end.
  match goal with H : Protocol.theorem_at logical tid=Some _ |- _ =>
    unfold Protocol.theorem_at in H; rewrite Hinvalid in H; discriminate end.
Qed.
Theorem generated_rejected_protocol s logical bs ns name tid first middle last tail observations :
  (17<length (memory s arraydef_0__meta))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
  meta_value s 15=50 -> meta_value s 8=0 -> Protocol.valid_name name -> Z.of_nat tid<=maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) ->
  HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
  SchemaMetadata.represents s (Protocol.expressions logical) -> invalid logical name tid ->
  TokenByteExecution.separator first -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s=52::first::name++middle::decimalBytes tid++last::tail ->
  exists final, execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
    observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.NO;unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 14 [tid] name) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final logical /\ NameRepresentation.represents final (Protocol.bindings logical) /\
    SchemaMetadata.represents final (Protocol.expressions logical).
Proof.
  intros Hmeta Htoken Hpending Herror Hvalid Htidword Harena Hclasses Hhistory Hnames Hschemas Hinvalid Hsep1 Hsep2 Hsep3 Hin.
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
  split; [apply logical_rejected; [exact Hinvalid|now apply (SemanticFrames.arena_NoDup s)]|].
  split; [eapply ArenaFrame.storage_arena; [apply arena_frame;exact Hparsedframe|exact Harena]|].
  split; [eapply classes; eassumption|]. split; [exact Hparsedhistory|].
  split; [eapply names; eassumption|]. eapply schemas; eassumption.
Qed.
End ClassCertifyRejection.
