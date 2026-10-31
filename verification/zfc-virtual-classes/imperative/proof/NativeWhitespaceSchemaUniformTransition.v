From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import NativeWhitespaceSchemaUniformCommand NativeGeneralCommandInvariant NativeNameCompact NativeUniformCommand LogicalStorageMonotone LogicalRegistryBounds NativeSchemaUniformBoundary Index SipHash TokenByte NativeWhitespaceSchemaArguments NativeWhitespaceSchemaConcrete NativeWhitespaceSchemaFinish NativeWhitespaceSchemaUniformHandler NativeSchemaUniformBoundary NativeWhitespaceSchemaIO NativeCommandLengths NativeCommandStop NativeCommandBoundary SchemaEvaluationCell SchemaInstanceGeneralProtocol SchemaInstanceCommand ObservedLocal RenameMemoControl CommandInput CommandDispatch CommandChain
 SchemaInstanceHandler SchemaInstancePrefix SchemaInstanceArguments SchemaInstanceProtocol NativeState NameRepresentation Representation ClassStorage HistoryRefinement
 ReadNat ReadToken TokenByte TokenFrame ArenaFrame FormulaProjection ClassLookup FormulaTopology HashTable SchemaRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaUniformTransition.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaUniformCommand.
Theorem generated E N F B C s bs ns logical fields name namespaces namesep countspaces countsep firstsep tail observations :
 (31<length (memory s arraydef_0__meta))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat ->
 (0<length (memory s arraydef_0__sipState))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=51 -> meta_value s 8=0 ->
 Protocol.valid_name name -> Forall(fun item=>Forall TokenByteExecution.separator(fst item) /\ Z.of_nat(snd item)<=maximum)fields -> Z.of_nat(length fields)<=maximum ->
 Forall TokenByteExecution.separator namespaces -> TokenByteExecution.separator namesep -> Forall TokenByteExecution.separator countspaces -> TokenByteExecution.separator countsep -> TokenByteExecution.separator firstsep ->
 stdin s=52::firstsep::payload name fields namespaces namesep countspaces countsep tail ->
 NativeState.represents s logical -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 Guarantees.safe logical -> LogicalRegistryBounds.unique logical -> NativeNameCompact.compact s logical -> NativeSchemaUniformBoundary.budget s logical E N F B C ->
 exists final reply next,
 execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 (map snd fields) name) reply next /\
 NativeState.represents final next /\ NativeCommandBoundary.io s final reply tail /\
 NativeGeneralCommandInvariant.post s logical final next /\
 NativeUniformCommand.quantitative final next (Protocol.Req 24 (map snd fields) name) F B C E N.
Proof.
 intros Hmeta Htoken Hsip Hprint Hpending Herror Hname Hfields Hlength Hns Hnsep Hcs Hcsep Hfirstsep Hinput Hstate Hgood Htop Hfalse Hsafe Hunique Hcompact Hbudget.
 destruct(NativeWhitespaceSchemaUniformCommand.generated E N F B C s bs ns logical fields name namespaces namesep countspaces countsep firstsep tail observations
  Hmeta Htoken Hsip Hprint Hpending Herror Hname Hfields Hlength Hns Hnsep Hcs Hcsep Hfirstsep Hinput Hstate Hgood Htop Hfalse Hsafe Hbudget)
 as(final & reply & next & Hrun & Hstep & Hnext & Hclear & HsafeNext & Hio & HgoodNext & HtopNext & Hforms & Hclasses & Hword & Hquant).
 assert(Hraw:memory final arraydef_0__names=memory s arraydef_0__names).
 { eapply NativeGeneralCommandInvariant.canonical_array with (opcode:=24%nat) (ch:=50) (chars:=[52]) (separator:=firstsep)
     (payload:=payload name fields namespaces namesep countspaces countsep tail) (bs:=bs) (ns:=ns) (observations:=observations);try eassumption;try discriminate;try reflexivity;try lia.
   apply NativeGeneralCommandInvariant.Names.handler_ro;lia. }
 assert(HcompactNext:NativeNameCompact.compact final next).
 { unfold NativeNameCompact.compact,NativeNameCompact.compact_bindings in *. rewrite Hraw.
   change(length(memory s arraydef_0__names)=NativeNameCompact.bytes next).
   rewrite(NativeNameCompact.step_bytes_unchanged logical (Protocol.Req 24 (map snd fields) name) reply next ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hstep). exact Hcompact. }
 pose proof(NativeCommandLengths.generated arraydef_0__meta s bs ns final observations _ NativeCommandLengths.meta_protected Hrun) as HmetaLength.
 pose proof(NativeCommandLengths.generated arraydef_0__sipState s bs ns final observations _ NativeCommandLengths.sipState_protected Hrun) as HsipLength.
 assert(Hpost:NativeGeneralCommandInvariant.post s logical final next).
 { unfold NativeGeneralCommandInvariant.post. split;[exact HsafeNext|]. split;[exact HtopNext|]. split;[exact HgoodNext|]. split;[exact HcompactNext|].
   split;[exact(LogicalRegistryBounds.step_unique _ _ _ _ Hstep Hunique)|]. split.
   - exact(LogicalStorageMonotone.formula_lookup logical next 0 SetTheory.falsity (LogicalStorageMonotone.step _ _ _ _ Hstep) Hfalse).
   - split;[exact HmetaLength|]. split;[exact HsipLength|]. split;[now rewrite HmetaLength|]. split;[now rewrite HsipLength|].
     split;[exact(LogicalStorageMonotone.step _ _ _ _ Hstep)|exact(LogicalRegistryBounds.step_counts _ _ _ _ Hstep)]. }
 assert(Hquantitative:NativeUniformCommand.quantitative final next (Protocol.Req 24 (map snd fields) name) F B C E N).
 { destruct Hquant as(Hfg & Hcg & Hbounded & Hgrowth). unfold NativeUniformCommand.quantitative,NativeUniformCommand.formula_end,NativeUniformCommand.index_end,NativeUniformCommand.class_end.
   cbn [Protocol.opcode Nat.eqb]. split;[exact Hfg|]. split;[exact Hbounded|]. split;[exact Hcg|].
   eapply NativeUniformCommand.expression_bound;[exact Hstep|exact(NativeSchemaUniformBoundary.expression_capacity _ _ _ _ _ _ _ Hbudget)]. }
 exists final,reply,next. repeat first [assumption|split].
Qed.
End NativeWhitespaceSchemaUniformTransition.
