From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeWhitespaceSchemaArguments NativeWhitespaceSchemaConcrete NativeWhitespaceSchemaFinish NativeWhitespaceSchemaGeneralInvariantHandler NativeWhitespaceSchemaIO NativeCommandLengths NativeCommandStop NativeCommandBoundary SchemaEvaluationCell SchemaInstanceGeneralProtocol SchemaInstanceCommand ObservedLocal RenameMemoControl CommandInput CommandDispatch CommandChain
 SchemaInstanceHandler SchemaInstancePrefix SchemaInstanceArguments SchemaInstanceProtocol NativeState NameRepresentation Representation ClassStorage HistoryRefinement
 ReadNat ReadToken TokenByte TokenFrame ArenaFrame FormulaProjection ClassLookup FormulaTopology HashTable SchemaRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaGeneralInvariantCommand.
Import IndexExecution SipHashExecution ObservedLocal SchemaInstanceCommand.
Definition payload name fields namespaces namesep countspaces countsep tail :=
 namespaces++name++namesep::countspaces++decimalBytes(length fields)++countsep::(NativeWhitespaceSchemaArguments.spaced_wire fields++tail).
Definition opcode_state s name fields namespaces namesep countspaces countsep tail :=
 CommandInput.parsed s 50 [52] (payload name fields namespaces namesep countspaces countsep tail).
Definition initial_frame s bs ns name fields namespaces namesep countspaces countsep tail :=
 CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} (opcode_state s name fields namespaces namesep countspaces countsep tail) 24.
Theorem handler_opcode (f final:Frame) logical name fields namespaces namesep countspaces countsep observations trace tail :
 (18<length(memory(machine f)arraydef_0__meta))%nat -> (1024<=length(memory(machine f)arraydef_0__token))%nat ->
 meta_value(machine f)15=0 -> meta_value(machine f)8=0 -> NameRepresentation.represents(machine f)(Protocol.bindings logical) -> Protocol.valid_name name ->
 Forall(fun item=>Forall TokenByteExecution.separator(fst item) /\ Z.of_nat(snd item)<=maximum)fields -> Z.of_nat(length fields)<=maximum ->
 Forall TokenByteExecution.separator namespaces -> TokenByteExecution.separator namesep -> Forall TokenByteExecution.separator countspaces -> TokenByteExecution.separator countsep ->
 stdin(machine f)=payload name fields namespaces namesep countspaces countsep tail ->
 execLocalObserved(CommandChain.handler_for funcdef_0__readNat 24)(f,observations)=Some(tt,(final,trace)) ->
 nums final vardef_0__command_op=nums f vardef_0__command_op.
Proof.
 intros Hmeta Htoken Hpending Herror Hnames Hname Hfields Hsize Hns Hnsep Hcs Hcsep Hin Hrun.
 destruct(NativeWhitespaceSchemaConcrete.generated_spaced f (Protocol.bindings logical) name fields namespaces namesep countspaces countsep tail SchemaInstanceHandler.suffix observations
   Hmeta Htoken Hpending Herror Hnames Hname Hfields Hsize Hns Hnsep Hcs Hcsep Hin)
 as(looked & Hframe & Houtcome & Hprefix & HlookLength).
 rewrite SchemaInstancePrefix.actual_handler in Hrun.
 assert(Hsuffix:execLocalObserved SchemaInstanceHandler.suffix
  (NativeWhitespaceSchemaConcrete.finished_spaced f looked fields tail,observations)=Some(tt,(final,trace))).
 { transitivity(execLocalObserved(SchemaInstancePrefix.with_suffix SchemaInstanceHandler.suffix)(f,observations));[symmetry;exact Hprefix|exact Hrun]. }
 rewrite(SchemaInstanceCommand.number_preserves vardef_0__command_op SchemaInstanceHandler.suffix
   (NativeWhitespaceSchemaConcrete.finished_spaced f looked fields tail) observations tt final trace SchemaInstanceCommand.suffix_opcode_readonly Hsuffix).
 rewrite NativeWhitespaceSchemaFinish.finished_spaced_canonical. apply SchemaInstancePrefix.finished_number;discriminate.
Qed.
Theorem generated s bs ns logical fields name namespaces namesep countspaces countsep firstsep tail observations :
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
 Guarantees.safe logical -> SchemaInstanceGeneralProtocol.resources s logical (map snd fields) name ->
 exists final reply next,
 execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 (map snd fields) name) reply next /\
 NativeState.represents final next /\ meta_value final 8=0 /\ Guarantees.safe next /\ NativeCommandBoundary.io s final reply tail /\
 ClassLookup.wellformed final /\ FormulaTopology.ordered final (length (Protocol.formulas next)) /\
 (exists extra,Protocol.formulas next=Protocol.formulas logical++extra) /\
 (exists extra,Protocol.classes next=Protocol.classes logical++extra) /\ word (Z.of_nat (length (Protocol.formulas next))).
Proof.
 intros Hmeta Htoken Hsip Hprint Hpending Herror Hname Hfields Hlength Hns Hnsep Hcs Hcsep Hfirstsep Hinput Hstate Hgood Htop Hfalse Hsafe Hresources.
 set (op:=opcode_state s name fields namespaces namesep countspaces countsep tail).
 set (f:=initial_frame s bs ns name fields namespaces namesep countspaces countsep tail).
 assert (HopMeta:(31<length (memory op arraydef_0__meta))%nat).
 { unfold op,opcode_state. now rewrite CommandInput.parsed_meta_length. }
 assert (HopToken:(1024<=length (memory op arraydef_0__token))%nat).
 { unfold op,opcode_state. now rewrite parsed_token_length. }
 assert (HopSip:(0<length (memory op arraydef_0__sipState))%nat).
 { unfold op,opcode_state. now rewrite CommandInput.parsed_other by discriminate. }
 assert (HopPrint:(20<=length (memory op arraydef_0__printBuffer))%nat).
 { unfold op,opcode_state. now rewrite CommandInput.parsed_other by discriminate. }
 assert (HopError:meta_value op 8=0).
 { unfold op,opcode_state. now rewrite CommandInput.parsed_meta_other by lia. }
 assert (HopPending:meta_value op 15=0).
 { unfold op,opcode_state. apply parsed_pending;lia. }
 assert (HopRead:execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (s,observations)=Some (tt,(op,observations))).
 { unfold op,opcode_state. apply (CommandInput.generated_pending s (fun _=>false) (fun _=>0) 24 50 [52] firstsep (payload name fields namespaces namesep countspaces countsep tail) observations);
   try assumption;try reflexivity;try (unfold maximum;lia);try lia.
   }
 assert (HopNumber:meta_value op 11=24).
 { unfold op,opcode_state. exact (CommandInput.parsed_number s 24 50 [52] (payload name fields namespaces namesep countspaces countsep tail) ltac:(lia) ltac:(unfold maximum;lia) eq_refl). }
 assert (HopValid:meta_value op 14=1).
 { unfold op,opcode_state. apply CommandInput.parsed_valid;lia. }
 assert (HopState:NativeState.represents op logical).
 { unfold op,opcode_state. exact (parsed_state s 50 [52] (payload name fields namespaces namesep countspaces countsep tail) logical Hstate). }
 assert (HopGood:ClassLookup.wellformed op).
 { eapply ClassLookup.transport;[|exact Hgood]. unfold op,opcode_state. apply CommandInput.parsed_other;discriminate. }
 assert (HopTop:FormulaTopology.ordered op (length (Protocol.formulas logical))).
 { apply (FormulaTopology.same s);[exact Htop|]. intros parent Hparent.
   unfold HashTableInvariant.tuple_at,op,opcode_state. now rewrite CommandInput.parsed_other by discriminate. }
 assert (HopInput:stdin op=payload name fields namespaces namesep countspaces countsep tail) by reflexivity.
 assert(HhandlerResources:SchemaInstanceGeneralProtocol.handler_resources f logical (map snd fields) name tail).
 { unfold SchemaInstanceGeneralProtocol.handler_resources.
   apply (SchemaInstanceGeneralProtocol.resources_transport s);[| |exact Hresources].
   all: unfold f,initial_frame,CommandDispatch.opcode_frame,op,opcode_state;cbn [machine setNum setMachine];apply CommandInput.parsed_other;discriminate. }
 destruct HopState as [HopArena HopClasses HopHistory HopNames HopSchemas].
 destruct (NativeWhitespaceSchemaGeneralInvariantHandler.generated_handler f logical fields name namespaces namesep countspaces countsep tail observations
   HopMeta HopToken HopSip HopPrint HopPending HopError Hname Hfields Hlength Hns Hnsep Hcs Hcsep HopInput
   HopArena HopClasses HopHistory HopNames HopSchemas HopGood HopTop Hfalse Hsafe HhandlerResources)
 as (after & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hschemas & Hclear & HnextSafe & HfinalGood & HfinalTop & HfinalFs & HfinalCs).
 assert(HfMeta:(18<length(memory(machine f)arraydef_0__meta))%nat).
 { unfold f,initial_frame,CommandDispatch.opcode_frame. cbn [machine setNum setMachine]. change (18<length(memory op arraydef_0__meta))%nat. lia. }
 assert(Hio:stdin(machine after)=tail /\ stdout(machine after)=stdout(machine f)++Protocol.reply_bytes reply).
 { exact(NativeWhitespaceSchemaIO.handler_io f (Protocol.bindings logical) name fields namespaces namesep countspaces countsep tail observations after reply
    HfMeta HopToken HopPending HopError HopNames Hname Hfields Hlength Hns Hnsep Hcs Hcsep HopInput Hrun). }
 assert (HopFinal:nums after vardef_0__command_op=24).
 { change (nums after vardef_0__command_op=nums f vardef_0__command_op).
   exact (handler_opcode f after logical name fields namespaces namesep countspaces countsep observations _ tail HfMeta HopToken HopPending HopError HopNames Hname Hfields Hlength Hns Hnsep Hcs Hcsep HopInput Hrun). }
 assert (HfinalMeta:(8<length (memory (machine after) arraydef_0__meta))%nat).
 { pose proof (proj1 (proj1 (proj1 Harena))) as Hbound. lia. }
 assert (Hcommand:execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(machine after,
   observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}]))).
 { pose proof (CommandDispatch.generated_positive_command s bs ns after op 24 observations
    (observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes reply;unreadInput:=tail|}])
    HopRead ltac:(lia) HopNumber HopValid HopError ltac:(lia) HopFinal Hrun HfinalMeta Hclear) as Hdispatch.
   unfold f,initial_frame,CommandDispatch.opcode_frame,op,opcode_state in Hdispatch.
   cbn [machine setNum setMachine] in Hdispatch. now rewrite CommandInput.parsed_output in Hdispatch. }
 exists (machine after),reply,next. split;[exact Hcommand|]. split;[exact Hstep|]. split.
 - constructor;assumption.
 - split;[exact Hclear|]. split;[exact HnextSafe|].
   split.
   2:{ split;[exact HfinalGood|]. split;[exact HfinalTop|]. split;[exact HfinalFs|]. split;[exact HfinalCs|].
       exact (SchemaEvaluationCell.arena_count_word _ _ Harena). }
   unfold NativeCommandBoundary.io. destruct Hio as [HfinalInput HfinalOutput].
   split;[exact HfinalInput|]. split.
   + exact(eq_trans HfinalOutput (f_equal (fun bytes=>bytes++Protocol.reply_bytes reply)
      (CommandInput.parsed_output s 50 [52] (payload name fields namespaces namesep countspaces countsep tail)))).
   + split.
     * rewrite(NativeCommandLengths.generated arraydef_0__token s bs ns (machine after) observations _ NativeCommandLengths.token_protected Hcommand). exact Htoken.
     * split.
       -- rewrite(NativeCommandLengths.generated arraydef_0__printBuffer s bs ns (machine after) observations _ NativeCommandLengths.printBuffer_protected Hcommand). exact Hprint.
       -- split;[exact Hclear|].
          exact(NativeCommandStop.canonical 24 50 [52] s bs ns firstsep (payload name fields namespaces namesep countspaces countsep tail) observations (machine after) _
            ltac:(lia) eq_refl ltac:(lia) Htoken Hpending Herror Hfirstsep Hinput Hcommand Hclear).
Qed.
End NativeWhitespaceSchemaGeneralInvariantCommand.
