From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal RenameMemoControl CommandInput CommandDispatch CommandChain
 SchemaInstanceHandler SchemaInstancePrefix SchemaInstanceArguments SchemaInstanceProtocol NativeState NameRepresentation Representation ClassStorage HistoryRefinement
 ReadNat ReadToken TokenByte TokenFrame ArenaFrame FormulaProjection ClassLookup FormulaTopology HashTable SchemaRepresentation SchemaInstanceCommand FlushFrame FlushFrameReplies NativeCommandLengths NativeCommandStop NativeCommandBoundary.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSchemaInstanceBoundary.
Import IndexExecution SipHashExecution ObservedLocal SchemaInstanceCommand.
Lemma handler_io (f:Frame) bindings name ids tail observations final reply :
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 (1024<=length (memory (machine f) arraydef_0__token))%nat ->
 meta_value (machine f) 15=0 -> meta_value (machine f) 8=0 ->
 NameRepresentation.represents (machine f) bindings -> Protocol.valid_name name ->
 Forall (fun id=>Z.of_nat id<=maximum) ids -> Z.of_nat (length ids)<=maximum ->
 stdin (machine f)=SchemaInstanceCommand.payload ids name tail ->
 execLocalObserved (CommandChain.handler_for funcdef_0__readNat 24) (f,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes reply;unreadInput:=tail|}])) ->
 stdin (machine final)=tail /\ stdout (machine final)=stdout (machine f)++Protocol.reply_bytes reply.
Proof.
 intros Hmeta Htoken Hpending Herror Hbindings Hname Hwords Hlength Hin Hrun.
 destruct(SchemaInstancePrefix.generated_canonical f bindings name ids tail SchemaInstanceHandler.suffix observations
  Hmeta Htoken Hpending Herror Hbindings Hname Hwords Hlength Hin)
 as (looked & Hframe & Hlookup & Hprefix & Hargs & Hinput & Houtput & Hclear & Hvalid & Hlen).
 rewrite SchemaInstancePrefix.actual_handler in Hrun.
 assert(Hsuffix:execLocalObserved SchemaInstanceHandler.suffix (SchemaInstancePrefix.finished f looked ids tail,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout(machine f)++Protocol.reply_bytes reply;unreadInput:=tail|}]))).
 { exact(eq_trans (eq_sym Hprefix) Hrun). }
 pose proof(FlushFrame.singleton _ _ _ _ (FlushFrameReplies.schema_suffix _ _ _ _ _ Hsuffix)) as Hfinal.
 split;[exact(f_equal unreadInput Hfinal)|exact(f_equal flushedOutput Hfinal)].
Qed.
Theorem generated_canonical s bs ns logical ids name tail observations :
 (31<length (memory s arraydef_0__meta))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat ->
 (0<length (memory s arraydef_0__sipState))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=51 -> meta_value s 8=0 ->
 Protocol.valid_name name -> Forall (fun id=>Z.of_nat id<=maximum) ids -> Z.of_nat (length ids)<=maximum ->
 stdin s=52::32::payload ids name tail ->
 NativeState.represents s logical -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 Guarantees.safe logical -> resources s bs ns logical ids name tail ->
 exists final reply next,
 execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) reply next /\
 NativeState.represents final next /\ meta_value final 8=0 /\ Guarantees.safe next /\ NativeCommandBoundary.io s final reply tail.
Proof.
 intros Hmeta Htoken Hsip Hprint Hpending Herror Hname Hwords Hlength Hinput Hstate Hgood Htop Hfalse Hsafe Hresources.
 set (op:=opcode_state s ids name tail).
 set (f:=initial_frame s bs ns ids name tail).
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
 { unfold op,opcode_state. apply (CommandInput.generated_pending s (fun _=>false) (fun _=>0) 24 50 [52] 32 (payload ids name tail) observations);
   try assumption;try reflexivity;try (unfold maximum;lia);try lia.
   unfold TokenByteExecution.separator;left;reflexivity. }
 assert (HopNumber:meta_value op 11=24).
 { unfold op,opcode_state. exact (CommandInput.parsed_number s 24 50 [52] (payload ids name tail) ltac:(lia) ltac:(unfold maximum;lia) eq_refl). }
 assert (HopValid:meta_value op 14=1).
 { unfold op,opcode_state. apply CommandInput.parsed_valid;lia. }
 assert (HopState:NativeState.represents op logical).
 { unfold op,opcode_state. exact (parsed_state s 50 [52] (payload ids name tail) logical Hstate). }
 assert (HopGood:ClassLookup.wellformed op).
 { eapply ClassLookup.transport;[|exact Hgood]. unfold op,opcode_state. apply CommandInput.parsed_other;discriminate. }
 assert (HopTop:FormulaTopology.ordered op (length (Protocol.formulas logical))).
 { apply (FormulaTopology.same s);[exact Htop|]. intros parent Hparent.
   unfold HashTableInvariant.tuple_at,op,opcode_state. now rewrite CommandInput.parsed_other by discriminate. }
 assert (HopInput:stdin op=payload ids name tail) by reflexivity.
 destruct HopState as [HopArena HopClasses HopHistory HopNames HopSchemas].
 destruct (SchemaInstanceProtocol.generated_handler f logical ids name tail observations
   HopMeta HopToken HopSip HopPrint HopPending HopError Hname Hwords Hlength HopInput
   HopArena HopClasses HopHistory HopNames HopSchemas HopGood HopTop Hfalse Hsafe Hresources)
 as (after & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hschemas & Hclear & HnextSafe).
 assert (Hio:stdin (machine after)=tail /\ stdout (machine after)=stdout (machine f)++Protocol.reply_bytes reply).
 { exact(handler_io f (Protocol.bindings logical) name ids tail observations after reply
   ltac:(change(18<length (memory op arraydef_0__meta))%nat;lia) HopToken HopPending HopError HopNames Hname Hwords Hlength HopInput Hrun). }
 assert (HopFinal:nums after vardef_0__command_op=24).
 { change (nums after vardef_0__command_op=nums f vardef_0__command_op).
   exact (handler_opcode f after logical name ids observations _ ltac:(change (18<length (memory op arraydef_0__meta))%nat;lia) HopToken HopPending HopError HopNames Hname Hwords Hlength tail HopInput Hrun). }
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
   unfold NativeCommandBoundary.io. destruct Hio as [HfinalInput HfinalOutput].
   split;[exact HfinalInput|]. split.
   + exact(eq_trans HfinalOutput (f_equal (fun bytes=>bytes++Protocol.reply_bytes reply)
      (CommandInput.parsed_output s 50 [52] (payload ids name tail)))).
   + split.
     * rewrite(NativeCommandLengths.generated arraydef_0__token s bs ns (machine after) observations _ NativeCommandLengths.token_protected Hcommand). exact Htoken.
     * split.
       -- rewrite(NativeCommandLengths.generated arraydef_0__printBuffer s bs ns (machine after) observations _ NativeCommandLengths.printBuffer_protected Hcommand). exact Hprint.
       -- split;[exact Hclear|].
          exact(NativeCommandStop.canonical 24 50 [52] s bs ns 32 (payload ids name tail) observations (machine after) _
            ltac:(lia) eq_refl ltac:(lia) Htoken Hpending Herror ltac:(unfold TokenByteExecution.separator;auto) Hinput Hcommand Hclear).
Qed.
End NativeSchemaInstanceBoundary.
