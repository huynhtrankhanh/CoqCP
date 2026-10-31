From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeWhitespaceSchemaArguments NativeWhitespaceSchemaConcrete NativeWhitespaceSchemaTransport NativeWhitespaceSchemaAligned NativeWhitespaceSchemaFacts SchemaInstanceProtocol SchemaInstanceGeneralProtocol NativeSchemaGeneralInvariant NativeSchemaSetBoundedBoundary SchemaEvaluationSetCell SchemaInstanceSetProtocol ObservedLocal TypedNameLookup NameRepresentation SchemaInstanceHandler SchemaInstanceReady
 SchemaInstanceCompletion SchemaInstancePrefix SchemaInstanceArguments CommandChain ReadName ReadToken NameSearch HashTable SchemaNodeMeaning SchemaMetadata SchemaMarking SchemaRepresentation Representation ClassStorage ClassLookup
 FormulaTopology HistoryRefinement SemanticFrames ReplyNO ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaSetInvariantHandler.
Import IndexExecution SipHashExecution ObservedLocal SchemaInstanceGeneralProtocol.
Theorem generated_handler (f:SchemaInstanceHandler.Frame) logical fields name namespaces namesep countspaces countsep tail observations :
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (1024<=length (memory (machine f) arraydef_0__token))%nat ->
 (0<length (memory (machine f) arraydef_0__sipState))%nat -> (20<=length (memory (machine f) arraydef_0__printBuffer))%nat ->
 meta_value (machine f) 15=0 -> meta_value (machine f) 8=0 -> Protocol.valid_name name ->
 Forall (fun item=>Forall TokenByteExecution.separator(fst item) /\ Z.of_nat(snd item)<=maximum) fields -> Z.of_nat(length fields)<=maximum ->
 Forall TokenByteExecution.separator namespaces -> TokenByteExecution.separator namesep -> Forall TokenByteExecution.separator countspaces -> TokenByteExecution.separator countsep ->
 stdin(machine f)=namespaces++name++namesep::countspaces++decimalBytes(length fields)++countsep::(NativeWhitespaceSchemaArguments.spaced_wire fields++tail) ->
 NativeRepresentation.canonical_arena (machine f) (Protocol.formulas logical) ->
 ClassStorage.represents (machine f) (Protocol.formulas logical) (Protocol.classes logical) ->
 HistoryRefinement.represents (machine f) logical -> NameRepresentation.represents (machine f) (Protocol.bindings logical) ->
 SchemaRepresentation.represents (machine f) logical -> ClassLookup.wellformed (machine f) ->
 FormulaTopology.ordered (machine f) (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 Guarantees.safe logical -> SchemaEvaluationSetCell.sets(Protocol.classes logical) -> SchemaInstanceSetProtocol.resources (machine f) logical (map snd fields) name ->
 exists final reply next,
 execLocalObserved (CommandChain.handler_for funcdef_0__readNat 24) (f,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 (map snd fields) name) reply next /\
 NativeRepresentation.canonical_arena (machine final) (Protocol.formulas next) /\
 ClassStorage.represents (machine final) (Protocol.formulas next) (Protocol.classes next) /\
 HistoryRefinement.represents (machine final) next /\ NameRepresentation.represents (machine final) (Protocol.bindings next) /\
 SchemaRepresentation.represents (machine final) next /\ meta_value (machine final) 8=0 /\ Guarantees.safe next /\
 ClassLookup.wellformed (machine final) /\ FormulaTopology.ordered (machine final) (length (Protocol.formulas next)) /\
 (exists extra,Protocol.formulas next=Protocol.formulas logical++extra) /\
 (exists extra,Protocol.classes next=Protocol.classes logical++extra) /\ NativeSchemaSetBoundedBoundary.post logical next.
Proof.
 intros Hmeta Htoken Hsip Hprint Hpending Herror Hname Hfields Hsize Hns Hnsep Hcs Hcsep Hinput Harena Hclasses Hhistory Hnames Hschemas Hgood Htop Hfalse Hsafe Hsets Hresources.
 assert(Hwords:Forall(fun id=>Z.of_nat id<=maximum)(map snd fields)).
 { apply Forall_map. eapply Forall_impl;[exact Hfields|intros item Hitem;exact (proj2 Hitem)]. }
 assert(Hwordsize:Z.of_nat(length(map snd fields))<=maximum) by (rewrite length_map;exact Hsize).
 destruct(NativeWhitespaceSchemaConcrete.generated_spaced f (Protocol.bindings logical) name fields namespaces namesep countspaces countsep tail SchemaInstanceHandler.suffix observations
   ltac:(lia) Htoken Hpending Herror Hnames Hname Hfields Hsize Hns Hnsep Hcs Hcsep Hinput)
 as(raw & HrawFrame & HrawOutcome & HrawPrefix & HrawLength).
 set(looked:=NativeWhitespaceSchemaTransport.aligned f raw name fields tail).
 assert(HlookupFrame:NameSearchExecution.storage_frame(SchemaInstancePrefix.named f name (map snd fields) tail)looked).
 { unfold looked. now apply NativeWhitespaceSchemaTransport.aligned_frame with (countspaces:=countspaces) (countsep:=countsep). }
 assert(Houtcome:TypedNameLookup.outcome looked (Protocol.bindings logical) name).
 { unfold looked. now apply NativeWhitespaceSchemaAligned.aligned_outcome. }
 assert(HlookLength:length(memory looked arraydef_0__meta)=length(memory(SchemaInstancePrefix.named f name (map snd fields) tail)arraydef_0__meta)).
 { unfold looked. now apply NativeWhitespaceSchemaAligned.aligned_length with (countspaces:=countspaces) (countsep:=countsep). }
 assert(Hprefix:execLocalObserved(SchemaInstancePrefix.with_suffix SchemaInstanceHandler.suffix)(f,observations)=
   execLocalObserved SchemaInstanceHandler.suffix(SchemaInstancePrefix.finished f looked (map snd fields) tail,observations)).
 { unfold looked. now apply NativeWhitespaceSchemaAligned.aligned_execution. }
 destruct(NativeWhitespaceSchemaFacts.finished_facts f looked name (map snd fields) tail observations ltac:(lia) Htoken Hpending Herror Hwords Hwordsize HlookupFrame HlookLength)
 as(Hvector & Hin & Hout & Hclear & Hvalid).
 set (parsed:=SchemaInstancePrefix.finished f looked (map snd fields) tail).
 assert (HparsedFrame:SchemaInstancePrefix.parsed_frame (machine f) (machine parsed)).
 { exact (SchemaInstancePrefix.finished_frame f looked name (map snd fields) tail ltac:(lia) HlookLength HlookupFrame). }
 destruct (SchemaInstancePrefix.parsed_representations (machine f) (machine parsed) logical HparsedFrame Harena Hclasses Hhistory Hnames Hschemas)
  as (HparsedArena & HparsedClasses & HparsedHistory & HparsedNames & HparsedSchemas).
 destruct HparsedFrame as [Hlength [Harrays Hcells]].
 assert (Hlooked:(18<length (memory looked arraydef_0__meta))%nat).
 { rewrite HlookLength. unfold SchemaInstancePrefix.named,ReadName.result. rewrite ReadTokenExecution.result_meta_length. lia. }
 assert (HparsedGood:ClassLookup.wellformed (machine parsed)).
 { eapply ClassLookup.transport;[apply Harrays;discriminate|exact Hgood]. }
 assert (HparsedTop:FormulaTopology.ordered (machine parsed) (length (Protocol.formulas logical))).
 { apply (FormulaTopology.same (machine f));[exact Htop|]. intros parent Hparent.
   unfold HashTableInvariant.tuple_at. now rewrite Harrays by discriminate. }
 assert (HvalidParsed:meta_value (machine parsed) 18=
  if forallb (fun id=>bool_decide (Z.of_nat id<meta_value (machine parsed) 2)) (map snd fields) then 1 else 0).
 { assert (HclassCount:meta_value (machine parsed) 2=meta_value (machine f) 2) by (apply Hcells;lia).
   rewrite HclassCount. exact Hvalid. }
 assert (HparsedResources:SchemaInstanceSetProtocol.resources (machine parsed) logical (map snd fields) name).
 { apply (SchemaInstanceSetProtocol.resources_transport (machine f));[apply Harrays;discriminate|exact Hresources]. }
 assert (HidWords:Forall (fun id=>word (Z.of_nat id)) (map snd fields)).
 { clear -Hwords. induction Hwords as [|head rest Hhead Hrest IH].
   - constructor.
   - constructor;[unfold word;lia|exact IH]. }
 destruct (NativeSchemaSetBoundedBoundary.ProtocolInvariant.generated_suffix parsed logical (map snd fields) name observations HidWords Hvector
   (SchemaInstancePrefix.finished_outcome f looked (map snd fields) tail (Protocol.bindings logical) name Hlooked Houtcome)
   (SchemaInstancePrefix.finished_binding_result f looked (map snd fields) tail Hlooked)
   (SchemaInstancePrefix.finished_count f looked (map snd fields) tail) HvalidParsed
   ltac:(now rewrite Hlength) ltac:(now rewrite Harrays by discriminate) ltac:(now rewrite Harrays by discriminate)
   Hclear HparsedArena HparsedClasses HparsedHistory HparsedNames HparsedSchemas HparsedGood HparsedTop Hfalse Hsafe Hsets HparsedResources)
   as (final & reply & next & Hchecked).
 destruct Hchecked as (Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfs & Hflag & HnextSafe & HfinalGood & HfinalTop & HfinalFs & HfinalCs & Hpost).
 exists final,reply,next. split.
 - rewrite SchemaInstancePrefix.actual_handler. fold parsed in Hprefix.
   etransitivity;[exact Hprefix|]. etransitivity;[exact Hrun|].
   unfold parsed. now rewrite Hin,Hout.
 - repeat first [assumption|split].
Qed.
End NativeWhitespaceSchemaSetInvariantHandler.
