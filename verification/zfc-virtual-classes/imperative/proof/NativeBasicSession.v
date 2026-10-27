From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees Spec.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeStartup NativeStartupCompact
 NativeDialogueComposition NativeBasicDispatcher NativeBasicCommandInvariant NativeBasicInvariant NativeNameCompact NativeCommandBoundary NativeCommandLengths
 CommandLoop NativeFullTapeStep Dialogue SeedBootstrap FormulaTopology HashTable ClassLookup LogicalRegistryBounds LogicalStorageMonotone
 NameRepresentation ClassStorage LogicalHistory LogicalNames.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeBasicSession.
Import IndexExecution SipHashExecution.
Lemma represented_bytes native first second : NameRepresentation.represents native first -> NameRepresentation.represents native second ->
 NativeNameCompact.name_bytes first=NativeNameCompact.name_bytes second.
Proof.
 intros [_ [_ [_ [_ Hfirst]]]] [_ [_ [_ [_ Hsecond]]]].
 induction Hfirst as [|raw [name meaning] raws first Hentry Hfirst IH] in second,Hsecond|-*.
 - inversion Hsecond;reflexivity.
 - inversion Hsecond as [|raw' [other value] raws' second' Hother Hrest];subst raw' raws' second.
   destruct raw as [[[[offset size] fid] flag] kind].
   cbn [NameRepresentation.entry_rep] in Hentry,Hother.
   destruct Hentry as [Hsize Hentry]. destruct Hother as [Hsize' Hother].
   cbn [NativeNameCompact.name_bytes]. rewrite (IH second' Hrest). lia.
Qed.
Lemma compact_transport native first second : NativeState.represents native first -> NativeState.represents native second ->
 NativeNameCompact.compact native first -> NativeNameCompact.compact native second.
Proof.
 intros Hfirst Hsecond Hcompact. unfold NativeNameCompact.compact,NativeNameCompact.compact_bindings in *.
 rewrite <-(represented_bytes native _ _ (NativeState.name_representation _ _ Hfirst) (NativeState.name_representation _ _ Hsecond)). exact Hcompact.
Qed.
Lemma compact_step native logical request bs ns tail observations final trace reply next :
 Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 Z.of_nat(length(Protocol.bindings logical))<maximum ->
 Z.of_nat(length(memory native arraydef_0__names)+length(Protocol.object_name request))<=maximum ->
 NativeState.represents native logical -> LogicalHistory.valid logical -> NativeNameCompact.compact native logical ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 Protocol.step logical request reply next -> NativeState.represents final next -> NativeNameCompact.compact final next.
Proof.
 intros Hshape Hsupported Hmeta Htoken Hprint Hpending Herror HbindingRoom HnameRoom Hstate Hhistory Hcompact Hinput Hrun Hstep Hnext.
 destruct(NativeBasicCommandInvariant.supported_dec (Protocol.opcode request)) as [Hnamed|Hnotnamed].
 - destruct request as [opcode values name]. cbn [Protocol.opcode] in Hnamed.
   unfold NativeBasicDispatcher.named in Hnamed. destruct Hnamed as [->|[->| ->]];
    destruct Hshape as [Hwords Hfields];cbn [Protocol.arguments Protocol.object_name] in Hwords,Hfields,HnameRoom;
    destruct Hfields as [Hlen Hname];destruct values as [|value [|bad values]];cbn [length] in Hlen;try lia;
    inversion Hwords as [|value' values Hvalue Hnil];subst value' values.
   + change(meta_value native 15=58) in Hpending.
     rewrite(NativeBasicDispatcher.named_rest 9 value name tail ltac:(unfold NativeBasicDispatcher.named;tauto)) in Hinput.
     change(stdin native=32::decimalBytes value++32::name++10::tail) in Hinput.
     destruct(NativeNameCompact.Class.generated_total_protocol native logical bs ns value name 32 32 10 tail observations
      Hmeta Htoken Hprint Hpending Herror Hvalue Hname Hstate HbindingRoom HnameRoom ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
      as(model & modelReply & after & HmodelRun & HmodelStep & HmodelState & Hio & Hsafe & Hgrowth & HcompactModel).
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. eapply compact_transport;[exact HmodelState|exact Hnext|now apply HcompactModel].
   + change(meta_value native 15=51) in Hpending.
     rewrite(NativeBasicDispatcher.named_rest 20 value name tail ltac:(unfold NativeBasicDispatcher.named;tauto)) in Hinput.
     change(stdin native=48::32::decimalBytes value++32::name++10::tail) in Hinput.
     destruct(NativeNameCompact.TheoremName.generated_total_protocol native logical bs ns value name 32 32 10 tail observations
      Hmeta Htoken Hprint Hpending Herror Hvalue Hname Hhistory Hstate HbindingRoom HnameRoom ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
      as(model & modelReply & after & HmodelRun & HmodelStep & HmodelState & Hio & Hsafe & Hgrowth & HcompactModel).
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. eapply compact_transport;[exact HmodelState|exact Hnext|now apply HcompactModel].
   + change(meta_value native 15=51) in Hpending.
     rewrite(NativeBasicDispatcher.named_rest 23 value name tail ltac:(unfold NativeBasicDispatcher.named;tauto)) in Hinput.
     change(stdin native=51::32::decimalBytes value++32::name++10::tail) in Hinput.
     destruct(NativeNameCompact.Schema.generated_total_protocol native logical bs ns value name 32 32 10 tail observations
      Hmeta Htoken Hprint Hpending Herror Hvalue Hname Hstate HbindingRoom HnameRoom ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
      as(model & modelReply & after & HmodelRun & HmodelStep & HmodelState & Hio & Hsafe & Hgrowth & HcompactModel).
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. eapply compact_transport;[exact HmodelState|exact Hnext|now apply HcompactModel].
 - assert(Hraw:memory final arraydef_0__names=memory native arraydef_0__names).
   { eapply NativeBasicCommandInvariant.request_array;try eassumption.
     - unfold NativeBasicInvariant.Arrays.kind;tauto.
     - unfold NativeBasicInvariant.Arrays.unchanged,NativeBasicDispatcher.named in *;intuition congruence. }
   unfold NativeNameCompact.compact,NativeNameCompact.compact_bindings in *.
   rewrite Hraw. change(length(memory native arraydef_0__names)=NativeNameCompact.bytes next).
   rewrite(NativeNameCompact.step_bytes_unchanged logical request reply next
     ltac:(unfold NativeBasicDispatcher.named in Hnotnamed;intuition) ltac:(unfold NativeBasicDispatcher.named in Hnotnamed;intuition)
     ltac:(unfold NativeBasicDispatcher.named in Hnotnamed;intuition) Hstep). exact Hcompact.
Qed.
Definition supported request := Protocol.opcode request=0%nat \/ NativeBasicDispatcher.supported(Protocol.opcode request).
(** Finite arithmetic headroom for every remaining request. Each basic command
    allocates at most one formula, class, theorem, binding or schema node, and
    consumes at most 1024 bytes of permanent name storage. *)
Definition capacity logical requests := Forall supported requests /\
 Z.of_nat(length(Protocol.formulas logical))+Z.of_nat(length requests)<=9223372036854775807 /\
 Z.of_nat(length(Protocol.classes logical))+Z.of_nat(length requests)<=maximum /\
 Z.of_nat(length(Protocol.history logical))+Z.of_nat(length requests)<=maximum /\
 Z.of_nat(length(Protocol.bindings logical))+Z.of_nat(length requests)<=maximum /\
 Z.of_nat(NativeNameCompact.bytes logical)+1024*Z.of_nat(length requests)<=maximum.
Record extra (native:Machine) logical : Prop := Extra {
 meta : (31<length(memory native arraydef_0__meta))%nat;
 sip : (0<length(memory native arraydef_0__sipState))%nat;
 safe : Guarantees.safe logical;
 topology : FormulaTopology.ordered native(length(Protocol.formulas logical));
 falsity : nth_error(Protocol.formulas logical)0=Some SetTheory.falsity;
 classes : ClassLookup.wellformed native;
 unique : LogicalRegistryBounds.unique logical;
 compact : NativeNameCompact.compact native logical
}.
Lemma request_name_bound request : Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) ->
 (length(Protocol.object_name request)<=1024)%nat.
Proof.
 destruct request as [opcode values name]. intros [_ Hshape] Hsupported.
 pose proof(NativeBasicDispatcher.supported_bound _ Hsupported) as Hbound. cbn [Protocol.opcode] in Hbound.
 let rec cases count tag := lazymatch count with O=>idtac|S ?rest=>let next:=fresh "opcode" in destruct tag as [|next];[idtac|cases rest next] end in cases 27%nat opcode.
 all:try lia.
 all:cbn [Protocol.opcode Protocol.arguments Protocol.object_name] in Hshape|-*.
 all:unfold Protocol.valid_name in Hshape.
 all:intuition subst;try lia.
all:cbn [length];lia.
Qed.
Lemma current_resources native logical request requests :
 Protocol.shape request -> Protocol.opcode request<>0%nat -> capacity logical(request::requests) ->
 NativeNameCompact.compact native logical -> NativeBasicDispatcher.resources native logical request.
Proof.
 intros Hshape Hpositive [Hsupported [HF [HC [HH [HB Hbytes]]]]] Hcompact.
 inversion Hsupported as [|request' requests' Hop Htail];subst request' requests'.
 destruct Hop as [Hzero|Hop];[contradiction|].
 pose proof(request_name_bound request Hshape Hop) as Hname.
 cbn [length] in HF,HC,HH,HB,Hbytes. rewrite Nat2Z.inj_succ in HF,HC,HH,HB,Hbytes.
 unfold NativeNameCompact.compact,NativeNameCompact.compact_bindings,NativeNameCompact.bytes in Hcompact.
 constructor;try lia. rewrite Nat2Z.inj_add,Hcompact. unfold NativeNameCompact.bytes in Hbytes. lia.
Qed.
Lemma capacity_tail logical request requests reply next :
 Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) -> capacity logical(request::requests) ->
 (length(Protocol.formulas next)<=S(length(Protocol.formulas logical)))%nat ->
 (length(Protocol.classes next)<=S(length(Protocol.classes logical)))%nat ->
 LogicalRegistryBounds.counts logical next 1 -> Protocol.step logical request reply next -> capacity next requests.
Proof.
 intros Hshape Hsupported [Hall [HF [HC [HH [HB Hbytes]]]]] Hform Hclass [Hbinding [Hhistory Hschema]] Hstep.
 pose proof(NativeNameCompact.step_bytes_bound _ _ _ _ Hstep) as Hbytegrowth.
 pose proof(request_name_bound request Hshape Hsupported) as Hname.
 inversion Hall;subst. unfold capacity. split;[assumption|].
 cbn [length] in HF,HC,HH,HB,Hbytes. rewrite Nat2Z.inj_succ in HF,HC,HH,HB,Hbytes.
 repeat split;lia.
Qed.

Theorem commands : NativeDialogueComposition.command_spec extra capacity.
Proof.
 intros native logical request requests observations Hboundary Hextra Hcapacity Hshape Hpositive Hinput.
 destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning].
 destruct Hextra as [Hmeta Hsip Hsafe Htop Hfalse Hgood Hunique Hcompact].
 pose proof(current_resources native logical request requests Hshape Hpositive Hcapacity Hcompact) as Hresources.
 destruct Hresources as [HF HC HH HB HnamesRoom] eqn:HresourceFields.
 assert(Hresource:NativeBasicDispatcher.resources native logical request) by (constructor;assumption).
 assert(Hsupported:NativeBasicDispatcher.supported(Protocol.opcode request)).
 { destruct Hcapacity as [Hall Hrest]. inversion Hall as [|request' requests' Hop Htail];subst.
   destruct Hop as [Hzero|Hop];[contradiction|exact Hop]. }
 destruct(NativeBasicDispatcher.request_encoding request Hsupported) as [Hwire Hbyte].
 change(stdin native=Protocol.request_bytes request++Protocol.wire requests) in Hinput.
 set(pending:=NativeFullTapeStep.entered native request (Protocol.wire requests)).
 assert(HpendingState:NativeState.represents pending logical).
 { unfold pending,NativeFullTapeStep.entered,CommandLoopExecution.pending_state.
   apply NativeSession.state_meta;try lia. now apply NativeSession.state_input. }
 assert(HpendingMeta:(31<length(memory pending arraydef_0__meta))%nat).
 { unfold pending. now rewrite NativeFullTapeStep.entered_meta_length. }
 assert(HpendingToken:(1024<=length(memory pending arraydef_0__token))%nat).
 { unfold pending. now rewrite NativeFullTapeStep.entered_arrays by discriminate. }
 assert(HpendingPrint:(20<=length(memory pending arraydef_0__printBuffer))%nat).
 { unfold pending. now rewrite NativeFullTapeStep.entered_arrays by discriminate. }
 assert(HpendingValue:meta_value pending 15=NativeBasicDispatcher.first(Protocol.opcode request)+1).
 { unfold pending,NativeFullTapeStep.entered,CommandLoopExecution.pending_state. apply meta_store_same.
   change(15<length(memory native arraydef_0__meta))%nat;lia. }
 assert(HpendingError:meta_value pending 8=0).
 { unfold pending,NativeFullTapeStep.entered,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
 assert(HpendingTop:FormulaTopology.ordered pending(length(Protocol.formulas logical))).
 { eapply FormulaTopology.same;[exact Htop|]. intros parent Hparent.
   unfold HashTableInvariant.tuple_at,pending. now rewrite NativeFullTapeStep.entered_arrays by discriminate. }
 assert(HpendingGood:ClassLookup.wellformed pending).
 { eapply ClassLookup.transport;[|exact Hgood]. unfold pending. apply NativeFullTapeStep.entered_arrays;discriminate. }
 assert(HpendingCompact:NativeNameCompact.compact pending logical).
 { unfold NativeNameCompact.compact,NativeNameCompact.compact_bindings in *. unfold pending.
   now rewrite NativeFullTapeStep.entered_arrays by discriminate. }
 assert(HpendingResource:NativeBasicDispatcher.resources pending logical request).
 { apply (NativeBasicDispatcher.resources_names native pending logical request);[|exact Hresource].
   unfold pending. apply NativeFullTapeStep.entered_arrays;discriminate. }
 destruct(NativeBasicCommandInvariant.generated_canonical pending logical request (fun _=>false) (fun _=>0)
  (Protocol.wire requests) observations Hshape Hsupported ltac:(lia) HpendingToken HpendingPrint HpendingValue HpendingError
  HpendingState Hsafe HpendingResource HpendingTop Hfalse HpendingGood Hunique eq_refl)
 as(after & reply & next & Hrun & Hstep & HnextState & Hio & HnextSafe & Hhistory & Hnames & Hpost).
 destruct Hpost as(HnextTop & HnextFalse & HnextGood & HformGrowth & HclassGrowth & HregistryGrowth & HnextUnique & HnameGrowth).
 assert(HnextCompact:NativeNameCompact.compact after next).
 { exact(compact_step pending logical request (fun _=>false) (fun _=>0) (Protocol.wire requests) observations after _ reply next
   Hshape Hsupported ltac:(lia) HpendingToken HpendingPrint HpendingValue HpendingError HB
   (NativeBasicDispatcher.name_room _ _ _ HpendingResource) HpendingState (NativeBasicDispatcher.safe_history _ Hsafe)
   HpendingCompact eq_refl Hrun Hstep HnextState). }
 assert(HnextMeta:(31<length(memory after arraydef_0__meta))%nat).
 { rewrite(NativeCommandLengths.generated arraydef_0__meta pending (fun _=>false) (fun _=>0) after observations _ NativeCommandLengths.meta_protected Hrun).
   exact HpendingMeta. }
 assert(HnextSip:(0<length(memory after arraydef_0__sipState))%nat).
 { rewrite(NativeCommandLengths.generated arraydef_0__sipState pending (fun _=>false) (fun _=>0) after observations _ NativeCommandLengths.sipState_protected Hrun).
   unfold pending. now rewrite NativeFullTapeStep.entered_arrays by discriminate. }
 destruct Hio as(Hin & Hout & HnextToken & HnextPrint & Hclear & Hstop).
 assert(HpendingStop:meta_value pending 9=meta_value native 9).
 { unfold pending,NativeFullTapeStep.entered,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. reflexivity. }
 exists(NativeBasicDispatcher.first(Protocol.opcode request)),(NativeBasicDispatcher.rest request++Protocol.wire requests),after,reply,next.
 split;[exact Hbyte|]. split;[rewrite Hinput,Hwire;reflexivity|]. split;[exact Hrun|]. split;[exact Hstep|].
 split;[constructor;try assumption;now rewrite Hstop,HpendingStop|].
 split;[constructor;assumption|]. split.
 - eapply capacity_tail;try eassumption.
 - split;[exact Hin|exact Hout].
Qed.

Theorem generated_main :
 forall key0 key1 requests bs ns,
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum ->
 Forall Protocol.shape requests -> capacity Protocol.initial requests ->
 exists replies final logical remaining,
 Protocol.dialogue Protocol.initial requests replies logical remaining /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved (funcdef_0__main bs ns)
   (SeedBootstrapExecution.initial key0 key1 (Protocol.wire requests) [],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++Protocol.wire requests|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=Protocol.wire requests|}]++
 Protocol.flush_schedule requests replies Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat (map Protocol.reply_bytes replies) /\ stdin final=remaining.
Proof.
 intros key0 key1 requests bs ns Hkey0 Hkey1 Hshape Hcapacity.
 destruct (NativeStartupCompact.main_to_commands key0 key1 (Protocol.wire requests) bs ns Hkey0 Hkey1)
 as (ready & Hstate & Htop & Hmeta32 & Hsip1 & Hzero & Herror & Hmeta & Htoken & Hprint & Hstop & Hhistory & Hinput & Houtput & Hmain & Hempty).
 assert (Hboundary:NativeDialogueComposition.boundary ready Protocol.initial) by (constructor;assumption).
 assert(Hextra:extra ready Protocol.initial).
 { constructor.
   - lia.
   - lia.
   - exact Guarantees.initial_safe.
   - exact Htop.
   - reflexivity.
   - apply ClassLookup.empty. exact(NativeState.empty_classes _ Hempty).
   - exact LogicalRegistryBounds.initial_unique.
   - apply NativeNameCompact.initial_compact. exact(NativeState.empty_names _ Hempty). }
 set (observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++Protocol.wire requests|};
   {|flushedOutput:=Protocol.handshake_output;unreadInput:=Protocol.wire requests|}]).
 destruct (NativeDialogueComposition.generated_finite extra capacity commands requests ready Protocol.initial observations
   Hshape Hboundary Hextra Hcapacity Hinput)
 as (final & replies & logical & remaining & Hrun & Hdialogue & Hfinal & Hclear & Hout & Hin).
 pose proof (DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as HcommandsRun.
 rewrite Houtput in HcommandsRun,Hout.
 exists replies,final,logical,remaining. split;[exact Hdialogue|].
 split;[exact (Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|]. split;[exact Hfinal|]. split;[exact Hclear|].
 split;[etransitivity;[exact Hmain|exact HcommandsRun]|]. split;assumption.
Qed.

Theorem required bs ns :
 Spec.required (funcdef_0__main bs ns) (arrays _ environment1) (capacity Protocol.initial).
Proof.
 intros key0 key1 requests Hkey0 Hkey1 Hshape Hcapacity.
 destruct (generated_main key0 key1 requests bs ns Hkey0 Hkey1 Hshape Hcapacity)
 as (replies & final & logical & remaining & Hdialogue & Hsafe & Hstate & Herror & Hrun & Hout & Hin).
 exists replies,final,logical,remaining. split;[exact Hdialogue|]. split;[exact Hsafe|].
 split;[exact Hrun|]. split;assumption.
Qed.
End NativeBasicSession.
