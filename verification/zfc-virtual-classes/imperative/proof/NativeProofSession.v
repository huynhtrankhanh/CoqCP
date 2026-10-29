From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees Spec.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeStartupCompact NativeBasicSession NativeDialogueComposition
 NativeBasicDispatcher NativeBasicCommandInvariant NativeGeneralDispatcher NativeFullDispatcher NativeFullTapeStep NativeCommandBoundary NativeCommandLengths
 NativeGeneralCommandInvariant NativeAxiomTotal NativeAxiomInvariant AxiomTaggedInvariant NativeNameCompact LogicalHistory LogicalNames LogicalRegistryBounds
 FormulaTopology ClassLookup LogicalStorageMonotone HashTable CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeProofSession.
Import IndexExecution SipHashExecution.
Definition simple_tag tag := tag<>3%nat /\ tag<>4%nat /\ tag<>15%nat /\ tag<>16%nat.
Definition pick fs index := match nth_error fs index with Some p=>p|None=>SetTheory.falsity end.
Lemma ready_from_concrete logical tag a b c wanted : Protocol.concrete_axiom logical tag a b c=Some wanted ->
 AxiomTaggedInvariant.ready (Protocol.formulas logical) tag a b c a b c
 (pick(Protocol.formulas logical)a) (pick(Protocol.formulas logical)b) (pick(Protocol.formulas logical)c).
Proof.
 intro Hconcrete. pose proof(NativeAxiomTotal.valid_tag _ _ _ _ _ _ Hconcrete) as Htag.
 let rec cases count tag := lazymatch count with O=>idtac|S ?rest=>let next:=fresh "tag" in destruct tag as [|next];[idtac|cases rest next] end in cases 18%nat tag.
 all:try lia.
 all:unfold Protocol.concrete_axiom,Protocol.formula_at in Hconcrete.
 all:cbn [existsb Nat.eqb orb] in Hconcrete.
 all:unfold AxiomTaggedInvariant.ready,AxiomTaggedInvariant.needs_p,AxiomTaggedInvariant.needs_q.
 all:cbn [existsb Nat.eqb orb].
 all:unfold pick.
 all:destruct(nth_error(Protocol.formulas logical)a) as [p|] eqn:Hp;
 destruct(nth_error(Protocol.formulas logical)b) as [q|] eqn:Hq;
 destruct(nth_error(Protocol.formulas logical)c) as [r|] eqn:Hr;
 cbn [option_map] in Hconcrete;try discriminate;repeat split;reflexivity.
Qed.
Lemma cost_bound tag root : simple_tag tag -> (AxiomTaggedInvariant.cost tag root<=42)%nat.
Proof.
 unfold simple_tag. intro Htag.
 let rec cases count tag := lazymatch count with O=>idtac|S ?rest=>let next:=fresh "tag" in destruct tag as [|next];[idtac|cases rest next] end in cases 18%nat tag.
 all:cbn [AxiomTaggedInvariant.cost];intuition lia.
Qed.
Lemma resources logical tag a b c : simple_tag tag ->
 Z.of_nat(length(Protocol.formulas logical))+42<=9223372036854775807 -> NativeAxiomTotal.resources logical tag a b c.
Proof.
 intros Htag Hroom wanted Hwanted.
 exists(pick(Protocol.formulas logical)a),(pick(Protocol.formulas logical)b),(pick(Protocol.formulas logical)c),0%nat.
 split;[now apply ready_from_concrete with(wanted:=wanted)|]. split.
 - unfold AxiomTaggedInvariant.renaming_ready,AxiomTaggedInvariant.uses_rename.
   let rec cases count tag := lazymatch count with O=>idtac|S ?rest=>let next:=fresh "tag" in destruct tag as [|next];[idtac|cases rest next] end in cases 18%nat tag.
   all:cbn [existsb Nat.eqb orb];unfold simple_tag in Htag;intuition lia.
 - pose proof(cost_bound tag a Htag). rewrite Nat2Z.inj_add. lia.
Qed.
Definition supported request := Protocol.opcode request=0%nat \/ NativeBasicDispatcher.supported(Protocol.opcode request) \/
 exists tag a b c,request=Protocol.Req 11 [tag;a;b;c] [] /\ simple_tag tag.
Definition capacity logical requests := Forall supported requests /\
 Z.of_nat(length(Protocol.formulas logical))+42*Z.of_nat(length requests)<=9223372036854775807 /\
 Z.of_nat(length(Protocol.classes logical))+Z.of_nat(length requests)<=maximum /\
 Z.of_nat(length(Protocol.history logical))+Z.of_nat(length requests)<=maximum /\
 Z.of_nat(length(Protocol.bindings logical))+Z.of_nat(length requests)<=maximum /\
 Z.of_nat(length(Protocol.expressions logical))+Z.of_nat(length requests)<=maximum /\
 Z.of_nat(NativeNameCompact.bytes logical)+1024*Z.of_nat(length requests)<=maximum.

Lemma supported_positive request : supported request -> Protocol.opcode request<>0%nat ->
 NativeBasicDispatcher.supported(Protocol.opcode request) \/ exists tag a b c,request=Protocol.Req 11[tag;a;b;c][] /\ simple_tag tag.
Proof. intros [Hzero|[Hbasic|Haxiom]] Hpositive;intuition. Qed.
Lemma supported_range request : supported request -> Protocol.opcode request<>0%nat -> (1<=Protocol.opcode request<=26)%nat.
Proof.
 intros Hsupported Hpositive. destruct(supported_positive _ Hsupported Hpositive) as [Hbasic|[tag [a [b [c [-> Htag]]]]]].
 - now apply NativeBasicDispatcher.supported_bound.
 - cbn [Protocol.opcode];lia.
Qed.
Lemma name_bound request : Protocol.shape request -> supported request -> Protocol.opcode request<>0%nat ->
 (length(Protocol.object_name request)<=1024)%nat.
Proof.
 intros Hshape Hsupported Hpositive. destruct(supported_positive _ Hsupported Hpositive) as [Hbasic|[tag [a [b [c [-> Htag]]]]]].
 - exact(NativeBasicSession.request_name_bound _ Hshape Hbasic).
 - cbn [Protocol.object_name length];lia.
Qed.
Lemma basic_specific native logical request : Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) ->
 NativeGeneralDispatcher.specific_resources native logical request.
Proof.
 intros Hshape Hsupported.
 destruct(NativeBasicDispatcher.shape_form request Hshape Hsupported) as
 [opcode a b Htag|opcode value Htag|opcode Htag|opcode value name Htag|opcode name Htag].
 all:unfold NativeGeneralDispatcher.specific_resources,NativeFullDispatcher.specific_resources.
 - unfold NativeBasicDispatcher.two in Htag. destruct Htag as [->|[->|[->|[->| ->]]]];exact I.
 - unfold NativeBasicDispatcher.one in Htag. destruct Htag as [->|[->|[->|[->| ->]]]];exact I.
 - unfold NativeBasicDispatcher.zero in Htag. destruct Htag as [->| ->];exact I.
 - unfold NativeBasicDispatcher.named in Htag. destruct Htag as [->|[->| ->]];exact I.
 - unfold NativeBasicDispatcher.query in Htag. destruct Htag as [->|[->|[->|[->| ->]]]];exact I.
Qed.
Lemma current_resources native logical request requests :
 Protocol.shape request -> Protocol.opcode request<>0%nat -> capacity logical(request::requests) ->
 NativeNameCompact.compact native logical -> NativeGeneralDispatcher.resources native logical request.
Proof.
 intros Hshape Hpositive [Hall [HF [HC [HH [HB [HE Hbytes]]]]]] Hcompact.
 inversion Hall as [|request' requests' Hsupported Htail];subst request' requests'.
 pose proof(name_bound _ Hshape Hsupported Hpositive) as Hname.
 cbn [length] in HF,HC,HH,HB,HE,Hbytes. rewrite Nat2Z.inj_succ in HF,HC,HH,HB,HE,Hbytes.
 constructor.
 - constructor;try lia.
   unfold NativeNameCompact.compact,NativeNameCompact.compact_bindings,NativeNameCompact.bytes in Hcompact.
   rewrite Nat2Z.inj_add,Hcompact. unfold NativeNameCompact.bytes in Hbytes. lia.
 - lia.
 - destruct(supported_positive _ Hsupported Hpositive) as [Hbasic|[tag [a [b [c [-> Htag]]]]]].
   + now apply basic_specific.
   + change(NativeAxiomTotal.resources logical tag a b c). apply resources;[exact Htag|lia].
Qed.
Lemma capacity_tail logical request requests reply next :
 Protocol.shape request -> supported request -> Protocol.opcode request<>0%nat -> capacity logical(request::requests) ->
 (length(Protocol.formulas next)<=length(Protocol.formulas logical)+42)%nat ->
 (length(Protocol.classes next)<=S(length(Protocol.classes logical)))%nat ->
 LogicalRegistryBounds.counts logical next 1 -> Protocol.step logical request reply next -> capacity next requests.
Proof.
 intros Hshape Hsupported Hpositive [Hall [HF [HC [HH [HB [HE Hbytes]]]]]] Hform Hclass [Hbinding [Hhistory Hschema]] Hstep.
 pose proof(NativeNameCompact.step_bytes_bound _ _ _ _ Hstep) as Hbytegrowth.
 pose proof(name_bound request Hshape Hsupported Hpositive) as Hname.
 inversion Hall;subst. unfold capacity. split;[assumption|].
 cbn [length] in HF,HC,HH,HB,HE,Hbytes. rewrite Nat2Z.inj_succ in HF,HC,HH,HB,HE,Hbytes.
 repeat split;lia.
Qed.

Lemma axiom_formula_growth native logical tag a b c bs ns tail observations final trace next :
 simple_tag tag ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat -> (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=50 -> meta_value native 8=0 -> Z.of_nat(length(Protocol.history logical))<maximum ->
 Z.of_nat tag<=maximum -> Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum ->
 NativeState.represents native logical -> NativeState.represents final next ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> NativeAxiomTotal.resources logical tag a b c ->
 stdin native=49::32::decimalBytes tag++32::decimalBytes a++32::decimalBytes b++32::decimalBytes c++10::tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 (length(Protocol.formulas next)<=length(Protocol.formulas logical)+42)%nat.
Proof.
 intros Htag Hmeta Hsip Htoken Hprint Hpending Herror HhistoryRoom Hwordtag Ha Hb Hc Hstate Hnext Htop Hfalse Hgood Hresources Hinput Hrun.
 destruct(NativeAxiomInvariant.generated_total native logical bs ns 49 [49] tag a b c 32 32 32 32 10 tail observations
   eq_refl Hmeta Hsip Htoken Hprint Hpending Herror HhistoryRoom Hwordtag Ha Hb Hc Hstate Htop Hfalse Hgood Hresources
   ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
   ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
   ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
 as(model & reply & after & HmodelRun & Hstep & HmodelState & Hio & Hsafe & HnextTop & HnextGood & Hprefix & Hgrowth).
 assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
 pose proof(NativeBasicCommandInvariant.same_formula_count final next _ Hnext (NativeState.formula_representation _ _ HmodelState)) as Hcount.
 pose proof(cost_bound tag a Htag). lia.
Qed.

Definition extra := NativeBasicSession.extra.
Theorem commands : NativeDialogueComposition.command_spec extra capacity.
Proof.
 intros native logical request requests observations Hboundary Hextra Hcapacity Hshape Hpositive Hinput.
 destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning].
 destruct Hextra as [Hmeta Hsip Hsafe Htop Hfalse Hgood Hunique Hcompact].
 assert(Hsupport:supported request) by (exact(Forall_inv(proj1 Hcapacity))).
 pose proof(supported_range request Hsupport Hpositive) as Hrange.
 destruct(NativeFullDispatcher.request_encoding request Hrange) as [Hwire Hbyte].
 change(stdin native=Protocol.request_bytes request++Protocol.wire requests) in Hinput.
 set(pending:=NativeFullTapeStep.entered native request (Protocol.wire requests)).
 assert(HpendingState:NativeState.represents pending logical).
 { unfold pending,NativeFullTapeStep.entered,CommandLoopExecution.pending_state.
   apply NativeSession.state_meta;try lia. now apply NativeSession.state_input. }
 assert(HpendingMeta:(31<length(memory pending arraydef_0__meta))%nat).
 { unfold pending. now rewrite NativeFullTapeStep.entered_meta_length. }
 assert(HpendingSip:(0<length(memory pending arraydef_0__sipState))%nat).
 { unfold pending. now rewrite NativeFullTapeStep.entered_arrays by discriminate. }
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
 pose proof(current_resources pending logical request requests Hshape Hpositive Hcapacity HpendingCompact) as Hresource.
 destruct(NativeGeneralCommandInvariant.graph_generated pending logical request (fun _=>false) (fun _=>0) (Protocol.wire requests) observations
  Hshape Hrange HpendingMeta HpendingSip HpendingToken HpendingPrint HpendingValue HpendingError HpendingState Hsafe
  HpendingTop Hfalse HpendingGood Hunique Hresource eq_refl)
 as(after & reply & next & Hrun & Hstep & HnextState & Hio & HnextSafe & HnextTop & HnextGood).
 assert(HnextCompact:NativeNameCompact.compact after next).
 { exact(NativeGeneralCommandInvariant.compact_step pending logical request (fun _=>false) (fun _=>0) (Protocol.wire requests)
   observations after _ reply next Hshape Hrange ltac:(lia) HpendingToken HpendingPrint HpendingValue HpendingError
   HpendingState Hsafe (NativeGeneralDispatcher.basic_resources _ _ _ Hresource) HpendingCompact eq_refl Hrun Hstep HnextState). }
 assert(Hgrowth:(length(Protocol.formulas next)<=length(Protocol.formulas logical)+42)%nat /\
  (length(Protocol.classes next)<=S(length(Protocol.classes logical)))%nat).
 { destruct(supported_positive request Hsupport Hpositive) as [Hbasic|[tag [a [b [c [Hrequest Htag]]]]]].
   - pose proof(NativeBasicCommandInvariant.preserves pending logical request (fun _=>false) (fun _=>0) (Protocol.wire requests)
      observations after _ reply next Hshape Hbasic ltac:(lia) HpendingToken HpendingPrint HpendingValue HpendingError HpendingState Hsafe
      (NativeGeneralDispatcher.basic_resources _ _ _ Hresource) HpendingTop Hfalse HpendingGood Hunique eq_refl Hrun Hstep HnextState)
     as(Hgraph & Hfalse' & Hgood' & HformGrowth & HclassGrowth & Hrest). split;lia.
   - subst request.
     pose proof(NativeGeneralCommandInvariant.axiom_class_count pending logical (Protocol.Req 11[tag;a;b;c][]) (fun _=>false) (fun _=>0)
      (Protocol.wire requests) observations after _ next Hshape eq_refl ltac:(lia) HpendingToken HpendingValue HpendingError eq_refl Hrun HpendingState HnextState)
      as HclassCount. split;[|lia].
     destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|tag' values Hwordtag Hrest];subst tag' values.
     inversion Hrest as [|a' values Ha Hrest2];subst a' values.
     inversion Hrest2 as [|b' values Hb Hrest3];subst b' values.
     inversion Hrest3 as [|c' values Hc Hnil];subst c' values.
     pose proof(NativeGeneralDispatcher.command_resources _ _ _ Hresource) as Hspecific.
     change(NativeAxiomTotal.resources logical tag a b c) in Hspecific.
     assert(HcommandInput:stdin pending=49::32::decimalBytes tag++32::decimalBytes a++32::decimalBytes b++32::decimalBytes c++10::Protocol.wire requests).
     { change(NativeBasicDispatcher.rest (Protocol.Req 11[tag;a;b;c][])++Protocol.wire requests=49::32::decimalBytes tag++32::decimalBytes a++32::decimalBytes b++32::decimalBytes c++10::Protocol.wire requests).
       apply NativeFullDispatcher.axiom_rest. }
     exact(axiom_formula_growth pending logical tag a b c (fun _=>false) (fun _=>0) (Protocol.wire requests) observations after _ next
       Htag HpendingMeta HpendingSip HpendingToken HpendingPrint HpendingValue HpendingError
       (NativeBasicDispatcher.history_room _ _ _ (NativeGeneralDispatcher.basic_resources _ _ _ Hresource))
       Hwordtag Ha Hb Hc HpendingState HnextState HpendingTop Hfalse HpendingGood Hspecific HcommandInput Hrun). }
 pose proof(LogicalRegistryBounds.step_counts _ _ _ _ Hstep) as Hcounts.
 pose proof(LogicalRegistryBounds.step_unique _ _ _ _ Hstep Hunique) as HnextUnique.
 pose proof(LogicalStorageMonotone.formula_lookup logical next 0 SetTheory.falsity (LogicalStorageMonotone.step _ _ _ _ Hstep) Hfalse) as HnextFalse.
 assert(HnextMeta:(31<length(memory after arraydef_0__meta))%nat).
 { rewrite(NativeCommandLengths.generated arraydef_0__meta pending (fun _=>false) (fun _=>0) after observations _ NativeCommandLengths.meta_protected Hrun). exact HpendingMeta. }
 assert(HnextSip:(0<length(memory after arraydef_0__sipState))%nat).
 { rewrite(NativeCommandLengths.generated arraydef_0__sipState pending (fun _=>false) (fun _=>0) after observations _ NativeCommandLengths.sipState_protected Hrun). exact HpendingSip. }
 destruct Hio as(Hin & Hout & HnextToken & HnextPrint & Hclear & Hstop).
 assert(HpendingStop:meta_value pending 9=meta_value native 9).
 { unfold pending,NativeFullTapeStep.entered,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. reflexivity. }
 exists(NativeBasicDispatcher.first(Protocol.opcode request)),(NativeBasicDispatcher.rest request++Protocol.wire requests),after,reply,next.
 split;[exact Hbyte|]. split;[rewrite Hinput,Hwire;reflexivity|]. split;[exact Hrun|]. split;[exact Hstep|].
 split;[constructor;try assumption;now rewrite Hstop,HpendingStop|].
 split;[constructor;assumption|]. split.
 - destruct Hgrowth. eapply capacity_tail;try eassumption.
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
End NativeProofSession.
