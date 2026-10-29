From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees Spec.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeStartupCompact NativeBasicSession NativeDialogueComposition
 NativeBasicDispatcher NativeBasicCommandInvariant NativeFullDispatcher NativeFullTapeStep NativeBudgetFrame NativeSetBudgetPlan NativeGeneralDispatcher NativeGeneralCommandInvariant
 NativeProofSession NativeSchemaInvariant NativeSchemaFlat NativeSetClassInvariant NativeSchemaSetBoundedBoundary NativeSchemaInstanceBoundary SchemaInstanceCommand
 SchemaEvaluationSetCell NativeNameCompact NativeRequestBounds NativeCommandBoundary NativeCommandLengths FormulaTopology ClassLookup LogicalRegistryBounds LogicalStorageMonotone
 CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSetSchemaSession.
Import IndexExecution SipHashExecution.
Definition extra native logical := NativeBasicSession.extra native logical /\ NativeSchemaFlat.flat native /\ SchemaEvaluationSetCell.sets(Protocol.classes logical).
Lemma basic_target request F E : NativeBasicDispatcher.supported(Protocol.opcode request) ->
 NativeSetBudgetPlan.formula_target request F E=S F.
Proof.
 intro Hsupported. unfold NativeBasicDispatcher.supported,NativeBasicDispatcher.two,NativeBasicDispatcher.one,NativeBasicDispatcher.zero,
 NativeBasicDispatcher.named,NativeBasicDispatcher.query in Hsupported.
 unfold NativeSetBudgetPlan.formula_target.
 repeat match goal with H:_ \/ _ |- _=>destruct H end;match goal with H:Protocol.opcode request=_ |- _=>rewrite H;reflexivity end.
Qed.
Lemma non_instance_growth native logical request bs ns tail observations final trace reply next before :
 Protocol.shape request -> Protocol.opcode request<>0%nat -> Protocol.opcode request<>24%nat ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat -> (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> LogicalRegistryBounds.unique logical ->
 NativeGeneralDispatcher.resources native logical request -> NativeSetBudgetPlan.bounds logical before -> NativeSetBudgetPlan.conditions before request ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 Protocol.step logical request reply next -> NativeState.represents final next ->
 SchemaEvaluationSetCell.sets(Protocol.classes logical) ->
 NativeSetBudgetPlan.quantitative logical request before next /\ SchemaEvaluationSetCell.sets(Protocol.classes next).
Proof.
 intros Hshape Hpositive Hnot24 Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hresource Hbounds Hconditions Hinput Hrun Hstep Hnext Hsets.
 pose proof(NativeSetBudgetPlan.formula_bound _ _ Hbounds) as HF.
 pose proof(NativeSetBudgetPlan.class_bound _ _ Hbounds) as HC.
 pose proof(NativeSetBudgetPlan.expression_bound _ _ Hbounds) as HE.
 assert(Hexpr:(length(Protocol.expressions next)<=NativeSetBudgetPlan.expression_target request (NativeSetBudgetPlan.expressions before))%nat).
 { pose proof(NativeRequestBounds.step_expression_count _ _ _ _ Hstep). unfold NativeSetBudgetPlan.expression_target. lia. }
 destruct(NativeSetBudgetPlan.form_view request Hshape Hpositive(NativeSetBudgetPlan.allowed_request _ _ Hconditions))
 as [request Hbasic Hnot6|tag a b c Hsimple|kind a b c d Hallowed|ids name];[| | |contradiction].
 - pose proof(NativeBasicCommandInvariant.preserves native logical request bs ns tail observations final trace reply next Hshape Hbasic ltac:(lia)
   Htoken Hprint Hpending Herror Hstate Hsafe(NativeGeneralDispatcher.basic_resources _ _ _ Hresource) Htop Hfalse Hgood Hunique Hinput Hrun Hstep Hnext)
   as(Htop' & Hfalse' & Hgood' & Hfg & Hcg & Hrest).
   split.
   + unfold NativeSetBudgetPlan.quantitative. rewrite(basic_target request _ _ Hbasic). repeat split;lia.
   + exact(NativeSetClassInvariant.basic native logical request bs ns tail observations final trace next Hshape Hbasic Hnot6 ltac:(lia) Htoken Hprint Hpending Herror
      (NativeBasicDispatcher.class_room _ _ _ (NativeGeneralDispatcher.basic_resources _ _ _ Hresource)) Hinput Hrun Hstate Hnext Hsets).
 - pose proof(NativeGeneralCommandInvariant.axiom_class_count native logical(Protocol.Req 11[tag;a;b;c][])bs ns tail observations final trace next
    Hshape eq_refl ltac:(lia) Htoken Hpending Herror Hinput Hrun Hstate Hnext) as Hclass.
   assert(Hgrowth:(length(Protocol.formulas next)<=length(Protocol.formulas logical)+42)%nat).
   { destruct Hshape as [Hwords Hformat]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|tag' values Htag Hrest];subst tag' values.
     inversion Hrest as [|a' values Ha Hrest2];subst a' values.
     inversion Hrest2 as [|b' values Hb Hrest3];subst b' values.
     inversion Hrest3 as [|c' values Hc Hnil];subst c' values.
     exact(NativeProofSession.axiom_formula_growth native logical tag a b c bs ns tail observations final trace next Hsimple Hmeta Hsip Htoken Hprint Hpending Herror
      (NativeBasicDispatcher.history_room _ _ _(NativeGeneralDispatcher.basic_resources _ _ _ Hresource)) Htag Ha Hb Hc Hstate Hnext Htop Hfalse Hgood
      (NativeGeneralDispatcher.command_resources _ _ _ Hresource) ltac:(now rewrite <-NativeFullDispatcher.axiom_rest) Hrun). }
   split.
   + unfold NativeSetBudgetPlan.quantitative. cbn [NativeSetBudgetPlan.formula_target Protocol.opcode]. repeat split;lia.
   + exact(NativeSetClassInvariant.axiom native logical(Protocol.Req 11[tag;a;b;c][])bs ns tail observations final trace reply next
      Hshape eq_refl ltac:(lia) Htoken Hpending Herror Hinput Hrun Hstate Hnext Hstep Hsets).
 - assert(Hform:length(Protocol.formulas next)=length(Protocol.formulas logical) /\ length(Protocol.classes next)=length(Protocol.classes logical)).
   { destruct Hshape as [Hwords Hformat]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|kind' values Hkind Hrest];subst kind' values.
     inversion Hrest as [|a' values Ha Hrest2];subst a' values.
     inversion Hrest2 as [|b' values Hb Hrest3];subst b' values.
     inversion Hrest3 as [|c' values Hc Hrest4];subst c' values.
     inversion Hrest4 as [|d' values Hd Hnil];subst d' values.
     change(meta_value native 15=51) in Hpending. rewrite NativeFullDispatcher.node_rest in Hinput.
     destruct(NativeSchemaInvariant.generated_total native logical bs ns 50 [50] kind a b c d 32 32 32 32 32 10 tail observations
       eq_refl Hsafe ltac:(lia) Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd(NativeGeneralDispatcher.schema_room _ _ _ Hresource)Hstate Hgood Htop
       ltac:(unfold TokenByteExecution.separator;tauto)ltac:(unfold TokenByteExecution.separator;tauto)ltac:(unfold TokenByteExecution.separator;tauto)
       ltac:(unfold TokenByteExecution.separator;tauto)ltac:(unfold TokenByteExecution.separator;tauto)ltac:(unfold TokenByteExecution.separator;tauto)Hinput)
       as(model & modelReply & target & Hcomplete & HmodelGood & HmodelTop & HformSame & HclassSame & Hgrowth).
     destruct Hcomplete as(Hchecked & HmodelState & Hio & Hunchanged & Houtcome). destruct Hchecked as(HmodelRun & Hrest').
     assert(Hsame:model=final) by(rewrite Hrun in HmodelRun;congruence). subst model.
     pose proof(NativeBasicCommandInvariant.same_formula_count _ _ _ Hnext(NativeState.formula_representation _ _ HmodelState)) as HfEqual.
     pose proof(NativeBasicCommandInvariant.class_count _ _ Hnext) as HcNext.
     pose proof(NativeBasicCommandInvariant.class_count _ _ HmodelState) as HcTarget. split;congruence. }
   split.
   + destruct Hform. unfold NativeSetBudgetPlan.quantitative. cbn [NativeSetBudgetPlan.formula_target Protocol.opcode]. repeat split;lia.
   + exact(NativeSetClassInvariant.node native logical(Protocol.Req 22[kind;a;b;c;d][])bs ns tail observations final trace next
      Hshape eq_refl ltac:(lia) Htoken Hpending Herror Hinput Hrun Hstate Hnext Hsets).
Qed.
Theorem generated_command native logical request bs ns tail observations before :
 Protocol.shape request -> Protocol.opcode request<>0%nat ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat -> (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> extra native logical ->
 NativeSetBudgetPlan.bounds logical before -> NativeSetBudgetPlan.conditions before request ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 exists final reply next,
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical request reply next /\ NativeState.represents final next /\
 NativeCommandBoundary.io native final reply tail /\ extra final next /\ NativeSetBudgetPlan.quantitative logical request before next.
Proof.
 intros Hshape Hpositive Hmeta Hsip Htoken Hprint Hpending Herror Hstate [Hextra [Hflat Hsets]] Hbounds Hconditions Hinput.
 destruct Hextra as [Hmeta' Hsip' Hsafe Htop Hfalse Hgood Hunique Hcompact].
 assert(Hrange:(1<=Protocol.opcode request<=26)%nat) by(pose proof(NativeSetBudgetPlan.opcode_bound _ _ Hconditions);lia).
 destruct(NativeSetBudgetPlan.basic_resources native logical before request Hshape Hcompact Hbounds Hconditions) as [Hbasic Hschema].
 assert(Hcore:exists final reply next,
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical request reply next /\ NativeState.represents final next /\
 NativeCommandBoundary.io native final reply tail /\ FormulaTopology.ordered final(length(Protocol.formulas next)) /\
 ClassLookup.wellformed final /\ SchemaEvaluationSetCell.sets(Protocol.classes next) /\ NativeSetBudgetPlan.quantitative logical request before next).
 { destruct(Nat.eq_dec(Protocol.opcode request)24%nat) as [H24|Hnot24].
   - destruct request as [opcode ids name]. cbn [Protocol.opcode] in H24. subst opcode.
     destruct Hshape as [Hwords [Hname Hlength]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hname,Hlength.
     change(meta_value native 15=51) in Hpending. rewrite NativeFullDispatcher.instance_rest in Hinput.
     destruct(NativeSchemaSetBoundedBoundary.generated_canonical native bs ns logical ids name tail observations
       Hmeta Htoken Hsip Hprint Hpending Herror Hname Hwords Hlength Hinput Hstate Hgood Htop Hfalse Hsafe Hsets
       (NativeSetBudgetPlan.instance_resources native logical before ids name Hstate Hflat Hsets Hbounds Hconditions))
       as(final & reply & next & Hrun & Hstep & Hnext & Hclear & HnextSafe & Hio & HnextGood & HnextTop & Hprefix & Hcprefix & Hword & Hpost).
     destruct Hpost as [Hfg [Hcs HnextSets]].
     assert(Hquant:NativeSetBudgetPlan.quantitative logical(Protocol.Req 24 ids name)before next).
     { pose proof(NativeSetBudgetPlan.formula_bound _ _ Hbounds) as HF.
       pose proof(NativeSetBudgetPlan.class_bound _ _ Hbounds) as HC.
       pose proof(NativeSetBudgetPlan.expression_bound _ _ Hbounds) as HE.
       pose proof(NativeRequestBounds.step_expression_count _ _ _ _ Hstep) as Hexpr.
       unfold NativeSetBudgetPlan.quantitative,NativeSetBudgetPlan.formula_target,NativeSetBudgetPlan.expression_target.
       cbn [Protocol.opcode] in *. rewrite Hcs. repeat split;nia. }
     exists final,reply,next. repeat first[assumption|split].
   - pose proof(NativeSetBudgetPlan.non_instance_resources native logical before request Hshape Hpositive Hnot24 Hcompact Hbounds Hconditions) as Hresource.
     destruct(NativeGeneralCommandInvariant.graph_generated native logical request bs ns tail observations Hshape Hrange Hmeta Hsip Htoken Hprint Hpending Herror
       Hstate Hsafe Htop Hfalse Hgood Hunique Hresource Hinput)
       as(final & reply & next & Hrun & Hstep & Hnext & Hio & HnextSafe & HnextTop & HnextGood).
     destruct(non_instance_growth native logical request bs ns tail observations final _ reply next before Hshape Hpositive Hnot24 Hmeta Hsip Htoken Hprint
       Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hresource Hbounds Hconditions Hinput Hrun Hstep Hnext Hsets) as [Hquant HnextSets].
     exists final,reply,next. repeat first[assumption|split]. }
 destruct Hcore as(final & reply & next & Hrun & Hstep & Hnext & Hio & HnextTop & HnextGood & HnextSets & Hquant).
 assert(HnextCompact:NativeNameCompact.compact final next).
 { exact(NativeGeneralCommandInvariant.compact_step native logical request bs ns tail observations final _ reply next Hshape Hrange ltac:(lia) Htoken Hprint
   Hpending Herror Hstate Hsafe Hbasic Hcompact Hinput Hrun Hstep Hnext). }
 assert(HnextFlat:NativeSchemaFlat.flat final).
 { exact(NativeSchemaFlat.preserves native logical request bs ns tail observations final _ Hshape Hrange ltac:(lia) Htoken Hprint Hpending Herror Hstate Hsafe Hschema
   Hflat(NativeSetBudgetPlan.form_flat request(NativeSetBudgetPlan.form_view request Hshape Hpositive(NativeSetBudgetPlan.allowed_request _ _ Hconditions))) Hinput Hrun). }
 assert(HnextMeta:(31<length(memory final arraydef_0__meta))%nat).
 { rewrite(NativeCommandLengths.generated arraydef_0__meta native bs ns final observations _ NativeCommandLengths.meta_protected Hrun). exact Hmeta. }
 assert(HnextSip:(0<length(memory final arraydef_0__sipState))%nat).
 { rewrite(NativeCommandLengths.generated arraydef_0__sipState native bs ns final observations _ NativeCommandLengths.sipState_protected Hrun). exact Hsip. }
 assert(HnextExtra:extra final next).
 { split;[|split;assumption]. constructor;try assumption.
   - exact(Guarantees.step_safe _ _ _ _ Hstep Hsafe).
   - exact(LogicalStorageMonotone.formula_lookup logical next 0 SetTheory.falsity(LogicalStorageMonotone.step _ _ _ _ Hstep)Hfalse).
   - exact(LogicalRegistryBounds.step_unique _ _ _ _ Hstep Hunique). }
 exists final,reply,next. repeat first[assumption|split].
Qed.
Theorem commands : NativeDialogueComposition.command_spec extra NativeSetBudgetPlan.capacity.
Proof.
 intros native logical request requests observations Hboundary [Hextra [Hflat Hsets]] [caps [Hbounds Hcheck]] Hshape Hpositive Hinput.
 destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning].
 destruct Hextra as [Hmeta Hsip Hsafe Htop Hfalse Hgood Hunique Hcompact].
 destruct(NativeSetBudgetPlan.check_tail caps request requests Hpositive Hcheck) as [Hconditions HtailCheck].
 assert(Hrange:(1<=Protocol.opcode request<=26)%nat) by (pose proof(NativeSetBudgetPlan.opcode_bound _ _ Hconditions);lia).
 destruct(NativeFullDispatcher.request_encoding request Hrange) as [Hwire Hbyte].
 change(stdin native=Protocol.request_bytes request++Protocol.wire requests) in Hinput.
 set(pending:=NativeFullTapeStep.entered native request (Protocol.wire requests)).
 assert(HpendingState:NativeState.represents pending logical) by (unfold pending;now apply NativeBudgetFrame.entered_state).
 assert(HpendingMeta:(31<length(memory pending arraydef_0__meta))%nat).
 { unfold pending. now rewrite NativeBudgetFrame.entered_lengths. }
 assert(HpendingSip:(0<length(memory pending arraydef_0__sipState))%nat).
 { unfold pending. now rewrite NativeBudgetFrame.entered_lengths. }
 assert(HpendingToken:(1024<=length(memory pending arraydef_0__token))%nat).
 { unfold pending. now rewrite NativeBudgetFrame.entered_lengths. }
 assert(HpendingPrint:(20<=length(memory pending arraydef_0__printBuffer))%nat).
 { unfold pending. now rewrite NativeBudgetFrame.entered_lengths. }
 assert(HpendingValue:meta_value pending 15=NativeBasicDispatcher.first(Protocol.opcode request)+1).
 { unfold pending. apply NativeBudgetFrame.entered_pending;lia. }
 assert(HpendingError:meta_value pending 8=0).
 { unfold pending. rewrite NativeBudgetFrame.entered_meta_other by lia. exact Herror. }
 assert(HpendingTop:FormulaTopology.ordered pending(length(Protocol.formulas logical))).
 { unfold pending. now apply NativeBudgetFrame.entered_top. }
 assert(HpendingGood:ClassLookup.wellformed pending).
 { unfold pending. now apply NativeBudgetFrame.entered_class_wellformed. }
 assert(HpendingCompact:NativeNameCompact.compact pending logical).
 { unfold pending. now apply NativeBudgetFrame.entered_compact. }
 assert(HpendingFlat:NativeSchemaFlat.flat pending) by(unfold pending;now apply NativeSchemaFlat.entered).
 destruct(generated_command pending logical request (fun _=>false) (fun _=>0)(Protocol.wire requests)observations caps
   Hshape Hpositive HpendingMeta HpendingSip HpendingToken HpendingPrint HpendingValue HpendingError HpendingState
   ltac:(split;[constructor;assumption|split;assumption]) Hbounds Hconditions eq_refl)
 as(after & reply & next & Hrun & Hstep & HnextState & Hio & HnextExtra & Hquantitative).
 pose proof(NativeSetBudgetPlan.capacity_next logical request requests reply next caps Hshape Hpositive Hstep Hbounds Hcheck Hquantitative) as HnextCapacity.
 destruct Hio as(Hin & Hout & HnextToken & HnextPrint & Hclear & Hstop).
 assert(HpendingStop:meta_value pending 9=meta_value native 9).
 { unfold pending. apply NativeBudgetFrame.entered_meta_other;lia. }
 exists(NativeBasicDispatcher.first(Protocol.opcode request)),(NativeBasicDispatcher.rest request++Protocol.wire requests),after,reply,next.
 split;[exact Hbyte|]. split;[rewrite Hinput,Hwire;reflexivity|]. split;[exact Hrun|]. split;[exact Hstep|].
 split;[constructor;try assumption;now rewrite Hstop,HpendingStop|]. split.
 - exact HnextExtra.
 - split;[exact HnextCapacity|]. split;[exact Hin|exact Hout].
Qed.
Theorem generated_finite requests native logical observations :
 Forall Protocol.shape requests -> NativeDialogueComposition.boundary native logical -> extra native logical ->
 NativeSetBudgetPlan.capacity logical requests -> stdin native=Protocol.wire requests ->
 exists final replies target remaining,
 DialogueExecution.run native observations final(observations++Protocol.flush_schedule requests replies(stdout native)) /\
 Protocol.dialogue logical requests replies target remaining /\ NativeState.represents final target /\ meta_value final 8=0 /\
 stdout final=stdout native++concat(map Protocol.reply_bytes replies) /\ stdin final=remaining.
Proof.
 exact(NativeDialogueComposition.generated_finite extra NativeSetBudgetPlan.capacity commands
   requests native logical observations).
Qed.
Theorem generated_main key0 key1 requests bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall Protocol.shape requests ->
 NativeSetBudgetPlan.capacity Protocol.initial requests ->
 exists replies final logical remaining,
 Protocol.dialogue Protocol.initial requests replies logical remaining /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(Protocol.wire requests)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++Protocol.wire requests|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=Protocol.wire requests|}]++
 Protocol.flush_schedule requests replies Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=remaining.
Proof.
 intros Hkey0 Hkey1 Hshape Hcapacity.
 destruct(NativeStartupCompact.main_to_commands key0 key1(Protocol.wire requests)bs ns Hkey0 Hkey1)
 as(ready & Hstate & Htop & Hmeta32 & Hsip1 & Hzero & Herror & Hmeta & Htoken & Hprint & Hstop & Hhistory & Hinput & Houtput & Hmain & Hempty).
 assert(Hboundary:NativeDialogueComposition.boundary ready Protocol.initial) by (constructor;assumption).
 assert(Hextra:extra ready Protocol.initial).
 { split.
   - constructor.
     + lia.
     + lia.
     + exact Guarantees.initial_safe.
     + exact Htop.
     + reflexivity.
     + apply ClassLookup.empty. exact(NativeState.empty_classes _ Hempty).
     + exact LogicalRegistryBounds.initial_unique.
     + apply NativeNameCompact.initial_compact. exact(NativeState.empty_names _ Hempty).
   - split.
     + apply NativeSchemaFlat.empty. exact(NativeState.empty_schemas _ Hempty).
     + constructor. }
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++Protocol.wire requests|};
   {|flushedOutput:=Protocol.handshake_output;unreadInput:=Protocol.wire requests|}]).
 destruct(generated_finite requests ready Protocol.initial observations Hshape Hboundary Hextra Hcapacity Hinput)
 as(final & replies & logical & remaining & Hrun & Hdialogue & Hfinal & Hclear & Hout & Hin).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as HcommandsRun.
 rewrite Houtput in HcommandsRun,Hout.
 exists replies,final,logical,remaining. split;[exact Hdialogue|].
 split;[exact(Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|]. split;[exact Hfinal|]. split;[exact Hclear|].
 split;[etransitivity;[exact Hmain|exact HcommandsRun]|]. split;assumption.
Qed.
(** Flat schemata with set-valued class parameters, quit and EOF, for the
    actual seeded main. The resource domain is a finite numeric Boolean plan. *)
Theorem required bs ns : Spec.required(funcdef_0__main bs ns)(arrays _ environment1)NativeSetBudgetPlan.domain.
Proof.
 intros key0 key1 requests Hkey0 Hkey1 Hshape Hdomain.
 destruct(generated_main key0 key1 requests bs ns Hkey0 Hkey1 Hshape
   (NativeSetBudgetPlan.initial_capacity requests Hdomain))
 as(replies & final & logical & remaining & Hdialogue & Hsafe & Hstate & Herror & Hrun & Hout & Hin).
 exists replies,final,logical,remaining. split;[exact Hdialogue|]. split;[exact Hsafe|]. split;[exact Hrun|]. split;assumption.
Qed.
End NativeSetSchemaSession.
