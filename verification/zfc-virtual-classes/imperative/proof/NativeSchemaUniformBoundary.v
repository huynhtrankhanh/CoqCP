From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl SchemaInstanceHandler SchemaInstanceCompletion SchemaEvaluation ReplyNO ArenaFrame SemanticFrames Representation ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation SchemaInstanceEntry SchemaEvaluationSetEntry SchemaEvaluationSetRun SchemaEvaluationSetCell SchemaEvaluationGeneralBudget SchemaEvaluationArguments SchemaEvaluationDependencies SchemaInstanceFinish SchemaInstanceLengths SchemaNodeMeaning SchemaMetadata SchemaMarking ClassLookup FormulaTopology InternalIO SchemaInstanceSetReady SchemaEvaluationIndexPractical SchemaEvaluationIndexReady SchemaEvaluationIndexCell SchemaEvaluationIndexBounds SchemaEvaluationBoundedCell TypedNameLookup SchemaInstanceReady SchemaInstanceGeneralReady SchemaInstanceProtocol SchemaGraph SchemaInstancePrefix SchemaInstanceArguments CommandChain ReadName ReadToken NameSearch HashTable SchemaInstanceSetProtocol CommandInput CommandDispatch NativeState ReadNat TokenByte TokenFrame FormulaProjection SchemaInstanceCommand FlushFrame FlushFrameReplies NativeCommandLengths NativeCommandStop NativeCommandBoundary NativeSchemaInstanceBoundary SchemaInstanceGeneralProtocol SchemaInstanceGeneralCommand NativeBasicInvariant EffectFrame SchemaEvaluationCell NativeSchemaGeneralBoundary.
From NativeProof Require Import ImmutableHandlers NativeSchemaGeneralInvariant SchemaEvaluationUniformEntry SchemaUniformBudget.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSchemaUniformBoundary.
Import IndexExecution SipHashExecution ObservedLocal.
Record budget (native:Machine) logical expression_cap field_cap initialF initialB initialC : Prop := Budget {
 expression_capacity : (length(Protocol.expressions logical)<=expression_cap)%nat;
 formula_capacity : (length(Protocol.formulas logical)<=initialF)%nat;
 class_capacity : (length(Protocol.classes logical)<=initialC)%nat;
 initial_indices : SchemaEvaluationIndexCell.bounded native (Protocol.formulas logical) (Protocol.classes logical) initialB;
 initial_fields : SchemaUniformBudget.encoded_fields native field_cap;
 history_room : Z.of_nat(length(Protocol.history logical))<maximum;
 formula_room : Z.of_nat(SchemaUniformBudget.formula_after initialF(SchemaUniformBudget.slots expression_cap))<=SchemaEvaluationBoundedCell.bound;
 index_room : Z.of_nat(SchemaUniformBudget.index_after expression_cap field_cap initialB(SchemaUniformBudget.slots expression_cap))<=maximum;
 fuel_room : Z.of_nat(5*(SchemaUniformBudget.formula_after initialF(SchemaUniformBudget.slots expression_cap)*SchemaUniformBudget.formula_after initialF(SchemaUniformBudget.slots expression_cap))+1)<=maximum;
 class_room : Z.of_nat(initialC+SchemaUniformBudget.slots expression_cap+1)<=maximum
}.
Definition post logical (native:Machine) next expression_cap field_cap initialF initialB initialC :=
 (length(Protocol.formulas next)<=SchemaUniformBudget.formula_after initialF(SchemaUniformBudget.slots expression_cap))%nat /\
 (length(Protocol.classes next)<=initialC+SchemaUniformBudget.slots expression_cap)%nat /\
 SchemaEvaluationIndexCell.bounded native (Protocol.formulas next) (Protocol.classes next)
   (SchemaUniformBudget.index_after expression_cap field_cap initialB(SchemaUniformBudget.slots expression_cap)) /\
 (length(Protocol.classes next)<=length(Protocol.classes logical)+SchemaUniformBudget.slots expression_cap)%nat.
Lemma budget_transport before after logical E N F B C :
 memory after arraydef_0__schemaNodes=memory before arraydef_0__schemaNodes ->
 memory after arraydef_0__formulas=memory before arraydef_0__formulas ->
 budget before logical E N F B C -> budget after logical E N F B C.
Proof.
 intros Hnodes Hformulas [HE HF0 HC0 Hbound Hfields Hhist HF HB Hfuel HC].
 constructor;try assumption.
 - exact(SchemaEvaluationIndexCell.bounded_array_frame before after _ _ B Hformulas Hbound).
 - unfold SchemaUniformBudget.encoded_fields in *. intros node k a b c d expression Hlookup.
   apply (Hfields node k a b c d expression). now rewrite <-Hnodes.
Qed.
Lemma general_resources native logical E N F B C ids name :
 SchemaRepresentation.represents native logical -> budget native logical E N F B C ->
 SchemaInstanceGeneralProtocol.resources native logical ids name.
Proof.
 intros Hschemas [HE HF0 HC0 Hbound Hfields Hhist HF HB Hfuel HC].
 exact(SchemaUniformBudget.protocol_resources native logical ids name E N F B C
   Hschemas HE Hfields HF0 HC0 Hbound Hhist HF HB Hfuel HC).
Qed.
Lemma rejected_post before after logical E N F B C :
 memory after arraydef_0__formulas=memory before arraydef_0__formulas ->
 budget before logical E N F B C -> post logical after logical E N F B C.
Proof.
 intros Hformulas [HE HF0 HC0 Hbound Hfields Hhist HF HB Hfuel HC].
 pose proof(SchemaUniformBudget.formula_mono F 0 (SchemaUniformBudget.slots E) ltac:(lia)) as HFstep.
 pose proof(SchemaUniformBudget.index_mono E N B 0 (SchemaUniformBudget.slots E) ltac:(lia)) as HBstep.
 cbn [SchemaUniformBudget.formula_after] in HFstep.
 cbn [SchemaUniformBudget.index_after] in HBstep.
 unfold post. split;[lia|]. split;[lia|]. split;[|lia].
 eapply SchemaEvaluationIndexCell.bounded_mono;[exact HBstep|].
 exact(SchemaEvaluationIndexCell.bounded_array_frame before after _ _ B Hformulas Hbound).
Qed.
Local Opaque funcdef_0__appendTheorem funcdef_0__no.
Lemma finish_formulas : EffectFrame.local_ro arraydef_0__formulas SchemaInstanceHandler.after_evaluation.
Proof.
 pose proof(NativeBasicInvariant.Arrays.appendTheorem_ro arraydef_0__formulas ltac:(repeat split;discriminate) ltac:(discriminate)) as Happend.
 pose proof(NativeBasicInvariant.Arrays.no_ro arraydef_0__formulas ltac:(repeat split;discriminate)) as Hno.
 unfold SchemaInstanceHandler.after_evaluation. EffectFrame.ro.
Qed.
Module Finish := NativeSchemaGeneralInvariant.Finish.
Module Ready.
Import SchemaInstanceGeneralReady.
Theorem generated E N F B C (f:SchemaInstanceHandler.Frame) logical index offset size root flag name cert ids actual observations :
 Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.schema_binding root) -> Protocol.pf logical root=Some cert ->
 length ids=Schemata.proof_arity cert -> Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual ->
 Forall (fun id=>word (Z.of_nat id)) ids -> SchemaEvaluationArguments.represents (machine f) ids ->
 nums f vardef_0__command_binding=Z.of_nat index -> Z.of_nat index<maximum ->
 nth_error (memory (machine f) arraydef_0__bindings) index=Some (offset,size,Z.of_nat root,flag,2) ->
 nums f vardef_0__command_a=Z.of_nat (length ids) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 (20<=length (memory (machine f) arraydef_0__printBuffer))%nat -> meta_value (machine f) 8=0 -> meta_value (machine f) 18<>0 ->
 Z.of_nat (SchemaMarking.size root)<=maximum -> Z.of_nat (length (Protocol.history logical))<maximum ->
 NativeRepresentation.canonical_arena (machine f) (Protocol.formulas logical) ->
 ClassStorage.represents (machine f) (Protocol.formulas logical) (Protocol.classes logical) ->
 HistoryRefinement.represents (machine f) logical -> NameRepresentation.represents (machine f) (Protocol.bindings logical) ->
 SchemaRepresentation.represents (machine f) logical -> ClassLookup.wellformed (machine f) ->
 FormulaTopology.ordered (machine f) (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 budget (machine f) logical E N F B C ->
 exists final reply next,
 execLocalObserved SchemaInstanceHandler.suffix (f,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes reply;unreadInput:=stdin (machine f)|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) reply next /\
 NativeRepresentation.canonical_arena (machine final) (Protocol.formulas next) /\
 ClassStorage.represents (machine final) (Protocol.formulas next) (Protocol.classes next) /\
 HistoryRefinement.represents (machine final) next /\ NameRepresentation.represents (machine final) (Protocol.bindings next) /\
 SchemaRepresentation.represents (machine final) next /\ meta_value (machine final) 8=0 /\
 (Guarantees.safe logical -> Guarantees.safe next) /\
 ClassLookup.wellformed (machine final) /\ FormulaTopology.ordered (machine final) (length (Protocol.formulas next)) /\
 (exists extra,Protocol.formulas next=Protocol.formulas logical++extra) /\
 (exists extra,Protocol.classes next=Protocol.classes logical++extra) /\
 post logical (machine final) next E N F B C.
Proof.
 intros Hname Hproof Hlength Hactual Hwords Hvector Hbinding Hindex Hbindingraw Hcount Hmeta Hsip Hprint Herror Hvalid
   Hgrid Hhistoryroom Harena Hclasses Hhistory Hnames Hschemas Hgood Htop Hfalse Hbudget.
 destruct Hbudget as [HE HF0 HC0 Hbounded Hfields Hhist HF HB Hfuel HC].
 pose proof (SchemaNodeMeaning.proof_lookup logical root cert Hproof) as Hlookup.
 destruct (SchemaMetadata.represented_lookup (machine f) (Protocol.expressions logical) root (Protocol.PE cert)
   (SchemaRepresentation.metadata _ _ Hschemas) Hlookup) as [raw [Hraw Hentry]].
 destruct raw as [[[[[[kind a] b] c] d] ty] arity].
 cbn [SchemaMetadata.entry SchemaMetadata.kind SchemaMetadata.arity] in Hentry.
 destruct Hentry as [Hty [Harity Hwidth]]. subst ty arity.
 assert (Hparameters:SchemaEvaluationGeneralBudget.parameters (machine f) root (machine f) (Protocol.classes logical) (substitution actual)).
 { eapply SchemaInstanceSetReady.parsed_parameters;[exact Hschemas|exact Hlookup|exact Hlength|exact Hactual|exact Hwords|exact Hvector]. }
 destruct (SchemaEvaluationUniformEntry.generated E N F B C (machine f) (fun _=>false) (SchemaInstanceHandler.instance_arguments (Z.of_nat root))
   logical root cert (substitution actual) observations Hschemas Hlookup Hgrid
   ltac:(unfold SchemaInstanceHandler.instance_arguments;apply RenameMemoControl.updated_same)
   Harena Hclasses Hgood Htop Hfalse Hhistory Hnames Hmeta Hsip Herror Hvalid HF0 Hbounded Hparameters
   HE HC0 Hfields HF HB Hfuel HC)
  as (built & fs & classes & Hrun & HnextArena & HnextClasses & HnextHistory & HnextNames & HnextSchemas & HnextWords
    & HnextTop & HnextError & Hio & Hfs & Hcs & HclassExact & HclassTotal & HformulaTotal & Hbounds & Hsafe & Hresult).
 assert (HnextMeta:(18<length (memory built arraydef_0__meta))%nat).
 { rewrite (SchemaInstanceLengths.generated arraydef_0__meta (machine f) _ _ built observations observations
     SchemaInstanceLengths.meta_protected Hrun). lia. }
 assert (HnextPrint:(20<=length (memory built arraydef_0__printBuffer))%nat).
 { rewrite (SchemaInstanceLengths.generated arraydef_0__printBuffer (machine f) _ _ built observations observations
     SchemaInstanceLengths.print_protected Hrun). exact Hprint. }
 set (middle:=setMachine (SchemaInstanceHandler.rooted f root) built).
 assert (Hchecked:((exists p,Schemata.infer (substitution actual) 0 cert=Some p /\
   SchemaEvaluation.formula_value fs (meta_value built 0) p /\ meta_value built 18<>0) \/
   (Schemata.infer (substitution actual) 0 cert=None /\ meta_value built 18=0))).
 { destruct Hresult as [[p [Hinfer [Hderive [Hmeaning Hflag]]]]|Hfailure].
   - left. exists p. split;[exact Hinfer|]. split;[exact Hmeaning|exact Hflag].
   - now right. }
 destruct (Finish.generated_verified middle logical fs classes name root cert ids actual observations
   Hname Hproof Hlength Hactual Hfs Hcs HnextMeta HnextPrint HnextError Hhistoryroom
   HnextArena HnextClasses HnextHistory HnextNames HnextSchemas HnextWords HnextTop Hchecked)
  as (final & reply & next & Hfinish & Hstep & Hfa & Hfc & Hfh & Hfn & Hfschema & Hflag & HnextSafe & HfinalGood & HfinalTop & HfinalFs & HfinalCs).
 assert(HfinalBound:SchemaEvaluationIndexCell.bounded (machine final) fs classes
   (SchemaUniformBudget.index_after E N B(SchemaUniformBudget.slots E))).
 { eapply SchemaEvaluationIndexCell.bounded_array_frame;[|exact Hbounds].
   change(memory(machine final)arraydef_0__formulas=memory(machine middle)arraydef_0__formulas).
   exact(ImmutableHandlers.local_observed_preserves arraydef_0__formulas _ _ _ _ _ finish_formulas Hfinish). }
 assert(Hsize:(SchemaMarking.size root<=SchemaUniformBudget.slots E)%nat).
 { assert(HrootCap:(root<length(Protocol.expressions logical))%nat) by (apply nth_error_Some;congruence).
   unfold SchemaMarking.size,SchemaGraph.width,SchemaUniformBudget.slots;nia. }
 assert(Hpost:post logical (machine final) next E N F B C).
 { unfold post. rewrite HfinalFs,HfinalCs. split;[exact HformulaTotal|]. split;[exact HclassTotal|].
   split;[exact HfinalBound|lia]. }
 exists final,reply,next. split.
 - rewrite (SchemaInstanceHandler.generated_checked f index offset size root flag kind a b c d 2
    (Schemata.proof_arity cert) observations ltac:(lia) Herror Hbinding Hindex Hbindingraw Hraw ltac:(now rewrite Hlength in Hcount) Hvalid).
   match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state]=>
     let expression:=constr:(@execLocalObserved I T EI V EV R code state) in
     let Hsame:=fresh in assert (Hsame:expression=execLocalObserved SchemaInstanceHandler.after_evaluation (middle,observations)) by
       exact (SchemaInstanceHandler.generated_evaluation (SchemaInstanceHandler.rooted f root) root built observations
         ltac:(unfold SchemaInstanceHandler.rooted;cbn [nums setNum];apply RenameMemoControl.updated_same) Hrun);
       rewrite Hsame;clear Hsame end.
   unfold InternalIO.preserves in Hio. destruct Hio as [Hinput Houtput].
   change (execLocalObserved SchemaInstanceHandler.after_evaluation (middle,observations)=Some (tt,(final,
     observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes reply;unreadInput:=stdin (machine f)|}]))).
   unfold middle in Hfinish. cbn [machine setMachine] in Hfinish. now rewrite Hinput,Houtput in Hfinish.
 - repeat first [assumption|split].
   + now rewrite HfinalFs.
   + now rewrite HfinalCs.
Qed.
End Ready.
Module ProtocolInvariant.
Import SchemaInstanceProtocol SchemaInstanceGeneralProtocol.
Definition checked E N F B C (f final:SchemaInstanceHandler.Frame) logical ids name observations reply next :=
 execLocalObserved SchemaInstanceHandler.suffix (f,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes reply;unreadInput:=stdin (machine f)|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) reply next /\
 NativeRepresentation.canonical_arena (machine final) (Protocol.formulas next) /\
 ClassStorage.represents (machine final) (Protocol.formulas next) (Protocol.classes next) /\
 HistoryRefinement.represents (machine final) next /\ NameRepresentation.represents (machine final) (Protocol.bindings next) /\
 SchemaRepresentation.represents (machine final) next /\ meta_value (machine final) 8=0 /\ Guarantees.safe next /\
 ClassLookup.wellformed (machine final) /\ FormulaTopology.ordered (machine final) (length (Protocol.formulas next)) /\
 (exists extra,Protocol.formulas next=Protocol.formulas logical++extra) /\
 (exists extra,Protocol.classes next=Protocol.classes logical++extra) /\
 post logical (machine final) next E N F B C.
Lemma checked_rejected E N F B C f final logical ids name observations :
 execLocalObserved SchemaInstanceHandler.suffix (f,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin (machine f)|}])) ->
 machine final=ReplyNOExecution.reply_state (machine f) ->
 (forall reply next,~Protocol.accepted logical (Protocol.Req 24 ids name) reply next) ->
 NativeRepresentation.canonical_arena (machine f) (Protocol.formulas logical) ->
 ClassStorage.represents (machine f) (Protocol.formulas logical) (Protocol.classes logical) ->
 HistoryRefinement.represents (machine f) logical -> NameRepresentation.represents (machine f) (Protocol.bindings logical) ->
 SchemaRepresentation.represents (machine f) logical -> meta_value (machine f) 8=0 -> Guarantees.safe logical ->
 ClassLookup.wellformed (machine f) -> FormulaTopology.ordered (machine f) (length (Protocol.formulas logical)) ->
 budget (machine f) logical E N F B C ->
 checked E N F B C f final logical ids name observations Protocol.NO logical.
Proof.
 intros Hrun Hmachine Hreject Harena Hclasses Hhistory Hnames Hschemas Herror Hsafe Hgood Htop Hbudget. unfold checked.
 split;[exact Hrun|]. split.
 - apply Protocol.step_reject;[exact Hreject|]. apply HistoryRefinement.retained_refl. exact (SemanticFrames.arena_NoDup _ _ Harena).
 - rewrite Hmachine. split.
   + exact (ArenaFrame.storage_arena (machine f) _ _ (ArenaFrame.storage_output (machine f) _) Harena).
   + split;[exact Hclasses|]. split;[exact Hhistory|]. split;[exact Hnames|]. split;[exact Hschemas|]. split;[exact Herror|]. split;[exact Hsafe|]. split;[exact Hgood|]. split;[exact Htop|].
     split;[exists [];now rewrite app_nil_r|]. split;[exists [];now rewrite app_nil_r|].
     apply(rejected_post (machine f));[reflexivity|exact Hbudget].
Qed.
Theorem generated_suffix E N F B C (f:SchemaInstanceHandler.Frame) logical ids name observations :
 Forall (fun id=>word (Z.of_nat id)) ids -> SchemaEvaluationArguments.represents (machine f) ids ->
 TypedNameLookup.outcome (machine f) (Protocol.bindings logical) name ->
 nums f vardef_0__command_binding=meta_value (machine f) 0 -> nums f vardef_0__command_a=Z.of_nat (length ids) ->
 meta_value (machine f) 18=(if forallb (fun id=>bool_decide (Z.of_nat id<meta_value (machine f) 2)) ids then 1 else 0) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 (20<=length (memory (machine f) arraydef_0__printBuffer))%nat -> meta_value (machine f) 8=0 ->
 NativeRepresentation.canonical_arena (machine f) (Protocol.formulas logical) ->
 ClassStorage.represents (machine f) (Protocol.formulas logical) (Protocol.classes logical) ->
 HistoryRefinement.represents (machine f) logical -> NameRepresentation.represents (machine f) (Protocol.bindings logical) ->
 SchemaRepresentation.represents (machine f) logical -> ClassLookup.wellformed (machine f) ->
 FormulaTopology.ordered (machine f) (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 Guarantees.safe logical -> budget (machine f) logical E N F B C ->
 exists final reply next,checked E N F B C f final logical ids name observations reply next.
Proof.
 intros Hwords Hvector Houtcome Hbinding Hcount Hvalid Hmeta Hsip Hprint Herror Harena Hclasses Hhistory Hnames Hschemas Hgood Htop Hfalse Hsafe Hresources.
 pose proof(general_resources (machine f) logical E N F B C ids name Hschemas Hresources) as Hgeneral.
 destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hlookup.
 - destruct (outcome_found (machine f) logical name meaning Hlookup Houtcome)
    as (index & offset & size & flag & HindexValue & Hindex & Hraw).
   assert (HnativeBinding:nums f vardef_0__command_binding=Z.of_nat index) by congruence.
   destruct meaning as [id certified|id|root].
   + exists (setMachine f (ReplyNOExecution.reply_state (machine f))),Protocol.NO,logical.
     eapply checked_rejected;try eassumption;[|reflexivity|].
     * apply (SchemaInstanceHandler.generated_wrong_kind f index offset size (Z.of_nat id) flag 0 observations ltac:(lia) Herror HnativeBinding Hindex Hraw ltac:(lia)).
     * apply rejected_name. intros root Hschema. congruence.
   + exists (setMachine f (ReplyNOExecution.reply_state (machine f))),Protocol.NO,logical.
     eapply checked_rejected;try eassumption;[|reflexivity|].
     * apply (SchemaInstanceHandler.generated_wrong_kind f index offset size (Z.of_nat id) flag 1 observations ltac:(lia) Herror HnativeBinding Hindex Hraw ltac:(lia)).
     * apply rejected_name. intros root Hschema. congruence.
   + destruct (Guarantees.lookup_sound logical name (Protocol.schema_binding root) (proj2 Hsafe) Hlookup) as [cert Hproof].
     pose proof (SchemaNodeMeaning.proof_lookup logical root cert Hproof) as HrootLookup.
     destruct (SchemaMetadata.represented_lookup (machine f) (Protocol.expressions logical) root (Protocol.PE cert)
       (SchemaRepresentation.metadata _ _ Hschemas) HrootLookup) as [raw [Hnode Hentry]].
     destruct raw as [[[[[[kind a] b] c] d] ty] arity].
     cbn [SchemaMetadata.entry SchemaMetadata.kind SchemaMetadata.arity] in Hentry.
     destruct Hentry as [Hty [Harity Hword]]. subst ty arity.
     destruct (Nat.eq_dec (length ids) (Schemata.proof_arity cert)) as [Hlength|Hlength].
     * destruct (forallb (fun id=>bool_decide (Z.of_nat id<meta_value (machine f) 2)) ids) eqn:Harguments.
       -- destruct (proj1 (SchemaInstancePrefix.native_class_arguments (machine f) logical (Protocol.formulas logical) ids Hclasses) Harguments) as [actual Hactual].
          destruct (Hgeneral root cert actual Hlookup Hproof Hlength Hactual) as [Hgrid [HhistoryRoom Hready]].
          destruct (Ready.generated E N F B C f logical index offset size root flag name cert ids actual observations
            Hlookup Hproof Hlength Hactual Hwords Hvector HnativeBinding Hindex Hraw Hcount Hmeta Hsip Hprint Herror ltac:(lia)
            Hgrid HhistoryRoom Harena Hclasses Hhistory Hnames Hschemas Hgood Htop Hfalse Hresources)
           as (final & reply & next & Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfs & Hflag & HnextSafe & HfinalGood & HfinalTop & HfinalFs & HfinalCs & Hpost).
          exists final,reply,next. unfold checked. repeat first [assumption|exact (HnextSafe Hsafe)|split].
       -- exists (setMachine (SchemaInstanceHandler.rooted f root) (ReplyNOExecution.reply_state (machine f))),Protocol.NO,logical.
          eapply checked_rejected;try eassumption;[|reflexivity|].
          ++ apply (SchemaInstanceHandler.generated_bad_arity f index offset size root flag kind a b c d 2 (Schemata.proof_arity cert) (length ids) observations
             ltac:(lia) Herror HnativeBinding Hindex Hraw Hnode Hcount). right;exact Hvalid.
          ++ apply rejected_arguments. intros [actual Hactual].
             pose proof (proj2 (SchemaInstancePrefix.native_class_arguments (machine f) logical (Protocol.formulas logical) ids Hclasses) (ex_intro _ actual Hactual)) as Htrue. congruence.
     * exists (setMachine (SchemaInstanceHandler.rooted f root) (ReplyNOExecution.reply_state (machine f))),Protocol.NO,logical.
       eapply checked_rejected;try eassumption;[|reflexivity|].
       -- apply (SchemaInstanceHandler.generated_bad_arity f index offset size root flag kind a b c d 2 (Schemata.proof_arity cert) (length ids) observations
            ltac:(lia) Herror HnativeBinding Hindex Hraw Hnode Hcount). now left.
       -- exact (rejected_arity logical ids name root cert Hlookup Hproof Hlength).
 - exists (setMachine f (ReplyNOExecution.reply_state (machine f))),Protocol.NO,logical.
   eapply checked_rejected;try eassumption;[|reflexivity|].
   + apply SchemaInstanceHandler.generated_absent;try assumption;[lia|].
     unfold TypedNameLookup.outcome in Houtcome. rewrite Hlookup in Houtcome. congruence.
   + apply rejected_name. intros root Hschema. congruence.
Qed.
Theorem generated_handler E N F B C (f:SchemaInstanceHandler.Frame) logical ids name tail observations :
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (1024<=length (memory (machine f) arraydef_0__token))%nat ->
 (0<length (memory (machine f) arraydef_0__sipState))%nat -> (20<=length (memory (machine f) arraydef_0__printBuffer))%nat ->
 meta_value (machine f) 15=0 -> meta_value (machine f) 8=0 -> Protocol.valid_name name ->
 Forall (fun id=>Z.of_nat id<=maximum) ids -> Z.of_nat (length ids)<=maximum ->
 stdin (machine f)=name++32::(decimalBytes (length ids)++SchemaInstanceArguments.separator_for ids::(SchemaInstanceArguments.wire ids++tail)) ->
 NativeRepresentation.canonical_arena (machine f) (Protocol.formulas logical) ->
 ClassStorage.represents (machine f) (Protocol.formulas logical) (Protocol.classes logical) ->
 HistoryRefinement.represents (machine f) logical -> NameRepresentation.represents (machine f) (Protocol.bindings logical) ->
 SchemaRepresentation.represents (machine f) logical -> ClassLookup.wellformed (machine f) ->
 FormulaTopology.ordered (machine f) (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 Guarantees.safe logical -> budget (machine f) logical E N F B C ->
 exists final reply next,
 execLocalObserved (CommandChain.handler_for funcdef_0__readNat 24) (f,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) reply next /\
 NativeRepresentation.canonical_arena (machine final) (Protocol.formulas next) /\
 ClassStorage.represents (machine final) (Protocol.formulas next) (Protocol.classes next) /\
 HistoryRefinement.represents (machine final) next /\ NameRepresentation.represents (machine final) (Protocol.bindings next) /\
 SchemaRepresentation.represents (machine final) next /\ meta_value (machine final) 8=0 /\ Guarantees.safe next /\
 ClassLookup.wellformed (machine final) /\ FormulaTopology.ordered (machine final) (length (Protocol.formulas next)) /\
 (exists extra,Protocol.formulas next=Protocol.formulas logical++extra) /\
 (exists extra,Protocol.classes next=Protocol.classes logical++extra) /\
 post logical (machine final) next E N F B C.
Proof.
 intros Hmeta Htoken Hsip Hprint Hpending Herror Hname Hwords Hsize Hinput Harena Hclasses Hhistory Hnames Hschemas Hgood Htop Hfalse Hsafe Hresources.
 destruct (SchemaInstancePrefix.generated_canonical f (Protocol.bindings logical) name ids tail SchemaInstanceHandler.suffix observations
   ltac:(lia) Htoken Hpending Herror Hnames Hname Hwords Hsize Hinput)
   as (looked & HlookupFrame & Houtcome & Hprefix & Hvector & Hin & Hout & Hclear & Hvalid & HlookLength).
 set (parsed:=SchemaInstancePrefix.finished f looked ids tail).
 assert (HparsedFrame:SchemaInstancePrefix.parsed_frame (machine f) (machine parsed)).
 { exact (SchemaInstancePrefix.finished_frame f looked name ids tail ltac:(lia) HlookLength HlookupFrame). }
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
  if forallb (fun id=>bool_decide (Z.of_nat id<meta_value (machine parsed) 2)) ids then 1 else 0).
 { assert (HclassCount:meta_value (machine parsed) 2=meta_value (machine f) 2) by (apply Hcells;lia).
   rewrite HclassCount. exact Hvalid. }
 assert (HparsedResources:budget (machine parsed) logical E N F B C).
 { apply (budget_transport (machine f));[apply Harrays;discriminate|apply Harrays;discriminate|exact Hresources]. }
 assert (HidWords:Forall (fun id=>word (Z.of_nat id)) ids).
 { clear -Hwords. induction Hwords as [|head rest Hhead Hrest IH].
   - constructor.
   - constructor;[unfold word;lia|exact IH]. }
 destruct (generated_suffix E N F B C parsed logical ids name observations HidWords Hvector
   (SchemaInstancePrefix.finished_outcome f looked ids tail (Protocol.bindings logical) name Hlooked Houtcome)
   (SchemaInstancePrefix.finished_binding_result f looked ids tail Hlooked)
   (SchemaInstancePrefix.finished_count f looked ids tail) HvalidParsed
   ltac:(now rewrite Hlength) ltac:(now rewrite Harrays by discriminate) ltac:(now rewrite Harrays by discriminate)
   Hclear HparsedArena HparsedClasses HparsedHistory HparsedNames HparsedSchemas HparsedGood HparsedTop Hfalse Hsafe HparsedResources)
   as (final & reply & next & Hchecked).
 destruct Hchecked as (Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfs & Hflag & HnextSafe & HfinalGood & HfinalTop & HfinalFs & HfinalCs & Hpost).
 exists final,reply,next. split.
 - rewrite SchemaInstancePrefix.actual_handler. fold parsed in Hprefix.
   etransitivity;[exact Hprefix|]. etransitivity;[exact Hrun|].
   unfold parsed. now rewrite Hin,Hout.
 - repeat first [assumption|split].
Qed.
End ProtocolInvariant.
Import SchemaInstanceCommand NativeSchemaInstanceBoundary.
Theorem generated_canonical E N F B C s bs ns logical ids name tail observations :
 (31<length (memory s arraydef_0__meta))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat ->
 (0<length (memory s arraydef_0__sipState))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=51 -> meta_value s 8=0 ->
 Protocol.valid_name name -> Forall (fun id=>Z.of_nat id<=maximum) ids -> Z.of_nat (length ids)<=maximum ->
 stdin s=52::32::payload ids name tail ->
 NativeState.represents s logical -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 Guarantees.safe logical -> budget s logical E N F B C ->
 exists final reply next,
 execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) reply next /\
 NativeState.represents final next /\ meta_value final 8=0 /\ Guarantees.safe next /\ NativeCommandBoundary.io s final reply tail /\
 ClassLookup.wellformed final /\ FormulaTopology.ordered final (length (Protocol.formulas next)) /\
 (exists extra,Protocol.formulas next=Protocol.formulas logical++extra) /\
 (exists extra,Protocol.classes next=Protocol.classes logical++extra) /\ word (Z.of_nat (length (Protocol.formulas next))) /\ post logical final next E N F B C.
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
 assert (HhandlerResources:budget (machine f) logical E N F B C).
 { apply (budget_transport s);[| |exact Hresources].
   all: unfold f,initial_frame,CommandDispatch.opcode_frame,op,opcode_state;cbn [machine setNum setMachine];apply CommandInput.parsed_other;discriminate. }
 destruct (ProtocolInvariant.generated_handler E N F B C f logical ids name tail observations
   HopMeta HopToken HopSip HopPrint HopPending HopError Hname Hwords Hlength HopInput
   HopArena HopClasses HopHistory HopNames HopSchemas HopGood HopTop Hfalse Hsafe HhandlerResources)
 as (after & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hschemas & Hclear & HnextSafe & HfinalGood & HfinalTop & HfinalFs & HfinalCs & Hpost).
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
   split.
   2:{ split;[exact HfinalGood|]. split;[exact HfinalTop|]. split;[exact HfinalFs|]. split;[exact HfinalCs|].
       split;[exact (SchemaEvaluationCell.arena_count_word _ _ Harena)|exact Hpost]. }
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
End NativeSchemaUniformBoundary.
