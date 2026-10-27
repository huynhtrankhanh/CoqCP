From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl SchemaInstanceHandler SchemaInstanceCompletion SchemaEvaluation ReplyNO ArenaFrame SemanticFrames Representation ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation SchemaInstanceEntry SchemaEvaluationSetEntry SchemaEvaluationSetRun SchemaEvaluationSetCell SchemaEvaluationGeneralBudget SchemaEvaluationArguments SchemaEvaluationDependencies SchemaInstanceFinish SchemaInstanceLengths SchemaNodeMeaning SchemaMetadata SchemaMarking ClassLookup FormulaTopology InternalIO SchemaInstanceSetReady SchemaEvaluationIndexPractical SchemaEvaluationIndexReady SchemaEvaluationIndexCell SchemaEvaluationIndexBounds SchemaEvaluationBoundedCell TypedNameLookup SchemaInstanceReady SchemaInstanceGeneralReady SchemaInstanceProtocol SchemaGraph SchemaInstancePrefix SchemaInstanceArguments CommandChain ReadName ReadToken NameSearch HashTable SchemaInstanceSetProtocol CommandInput CommandDispatch NativeState ReadNat TokenByte TokenFrame FormulaProjection SchemaInstanceCommand FlushFrame FlushFrameReplies NativeCommandLengths NativeCommandStop NativeCommandBoundary NativeSchemaInstanceBoundary SchemaInstanceGeneralProtocol SchemaInstanceGeneralCommand NativeBasicInvariant EffectFrame SchemaEvaluationCell NativeSchemaGeneralBoundary.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSchemaGeneralInvariant.
Import IndexExecution SipHashExecution ObservedLocal.
Module Finish.
Import SchemaInstanceFinish.
Theorem generated_verified (f:SchemaInstanceHandler.Frame) logical fs classes name root cert ids actual observations :
 Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.schema_binding root) ->
 Protocol.pf logical root=Some cert -> length ids=Schemata.proof_arity cert ->
 Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual ->
 (exists extra,fs=Protocol.formulas logical++extra) -> (exists extra,classes=Protocol.classes logical++extra) ->
 (18<length (memory (machine f) arraydef_0__meta))%nat -> (20<=length (memory (machine f) arraydef_0__printBuffer))%nat ->
 meta_value (machine f) 8=0 -> Z.of_nat (length (Protocol.history logical))<maximum ->
 NativeRepresentation.canonical_arena (machine f) fs -> ClassStorage.represents (machine f) fs classes ->
 HistoryRefinement.represents (machine f) logical -> NameRepresentation.represents (machine f) (Protocol.bindings logical) ->
 SchemaRepresentation.represents (machine f) (SchemaInstanceCompletion.prepared logical fs classes) ->
 ClassLookup.wellformed (machine f) -> FormulaTopology.ordered (machine f) (length fs) ->
 ((exists p,Schemata.infer (fun i=>List.nth i actual (VirtualClasses.set 0)) 0 cert=Some p /\
    SchemaEvaluation.formula_value fs (meta_value (machine f) 0) p /\ meta_value (machine f) 18<>0) \/
  (Schemata.infer (fun i=>List.nth i actual (VirtualClasses.set 0)) 0 cert=None /\ meta_value (machine f) 18=0)) ->
 exists final reply next,
 execLocalObserved SchemaInstanceHandler.after_evaluation (f,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes reply;unreadInput:=stdin (machine f)|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) reply next /\
 NativeRepresentation.canonical_arena (machine final) (Protocol.formulas next) /\
 ClassStorage.represents (machine final) (Protocol.formulas next) (Protocol.classes next) /\
 HistoryRefinement.represents (machine final) next /\ NameRepresentation.represents (machine final) (Protocol.bindings next) /\
 SchemaRepresentation.represents (machine final) next /\ meta_value (machine final) 8=0 /\
 (Guarantees.safe logical -> Guarantees.safe next) /\
 ClassLookup.wellformed (machine final) /\ FormulaTopology.ordered (machine final) (length (Protocol.formulas next)) /\
 Protocol.formulas next=fs /\ Protocol.classes next=classes.
Proof.
 intros Hname Hroot Hlength Hactual Hfs Hcs Hmeta Hprint Herror Hroom Harena Hclasses Hhistory Hnames Hschemas Hgood HtopInitial Hresult.
 destruct Hresult as [[p [Hinfer [Hmeaning Hvalid]]]|[Hfailure Hinvalid]].
 - destruct (SchemaInstanceCompletion.generated_accepted (machine f) logical fs classes (fun _=>false)
     (arguments (meta_value (machine f) 0)) name root cert ids actual p observations
     Hname Hroot Hlength Hactual Hinfer Hfs Hcs ltac:(lia) Hprint Herror Hroom Harena Hclasses Hhistory Hnames Hschemas Hmeaning
     ltac:(unfold arguments;apply RenameMemoControl.updated_same))
    as (built & id & Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfschema & Hflag & Htop & Hsafe).
   assert (HbuiltGood:ClassLookup.wellformed built).
   { apply (ClassLookup.transport (machine f) built);[|exact Hgood].
     exact (EffectFrame.observed_preserves arraydef_0__classes _ _ _ _ _ _
       (NativeBasicInvariant.Arrays.appendTheorem_ro arraydef_0__classes ltac:(repeat split;discriminate) ltac:(discriminate) _ _) Hrun). }
   pose proof (Htop HtopInitial) as HbuiltTop.
   exists (setMachine f built),(Protocol.OK (length (Protocol.history logical))),(SchemaInstanceCompletion.committed logical fs classes id).
   split;[apply generated_accepted;assumption|]. repeat first [assumption|split|reflexivity].
 - pose proof (SchemaInstanceCompletion.logical_rejected logical fs classes name root cert ids actual
     Hname Hroot Hactual Hfailure Hfs Hcs (SemanticFrames.arena_NoDup (machine f) fs Harena)) as Hstep.
   exists (setMachine f (ReplyNOExecution.reply_state (machine f))),Protocol.NO,(SchemaInstanceCompletion.prepared logical fs classes).
   split;[exact (generated_rejected f observations Hmeta Herror Hinvalid)|].
   split;[exact Hstep|]. split.
   + exact (ArenaFrame.storage_arena (machine f) _ _ (ArenaFrame.storage_output (machine f) _) Harena).
   + split;[exact Hclasses|]. split;[exact Hhistory|]. split;[exact Hnames|]. split;[exact Hschemas|].
     split;[exact Herror|]. split;[exact (Guarantees.step_safe logical _ _ _ Hstep)|].
     split;[exact Hgood|]. split;[exact HtopInitial|]. split;reflexivity.
Qed.
End Finish.
Module Ready.
Import SchemaInstanceGeneralReady.
Theorem generated (f:SchemaInstanceHandler.Frame) logical index offset size root flag name cert ids actual observations :
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
 resources (machine f) logical root actual ->
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
 (exists extra,Protocol.classes next=Protocol.classes logical++extra).
Proof.
 intros Hname Hproof Hlength Hactual Hwords Hvector Hbinding Hindex Hbindingraw Hcount Hmeta Hsip Hprint Herror Hvalid
   Hgrid Hhistoryroom Harena Hclasses Hhistory Hnames Hschemas Hgood Htop Hfalse (ceiling & index_ceiling & HceilingWord & HceilingStep & HindexWord & HindexStep & HinitialCapacity & HinitialBounds & Hscalar).
 pose proof (SchemaNodeMeaning.proof_lookup logical root cert Hproof) as Hlookup.
 destruct (SchemaMetadata.represented_lookup (machine f) (Protocol.expressions logical) root (Protocol.PE cert)
   (SchemaRepresentation.metadata _ _ Hschemas) Hlookup) as [raw [Hraw Hentry]].
 destruct raw as [[[[[[kind a] b] c] d] ty] arity].
 cbn [SchemaMetadata.entry SchemaMetadata.kind SchemaMetadata.arity] in Hentry.
 destruct Hentry as [Hty [Harity Hwidth]]. subst ty arity.
 assert (Hparameters:SchemaEvaluationGeneralBudget.parameters (machine f) root (machine f) (Protocol.classes logical) (substitution actual)).
 { eapply SchemaInstanceSetReady.parsed_parameters;[exact Hschemas|exact Hlookup|exact Hlength|exact Hactual|exact Hwords|exact Hvector]. }
 destruct (SchemaEvaluationIndexPractical.generated ceiling index_ceiling (machine f) (fun _=>false) (SchemaInstanceHandler.instance_arguments (Z.of_nat root))
   logical root cert (substitution actual) observations HceilingWord HceilingStep HindexWord HindexStep Hschemas Hlookup Hgrid
   ltac:(unfold SchemaInstanceHandler.instance_arguments;apply RenameMemoControl.updated_same)
   Harena Hclasses Hgood Htop Hfalse Hhistory Hnames Hmeta Hsip Herror Hvalid HinitialCapacity HinitialBounds Hparameters Hscalar)
  as (built & fs & classes & Hrun & HnextArena & HnextClasses & HnextHistory & HnextNames & HnextSchemas & HnextWords
    & HnextTop & HnextError & Hio & Hfs & Hcs & Hcapacity & Hbounds & Hsafe & Hresult).
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
Definition checked (f final:SchemaInstanceHandler.Frame) logical ids name observations reply next :=
 execLocalObserved SchemaInstanceHandler.suffix (f,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes reply;unreadInput:=stdin (machine f)|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) reply next /\
 NativeRepresentation.canonical_arena (machine final) (Protocol.formulas next) /\
 ClassStorage.represents (machine final) (Protocol.formulas next) (Protocol.classes next) /\
 HistoryRefinement.represents (machine final) next /\ NameRepresentation.represents (machine final) (Protocol.bindings next) /\
 SchemaRepresentation.represents (machine final) next /\ meta_value (machine final) 8=0 /\ Guarantees.safe next /\
 ClassLookup.wellformed (machine final) /\ FormulaTopology.ordered (machine final) (length (Protocol.formulas next)) /\
 (exists extra,Protocol.formulas next=Protocol.formulas logical++extra) /\
 (exists extra,Protocol.classes next=Protocol.classes logical++extra).
Lemma checked_rejected f final logical ids name observations :
 execLocalObserved SchemaInstanceHandler.suffix (f,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin (machine f)|}])) ->
 machine final=ReplyNOExecution.reply_state (machine f) ->
 (forall reply next,~Protocol.accepted logical (Protocol.Req 24 ids name) reply next) ->
 NativeRepresentation.canonical_arena (machine f) (Protocol.formulas logical) ->
 ClassStorage.represents (machine f) (Protocol.formulas logical) (Protocol.classes logical) ->
 HistoryRefinement.represents (machine f) logical -> NameRepresentation.represents (machine f) (Protocol.bindings logical) ->
 SchemaRepresentation.represents (machine f) logical -> meta_value (machine f) 8=0 -> Guarantees.safe logical ->
 ClassLookup.wellformed (machine f) -> FormulaTopology.ordered (machine f) (length (Protocol.formulas logical)) ->
 checked f final logical ids name observations Protocol.NO logical.
Proof.
 intros Hrun Hmachine Hreject Harena Hclasses Hhistory Hnames Hschemas Herror Hsafe Hgood Htop. unfold checked.
 split;[exact Hrun|]. split.
 - apply Protocol.step_reject;[exact Hreject|]. apply HistoryRefinement.retained_refl. exact (SemanticFrames.arena_NoDup _ _ Harena).
 - rewrite Hmachine. split.
   + exact (ArenaFrame.storage_arena (machine f) _ _ (ArenaFrame.storage_output (machine f) _) Harena).
   + split;[exact Hclasses|]. split;[exact Hhistory|]. split;[exact Hnames|]. split;[exact Hschemas|]. split;[exact Herror|]. split;[exact Hsafe|]. split;[exact Hgood|]. split;[exact Htop|].
     split;exists [];now rewrite app_nil_r.
Qed.
Theorem generated_suffix (f:SchemaInstanceHandler.Frame) logical ids name observations :
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
 Guarantees.safe logical -> resources (machine f) logical ids name ->
 exists final reply next,checked f final logical ids name observations reply next.
Proof.
 intros Hwords Hvector Houtcome Hbinding Hcount Hvalid Hmeta Hsip Hprint Herror Harena Hclasses Hhistory Hnames Hschemas Hgood Htop Hfalse Hsafe Hresources.
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
          destruct (Hresources root cert actual Hlookup Hproof Hlength Hactual) as [Hgrid [HhistoryRoom Hready]].
          destruct (Ready.generated f logical index offset size root flag name cert ids actual observations
            Hlookup Hproof Hlength Hactual Hwords Hvector HnativeBinding Hindex Hraw Hcount Hmeta Hsip Hprint Herror ltac:(lia)
            Hgrid HhistoryRoom Harena Hclasses Hhistory Hnames Hschemas Hgood Htop Hfalse Hready)
           as (final & reply & next & Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfs & Hflag & HnextSafe & HfinalGood & HfinalTop & HfinalFs & HfinalCs).
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
Theorem generated_handler (f:SchemaInstanceHandler.Frame) logical ids name tail observations :
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
 Guarantees.safe logical -> handler_resources f logical ids name tail ->
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
 (exists extra,Protocol.classes next=Protocol.classes logical++extra).
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
 assert (HparsedResources:resources (machine parsed) logical ids name).
 { apply (resources_transport (machine f));[apply Harrays;discriminate|apply Harrays;discriminate|exact Hresources]. }
 assert (HidWords:Forall (fun id=>word (Z.of_nat id)) ids).
 { clear -Hwords. induction Hwords as [|head rest Hhead Hrest IH].
   - constructor.
   - constructor;[unfold word;lia|exact IH]. }
 destruct (generated_suffix parsed logical ids name observations HidWords Hvector
   (SchemaInstancePrefix.finished_outcome f looked ids tail (Protocol.bindings logical) name Hlooked Houtcome)
   (SchemaInstancePrefix.finished_binding_result f looked ids tail Hlooked)
   (SchemaInstancePrefix.finished_count f looked ids tail) HvalidParsed
   ltac:(now rewrite Hlength) ltac:(now rewrite Harrays by discriminate) ltac:(now rewrite Harrays by discriminate)
   Hclear HparsedArena HparsedClasses HparsedHistory HparsedNames HparsedSchemas HparsedGood HparsedTop Hfalse Hsafe HparsedResources)
   as (final & reply & next & Hchecked).
 destruct Hchecked as (Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfs & Hflag & HnextSafe & HfinalGood & HfinalTop & HfinalFs & HfinalCs).
 exists final,reply,next. split.
 - rewrite SchemaInstancePrefix.actual_handler. fold parsed in Hprefix.
   etransitivity;[exact Hprefix|]. etransitivity;[exact Hrun|].
   unfold parsed. now rewrite Hin,Hout.
 - repeat first [assumption|split].
Qed.
End ProtocolInvariant.
Import SchemaInstanceCommand NativeSchemaInstanceBoundary.
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
 Guarantees.safe logical -> SchemaInstanceGeneralCommand.resources s logical ids name ->
 exists final reply next,
 execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) reply next /\
 NativeState.represents final next /\ meta_value final 8=0 /\ Guarantees.safe next /\ NativeCommandBoundary.io s final reply tail /\
 ClassLookup.wellformed final /\ FormulaTopology.ordered final (length (Protocol.formulas next)) /\
 (exists extra,Protocol.formulas next=Protocol.formulas logical++extra) /\
 (exists extra,Protocol.classes next=Protocol.classes logical++extra) /\ word (Z.of_nat (length (Protocol.formulas next))).
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
 assert (HhandlerResources:SchemaInstanceGeneralProtocol.handler_resources f logical ids name tail).
 { unfold SchemaInstanceGeneralProtocol.handler_resources.
   apply (SchemaInstanceGeneralProtocol.resources_transport s);[| |exact Hresources].
   all: unfold f,initial_frame,CommandDispatch.opcode_frame,op,opcode_state;cbn [machine setNum setMachine];apply CommandInput.parsed_other;discriminate. }
 destruct (ProtocolInvariant.generated_handler f logical ids name tail observations
   HopMeta HopToken HopSip HopPrint HopPending HopError Hname Hwords Hlength HopInput
   HopArena HopClasses HopHistory HopNames HopSchemas HopGood HopTop Hfalse Hsafe HhandlerResources)
 as (after & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hschemas & Hclear & HnextSafe & HfinalGood & HfinalTop & HfinalFs & HfinalCs).
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
       exact (SchemaEvaluationCell.arena_count_word _ _ Harena). }
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
End NativeSchemaGeneralInvariant.
