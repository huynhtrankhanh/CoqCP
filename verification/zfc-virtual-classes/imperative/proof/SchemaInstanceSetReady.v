From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal RenameMemoControl SchemaInstanceHandler SchemaInstanceEntry SchemaEvaluationSetEntry SchemaEvaluationSetRun SchemaEvaluationSetCell SchemaEvaluationGeneralBudget SchemaEvaluationArguments SchemaEvaluationDependencies
 SchemaInstanceFinish SchemaInstanceLengths SchemaInstanceCompletion SchemaNodeMeaning SchemaMetadata SchemaMarking
 SchemaRepresentation SchemaEvaluation Representation ClassStorage ClassLookup FormulaTopology HistoryRefinement NameRepresentation InternalIO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaInstanceSetReady.
Import IndexExecution SipHashExecution ObservedLocal.
Definition substitution actual := fun index=>List.nth index actual (VirtualClasses.set 0).
(** Inspectable finite mathematical constraints, with no fits predicate or
    successful helper execution premise. *)
Definition resources s logical root (actual:list VirtualClasses.class) :=
 SchemaEvaluationSetRun.fragment s root /\
 SchemaEvaluationSetCell.sets (Protocol.classes logical) /\
 Z.of_nat (length (Protocol.formulas logical)+42*SchemaMarking.size root)<=SchemaEvaluationSetCell.bound.
Lemma encoded_meta_lookup native logical node a b c d expression :
 SchemaRepresentation.represents native logical ->
 nth_error (memory native arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode 0 a b c d expression) ->
 nth_error (Protocol.expressions logical) node=Some (Protocol.CE (Schemata.metavariable a)).
Proof.
 intros Hschemas Hraw.
 assert (Hbound:(node<length (Protocol.expressions logical))%nat).
 { rewrite <-(SchemaMetadata.represents_length _ _ (SchemaRepresentation.metadata _ _ Hschemas)). apply nth_error_Some;congruence. }
 destruct (nth_error (Protocol.expressions logical) node) as [actualExpression|] eqn:Hlookup;
 [|apply nth_error_None in Hlookup;lia].
 pose proof (proj2 Hschemas node _ actualExpression Hraw Hlookup) as Hentry.
 destruct Hentry as (kind & aa & bb & cc & dd & Hencode & Hfit & Hdenotes).
 assert (Hfields:kind=0%nat /\ aa=a /\ bb=b /\ cc=c /\ dd=d).
 { unfold SchemaRepresentation.encode in Hencode. injection Hencode;lia. }
 destruct Hfields as [-> [-> [-> [-> ->]]]].
 destruct Hdenotes as [[HnotSaved Hbuild]|(p & checked & Hbad & Hrest)];[|discriminate].
 inversion Hbuild;subst. reflexivity.
Qed.
Theorem parsed_parameters native logical root cert ids actual :
 SchemaRepresentation.represents native logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE cert) ->
 length ids=Schemata.proof_arity cert -> Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual ->
 Forall (fun id=>word (Z.of_nat id)) ids -> SchemaEvaluationArguments.represents native ids ->
 SchemaEvaluationGeneralBudget.parameters native root native (Protocol.classes logical) (substitution actual).
Proof.
 intros Hschemas Hroot Hlength Hactual Hwords Hvector node depth a b c d expression Hreachable Hraw.
 assert (Hlookup:nth_error (Protocol.expressions logical) node=Some (Protocol.CE (Schemata.metavariable a)))
   by (eapply encoded_meta_lookup;eassumption).
 pose proof (SchemaEvaluationArguments.reachable_argument native native logical root cert node depth a ids actual []
   Hschemas Hroot Hreachable Hlookup Hlength Hactual Hwords Hvector) as Hargument.
 now rewrite app_nil_r in Hargument.
Qed.
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
 (Guarantees.safe logical -> Guarantees.safe next).
Proof.
 intros Hname Hproof Hlength Hactual Hwords Hvector Hbinding Hindex Hbindingraw Hcount Hmeta Hsip Hprint Herror Hvalid
   Hgrid Hhistoryroom Harena Hclasses Hhistory Hnames Hschemas Hgood Htop Hfalse [Hfragment [Hsets Hbudget]].
 pose proof (SchemaNodeMeaning.proof_lookup logical root cert Hproof) as Hlookup.
 destruct (SchemaMetadata.represented_lookup (machine f) (Protocol.expressions logical) root (Protocol.PE cert)
   (SchemaRepresentation.metadata _ _ Hschemas) Hlookup) as [raw [Hraw Hentry]].
 destruct raw as [[[[[[kind a] b] c] d] ty] arity].
 cbn [SchemaMetadata.entry SchemaMetadata.kind SchemaMetadata.arity] in Hentry.
 destruct Hentry as [Hty [Harity Hwidth]]. subst ty arity.
 assert (Hparameters:SchemaEvaluationGeneralBudget.parameters (machine f) root (machine f) (Protocol.classes logical) (substitution actual)).
 { eapply parsed_parameters;[exact Hschemas|exact Hlookup|exact Hlength|exact Hactual|exact Hwords|exact Hvector]. }
 destruct (SchemaEvaluationSetEntry.generated (machine f) (fun _=>false) (SchemaInstanceHandler.instance_arguments (Z.of_nat root))
   logical root cert (substitution actual) observations Hschemas Hlookup Hfragment Hsets Hparameters Hbudget
   ltac:(unfold SchemaInstanceHandler.instance_arguments;apply RenameMemoControl.updated_same)
   Harena Hclasses Hgood Htop Hfalse Hhistory Hnames Hmeta Hsip Herror Hvalid)
  as (built & fs & classes & Hrun & HnextArena & HnextClasses & HnextHistory & HnextNames & HnextSchemas & HnextWords
    & HnextTop & HnextError & Hio & Hfs & Hcs & Hsafe & Hresult).
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
 destruct (SchemaInstanceFinish.generated_verified middle logical fs classes name root cert ids actual observations
   Hname Hproof Hlength Hactual Hfs Hcs HnextMeta HnextPrint HnextError Hhistoryroom
   HnextArena HnextClasses HnextHistory HnextNames HnextSchemas Hchecked)
  as (final & reply & next & Hfinish & Hstep & Hfa & Hfc & Hfh & Hfn & Hfschema & Hflag & HnextSafe).
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
Qed.
End SchemaInstanceSetReady.
