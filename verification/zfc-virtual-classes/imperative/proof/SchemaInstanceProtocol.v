From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal TypedNameLookup NameRepresentation SchemaInstanceHandler SchemaInstanceReady
 SchemaInstanceCompletion SchemaInstancePrefix SchemaInstanceArguments CommandChain ReadName ReadToken NameSearch HashTable SchemaNodeMeaning SchemaMetadata SchemaMarking SchemaRepresentation Representation ClassStorage ClassLookup
 FormulaTopology HistoryRefinement SemanticFrames ReplyNO ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaInstanceProtocol.
Import IndexExecution SipHashExecution ObservedLocal.
Lemma accepted_requirements logical ids name reply next : Protocol.accepted logical (Protocol.Req 24 ids name) reply next ->
 exists root cert actual p,Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.schema_binding root) /\
 Protocol.pf logical root=Some cert /\ length ids=Schemata.proof_arity cert /\
 Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual /\
 Schemata.infer (fun i=>List.nth i actual (VirtualClasses.set 0)) 0 cert=Some p.
Proof.
 intro Haccepted. inversion Haccepted;subst;
 first [match goal with H:Protocol.formula_request _ _ _ |- _=>inversion H end|
 match goal with H:Protocol.proof_request _ _ _ |- _=>inversion H;subst end].
 match goal with
 | Hname:Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.schema_binding ?root),
   Hroot:Protocol.pf logical ?root=Some ?cert,
   Hactual:Forall2 _ ids ?actual,
   Hinfer:Schemata.infer _ 0 ?cert=Some ?p |- _=>exists root,cert,actual,p
 end.
 repeat first [assumption|split].
Qed.
Lemma rejected_name logical ids name :
 (forall root,Protocol.lookup name (Protocol.bindings logical)<>Some (Protocol.schema_binding root)) ->
 forall reply next,~Protocol.accepted logical (Protocol.Req 24 ids name) reply next.
Proof.
 intros Hname reply next Haccepted. destruct (accepted_requirements _ _ _ _ _ Haccepted) as (root & cert & actual & p & Hlookup & Hrest).
 exact (Hname root Hlookup).
Qed.
Lemma rejected_arity logical ids name root cert :
 Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.schema_binding root) -> Protocol.pf logical root=Some cert ->
 length ids<>Schemata.proof_arity cert -> forall reply next,~Protocol.accepted logical (Protocol.Req 24 ids name) reply next.
Proof.
 intros Hname Hroot Hlength reply next Haccepted.
 destruct (accepted_requirements _ _ _ _ _ Haccepted) as (otherRoot & otherCert & actual & p & Hlookup & Hproof & Hsize & Hrest).
 assert (otherRoot=root) by congruence. subst otherRoot. assert (otherCert=cert) by congruence. subst otherCert. contradiction.
Qed.
Lemma rejected_arguments logical ids name :
 (~exists actual,Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual) ->
 forall reply next,~Protocol.accepted logical (Protocol.Req 24 ids name) reply next.
Proof.
 intros Harguments reply next Haccepted.
 destruct (accepted_requirements _ _ _ _ _ Haccepted) as (root & cert & actual & p & Hlookup & Hproof & Hsize & Hactual & Hinfer).
 apply Harguments. now exists actual.
Qed.
Definition checked (f final:SchemaInstanceHandler.Frame) logical ids name observations reply next :=
 execLocalObserved SchemaInstanceHandler.suffix (f,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes reply;unreadInput:=stdin (machine f)|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) reply next /\
 NativeRepresentation.canonical_arena (machine final) (Protocol.formulas next) /\
 ClassStorage.represents (machine final) (Protocol.formulas next) (Protocol.classes next) /\
 HistoryRefinement.represents (machine final) next /\ NameRepresentation.represents (machine final) (Protocol.bindings next) /\
 SchemaRepresentation.represents (machine final) next /\ meta_value (machine final) 8=0 /\ Guarantees.safe next.
Lemma checked_rejected f final logical ids name observations :
 execLocalObserved SchemaInstanceHandler.suffix (f,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin (machine f)|}])) ->
 machine final=ReplyNOExecution.reply_state (machine f) ->
 (forall reply next,~Protocol.accepted logical (Protocol.Req 24 ids name) reply next) ->
 NativeRepresentation.canonical_arena (machine f) (Protocol.formulas logical) ->
 ClassStorage.represents (machine f) (Protocol.formulas logical) (Protocol.classes logical) ->
 HistoryRefinement.represents (machine f) logical -> NameRepresentation.represents (machine f) (Protocol.bindings logical) ->
 SchemaRepresentation.represents (machine f) logical -> meta_value (machine f) 8=0 -> Guarantees.safe logical ->
 checked f final logical ids name observations Protocol.NO logical.
Proof.
 intros Hrun Hmachine Hreject Harena Hclasses Hhistory Hnames Hschemas Herror Hsafe. unfold checked.
 split;[exact Hrun|]. split.
 - apply Protocol.step_reject;[exact Hreject|]. apply HistoryRefinement.retained_refl. exact (SemanticFrames.arena_NoDup _ _ Harena).
 - rewrite Hmachine. split.
   + exact (ArenaFrame.storage_arena (machine f) _ _ (ArenaFrame.storage_output (machine f) _) Harena).
   + split;[exact Hclasses|]. split;[exact Hhistory|]. split;[exact Hnames|]. split;[exact Hschemas|]. split;assumption.
Qed.
Definition resources native logical ids name := forall root cert actual,
 Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.schema_binding root) -> Protocol.pf logical root=Some cert ->
 length ids=Schemata.proof_arity cert -> Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual ->
 Z.of_nat (SchemaMarking.size root)<=maximum /\ Z.of_nat (length (Protocol.history logical))<maximum /\
 SchemaInstanceReady.resources native logical root actual.
Lemma outcome_found native logical name meaning :
 Protocol.lookup name (Protocol.bindings logical)=Some meaning -> TypedNameLookup.outcome native (Protocol.bindings logical) name ->
 exists index offset size flag,
 meta_value native 0=Z.of_nat index /\ Z.of_nat index<maximum /\
 nth_error (memory native arraydef_0__bindings) index=
   Some (offset,size,Z.of_nat (TypedNameLookup.binding_value meaning),flag,TypedNameLookup.binding_kind meaning).
Proof.
 intros Hlookup Houtcome. unfold TypedNameLookup.outcome in Houtcome. rewrite Hlookup in Houtcome.
 destruct Houtcome as (index & raw & Hresult & Hword & Hbound & Hnth & Hentry).
 destruct raw as [[[[offset size] value] flag] kind].
 destruct Hentry as (Hsize & Hoffset & Hspan & Hvalue & Hflag & Hbytes & HnameBytes & Hdecode & HnameValid).
 pose proof (TypedNameLookup.decode_kind value flag kind meaning Hdecode) as Hkind.
 pose proof (TypedNameLookup.decode_value value flag kind meaning Hvalue Hdecode) as Hvalue'.
 exists index,offset,size,flag. split;[exact Hresult|]. split;[lia|].
 destruct (nth_error (memory native arraydef_0__bindings) index) as [found|] eqn:Hfound;
 [|apply nth_error_None in Hfound;lia].
 pose proof (List.nth_error_nth _ _ (0,0,0,0,0) Hfound) as Hsame.
 assert (HfoundEqual:found=(offset,size,value,flag,kind)) by exact (eq_trans (eq_sym Hsame) Hnth).
 now rewrite HfoundEqual,Hvalue',Hkind.
Qed.
Theorem generated_suffix (f:SchemaInstanceHandler.Frame) logical ids name observations :
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
 intros Houtcome Hbinding Hcount Hvalid Hmeta Hsip Hprint Herror Harena Hclasses Hhistory Hnames Hschemas Hgood Htop Hfalse Hsafe Hresources.
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
          destruct (SchemaInstanceReady.generated f logical index offset size root flag name cert ids actual observations
            Hlookup Hproof Hlength Hactual HnativeBinding Hindex Hraw Hcount Hmeta Hsip Hprint Herror ltac:(lia)
            Hgrid HhistoryRoom Harena Hclasses Hhistory Hnames Hschemas Hgood Htop Hfalse Hready)
           as (final & reply & next & Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfs & Hflag & HnextSafe).
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
Definition handler_resources (f:SchemaInstanceHandler.Frame) logical ids name tail := forall looked,
 NameSearchExecution.storage_frame (SchemaInstancePrefix.named f name ids tail) looked ->
 TypedNameLookup.outcome looked (Protocol.bindings logical) name ->
 length (memory looked arraydef_0__meta)=length (memory (SchemaInstancePrefix.named f name ids tail) arraydef_0__meta) ->
 resources (machine (SchemaInstancePrefix.finished f looked ids tail)) logical ids name.
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
 SchemaRepresentation.represents (machine final) next /\ meta_value (machine final) 8=0 /\ Guarantees.safe next.
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
 { exact (Hresources looked HlookupFrame Houtcome HlookLength). }
 destruct (generated_suffix parsed logical ids name observations
   (SchemaInstancePrefix.finished_outcome f looked ids tail (Protocol.bindings logical) name Hlooked Houtcome)
   (SchemaInstancePrefix.finished_binding_result f looked ids tail Hlooked)
   (SchemaInstancePrefix.finished_count f looked ids tail) HvalidParsed
   ltac:(now rewrite Hlength) ltac:(now rewrite Harrays by discriminate) ltac:(now rewrite Harrays by discriminate)
   Hclear HparsedArena HparsedClasses HparsedHistory HparsedNames HparsedSchemas HparsedGood HparsedTop Hfalse Hsafe HparsedResources)
   as (final & reply & next & Hchecked).
 destruct Hchecked as (Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfs & Hflag & HnextSafe).
 exists final,reply,next. split.
 - rewrite SchemaInstancePrefix.actual_handler. fold parsed in Hprefix.
   etransitivity;[exact Hprefix|]. etransitivity;[exact Hrun|].
   unfold parsed. now rewrite Hin,Hout.
 - repeat first [assumption|split].
Qed.
End SchemaInstanceProtocol.
