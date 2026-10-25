From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal SchemaEvaluation AppendTheorem HistoryStorage HistoryRefinement
 NameRepresentation SchemaRepresentation Representation ClassStorage ClassLookup FormulaTopology HashTable SemanticFrames ReplyOK ReplyNO ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaInstanceCompletion.
Import IndexExecution SipHashExecution ObservedLocal.
Definition prepared logical fs classes := Protocol.State fs classes (Protocol.history logical) (Protocol.bindings logical) (Protocol.expressions logical).
Definition committed logical fs classes id := Protocol.with_history (prepared logical fs classes) (Protocol.history logical++[id]).
Lemma request logical name root cert ids actual p :
 Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.schema_binding root) ->
 Protocol.pf logical root=Some cert -> length ids=Schemata.proof_arity cert ->
 Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual ->
 Schemata.infer (fun i=>List.nth i actual (VirtualClasses.set 0)) 0 cert=Some p ->
 Protocol.proof_request logical (Protocol.Req 24 ids name) p.
Proof. intros. eapply Protocol.req_instance;eassumption. Qed.
Lemma logical_accepted logical fs classes name root cert ids actual p id :
 Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.schema_binding root) ->
 Protocol.pf logical root=Some cert -> length ids=Schemata.proof_arity cert ->
 Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual ->
 Schemata.infer (fun i=>List.nth i actual (VirtualClasses.set 0)) 0 cert=Some p ->
 (exists extra,fs=Protocol.formulas logical++extra) -> (exists extra,classes=Protocol.classes logical++extra) ->
 NoDup fs -> nth_error fs id=Some p ->
 Protocol.step logical (Protocol.Req 24 ids name) (Protocol.OK (length (Protocol.history logical))) (committed logical fs classes id).
Proof.
 intros Hname Hroot Hlength Hactual Hinfer Hfs Hclasses Hunique Hid.
 eapply Protocol.step_accept with (t:=committed logical fs classes id).
 - unfold committed,prepared. cbn [Protocol.with_history Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
   apply (Protocol.accept_proof logical (Protocol.Req 24 ids name) p fs classes id).
   + exact (request logical name root cert ids actual p Hname Hroot Hlength Hactual Hinfer).
   + repeat first [assumption|split].
 - now apply HistoryRefinement.retained_refl.
Qed.
Lemma result_names s n value bindings : NameRepresentation.represents s bindings -> NameRepresentation.represents (HistoryStorage.result s n value) bindings.
Proof.
 unfold NameRepresentation.represents. rewrite !HistoryStorage.result_meta_other by lia.
 rewrite !HistoryStorage.result_other by discriminate. trivial.
Qed.
Lemma result_schemas s n value logical : SchemaRepresentation.represents s logical -> SchemaRepresentation.represents (HistoryStorage.result s n value) logical.
Proof.
 intro Hrep. eapply SchemaRepresentation.transport;[exact Hrep| | |reflexivity|reflexivity|reflexivity].
 - now apply HistoryStorage.result_meta_other.
 - apply HistoryStorage.result_other;discriminate.
Qed.
Lemma result_topology s n value count : FormulaTopology.ordered s count -> FormulaTopology.ordered (HistoryStorage.result s n value) count.
Proof.
 intro Htop. apply (FormulaTopology.same s);[exact Htop|]. intros parent Hparent.
 unfold HashTableInvariant.tuple_at. now rewrite HistoryStorage.result_other by discriminate.
Qed.
Lemma result_wellformed s n value : ClassLookup.wellformed s -> ClassLookup.wellformed (HistoryStorage.result s n value).
Proof. apply ClassLookup.transport. apply HistoryStorage.result_other;discriminate. Qed.
Lemma result_lengths s n value watched : watched<>arraydef_0__theorems ->
 length (memory (HistoryStorage.result s n value) watched)=length (memory s watched).
Proof.
 intro Hhistory. destruct (decide (watched=arraydef_0__meta)) as [->|Hmeta].
 - apply HistoryStorage.result_meta_length.
 - destruct (decide (watched=arraydef_0__printBuffer)) as [->|Hbuffer].
   + unfold HistoryStorage.result. rewrite store_meta_other by discriminate.
     rewrite ReplyOKExecution.reply_buffer_length,HistoryStorage.written_other by discriminate. reflexivity.
   + now rewrite HistoryStorage.result_other.
Qed.
Lemma result_input s n value : stdin (HistoryStorage.result s n value)=stdin s.
Proof. unfold HistoryStorage.result. cbn [stdin store_meta withMemory]. rewrite ReplyOKExecution.reply_input. reflexivity. Qed.
Lemma result_output s n value : stdout (HistoryStorage.result s n value)=stdout s++Protocol.reply_bytes (Protocol.OK n).
Proof. unfold HistoryStorage.result. cbn [stdout store_meta withMemory]. rewrite ReplyOKExecution.reply_output. reflexivity. Qed.
Theorem generated_accepted s logical fs classes bs ns name root cert ids actual p observations :
 Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.schema_binding root) ->
 Protocol.pf logical root=Some cert -> length ids=Schemata.proof_arity cert ->
 Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual ->
 Schemata.infer (fun i=>List.nth i actual (VirtualClasses.set 0)) 0 cert=Some p ->
 (exists extra,fs=Protocol.formulas logical++extra) -> (exists extra,classes=Protocol.classes logical++extra) ->
 (8<length (memory s arraydef_0__meta))%nat -> (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 8=0 -> Z.of_nat (length (Protocol.history logical))<maximum ->
 NativeRepresentation.canonical_arena s fs -> ClassStorage.represents s fs classes ->
 HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
 SchemaRepresentation.represents s (prepared logical fs classes) ->
 SchemaEvaluation.formula_value fs (meta_value s 0) p ->
 ns vardef_0__appendTheorem_node=meta_value s 0 ->
 exists final id,
 execObserved (funcdef_0__appendTheorem bs ns) (s,observations)=Some (tt,(final,
   observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)));unreadInput:=stdin s|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) (Protocol.OK (length (Protocol.history logical))) (committed logical fs classes id) /\
 NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs classes /\
 HistoryRefinement.represents final (committed logical fs classes id) /\
 NameRepresentation.represents final (Protocol.bindings logical) /\ SchemaRepresentation.represents final (committed logical fs classes id) /\
 meta_value final 8=0 /\
 (FormulaTopology.ordered s (length fs) -> FormulaTopology.ordered final (length fs)) /\
 (Guarantees.safe logical -> Guarantees.safe (committed logical fs classes id)).
Proof.
 intros Hname Hroot Hlength Hactual Hinfer Hfs Hclasses Hmeta Hbuffer Herror Hroom Harena Hclassrep Hhistory Hnames Hschemas [Hidword Hid] Hargument.
 set (id:=Z.to_nat (meta_value s 0)).
 assert (Hnatural:meta_value s 0=Z.of_nat id) by (unfold id;rewrite Z2Nat.id by exact (proj1 Hidword);reflexivity).
 assert (Hstep:Protocol.step logical (Protocol.Req 24 ids name) (Protocol.OK (length (Protocol.history logical))) (committed logical fs classes id)).
 { eapply logical_accepted;try eassumption. exact (SemanticFrames.arena_NoDup s fs Harena). }
 exists (HistoryStorage.result s (length (Protocol.history logical)) (meta_value s 0)),id. split.
 - apply AppendTheoremExecution.generated_append;try assumption. exact (proj1 Hhistory).
 - split;[exact Hstep|]. split;[now apply HistoryStorage.result_arena|]. split;[now apply HistoryStorage.result_classes|]. split.
   + rewrite Hnatural. apply (HistoryStorage.append_represents s (prepared logical fs classes) id ltac:(lia) Hhistory).
   + split;[now apply result_names|]. split.
     * eapply SchemaRepresentation.transport;[apply result_schemas;exact Hschemas|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity].
     * split;[now rewrite HistoryStorage.result_meta_other by lia|]. split.
       -- apply result_topology.
       -- exact (Guarantees.step_safe logical _ _ _ Hstep).
Qed.
Lemma actual_unique logical ids left right :
 Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids left ->
 Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids right -> left=right.
Proof.
 intros Hleft. induction Hleft as [|id cls ids rest Hclass Hrest IH] in right|-*.
 - intro Hright. inversion Hright. reflexivity.
 - intro Hright. inversion Hright as [|id' cls' ids' rest' Hhead Htail];subst.
   f_equal;[congruence|now apply IH].
Qed.
Lemma accepted_impossible logical name root cert ids actual :
 Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.schema_binding root) ->
 Protocol.pf logical root=Some cert ->
 Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual ->
 Schemata.infer (fun i=>List.nth i actual (VirtualClasses.set 0)) 0 cert=None ->
 forall reply next,~Protocol.accepted logical (Protocol.Req 24 ids name) reply next.
Proof.
 intros Hname Hroot Hactual Hfailure reply next Haccepted.
 inversion Haccepted;subst;
   first [match goal with H:Protocol.formula_request _ _ _ |- _=>inversion H end
         |match goal with H:Protocol.proof_request _ _ _ |- _=>inversion H;subst end].
 match goal with Hsome:Schemata.infer (fun i=>List.nth i ?otherActual (VirtualClasses.set 0)) 0 ?otherCert=Some _ |- _=>
  assert (HsameActual:otherActual=actual) by (eapply actual_unique;eassumption);
  assert (HsameCert:otherCert=cert) by congruence;
  rewrite HsameActual,HsameCert in Hsome;congruence end.
Qed.
Lemma logical_rejected logical fs classes name root cert ids actual :
 Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.schema_binding root) ->
 Protocol.pf logical root=Some cert ->
 Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual ->
 Schemata.infer (fun i=>List.nth i actual (VirtualClasses.set 0)) 0 cert=None ->
 (exists extra,fs=Protocol.formulas logical++extra) -> (exists extra,classes=Protocol.classes logical++extra) -> NoDup fs ->
 Protocol.step logical (Protocol.Req 24 ids name) Protocol.NO (prepared logical fs classes).
Proof.
 intros Hname Hroot Hactual Hfailure Hfs Hclasses Hunique. apply Protocol.step_reject.
 - exact (accepted_impossible logical name root cert ids actual Hname Hroot Hactual Hfailure).
 - unfold Protocol.retained_storage,prepared. cbn [Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
   repeat first [assumption|reflexivity|split].
Qed.
Theorem generated_rejected s logical fs classes bs ns name root cert ids actual observations :
 Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.schema_binding root) ->
 Protocol.pf logical root=Some cert ->
 Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual ->
 Schemata.infer (fun i=>List.nth i actual (VirtualClasses.set 0)) 0 cert=None ->
 (exists extra,fs=Protocol.formulas logical++extra) -> (exists extra,classes=Protocol.classes logical++extra) ->
 NativeRepresentation.canonical_arena s fs -> ClassStorage.represents s fs classes ->
 HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
 SchemaRepresentation.represents s (prepared logical fs classes) -> meta_value s 8=0 ->
 exists final,
 execObserved (funcdef_0__no bs ns) (s,observations)=Some (tt,(final,
   observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin s|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) Protocol.NO (prepared logical fs classes) /\
 NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs classes /\
 HistoryRefinement.represents final (prepared logical fs classes) /\ NameRepresentation.represents final (Protocol.bindings logical) /\
 SchemaRepresentation.represents final (prepared logical fs classes) /\ meta_value final 8=0 /\
 (FormulaTopology.ordered s (length fs) -> FormulaTopology.ordered final (length fs)) /\
 (Guarantees.safe logical -> Guarantees.safe (prepared logical fs classes)).
Proof.
 intros Hname Hroot Hactual Hfailure Hfs Hclasses Harena Hclassrep Hhistory Hnames Hschemas Herror.
 pose proof (logical_rejected logical fs classes name root cert ids actual Hname Hroot Hactual Hfailure Hfs Hclasses
   (SemanticFrames.arena_NoDup s fs Harena)) as Hstep.
 exists (ReplyNOExecution.reply_state s). split;[apply ReplyNOExecution.generated_no|]. split;[exact Hstep|].
 split;[exact (ArenaFrame.storage_arena s _ _ (ArenaFrame.storage_output s _) Harena)|]. split;[exact Hclassrep|]. split;[exact Hhistory|]. split;[exact Hnames|].
 split;[exact Hschemas|]. split;[exact Herror|]. split;[tauto|exact (Guarantees.step_safe logical _ _ _ Hstep)].
Qed.
End SchemaInstanceCompletion.
