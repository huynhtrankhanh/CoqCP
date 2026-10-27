From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl SchemaInstanceHandler
 SchemaInstanceCompletion SchemaEvaluation ReplyNO ArenaFrame SemanticFrames Representation ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaInstanceFinish.
Import IndexExecution SipHashExecution ObservedLocal.
Definition arguments node : varsfuncdef_0__appendTheorem->Z := update (fun _=>0) vardef_0__appendTheorem_node node.
Lemma generated_rejected (f:SchemaInstanceHandler.Frame) observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 -> meta_value (machine f) 18=0 ->
 execLocalObserved SchemaInstanceHandler.after_evaluation (f,observations)=Some (tt,(setMachine f (ReplyNOExecution.reply_state (machine f)),
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin (machine f)|}])).
Proof.
 intros Hmeta Herror Hvalid. unfold SchemaInstanceHandler.after_evaluation.
 repeat first [progress cbn [optionBind fst snd bind]
  |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine];lia)
  |progress rewrite Herror|progress rewrite Hvalid
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |progress replace (Z.to_nat 18) with 18%nat by reflexivity
  |multimatch goal with |-context[bool_decide ?P]=>first
   [progress rewrite (bool_decide_true P) by congruence|progress rewrite (bool_decide_false P) by congruence] end
  |match goal with |-context[@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bs ?ns) (?current,?trace)]=>
    let expression:=constr:(@execObserved I T EI R (funcdef_0__no bs ns) (current,trace)) in
    let Hsame:=fresh in assert (Hsame:expression=Some (tt,(ReplyNOExecution.reply_state current,
      trace++[{|flushedOutput:=stdout current++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin current|}]))) by apply ReplyNOExecution.generated_no;
    rewrite Hsame;clear Hsame end].
 reflexivity.
Qed.
Lemma generated_accepted (f:SchemaInstanceHandler.Frame) final observations after :
 (18<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 -> meta_value (machine f) 18<>0 ->
 execObserved (funcdef_0__appendTheorem (fun _=>false) (arguments (meta_value (machine f) 0))) (machine f,observations)=Some (tt,(final,after)) ->
 execLocalObserved SchemaInstanceHandler.after_evaluation (f,observations)=Some (tt,(setMachine f final,after)).
Proof.
 intros Hmeta Herror Hvalid Happend. unfold SchemaInstanceHandler.after_evaluation.
 repeat first [progress cbn [optionBind fst snd bind]
  |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine];lia)
  |progress rewrite Herror
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |progress replace (Z.to_nat 18) with 18%nat by reflexivity
  |progress replace (Z.to_nat 0) with 0%nat by reflexivity
  |multimatch goal with |-context[bool_decide ?P]=>first
   [progress rewrite (bool_decide_true P) by congruence|progress rewrite (bool_decide_false P) by congruence] end
  |match goal with |-context[@execObserved ?I ?T ?EI ?R (funcdef_0__appendTheorem ?bs ?ns) ?state]=>
    let expression:=constr:(@execObserved I T EI R (funcdef_0__appendTheorem bs ns) state) in
    let Hsame:=fresh in assert (Hsame:expression=Some (tt,(final,after))) by exact Happend;rewrite Hsame;clear Hsame end].
 reflexivity.
Qed.
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
 (Guarantees.safe logical -> Guarantees.safe next).
Proof.
 intros Hname Hroot Hlength Hactual Hfs Hcs Hmeta Hprint Herror Hroom Harena Hclasses Hhistory Hnames Hschemas Hresult.
 destruct Hresult as [[p [Hinfer [Hmeaning Hvalid]]]|[Hfailure Hinvalid]].
 - destruct (SchemaInstanceCompletion.generated_accepted (machine f) logical fs classes (fun _=>false)
     (arguments (meta_value (machine f) 0)) name root cert ids actual p observations
     Hname Hroot Hlength Hactual Hinfer Hfs Hcs ltac:(lia) Hprint Herror Hroom Harena Hclasses Hhistory Hnames Hschemas Hmeaning
     ltac:(unfold arguments;apply RenameMemoControl.updated_same))
    as (built & id & Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfschema & Hflag & Htop & Hsafe).
   exists (setMachine f built),(Protocol.OK (length (Protocol.history logical))),(SchemaInstanceCompletion.committed logical fs classes id).
   split;[apply generated_accepted;assumption|]. repeat first [assumption|split].
 - pose proof (SchemaInstanceCompletion.logical_rejected logical fs classes name root cert ids actual
     Hname Hroot Hactual Hfailure Hfs Hcs (SemanticFrames.arena_NoDup (machine f) fs Harena)) as Hstep.
   exists (setMachine f (ReplyNOExecution.reply_state (machine f))),Protocol.NO,(SchemaInstanceCompletion.prepared logical fs classes).
   split;[exact (generated_rejected f observations Hmeta Herror Hinvalid)|].
   split;[exact Hstep|]. split.
   + exact (ArenaFrame.storage_arena (machine f) _ _ (ArenaFrame.storage_output (machine f) _) Harena).
   + split;[exact Hclasses|]. split;[exact Hhistory|]. split;[exact Hnames|]. split;[exact Hschemas|].
     split;[exact Herror|exact (Guarantees.step_safe logical _ _ _ Hstep)].
Qed.
End SchemaInstanceFinish.
