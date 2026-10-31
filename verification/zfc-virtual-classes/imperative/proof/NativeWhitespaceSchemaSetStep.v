From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeBasicSession NativeDialogueComposition NativeSetSchemaSession NativeSetBudgetPlan NativeUniformCommand NativeGeneralCommandInvariant NativeWhitespaceSchemaSetTransition NativeWhitespaceSchemaUniformCommand NativeWhitespaceSchemaFields NativeSchemaFieldBounds.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaSetStep.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaUniformCommand.
Theorem generated native logical fields name namespaces namesep countspaces countsep firstsep tail requests observations :
 NativeDialogueComposition.boundary native logical -> NativeSetSchemaSession.extra native logical ->
 NativeSetBudgetPlan.capacity logical (Protocol.Req 24 (map snd fields) name::requests) ->
 Protocol.shape(Protocol.Req 24 (map snd fields) name) -> meta_value native 15=51 ->
 Forall(fun item=>Forall TokenByteExecution.separator(fst item) /\ Z.of_nat(snd item)<=maximum)fields ->
 Forall TokenByteExecution.separator namespaces -> TokenByteExecution.separator namesep -> Forall TokenByteExecution.separator countspaces -> TokenByteExecution.separator countsep -> TokenByteExecution.separator firstsep ->
 stdin native=52::firstsep::payload name fields namespaces namesep countspaces countsep tail ->
 exists after reply next,
 execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(native,observations)=Some(tt,(after,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 (map snd fields) name) reply next /\ NativeDialogueComposition.boundary after next /\
 NativeSetSchemaSession.extra after next /\ NativeSetBudgetPlan.capacity next requests /\
 stdin after=tail /\ stdout after=stdout native++Protocol.reply_bytes reply.
Proof.
 intros Hboundary [Hextra [Hflat Hsets]] [caps [Hbounds Hcheck]] Hshape Hpending HfieldWords Hns Hnsep Hcs Hcsep Hfirstsep Hinput.
 destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning].
 destruct Hextra as [Hmeta Hsip Hsafe Htop Hfalse Hgood Hunique Hcompact].
 destruct(NativeSetBudgetPlan.check_tail caps (Protocol.Req 24 (map snd fields) name) requests ltac:(discriminate) Hcheck) as [Hconditions HtailCheck].
 destruct Hshape as [Hwords [Hname Hlength]]. cbn [Protocol.arguments Protocol.object_name] in Hname,Hlength.
 assert(HfieldLength:Z.of_nat(length fields)<=maximum) by (rewrite <- (length_map snd fields);exact Hlength).
 destruct(NativeWhitespaceSchemaSetTransition.generated caps native (fun _=>false)(fun _=>0) logical fields name namespaces namesep countspaces countsep firstsep tail observations
  Hmeta Htoken Hsip Hprint Hpending Herror Hname HfieldWords HfieldLength Hns Hnsep Hcs Hcsep Hfirstsep Hinput Hstate Hgood Htop Hfalse Hsafe Hunique Hcompact Hflat Hsets Hbounds Hconditions)
 as(after & reply & next & Hrun & Hstep & HnextState & Hio & Hpost & Hquantitative & HnextFlat & HnextSets).
 destruct Hpost as(HnextSafe & HnextTop & HnextGood & HnextCompact & HnextUnique & HnextFalse & HmetaLength & HsipLength & HnextMeta & HnextSip & Hextends & HregistryCounts).
 assert(Hshape':Protocol.shape(Protocol.Req 24 (map snd fields) name)) by (split;[exact Hwords|split;assumption]).
 pose proof(NativeSetBudgetPlan.capacity_next logical (Protocol.Req 24 (map snd fields) name) requests reply next caps Hshape' ltac:(discriminate) Hstep Hbounds Hcheck Hquantitative) as HnextCapacity.
 destruct Hio as(Hin & Hout & HnextToken & HnextPrint & Hclear & Hstop).
 exists after,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - constructor;try assumption. now rewrite Hstop,Hrunning.
 - split;[split;[constructor;assumption|split;assumption]|]. repeat first [assumption|split].
Qed.
End NativeWhitespaceSchemaSetStep.
