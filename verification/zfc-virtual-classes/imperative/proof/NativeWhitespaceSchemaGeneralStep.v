From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeBasicSession NativeDialogueComposition NativeGeneralSession NativeBudgetPlan NativeUniformCommand NativeGeneralCommandInvariant NativeWhitespaceSchemaUniformTransition NativeWhitespaceSchemaUniformCommand NativeWhitespaceSchemaFields NativeSchemaFieldBounds.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaGeneralStep.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaUniformCommand.
Theorem generated argument_cap native logical fields name namespaces namesep countspaces countsep firstsep tail requests observations :
 NativeDialogueComposition.boundary native logical -> NativeGeneralSession.extra argument_cap native logical ->
 NativeBudgetPlan.capacity argument_cap logical (Protocol.Req 24 (map snd fields) name::requests) ->
 Protocol.shape(Protocol.Req 24 (map snd fields) name) -> meta_value native 15=51 ->
 Forall(fun item=>Forall TokenByteExecution.separator(fst item) /\ Z.of_nat(snd item)<=maximum)fields ->
 Forall TokenByteExecution.separator namespaces -> TokenByteExecution.separator namesep -> Forall TokenByteExecution.separator countspaces -> TokenByteExecution.separator countsep -> TokenByteExecution.separator firstsep ->
 stdin native=52::firstsep::payload name fields namespaces namesep countspaces countsep tail ->
 exists after reply next,
 execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(native,observations)=Some(tt,(after,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 (map snd fields) name) reply next /\ NativeDialogueComposition.boundary after next /\
 NativeGeneralSession.extra argument_cap after next /\ NativeBudgetPlan.capacity argument_cap next requests /\
 stdin after=tail /\ stdout after=stdout native++Protocol.reply_bytes reply.
Proof.
 intros Hboundary [Hextra Hfields] [caps [Hbounds Hcheck]] Hshape Hpending HfieldWords Hns Hnsep Hcs Hcsep Hfirstsep Hinput.
 destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning].
 destruct Hextra as [Hmeta Hsip Hsafe Htop Hfalse Hgood Hunique Hcompact].
 destruct(NativeBudgetPlan.check_tail argument_cap caps (Protocol.Req 24 (map snd fields) name) requests ltac:(discriminate) Hcheck) as [Hconditions HtailCheck].
 pose proof(NativeBudgetPlan.arithmetic native logical argument_cap caps (Protocol.Req 24 (map snd fields) name) Hstate Hfields Hbounds Hconditions) as Harithmetic.
 destruct Harithmetic as [HF HC HE Hbounded Hargs HindexWord Hinstance].
 destruct Hshape as [Hwords [Hname Hlength]]. cbn [Protocol.arguments Protocol.object_name] in Hname,Hlength.
 assert(HfieldLength:Z.of_nat(length fields)<=maximum) by (rewrite <- (length_map snd fields);exact Hlength).
 destruct(NativeWhitespaceSchemaUniformTransition.generated (NativeBudgetPlan.expressions caps) argument_cap (NativeBudgetPlan.formulas caps) (NativeBudgetPlan.indices caps) (NativeBudgetPlan.classes caps)
  native (fun _=>false)(fun _=>0) logical fields name namespaces namesep countspaces countsep firstsep tail observations
  Hmeta Htoken Hsip Hprint Hpending Herror Hname HfieldWords HfieldLength Hns Hnsep Hcs Hcsep Hfirstsep Hinput Hstate Hgood Htop Hfalse Hsafe Hunique Hcompact (Hinstance eq_refl))
 as(after & reply & next & Hrun & Hstep & HnextState & Hio & Hpost & Hquantitative).
 destruct Hpost as(HnextSafe & HnextTop & HnextGood & HnextCompact & HnextUnique & HnextFalse & HmetaLength & HsipLength & HnextMeta & HnextSip & Hextends & HregistryCounts).
 assert(HnextFields:NativeSchemaFieldBounds.fields after argument_cap).
 { eapply (NativeWhitespaceSchemaFields.preserves native (fun _=>false) (fun _=>0) firstsep (payload name fields namespaces namesep countspaces countsep tail) observations after _ argument_cap);[lia|exact Htoken|exact Hpending|exact Herror|exact Hfirstsep|exact Hinput|exact Hfields|exact Hrun]. }
 assert(Hshape':Protocol.shape(Protocol.Req 24 (map snd fields) name)) by (split;[exact Hwords|split;assumption]).
 pose proof(NativeBudgetPlan.capacity_next after logical (Protocol.Req 24 (map snd fields) name) requests reply next argument_cap caps Hshape' ltac:(discriminate) Hstep HnextState HnextTop Hbounds Hcheck Hquantitative) as HnextCapacity.
 destruct Hio as(Hin & Hout & HnextToken & HnextPrint & Hclear & Hstop).
 exists after,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - constructor;try assumption. now rewrite Hstop,Hrunning.
 - split;[split;[constructor;assumption|exact HnextFields]|]. repeat first [assumption|split].
Qed.
End NativeWhitespaceSchemaGeneralStep.
