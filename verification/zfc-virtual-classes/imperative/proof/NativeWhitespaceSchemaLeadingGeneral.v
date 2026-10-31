From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeGeneralSession NativeBudgetPlan NativeDialogueComposition NativeCommandWhitespace NativePointwiseState NativeWhitespaceSchemaArguments NativeWhitespaceSchemaUniformCommand NativeWhitespaceSchemaGeneralEntry CommandLoop.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaLeadingGeneral.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaUniformCommand.
Theorem generated argument_cap native logical fields name namespaces namesep countspaces countsep firstsep tail requests observations ch prefix :
 NativeDialogueComposition.boundary native logical -> NativeGeneralSession.extra argument_cap native logical ->
 NativeBudgetPlan.capacity argument_cap logical (Protocol.Req 24 (map snd fields) name::requests) -> Protocol.shape(Protocol.Req 24 (map snd fields) name) ->
 Forall(fun item=>Forall TokenByteExecution.separator(fst item) /\ Z.of_nat(snd item)<=maximum)fields ->
 Forall TokenByteExecution.separator namespaces -> TokenByteExecution.separator namesep -> Forall TokenByteExecution.separator countspaces -> TokenByteExecution.separator countsep -> TokenByteExecution.separator firstsep ->
 0<=ch<256 -> TokenByteExecution.separator ch -> Forall TokenByteExecution.separator prefix ->
 exists after reply next,
 execObserved(funcdef_0__command (fun _=>false)(fun _=>0))
  (CommandLoopExecution.pending_state(withInput native(prefix++50::52::firstsep::payload name fields namespaces namesep countspaces countsep tail))ch,observations)=Some(tt,(after,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 (map snd fields) name) reply next /\ NativeDialogueComposition.boundary after next /\
 NativeGeneralSession.extra argument_cap after next /\ NativeBudgetPlan.capacity argument_cap next requests /\
 stdin after=tail /\ stdout after=stdout native++Protocol.reply_bytes reply.
Proof.
 intros Hboundary Hextra Hcapacity Hshape Hfields Hns Hnsep Hcs Hcsep Hfirst Hch Hsep Hprefix.
 set(base:=withInput native(50::52::firstsep::payload name fields namespaces namesep countspaces countsep tail)).
 assert(HbaseBoundary:NativeDialogueComposition.boundary base logical).
 { destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning]. constructor;try assumption. unfold base. now apply NativeSession.state_input. }
 assert(HbaseExtra:NativeGeneralSession.extra argument_cap base logical).
 { destruct Hextra as [Hbasic Hfield]. destruct Hbasic as [Hmeta Hsip Hsafe Htop Hfalse Hclasses Hunique Hcompact]. split;[constructor;assumption|exact Hfield]. }
 destruct(NativeWhitespaceSchemaGeneralEntry.generated argument_cap base logical fields name namespaces namesep countspaces countsep firstsep tail requests observations
  HbaseBoundary HbaseExtra Hcapacity Hshape Hfields Hns Hnsep Hcs Hcsep Hfirst eq_refl)
 as(final & reply & next & Hrun & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
 change(execObserved(funcdef_0__command (fun _=>false)(fun _=>0))
  (NativeCommandWhitespace.canonical native 50 [52] firstsep (payload name fields namespaces namesep countspaces countsep tail),observations)=
  Some(tt,(final,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}]))) in Hrun.
 destruct(NativeCommandWhitespace.generated native (fun _=>false)(fun _=>0) ch prefix 50 [52] firstsep (payload name fields namespaces namesep countspaces countsep tail) observations final _
  ltac:(pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia)
  (NativeDialogueComposition.token _ _ Hboundary) (NativeDialogueComposition.error _ _ Hboundary) Hch Hsep Hprefix
  ltac:(lia) ltac:(repeat constructor;lia) ltac:(cbn;unfold maximum;lia) Hfirst Hrun) as(after & Hactual & Hsame).
 exists after,reply,next. split;[exact Hactual|]. split;[exact Hstep|].
 split;[exact(NativePointwiseState.boundary _ _ _ Hsame HnextBoundary)|].
 split;[exact(NativePointwiseState.extra _ _ _ _ Hsame HnextExtra)|]. split;[exact HnextCapacity|].
 destruct Hsame as [Hinsame [Houtsame Hmemory]]. split;congruence.
Qed.
End NativeWhitespaceSchemaLeadingGeneral.
