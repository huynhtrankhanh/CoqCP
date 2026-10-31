From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte SeedSeparator NativeState NativeSession NativeBasicSession NativeSetSchemaSession NativeSetBudgetPlan NativeDialogueComposition NativeBudgetFrame NativeFullTapeStep NativeBasicDispatcher NativeWhitespaceSchemaUniformCommand NativeWhitespaceSchemaSetStep NativeSchemaFlat FormulaTopology ClassLookup NativeNameCompact NativeSchemaFieldBounds CommandLoop.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaSetEntry.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaUniformCommand.
Theorem generated native logical fields name namespaces namesep countspaces countsep firstsep tail requests observations :
 NativeDialogueComposition.boundary native logical -> NativeSetSchemaSession.extra native logical ->
 NativeSetBudgetPlan.capacity logical (Protocol.Req 24 (map snd fields) name::requests) -> Protocol.shape(Protocol.Req 24 (map snd fields) name) ->
 Forall(fun item=>Forall TokenByteExecution.separator(fst item) /\ Z.of_nat(snd item)<=maximum)fields ->
 Forall TokenByteExecution.separator namespaces -> TokenByteExecution.separator namesep -> Forall TokenByteExecution.separator countspaces -> TokenByteExecution.separator countsep -> TokenByteExecution.separator firstsep ->
 stdin native=50::52::firstsep::payload name fields namespaces namesep countspaces countsep tail ->
 exists after reply next,
 execObserved(funcdef_0__command (fun _=>false)(fun _=>0))
  (CommandLoopExecution.pending_state(withInput native(52::firstsep::payload name fields namespaces namesep countspaces countsep tail))50,observations)=Some(tt,(after,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 (map snd fields) name) reply next /\ NativeDialogueComposition.boundary after next /\
 NativeSetSchemaSession.extra after next /\ NativeSetBudgetPlan.capacity next requests /\
 stdin after=tail /\ stdout after=stdout native++Protocol.reply_bytes reply.
Proof.
 intros Hboundary [Hbasic [Hflat Hsets]] Hcapacity Hshape HfieldWords Hns Hnsep Hcs Hcsep Hfirstsep Hinput.
 pose proof Hbasic as [Hmeta Hsip Hsafe Htop Hfalse Hgood Hunique Hcompact].
 set(request:=Protocol.Req 24 (map snd fields) name).
 set(base:=NativeFullTapeStep.entered native request []).
 set(unread:=52::firstsep::payload name fields namespaces namesep countspaces countsep tail).
 set(pending:=withInput base unread).
 assert(Hsame:pending=CommandLoopExecution.pending_state(withInput native unread)50).
 { unfold pending,base,request,NativeFullTapeStep.entered,CommandLoopExecution.pending_state. cbn [Protocol.opcode NativeBasicDispatcher.first].
   rewrite SeedSeparator.store_input. destruct native;reflexivity. }
 assert(Hpstate:NativeState.represents pending logical).
 { unfold pending,base. apply NativeSession.state_input. apply NativeBudgetFrame.entered_state. exact(NativeDialogueComposition.state _ _ Hboundary). }
 assert(Hpmeta:(31<length(memory pending arraydef_0__meta))%nat) by (unfold pending;cbn [memory withInput];unfold base;rewrite NativeBudgetFrame.entered_lengths;exact Hmeta).
 assert(Hpsip:(0<length(memory pending arraydef_0__sipState))%nat) by (unfold pending;cbn [memory withInput];unfold base;rewrite NativeBudgetFrame.entered_lengths;exact Hsip).
 assert(Hptoken:(1024<=length(memory pending arraydef_0__token))%nat) by (unfold pending;cbn [memory withInput];unfold base;rewrite NativeBudgetFrame.entered_lengths;exact(NativeDialogueComposition.token _ _ Hboundary)).
 assert(Hpprint:(20<=length(memory pending arraydef_0__printBuffer))%nat) by (unfold pending;cbn [memory withInput];unfold base;rewrite NativeBudgetFrame.entered_lengths;exact(NativeDialogueComposition.print _ _ Hboundary)).
 assert(Hperror:meta_value pending 8=0) by (change(meta_value base 8=0);unfold base;rewrite NativeBudgetFrame.entered_meta_other by lia;exact(NativeDialogueComposition.error _ _ Hboundary)).
 assert(Hprunning:meta_value pending 9=0) by (change(meta_value base 9=0);unfold base;rewrite NativeBudgetFrame.entered_meta_other by lia;exact(NativeDialogueComposition.running _ _ Hboundary)).
 assert(Hppending:meta_value pending 15=51) by (change(meta_value base 15=51);unfold base,request;rewrite NativeBudgetFrame.entered_pending by lia;reflexivity).
 assert(Hptop:FormulaTopology.ordered pending(length(Protocol.formulas logical))) by (unfold pending,base;apply NativeBudgetFrame.entered_top;exact Htop).
 assert(Hpgood:ClassLookup.wellformed pending) by (unfold pending,base;apply NativeBudgetFrame.entered_class_wellformed;exact Hgood).
 assert(Hpcompact:NativeNameCompact.compact pending logical) by (unfold pending,base;apply NativeBudgetFrame.entered_compact;exact Hcompact).
 assert(Hpflat:NativeSchemaFlat.flat pending).
 { unfold NativeSchemaFlat.flat in *. intros node raw Hnode. apply Hflat with (node:=node).
   unfold pending,base in Hnode. cbn [memory withInput] in Hnode. rewrite NativeFullTapeStep.entered_arrays in Hnode by discriminate. exact Hnode. }
 assert(Hpboundary:NativeDialogueComposition.boundary pending logical) by (constructor;assumption).
 assert(Hpextra:NativeSetSchemaSession.extra pending logical) by (split;[constructor;assumption|split;assumption]).
 destruct(NativeWhitespaceSchemaSetStep.generated pending logical fields name namespaces namesep countspaces countsep firstsep tail requests observations
  Hpboundary Hpextra Hcapacity Hshape Hppending HfieldWords Hns Hnsep Hcs Hcsep Hfirstsep eq_refl)
 as(after & reply & next & Hrun & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
 exists after,reply,next. rewrite <-Hsame. repeat first[assumption|split].
Qed.
End NativeWhitespaceSchemaSetEntry.
