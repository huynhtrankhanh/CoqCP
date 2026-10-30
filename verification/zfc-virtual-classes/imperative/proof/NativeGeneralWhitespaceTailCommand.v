From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte DecimalInput NativeState NativeBasicDispatcher NativeFullDispatcher
 NativeGeneralCommandInvariant NativeGeneralSession NativeGeneralArbitraryTailCommand NativeBudgetPlan NativeDialogueComposition NativeCommandWhitespace NativePointwiseState MachinePointwise CommandLoop.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeGeneralWhitespaceTailCommand.
Import IndexExecution SipHashExecution.
Theorem generated argument_cap native logical request requests tail observations ch prefix :
 NativeDialogueComposition.boundary native logical -> NativeGeneralSession.extra argument_cap native logical ->
 NativeBudgetPlan.capacity argument_cap logical (request::requests) -> Protocol.shape request -> Protocol.opcode request<>0%nat ->
 stdin native=Protocol.request_bytes request++tail -> 0<=ch<256 -> TokenByteExecution.separator ch -> Forall TokenByteExecution.separator prefix ->
 exists after reply next,
 execObserved(funcdef_0__command (fun _=>false)(fun _=>0))
 (CommandLoopExecution.pending_state(withInput native(prefix++Protocol.request_bytes request++tail))ch,observations)=
 Some(tt,(after,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical request reply next /\ NativeDialogueComposition.boundary after next /\
 NativeGeneralSession.extra argument_cap after next /\ NativeBudgetPlan.capacity argument_cap next requests /\
 stdin after=tail /\ stdout after=stdout native++Protocol.reply_bytes reply.
Proof.
 intros Hboundary Hextra Hcapacity Hshape Hpositive Hinput Hch Hsep Hprefix.
 destruct Hextra as [Hbasic Hfields]. pose proof Hbasic as [Hmeta Hsip Hsafe Htop Hfalse Hclasses Hunique Hcompact].
 destruct (NativeGeneralArbitraryTailCommand.commands argument_cap native logical request requests tail observations Hboundary (conj Hbasic Hfields) Hcapacity Hshape Hpositive Hinput)
 as(first & unread & final & reply & next & Hbyte & Hwire & Hrun & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
 destruct Hshape as [Hwords Hformat].
 destruct Hcapacity as [caps [Hbounds Hcheck]].
 destruct (NativeBudgetPlan.check_tail argument_cap caps request requests Hpositive Hcheck) as [Hconditions Htail].
 assert(Hrange:(1<=Protocol.opcode request<=26)%nat) by (pose proof (NativeBudgetPlan.opcode_bound _ _ _ Hconditions);lia).
 destruct (NativeFullDispatcher.request_encoding request Hrange) as [Hencoding Hfirstword].
 change(stdin native=Protocol.request_bytes request++tail) in Hinput.
 rewrite Hencoding in Hinput. cbn [List.app] in Hinput. rewrite Hwire in Hinput. injection Hinput as Hfirst Hunread. subst first unread.
 destruct (NativeGeneralCommandInvariant.request_parts request (conj Hwords Hformat) Hrange) as (digits & sep & payload & Hdecimal & Hseparator & Hrest).
 pose proof (DecimalInput.decimal_word (Protocol.opcode request) ltac:(unfold maximum;lia)) as [Hvalue [Hdigits Hlength]].
 rewrite Hdecimal in Hvalue,Hdigits,Hlength. cbn [length] in Hlength.
 rewrite Hrest in Hrun. rewrite <-app_assoc in Hrun. cbn [List.app] in Hrun.
 change(execObserved (funcdef_0__command (fun _=>false)(fun _=>0))
   (NativeCommandWhitespace.canonical native (NativeBasicDispatcher.first(Protocol.opcode request)) digits sep (payload++tail),observations)=
    Some(tt,(final,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}]))) in Hrun.
 destruct(NativeCommandWhitespace.generated native (fun _=>false)(fun _=>0) ch prefix
   (NativeBasicDispatcher.first(Protocol.opcode request)) digits sep (payload++tail) observations final _
   ltac:(lia) (NativeDialogueComposition.token _ _ Hboundary) (NativeDialogueComposition.error _ _ Hboundary) Hch Hsep Hprefix
   ltac:(lia) Hdigits ltac:(rewrite Hvalue;unfold maximum;lia) Hseparator Hrun) as [after [Hrun' Hsame]].
 exists after,reply,next. split.
 - rewrite Hencoding,Hrest. cbn [List.app]. rewrite <-app_assoc. exact Hrun'.
 - split;[exact Hstep|]. split;[exact(NativePointwiseState.boundary _ _ _ Hsame HnextBoundary)|].
   split;[exact(NativePointwiseState.extra _ _ _ _ Hsame HnextExtra)|]. split;[exact HnextCapacity|].
   destruct Hsame as [Hinsame [Houtsame Hmemory]]. split;congruence.
Qed.
End NativeGeneralWhitespaceTailCommand.
