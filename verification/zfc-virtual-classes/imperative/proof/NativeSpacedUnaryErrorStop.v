From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat CommandLoop Dialogue NativeState NativeSession NativeDialogueComposition NativeGeneralPrefixStop NativeCommandWhitespace NativePointwiseState MachinePointwise.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeSpacedUnaryErrorStop.
Import IndexExecution SipHashExecution.
Definition canonical_error separator rest tail := forall s observations,
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=53 -> meta_value s 8=0 -> stdin s=separator::rest ->
 exists final, execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(s,observations)=Some(tt,
 (final, observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Theorem spaced ch prefix separator rest tail :
 0<=ch<256 -> TokenByteExecution.separator ch -> Forall TokenByteExecution.separator prefix ->
 TokenByteExecution.separator separator -> canonical_error separator rest tail ->
 NativeGeneralPrefixStop.stop_spec (ch::prefix++52::separator::rest) tail.
Proof.
 intros Hch Hchsep Hprefix Hsep Hcanonical native logical observations Hboundary Hinput.
 pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary)) as Hmeta.
 pose proof(NativeDialogueComposition.token _ _ Hboundary) as Htoken.
 pose proof(NativeDialogueComposition.error _ _ Hboundary) as Herror.
 set(first:=NativeCommandWhitespace.canonical native 52 [] separator rest).
 assert(Hfirstmeta:(17<length(memory first arraydef_0__meta))%nat).
 { unfold first,NativeCommandWhitespace.canonical. rewrite store_meta_length. cbn [memory withInput]. lia. }
 assert(Hfirsttoken:(1024<=length(memory first arraydef_0__token))%nat).
 { unfold first,NativeCommandWhitespace.canonical. rewrite store_meta_other by discriminate. exact Htoken. }
 assert(Hfirstvalue:meta_value first 15=53).
 { unfold first,NativeCommandWhitespace.canonical. replace 53 with (52+1) by lia. apply meta_store_same. cbn [memory withInput]. lia. }
 assert(Hfirsterror:meta_value first 8=0).
 { unfold first,NativeCommandWhitespace.canonical. rewrite meta_store_other by lia. exact Herror. }
 destruct(Hcanonical first observations Hfirstmeta Hfirsttoken Hfirstvalue Hfirsterror eq_refl)
 as(final & Hrun & Hin & Hout & Hstop & Hfinalmeta).
 destruct(NativeCommandWhitespace.generated native (fun _=>false)(fun _=>0) ch prefix 52 [] separator rest observations final _
   ltac:(lia) Htoken Herror Hch Hchsep Hprefix ltac:(cbn;lia) ltac:(repeat constructor;lia)
   ltac:(cbn [ReadNatExecution.number_from];unfold maximum;lia) Hsep Hrun) as(target & Hactual & Hsame).
 destruct Hsame as (Hsamein & Hsameout & Hsamemem).
 assert(Htargetmeta:(9<length(memory target arraydef_0__meta))%nat) by (rewrite <-Hsamemem;exact Hfinalmeta).
 assert(Htargetstop:meta_value target 9=1) by (unfold meta_value in *;rewrite <-Hsamemem;exact Hstop).
 exists target. split.
 - eapply DialogueExecution.stop with (ch:=ch) (tail:=prefix++52::separator::rest);[exact Hch|exact Hinput|lia| |exact Htargetmeta|].
   + change(execObserved(funcdef_0__command (fun _=>false)(fun _=>0))
       (NativeCommandWhitespace.spaced native ch prefix 52 [] separator rest,observations)=Some(tt,
       (target,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}]))).
     exact Hactual.
   + rewrite Htargetstop;discriminate.
 - split;[rewrite <-Hsameout;exact Hout|]. split;[congruence|exact Htargetstop].
Qed.
Theorem any_spaces spaces separator rest tail :
 Forall TokenByteExecution.separator spaces -> TokenByteExecution.separator separator -> canonical_error separator rest tail ->
 NativeGeneralPrefixStop.stop_spec (spaces++52::separator::rest) tail.
Proof.
 intros Hspaces Hsep Hcanonical. destruct spaces as [|ch prefix].
 - intros native logical observations Hboundary Hinput.
   pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary)) as Hmeta.
   pose proof(NativeDialogueComposition.token _ _ Hboundary) as Htoken.
   pose proof(NativeDialogueComposition.error _ _ Hboundary) as Herror.
   set(pending:=CommandLoopExecution.pending_state(withInput native(separator::rest))52).
   assert(Hpmeta:(17<length(memory pending arraydef_0__meta))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. cbn [memory withInput]. lia. }
   assert(Hptoken:(1024<=length(memory pending arraydef_0__token))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
   assert(Hpvalue:meta_value pending 15=53).
   { unfold pending,CommandLoopExecution.pending_state. replace 53 with (52+1) by lia. apply meta_store_same. cbn [memory withInput]. lia. }
   assert(Hperror:meta_value pending 8=0).
   { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
   destruct(Hcanonical pending observations Hpmeta Hptoken Hpvalue Hperror eq_refl) as(final & Hrun & Hin & Hout & Hstop & Hfinalmeta).
   exists final. split.
   + eapply DialogueExecution.stop with (ch:=52) (tail:=separator::rest);[lia|exact Hinput|lia| |exact Hfinalmeta|].
     * change(execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,
       (final,observations++[{|flushedOutput:=stdout pending++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}]))). exact Hrun.
     * rewrite Hstop;discriminate.
   + split;[change(stdout final=stdout pending++Protocol.reply_bytes Protocol.ERR);exact Hout|]. now split.
 - inversion Hspaces as [|? ? Hch Hprefix];subst.
   assert(Hchbyte:0<=ch<256) by (unfold TokenByteExecution.separator in Hch;lia).
   exact(spaced ch prefix separator rest tail Hchbyte Hch Hprefix Hsep Hcanonical).
Qed.
End NativeSpacedUnaryErrorStop.
