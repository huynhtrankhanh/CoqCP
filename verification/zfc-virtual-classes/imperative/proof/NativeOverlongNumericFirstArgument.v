From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat CommandInput CommandArgs NativeMissingNumberEOF NativeReadTokenLeadingMissing NativeMalformedUnaryCommand NativeMalformedFirstArgumentCommand NativeMalformedFirstArgumentHandlers NativeMalformedTagHandlers NativeMalformedTagCommand NativeMalformedNumericFirstCommand NativeInvalidNumericReader NativeOverlongNumericReader.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeOverlongNumericFirstArgument.
Import IndexExecution SipHashExecution ReadTokenExecution ReadNatExecution.
Theorem generated s bs ns opcode digit digits separator chars spaces extra tail observations :
 (NativeMalformedFirstArgumentHandlers.supported (Z.of_nat opcode) \/ NativeMalformedTagHandlers.supported (Z.of_nat opcode)) -> Z.of_nat opcode<=maximum -> decimalBytes opcode=digit::digits ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=digit+1 -> meta_value s 8=0 -> TokenByteExecution.separator separator ->
 length chars=1024%nat -> Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars ->
 Forall TokenByteExecution.separator spaces -> 0<=extra<256 -> ~TokenByteExecution.separator extra ->
 stdin s=digits++separator::spaces++chars++extra::tail ->
 exists final, execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (final, observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Proof.
 intros Hsupported Hword Hopencoding Hmeta Htoken Hpending Herror Hseparator Hlength Hbytes Hspaces Hextra Hbad Hinput.
 set(rest:=spaces++chars++extra::tail).
 assert(Hinput':stdin s=digits++separator::rest) by exact Hinput.
 set(op:=CommandInput.parsed s digit digits rest).
 assert(Hopcode:execObserved(funcdef_0__readNat(fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations))).
 { unfold op. eapply(CommandInput.generated_pending s (fun _=>false)(fun _=>0) opcode digit digits separator rest observations);try assumption;
   try exact Hinput';assumption. }
 assert(Hopmeta:(17<length(memory op arraydef_0__meta))%nat) by (unfold op;rewrite CommandInput.parsed_meta_length;exact Hmeta).
 assert(Hoptoken:(1024<=length(memory op arraydef_0__token))%nat) by (unfold op;rewrite CommandArgs.pending_token_length;exact Htoken).
 assert(Hoppending:meta_value op 15=0) by (unfold op;apply CommandArgs.pending_cleared;exact Hmeta).
 assert(Hopvalid:meta_value op 14=1) by (unfold op;apply CommandInput.parsed_valid;exact Hmeta).
 assert(Hopnumber:meta_value op 11=Z.of_nat opcode) by (unfold op;now apply CommandInput.parsed_number).
 assert(Hoperror:meta_value op 8=0) by (unfold op;rewrite CommandInput.parsed_meta_other by lia;exact Herror).
 assert(Hopin:stdin op=rest) by reflexivity.
 destruct(NativeOverlongNumericReader.generated_number op (fun _=>false)(fun _=>0) spaces chars extra tail observations
   Hopmeta Hoptoken Hoppending Hoperror Hlength Hbytes Hextra Hbad Hspaces Hopin)
 as(Harg & Hargmeta & Hargnumber & Hargvalid & Hargerror & Hargin & Hargout).
 set(arg:=NativeOverlongNumericReader.parsed op chars tail) in *.
 pose proof(NativeMalformedNumericFirstCommand.generated s bs ns op arg (Z.of_nat opcode) 0 observations Hsupported Hopcode Hopmeta Hopnumber Hopvalid Hoperror Harg Hargmeta Hargnumber Hargvalid) as Hrun.
 assert(Hout:stdout arg=stdout s) by (rewrite Hargout;unfold op;apply CommandInput.parsed_output).
 exists(NativeMalformedNumericFirstCommand.final arg). rewrite Hout,Hargin in Hrun. split;[exact Hrun|].
 split;[exact Hargin|]. split;[change(stdout arg++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR);now rewrite Hout|].
 split.
 - unfold NativeMalformedNumericFirstCommand.final. apply meta_store_same. cbn [memory withOutput]. unfold NativeMalformedNumericFirstCommand.failed. rewrite store_meta_length. lia.
 - unfold NativeMalformedNumericFirstCommand.final. rewrite store_meta_length. cbn [memory withOutput]. unfold NativeMalformedNumericFirstCommand.failed. rewrite store_meta_length. lia.
Qed.
End NativeOverlongNumericFirstArgument.
