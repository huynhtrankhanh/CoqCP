From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat CommandInput CommandArgs NativeMissingNumberEOF NativeReadTokenLeadingMissing NativeMalformedUnaryCommand NativeMalformedFirstArgumentCommand NativeMalformedFirstArgumentHandlers NativeInvalidNumericReader.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeInvalidFirstArgument.
Import IndexExecution SipHashExecution ReadTokenExecution ReadNatExecution.
Theorem generated s bs ns opcode digit digits separator chars spaces sep tail (ended:bool) prefix bad suffix observations :
 NativeMalformedFirstArgumentHandlers.supported (Z.of_nat opcode) -> Z.of_nat opcode<=maximum -> decimalBytes opcode=digit::digits ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=digit+1 -> meta_value s 8=0 -> TokenByteExecution.separator separator ->
 (0<length chars<=1024)%nat -> Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars ->
 Forall TokenByteExecution.separator spaces -> TokenByteExecution.separator sep ->
 (if ended then stdin s=digits++separator::spaces++chars /\ tail=[] else stdin s=digits++separator::spaces++chars++sep::tail) ->
 prefix++bad::suffix=chars -> Forall(fun c=>48<=c<=57)prefix -> number_from 0 prefix<=maximum ->
 ((bad<48 \/ 57<bad) \/ (48<=bad<=57 /\ maximum<10*(number_from 0 prefix)+(bad-48))) ->
 exists final, execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (final, observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Proof.
 intros Hsupported Hword Hopencoding Hmeta Htoken Hpending Herror Hseparator Hlength Hbytes Hspaces Hsep Hinput Hencoding Hdigits Hbound Hbad.
 set(rest:=if ended then spaces++chars else spaces++chars++sep::tail).
 assert(Hinput':stdin s=digits++separator::rest) by (unfold rest;destruct ended;cbn in *;tauto).
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
 assert(Harginput:if ended then stdin op=spaces++chars /\ tail=[] else stdin op=spaces++chars++sep::tail).
 { unfold op,rest. destruct ended;cbn in *;tauto. }
 destruct(NativeInvalidNumericReader.generated op (fun _=>false)(fun _=>0) chars spaces sep tail ended prefix bad suffix observations
   Hopmeta Hoptoken Hoppending Hoperror Hlength Hbytes Hspaces Hsep Harginput Hencoding Hdigits Hbound Hbad)
 as(Harg & Hargmeta & Hargnumber & Hargvalid & Hargout & Hargin).
 set(arg:=NativeInvalidNumericReader.parsed op chars sep tail ended prefix) in *.
 pose proof(NativeMalformedFirstArgumentCommand.generated s bs ns op arg (Z.of_nat opcode) (number_from 0 prefix) observations Hsupported Hopcode Hopmeta Hopnumber Hopvalid Hoperror Harg Hargmeta Hargnumber Hargvalid) as Hrun.
 assert(Hout:stdout arg=stdout s) by (rewrite Hargout;unfold op;apply CommandInput.parsed_output).
 exists(NativeMalformedFirstArgumentCommand.final arg). rewrite Hout,Hargin in Hrun. split;[exact Hrun|].
 split;[exact Hargin|]. split;[change(stdout arg++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR);now rewrite Hout|].
 split.
 - unfold NativeMalformedFirstArgumentCommand.final. apply meta_store_same. cbn [memory withOutput]. unfold NativeMalformedFirstArgumentCommand.failed. rewrite store_meta_length. lia.
 - unfold NativeMalformedFirstArgumentCommand.final. rewrite store_meta_length. cbn [memory withOutput]. unfold NativeMalformedFirstArgumentCommand.failed. rewrite store_meta_length. lia.
Qed.
End NativeInvalidFirstArgument.
