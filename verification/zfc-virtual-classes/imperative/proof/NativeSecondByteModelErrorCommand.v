From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte CommandInput CommandArgs NativeValidByteModelReader NativeByteErrorNumericReader NativeMalformedSecondArgumentHandlers NativeMalformedSecondArgumentCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeSecondByteModelErrorCommand.
Import IndexExecution SipHashExecution.
Theorem generated s bs ns opcode ch chars sep0 first_input value input ended tail observations :
 NativeMalformedSecondArgumentHandlers.supported (Z.of_nat opcode) -> Z.of_nat opcode<=maximum -> decimalBytes opcode=ch::chars ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> TokenByteExecution.separator sep0 -> stdin s=chars++sep0::first_input ->
 ByteProtocol.byte_stream first_input -> ByteProtocol.byte_stream input ->
 ByteProtocol.read_number first_input=ByteProtocol.number_token value input ended ->
 NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 exists final, execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Proof.
 intros Hsupported Hword Hencoding Hmeta Htoken Hpending Herror Hsep0 Hinput Hbytes Hbytes2 Hfirst Hbad.
 set(op:=CommandInput.parsed s ch chars first_input).
 assert(Hopcode:execObserved(funcdef_0__readNat(fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations))).
 { unfold op. exact(CommandInput.generated_pending s (fun _=>false)(fun _=>0) opcode ch chars sep0 first_input observations Hmeta Htoken Hpending Herror Hword Hencoding Hsep0 Hinput). }
 assert(Hopmeta:(17<length(memory op arraydef_0__meta))%nat) by (unfold op;rewrite CommandInput.parsed_meta_length;exact Hmeta).
 assert(Hoptoken:(1024<=length(memory op arraydef_0__token))%nat) by (unfold op;rewrite CommandArgs.pending_token_length;exact Htoken).
 assert(Hoppending:meta_value op 15=0) by (unfold op;apply CommandArgs.pending_cleared;exact Hmeta).
 assert(Hopvalid:meta_value op 14=1) by (unfold op;apply CommandInput.parsed_valid;exact Hmeta).
 assert(Hopnumber:meta_value op 11=Z.of_nat opcode) by (unfold op;now apply CommandInput.parsed_number).
 assert(Hoperror:meta_value op 8=0) by (unfold op;rewrite CommandInput.parsed_meta_other by lia;exact Herror).
 assert(Hopin:stdin op=first_input) by reflexivity.
 assert(Hopout:stdout op=stdout s) by (unfold op;apply CommandInput.parsed_output).
 assert(Hfirstmodel:ByteProtocol.read_number(stdin op)=ByteProtocol.number_token value input ended) by now rewrite Hopin.
 assert(Hfirstrange:ByteProtocol.byte_stream(stdin op)) by now rewrite Hopin.
 destruct(NativeValidByteModelReader.generated op (fun _=>false)(fun _=>0) value input ended observations
   Hopmeta Hoptoken Hoppending Hoperror Hfirstrange Hfirstmodel)
 as(first & Hreadfirst & Hfirstmeta & Hfirsttoken & Hfirstpending & Hfirsterror & Hfirstvalid & Hfirstnumber & Hfirstin & Hfirstout).
 assert(Hmodel:NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number(stdin first))=Some tail) by now rewrite Hfirstin.
 assert(Hrange:ByteProtocol.byte_stream(stdin first)) by now rewrite Hfirstin.
 destruct(NativeByteErrorNumericReader.generated first (fun _=>false)(fun _=>0) observations tail Hfirstmeta Hfirsttoken Hfirstpending Hfirsterror Hrange Hmodel)
  as(arg & Harg & Hargmeta & Hargvalid & Hargin & Hargout).
 pose proof(NativeMalformedSecondArgumentCommand.generated s bs ns op first arg (Z.of_nat opcode) value (meta_value arg 11) observations
   Hsupported Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hreadfirst Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror Harg Hargmeta eq_refl Hargvalid) as Hrun.
 assert(Hout:stdout arg=stdout s) by congruence.
 exists(NativeMalformedSecondArgumentCommand.final arg). rewrite Hout,Hargin in Hrun. split;[exact Hrun|].
 split;[exact Hargin|]. split;[change(stdout arg++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR);now rewrite Hout|].
 split.
 - unfold NativeMalformedSecondArgumentCommand.final. apply meta_store_same. cbn [memory withOutput]. unfold NativeMalformedSecondArgumentCommand.failed. rewrite store_meta_length. lia.
 - unfold NativeMalformedSecondArgumentCommand.final. rewrite store_meta_length. cbn [memory withOutput]. unfold NativeMalformedSecondArgumentCommand.failed. rewrite store_meta_length. lia.
Qed.
End NativeSecondByteModelErrorCommand.
