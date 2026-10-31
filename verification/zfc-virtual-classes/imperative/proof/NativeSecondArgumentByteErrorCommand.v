From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat DecimalInput CommandInput CommandArgs ReadOne NativeArgumentReads NativeByteErrorNumericReader NativeMalformedSecondArgumentHandlers NativeMalformedSecondArgumentCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeSecondArgumentByteErrorCommand.
Import IndexExecution SipHashExecution.
Theorem generated s bs ns opcode ch chars value sep0 spaces sep1 input tail observations :
 NativeMalformedSecondArgumentHandlers.supported (Z.of_nat opcode) -> Z.of_nat opcode<=maximum -> decimalBytes opcode=ch::chars ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 (20<=length(memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
 Z.of_nat value<=maximum -> TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> Forall TokenByteExecution.separator spaces ->
 stdin s=chars++sep0::spaces++decimalBytes value++sep1::input ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 exists final, execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Proof.
 intros Hsupported Hword Hencoding Hmeta Htoken Hbuffer Hpending Herror Hvalue Hsep0 Hsep1 Hspaces Hinput Hbytes Hbad.
 destruct(NativeArgumentReads.generated_reads s (fun _=>false)(fun _=>0) opcode ch chars value sep0 spaces sep1 input observations
   Hmeta Htoken Hbuffer Hpending Herror Hword Hencoding Hvalue Hsep0 Hsep1 Hspaces Hinput)
  as(Hopcode & Hfirst & Hopmeta & Hopnumber & Hopvalid & Hoperror & Hfirstmeta & Hfirstbuffer & Hfirstnumber & Hfirstvalid & Hfirsterror & Hfirstin & Hfirstout).
 set(op:=CommandInput.parsed s ch chars (spaces++decimalBytes value++sep1::input)) in *.
 set(first:=ReadOne.argument_state s ch chars value sep1 input) in *.
 assert(Hfirsttoken:(1024<=length(memory first arraydef_0__token))%nat).
 { unfold first,ReadOne.argument_state. rewrite DecimalInput.encoded_token_length. unfold ReadOne.opcode_state. now rewrite CommandArgs.pending_token_length. }
 assert(Hfirstpending:meta_value first 15=0).
 { unfold first,ReadOne.argument_state. rewrite DecimalInput.encoded_meta_other;[|unfold ReadOne.opcode_state;now rewrite CommandInput.parsed_meta_length|lia|lia|lia|lia].
   unfold ReadOne.opcode_state. apply CommandArgs.pending_cleared. exact Hmeta. }
 assert(Hmodel:NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number(stdin first))=Some tail) by now rewrite Hfirstin.
 assert(Hrange:ByteProtocol.byte_stream(stdin first)) by now rewrite Hfirstin.
 destruct(NativeByteErrorNumericReader.generated first (fun _=>false)(fun _=>0) observations tail Hfirstmeta Hfirsttoken Hfirstpending Hfirsterror Hrange Hmodel)
  as(arg & Harg & Hargmeta & Hargvalid & Hargin & Hargout).
 pose proof(NativeMalformedSecondArgumentCommand.generated s bs ns op first arg (Z.of_nat opcode) (Z.of_nat value) (meta_value arg 11) observations
   Hsupported Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hfirst Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror Harg Hargmeta eq_refl Hargvalid) as Hrun.
 assert(Hout:stdout arg=stdout s) by congruence.
 exists(NativeMalformedSecondArgumentCommand.final arg). rewrite Hout,Hargin in Hrun. split;[exact Hrun|].
 split;[exact Hargin|]. split;[change(stdout arg++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR);now rewrite Hout|].
 split.
 - unfold NativeMalformedSecondArgumentCommand.final. apply meta_store_same. cbn [memory withOutput]. unfold NativeMalformedSecondArgumentCommand.failed. rewrite store_meta_length. lia.
 - unfold NativeMalformedSecondArgumentCommand.final. rewrite store_meta_length. cbn [memory withOutput]. unfold NativeMalformedSecondArgumentCommand.failed. rewrite store_meta_length. lia.
Qed.
End NativeSecondArgumentByteErrorCommand.
