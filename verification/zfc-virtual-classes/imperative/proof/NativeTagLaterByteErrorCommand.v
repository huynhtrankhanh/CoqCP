From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat DecimalInput CommandInput CommandArgs NativeValidNumericReader NativeByteErrorNumericReader NativeMalformedTagLaterCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeTagLaterByteErrorCommand.
Import IndexExecution SipHashExecution.
Theorem generated_11_2 s bs ns digit digits sep0 value1 space1 sep1 input tail observations :
 decimalBytes 11=digit::digits ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=digit+1 -> meta_value s 8=0 -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 stdin s=digits++sep0::(space1++decimalBytes value1++sep1::input) -> ByteProtocol.byte_stream input ->
 NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 exists final, execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Proof.
 intros Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hinput Hbytes Hbad.
 set(op:=CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::input)).
 assert(Hopcode:execObserved(funcdef_0__readNat(fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations))).
 { unfold op. eapply(CommandInput.generated_pending s (fun _=>false)(fun _=>0) 11 digit digits sep0 (space1++decimalBytes value1++sep1::input) observations);try eassumption;unfold maximum;lia. }
 assert(Hopmeta:(17<length(memory op arraydef_0__meta))%nat) by (unfold op;rewrite CommandInput.parsed_meta_length;exact Hmeta).
 assert(Hoptoken:(1024<=length(memory op arraydef_0__token))%nat) by (unfold op;rewrite CommandArgs.pending_token_length;exact Htoken).
 assert(Hoppending:meta_value op 15=0) by (unfold op;apply CommandArgs.pending_cleared;exact Hmeta).
 assert(Hopvalid:meta_value op 14=1) by (unfold op;apply CommandInput.parsed_valid;exact Hmeta).
 assert(Hopnumber:meta_value op 11=11) by (unfold op;change(meta_value(CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::input))11=Z.of_nat 11);apply CommandInput.parsed_number;try assumption;unfold maximum;lia).
 assert(Hoperror:meta_value op 8=0) by (unfold op;rewrite CommandInput.parsed_meta_other by lia;exact Herror).
 assert(Hopin:stdin op=(space1++decimalBytes value1++sep1::input)) by reflexivity.
 assert(Hopout:stdout op=stdout s) by (unfold op;apply CommandInput.parsed_output).
 pose proof(NativeValidNumericReader.generated op (fun _=>false)(fun _=>0) value1 space1 sep1 input observations
   Hopmeta Hoptoken Hoppending Hoperror Hvalue1 Hsep1 Hspace1 Hopin) as Hreader1.
 set(p1:=DecimalInput.encoded_result op value1 input) in Hreader1.
 destruct Hreader1 as (Hread1 & Hp1meta & Hp1token & Hp1pending & Hp1error & Hp1valid & Hp1number & Hp1in & Hp1out).
 assert(Hmodel:NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number(stdin p1))=Some tail) by now rewrite Hp1in.
 assert(Hrange:ByteProtocol.byte_stream(stdin p1)) by now rewrite Hp1in.
 destruct(NativeByteErrorNumericReader.generated p1 (fun _=>false)(fun _=>0) observations tail Hp1meta Hp1token Hp1pending Hp1error Hrange Hmodel)
  as(arg & Harg & Hargmeta & Hargvalid & Hargin & Hargout).
 pose proof(NativeMalformedTagLaterCommand.generated_11_2 s bs ns op p1 (Z.of_nat value1) arg (meta_value arg 11) observations
   Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread1 Hp1meta Hp1number Hp1valid Hp1error Harg Hargmeta eq_refl Hargvalid) as Hrun.
 assert(Hout:stdout arg=stdout s) by congruence.
 exists(NativeMalformedTagLaterCommand.final arg). rewrite Hout,Hargin in Hrun. split;[exact Hrun|].
 split;[exact Hargin|]. split;[change(stdout arg++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR);now rewrite Hout|].
 split.
 - unfold NativeMalformedTagLaterCommand.final. apply meta_store_same. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
 - unfold NativeMalformedTagLaterCommand.final. rewrite store_meta_length. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
Qed.
Theorem generated_11_3 s bs ns digit digits sep0 value1 space1 sep1 value2 space2 sep2 input tail observations :
 decimalBytes 11=digit::digits ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=digit+1 -> meta_value s 8=0 -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 stdin s=digits++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)) -> ByteProtocol.byte_stream input ->
 NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 exists final, execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Proof.
 intros Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hinput Hbytes Hbad.
 set(op:=CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input))).
 assert(Hopcode:execObserved(funcdef_0__readNat(fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations))).
 { unfold op. eapply(CommandInput.generated_pending s (fun _=>false)(fun _=>0) 11 digit digits sep0 (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)) observations);try eassumption;unfold maximum;lia. }
 assert(Hopmeta:(17<length(memory op arraydef_0__meta))%nat) by (unfold op;rewrite CommandInput.parsed_meta_length;exact Hmeta).
 assert(Hoptoken:(1024<=length(memory op arraydef_0__token))%nat) by (unfold op;rewrite CommandArgs.pending_token_length;exact Htoken).
 assert(Hoppending:meta_value op 15=0) by (unfold op;apply CommandArgs.pending_cleared;exact Hmeta).
 assert(Hopvalid:meta_value op 14=1) by (unfold op;apply CommandInput.parsed_valid;exact Hmeta).
 assert(Hopnumber:meta_value op 11=11) by (unfold op;change(meta_value(CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)))11=Z.of_nat 11);apply CommandInput.parsed_number;try assumption;unfold maximum;lia).
 assert(Hoperror:meta_value op 8=0) by (unfold op;rewrite CommandInput.parsed_meta_other by lia;exact Herror).
 assert(Hopin:stdin op=(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input))) by reflexivity.
 assert(Hopout:stdout op=stdout s) by (unfold op;apply CommandInput.parsed_output).
 pose proof(NativeValidNumericReader.generated op (fun _=>false)(fun _=>0) value1 space1 sep1 (space2++decimalBytes value2++sep2::input) observations
   Hopmeta Hoptoken Hoppending Hoperror Hvalue1 Hsep1 Hspace1 Hopin) as Hreader1.
 set(p1:=DecimalInput.encoded_result op value1 (space2++decimalBytes value2++sep2::input)) in Hreader1.
 destruct Hreader1 as (Hread1 & Hp1meta & Hp1token & Hp1pending & Hp1error & Hp1valid & Hp1number & Hp1in & Hp1out).
 pose proof(NativeValidNumericReader.generated p1 (fun _=>false)(fun _=>0) value2 space2 sep2 input observations
   Hp1meta Hp1token Hp1pending Hp1error Hvalue2 Hsep2 Hspace2 Hp1in) as Hreader2.
 set(p2:=DecimalInput.encoded_result p1 value2 input) in Hreader2.
 destruct Hreader2 as (Hread2 & Hp2meta & Hp2token & Hp2pending & Hp2error & Hp2valid & Hp2number & Hp2in & Hp2out).
 assert(Hmodel:NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number(stdin p2))=Some tail) by now rewrite Hp2in.
 assert(Hrange:ByteProtocol.byte_stream(stdin p2)) by now rewrite Hp2in.
 destruct(NativeByteErrorNumericReader.generated p2 (fun _=>false)(fun _=>0) observations tail Hp2meta Hp2token Hp2pending Hp2error Hrange Hmodel)
  as(arg & Harg & Hargmeta & Hargvalid & Hargin & Hargout).
 pose proof(NativeMalformedTagLaterCommand.generated_11_3 s bs ns op p1 (Z.of_nat value1) p2 (Z.of_nat value2) arg (meta_value arg 11) observations
   Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread1 Hp1meta Hp1number Hp1valid Hp1error Hread2 Hp2meta Hp2number Hp2valid Hp2error Harg Hargmeta eq_refl Hargvalid) as Hrun.
 assert(Hout:stdout arg=stdout s) by congruence.
 exists(NativeMalformedTagLaterCommand.final arg). rewrite Hout,Hargin in Hrun. split;[exact Hrun|].
 split;[exact Hargin|]. split;[change(stdout arg++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR);now rewrite Hout|].
 split.
 - unfold NativeMalformedTagLaterCommand.final. apply meta_store_same. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
 - unfold NativeMalformedTagLaterCommand.final. rewrite store_meta_length. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
Qed.
Theorem generated_11_4 s bs ns digit digits sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 input tail observations :
 decimalBytes 11=digit::digits ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=digit+1 -> meta_value s 8=0 -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 Z.of_nat value3<=maximum -> Forall TokenByteExecution.separator space3 -> TokenByteExecution.separator sep3 ->
 stdin s=digits++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))) -> ByteProtocol.byte_stream input ->
 NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 exists final, execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Proof.
 intros Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hinput Hbytes Hbad.
 set(op:=CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input)))).
 assert(Hopcode:execObserved(funcdef_0__readNat(fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations))).
 { unfold op. eapply(CommandInput.generated_pending s (fun _=>false)(fun _=>0) 11 digit digits sep0 (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))) observations);try eassumption;unfold maximum;lia. }
 assert(Hopmeta:(17<length(memory op arraydef_0__meta))%nat) by (unfold op;rewrite CommandInput.parsed_meta_length;exact Hmeta).
 assert(Hoptoken:(1024<=length(memory op arraydef_0__token))%nat) by (unfold op;rewrite CommandArgs.pending_token_length;exact Htoken).
 assert(Hoppending:meta_value op 15=0) by (unfold op;apply CommandArgs.pending_cleared;exact Hmeta).
 assert(Hopvalid:meta_value op 14=1) by (unfold op;apply CommandInput.parsed_valid;exact Hmeta).
 assert(Hopnumber:meta_value op 11=11) by (unfold op;change(meta_value(CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))))11=Z.of_nat 11);apply CommandInput.parsed_number;try assumption;unfold maximum;lia).
 assert(Hoperror:meta_value op 8=0) by (unfold op;rewrite CommandInput.parsed_meta_other by lia;exact Herror).
 assert(Hopin:stdin op=(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input)))) by reflexivity.
 assert(Hopout:stdout op=stdout s) by (unfold op;apply CommandInput.parsed_output).
 pose proof(NativeValidNumericReader.generated op (fun _=>false)(fun _=>0) value1 space1 sep1 (space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input)) observations
   Hopmeta Hoptoken Hoppending Hoperror Hvalue1 Hsep1 Hspace1 Hopin) as Hreader1.
 set(p1:=DecimalInput.encoded_result op value1 (space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))) in Hreader1.
 destruct Hreader1 as (Hread1 & Hp1meta & Hp1token & Hp1pending & Hp1error & Hp1valid & Hp1number & Hp1in & Hp1out).
 pose proof(NativeValidNumericReader.generated p1 (fun _=>false)(fun _=>0) value2 space2 sep2 (space3++decimalBytes value3++sep3::input) observations
   Hp1meta Hp1token Hp1pending Hp1error Hvalue2 Hsep2 Hspace2 Hp1in) as Hreader2.
 set(p2:=DecimalInput.encoded_result p1 value2 (space3++decimalBytes value3++sep3::input)) in Hreader2.
 destruct Hreader2 as (Hread2 & Hp2meta & Hp2token & Hp2pending & Hp2error & Hp2valid & Hp2number & Hp2in & Hp2out).
 pose proof(NativeValidNumericReader.generated p2 (fun _=>false)(fun _=>0) value3 space3 sep3 input observations
   Hp2meta Hp2token Hp2pending Hp2error Hvalue3 Hsep3 Hspace3 Hp2in) as Hreader3.
 set(p3:=DecimalInput.encoded_result p2 value3 input) in Hreader3.
 destruct Hreader3 as (Hread3 & Hp3meta & Hp3token & Hp3pending & Hp3error & Hp3valid & Hp3number & Hp3in & Hp3out).
 assert(Hmodel:NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number(stdin p3))=Some tail) by now rewrite Hp3in.
 assert(Hrange:ByteProtocol.byte_stream(stdin p3)) by now rewrite Hp3in.
 destruct(NativeByteErrorNumericReader.generated p3 (fun _=>false)(fun _=>0) observations tail Hp3meta Hp3token Hp3pending Hp3error Hrange Hmodel)
  as(arg & Harg & Hargmeta & Hargvalid & Hargin & Hargout).
 pose proof(NativeMalformedTagLaterCommand.generated_11_4 s bs ns op p1 (Z.of_nat value1) p2 (Z.of_nat value2) p3 (Z.of_nat value3) arg (meta_value arg 11) observations
   Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread1 Hp1meta Hp1number Hp1valid Hp1error Hread2 Hp2meta Hp2number Hp2valid Hp2error Hread3 Hp3meta Hp3number Hp3valid Hp3error Harg Hargmeta eq_refl Hargvalid) as Hrun.
 assert(Hout:stdout arg=stdout s) by congruence.
 exists(NativeMalformedTagLaterCommand.final arg). rewrite Hout,Hargin in Hrun. split;[exact Hrun|].
 split;[exact Hargin|]. split;[change(stdout arg++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR);now rewrite Hout|].
 split.
 - unfold NativeMalformedTagLaterCommand.final. apply meta_store_same. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
 - unfold NativeMalformedTagLaterCommand.final. rewrite store_meta_length. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
Qed.
Theorem generated_22_2 s bs ns digit digits sep0 value1 space1 sep1 input tail observations :
 decimalBytes 22=digit::digits ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=digit+1 -> meta_value s 8=0 -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 stdin s=digits++sep0::(space1++decimalBytes value1++sep1::input) -> ByteProtocol.byte_stream input ->
 NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 exists final, execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Proof.
 intros Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hinput Hbytes Hbad.
 set(op:=CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::input)).
 assert(Hopcode:execObserved(funcdef_0__readNat(fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations))).
 { unfold op. eapply(CommandInput.generated_pending s (fun _=>false)(fun _=>0) 22 digit digits sep0 (space1++decimalBytes value1++sep1::input) observations);try eassumption;unfold maximum;lia. }
 assert(Hopmeta:(17<length(memory op arraydef_0__meta))%nat) by (unfold op;rewrite CommandInput.parsed_meta_length;exact Hmeta).
 assert(Hoptoken:(1024<=length(memory op arraydef_0__token))%nat) by (unfold op;rewrite CommandArgs.pending_token_length;exact Htoken).
 assert(Hoppending:meta_value op 15=0) by (unfold op;apply CommandArgs.pending_cleared;exact Hmeta).
 assert(Hopvalid:meta_value op 14=1) by (unfold op;apply CommandInput.parsed_valid;exact Hmeta).
 assert(Hopnumber:meta_value op 11=22) by (unfold op;change(meta_value(CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::input))11=Z.of_nat 22);apply CommandInput.parsed_number;try assumption;unfold maximum;lia).
 assert(Hoperror:meta_value op 8=0) by (unfold op;rewrite CommandInput.parsed_meta_other by lia;exact Herror).
 assert(Hopin:stdin op=(space1++decimalBytes value1++sep1::input)) by reflexivity.
 assert(Hopout:stdout op=stdout s) by (unfold op;apply CommandInput.parsed_output).
 pose proof(NativeValidNumericReader.generated op (fun _=>false)(fun _=>0) value1 space1 sep1 input observations
   Hopmeta Hoptoken Hoppending Hoperror Hvalue1 Hsep1 Hspace1 Hopin) as Hreader1.
 set(p1:=DecimalInput.encoded_result op value1 input) in Hreader1.
 destruct Hreader1 as (Hread1 & Hp1meta & Hp1token & Hp1pending & Hp1error & Hp1valid & Hp1number & Hp1in & Hp1out).
 assert(Hmodel:NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number(stdin p1))=Some tail) by now rewrite Hp1in.
 assert(Hrange:ByteProtocol.byte_stream(stdin p1)) by now rewrite Hp1in.
 destruct(NativeByteErrorNumericReader.generated p1 (fun _=>false)(fun _=>0) observations tail Hp1meta Hp1token Hp1pending Hp1error Hrange Hmodel)
  as(arg & Harg & Hargmeta & Hargvalid & Hargin & Hargout).
 pose proof(NativeMalformedTagLaterCommand.generated_22_2 s bs ns op p1 (Z.of_nat value1) arg (meta_value arg 11) observations
   Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread1 Hp1meta Hp1number Hp1valid Hp1error Harg Hargmeta eq_refl Hargvalid) as Hrun.
 assert(Hout:stdout arg=stdout s) by congruence.
 exists(NativeMalformedTagLaterCommand.final arg). rewrite Hout,Hargin in Hrun. split;[exact Hrun|].
 split;[exact Hargin|]. split;[change(stdout arg++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR);now rewrite Hout|].
 split.
 - unfold NativeMalformedTagLaterCommand.final. apply meta_store_same. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
 - unfold NativeMalformedTagLaterCommand.final. rewrite store_meta_length. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
Qed.
Theorem generated_22_3 s bs ns digit digits sep0 value1 space1 sep1 value2 space2 sep2 input tail observations :
 decimalBytes 22=digit::digits ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=digit+1 -> meta_value s 8=0 -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 stdin s=digits++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)) -> ByteProtocol.byte_stream input ->
 NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 exists final, execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Proof.
 intros Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hinput Hbytes Hbad.
 set(op:=CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input))).
 assert(Hopcode:execObserved(funcdef_0__readNat(fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations))).
 { unfold op. eapply(CommandInput.generated_pending s (fun _=>false)(fun _=>0) 22 digit digits sep0 (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)) observations);try eassumption;unfold maximum;lia. }
 assert(Hopmeta:(17<length(memory op arraydef_0__meta))%nat) by (unfold op;rewrite CommandInput.parsed_meta_length;exact Hmeta).
 assert(Hoptoken:(1024<=length(memory op arraydef_0__token))%nat) by (unfold op;rewrite CommandArgs.pending_token_length;exact Htoken).
 assert(Hoppending:meta_value op 15=0) by (unfold op;apply CommandArgs.pending_cleared;exact Hmeta).
 assert(Hopvalid:meta_value op 14=1) by (unfold op;apply CommandInput.parsed_valid;exact Hmeta).
 assert(Hopnumber:meta_value op 11=22) by (unfold op;change(meta_value(CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)))11=Z.of_nat 22);apply CommandInput.parsed_number;try assumption;unfold maximum;lia).
 assert(Hoperror:meta_value op 8=0) by (unfold op;rewrite CommandInput.parsed_meta_other by lia;exact Herror).
 assert(Hopin:stdin op=(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input))) by reflexivity.
 assert(Hopout:stdout op=stdout s) by (unfold op;apply CommandInput.parsed_output).
 pose proof(NativeValidNumericReader.generated op (fun _=>false)(fun _=>0) value1 space1 sep1 (space2++decimalBytes value2++sep2::input) observations
   Hopmeta Hoptoken Hoppending Hoperror Hvalue1 Hsep1 Hspace1 Hopin) as Hreader1.
 set(p1:=DecimalInput.encoded_result op value1 (space2++decimalBytes value2++sep2::input)) in Hreader1.
 destruct Hreader1 as (Hread1 & Hp1meta & Hp1token & Hp1pending & Hp1error & Hp1valid & Hp1number & Hp1in & Hp1out).
 pose proof(NativeValidNumericReader.generated p1 (fun _=>false)(fun _=>0) value2 space2 sep2 input observations
   Hp1meta Hp1token Hp1pending Hp1error Hvalue2 Hsep2 Hspace2 Hp1in) as Hreader2.
 set(p2:=DecimalInput.encoded_result p1 value2 input) in Hreader2.
 destruct Hreader2 as (Hread2 & Hp2meta & Hp2token & Hp2pending & Hp2error & Hp2valid & Hp2number & Hp2in & Hp2out).
 assert(Hmodel:NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number(stdin p2))=Some tail) by now rewrite Hp2in.
 assert(Hrange:ByteProtocol.byte_stream(stdin p2)) by now rewrite Hp2in.
 destruct(NativeByteErrorNumericReader.generated p2 (fun _=>false)(fun _=>0) observations tail Hp2meta Hp2token Hp2pending Hp2error Hrange Hmodel)
  as(arg & Harg & Hargmeta & Hargvalid & Hargin & Hargout).
 pose proof(NativeMalformedTagLaterCommand.generated_22_3 s bs ns op p1 (Z.of_nat value1) p2 (Z.of_nat value2) arg (meta_value arg 11) observations
   Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread1 Hp1meta Hp1number Hp1valid Hp1error Hread2 Hp2meta Hp2number Hp2valid Hp2error Harg Hargmeta eq_refl Hargvalid) as Hrun.
 assert(Hout:stdout arg=stdout s) by congruence.
 exists(NativeMalformedTagLaterCommand.final arg). rewrite Hout,Hargin in Hrun. split;[exact Hrun|].
 split;[exact Hargin|]. split;[change(stdout arg++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR);now rewrite Hout|].
 split.
 - unfold NativeMalformedTagLaterCommand.final. apply meta_store_same. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
 - unfold NativeMalformedTagLaterCommand.final. rewrite store_meta_length. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
Qed.
Theorem generated_22_4 s bs ns digit digits sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 input tail observations :
 decimalBytes 22=digit::digits ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=digit+1 -> meta_value s 8=0 -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 Z.of_nat value3<=maximum -> Forall TokenByteExecution.separator space3 -> TokenByteExecution.separator sep3 ->
 stdin s=digits++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))) -> ByteProtocol.byte_stream input ->
 NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 exists final, execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Proof.
 intros Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hinput Hbytes Hbad.
 set(op:=CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input)))).
 assert(Hopcode:execObserved(funcdef_0__readNat(fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations))).
 { unfold op. eapply(CommandInput.generated_pending s (fun _=>false)(fun _=>0) 22 digit digits sep0 (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))) observations);try eassumption;unfold maximum;lia. }
 assert(Hopmeta:(17<length(memory op arraydef_0__meta))%nat) by (unfold op;rewrite CommandInput.parsed_meta_length;exact Hmeta).
 assert(Hoptoken:(1024<=length(memory op arraydef_0__token))%nat) by (unfold op;rewrite CommandArgs.pending_token_length;exact Htoken).
 assert(Hoppending:meta_value op 15=0) by (unfold op;apply CommandArgs.pending_cleared;exact Hmeta).
 assert(Hopvalid:meta_value op 14=1) by (unfold op;apply CommandInput.parsed_valid;exact Hmeta).
 assert(Hopnumber:meta_value op 11=22) by (unfold op;change(meta_value(CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))))11=Z.of_nat 22);apply CommandInput.parsed_number;try assumption;unfold maximum;lia).
 assert(Hoperror:meta_value op 8=0) by (unfold op;rewrite CommandInput.parsed_meta_other by lia;exact Herror).
 assert(Hopin:stdin op=(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input)))) by reflexivity.
 assert(Hopout:stdout op=stdout s) by (unfold op;apply CommandInput.parsed_output).
 pose proof(NativeValidNumericReader.generated op (fun _=>false)(fun _=>0) value1 space1 sep1 (space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input)) observations
   Hopmeta Hoptoken Hoppending Hoperror Hvalue1 Hsep1 Hspace1 Hopin) as Hreader1.
 set(p1:=DecimalInput.encoded_result op value1 (space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))) in Hreader1.
 destruct Hreader1 as (Hread1 & Hp1meta & Hp1token & Hp1pending & Hp1error & Hp1valid & Hp1number & Hp1in & Hp1out).
 pose proof(NativeValidNumericReader.generated p1 (fun _=>false)(fun _=>0) value2 space2 sep2 (space3++decimalBytes value3++sep3::input) observations
   Hp1meta Hp1token Hp1pending Hp1error Hvalue2 Hsep2 Hspace2 Hp1in) as Hreader2.
 set(p2:=DecimalInput.encoded_result p1 value2 (space3++decimalBytes value3++sep3::input)) in Hreader2.
 destruct Hreader2 as (Hread2 & Hp2meta & Hp2token & Hp2pending & Hp2error & Hp2valid & Hp2number & Hp2in & Hp2out).
 pose proof(NativeValidNumericReader.generated p2 (fun _=>false)(fun _=>0) value3 space3 sep3 input observations
   Hp2meta Hp2token Hp2pending Hp2error Hvalue3 Hsep3 Hspace3 Hp2in) as Hreader3.
 set(p3:=DecimalInput.encoded_result p2 value3 input) in Hreader3.
 destruct Hreader3 as (Hread3 & Hp3meta & Hp3token & Hp3pending & Hp3error & Hp3valid & Hp3number & Hp3in & Hp3out).
 assert(Hmodel:NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number(stdin p3))=Some tail) by now rewrite Hp3in.
 assert(Hrange:ByteProtocol.byte_stream(stdin p3)) by now rewrite Hp3in.
 destruct(NativeByteErrorNumericReader.generated p3 (fun _=>false)(fun _=>0) observations tail Hp3meta Hp3token Hp3pending Hp3error Hrange Hmodel)
  as(arg & Harg & Hargmeta & Hargvalid & Hargin & Hargout).
 pose proof(NativeMalformedTagLaterCommand.generated_22_4 s bs ns op p1 (Z.of_nat value1) p2 (Z.of_nat value2) p3 (Z.of_nat value3) arg (meta_value arg 11) observations
   Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread1 Hp1meta Hp1number Hp1valid Hp1error Hread2 Hp2meta Hp2number Hp2valid Hp2error Hread3 Hp3meta Hp3number Hp3valid Hp3error Harg Hargmeta eq_refl Hargvalid) as Hrun.
 assert(Hout:stdout arg=stdout s) by congruence.
 exists(NativeMalformedTagLaterCommand.final arg). rewrite Hout,Hargin in Hrun. split;[exact Hrun|].
 split;[exact Hargin|]. split;[change(stdout arg++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR);now rewrite Hout|].
 split.
 - unfold NativeMalformedTagLaterCommand.final. apply meta_store_same. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
 - unfold NativeMalformedTagLaterCommand.final. rewrite store_meta_length. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
Qed.
Theorem generated_22_5 s bs ns digit digits sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 value4 space4 sep4 input tail observations :
 decimalBytes 22=digit::digits ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=digit+1 -> meta_value s 8=0 -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 Z.of_nat value3<=maximum -> Forall TokenByteExecution.separator space3 -> TokenByteExecution.separator sep3 ->
 Z.of_nat value4<=maximum -> Forall TokenByteExecution.separator space4 -> TokenByteExecution.separator sep4 ->
 stdin s=digits++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input)))) -> ByteProtocol.byte_stream input ->
 NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 exists final, execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Proof.
 intros Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hvalue4 Hspace4 Hsep4 Hinput Hbytes Hbad.
 set(op:=CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input))))).
 assert(Hopcode:execObserved(funcdef_0__readNat(fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations))).
 { unfold op. eapply(CommandInput.generated_pending s (fun _=>false)(fun _=>0) 22 digit digits sep0 (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input)))) observations);try eassumption;unfold maximum;lia. }
 assert(Hopmeta:(17<length(memory op arraydef_0__meta))%nat) by (unfold op;rewrite CommandInput.parsed_meta_length;exact Hmeta).
 assert(Hoptoken:(1024<=length(memory op arraydef_0__token))%nat) by (unfold op;rewrite CommandArgs.pending_token_length;exact Htoken).
 assert(Hoppending:meta_value op 15=0) by (unfold op;apply CommandArgs.pending_cleared;exact Hmeta).
 assert(Hopvalid:meta_value op 14=1) by (unfold op;apply CommandInput.parsed_valid;exact Hmeta).
 assert(Hopnumber:meta_value op 11=22) by (unfold op;change(meta_value(CommandInput.parsed s digit digits (space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input)))))11=Z.of_nat 22);apply CommandInput.parsed_number;try assumption;unfold maximum;lia).
 assert(Hoperror:meta_value op 8=0) by (unfold op;rewrite CommandInput.parsed_meta_other by lia;exact Herror).
 assert(Hopin:stdin op=(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input))))) by reflexivity.
 assert(Hopout:stdout op=stdout s) by (unfold op;apply CommandInput.parsed_output).
 pose proof(NativeValidNumericReader.generated op (fun _=>false)(fun _=>0) value1 space1 sep1 (space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input))) observations
   Hopmeta Hoptoken Hoppending Hoperror Hvalue1 Hsep1 Hspace1 Hopin) as Hreader1.
 set(p1:=DecimalInput.encoded_result op value1 (space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input)))) in Hreader1.
 destruct Hreader1 as (Hread1 & Hp1meta & Hp1token & Hp1pending & Hp1error & Hp1valid & Hp1number & Hp1in & Hp1out).
 pose proof(NativeValidNumericReader.generated p1 (fun _=>false)(fun _=>0) value2 space2 sep2 (space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input)) observations
   Hp1meta Hp1token Hp1pending Hp1error Hvalue2 Hsep2 Hspace2 Hp1in) as Hreader2.
 set(p2:=DecimalInput.encoded_result p1 value2 (space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input))) in Hreader2.
 destruct Hreader2 as (Hread2 & Hp2meta & Hp2token & Hp2pending & Hp2error & Hp2valid & Hp2number & Hp2in & Hp2out).
 pose proof(NativeValidNumericReader.generated p2 (fun _=>false)(fun _=>0) value3 space3 sep3 (space4++decimalBytes value4++sep4::input) observations
   Hp2meta Hp2token Hp2pending Hp2error Hvalue3 Hsep3 Hspace3 Hp2in) as Hreader3.
 set(p3:=DecimalInput.encoded_result p2 value3 (space4++decimalBytes value4++sep4::input)) in Hreader3.
 destruct Hreader3 as (Hread3 & Hp3meta & Hp3token & Hp3pending & Hp3error & Hp3valid & Hp3number & Hp3in & Hp3out).
 pose proof(NativeValidNumericReader.generated p3 (fun _=>false)(fun _=>0) value4 space4 sep4 input observations
   Hp3meta Hp3token Hp3pending Hp3error Hvalue4 Hsep4 Hspace4 Hp3in) as Hreader4.
 set(p4:=DecimalInput.encoded_result p3 value4 input) in Hreader4.
 destruct Hreader4 as (Hread4 & Hp4meta & Hp4token & Hp4pending & Hp4error & Hp4valid & Hp4number & Hp4in & Hp4out).
 assert(Hmodel:NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number(stdin p4))=Some tail) by now rewrite Hp4in.
 assert(Hrange:ByteProtocol.byte_stream(stdin p4)) by now rewrite Hp4in.
 destruct(NativeByteErrorNumericReader.generated p4 (fun _=>false)(fun _=>0) observations tail Hp4meta Hp4token Hp4pending Hp4error Hrange Hmodel)
  as(arg & Harg & Hargmeta & Hargvalid & Hargin & Hargout).
 pose proof(NativeMalformedTagLaterCommand.generated_22_5 s bs ns op p1 (Z.of_nat value1) p2 (Z.of_nat value2) p3 (Z.of_nat value3) p4 (Z.of_nat value4) arg (meta_value arg 11) observations
   Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hread1 Hp1meta Hp1number Hp1valid Hp1error Hread2 Hp2meta Hp2number Hp2valid Hp2error Hread3 Hp3meta Hp3number Hp3valid Hp3error Hread4 Hp4meta Hp4number Hp4valid Hp4error Harg Hargmeta eq_refl Hargvalid) as Hrun.
 assert(Hout:stdout arg=stdout s) by congruence.
 exists(NativeMalformedTagLaterCommand.final arg). rewrite Hout,Hargin in Hrun. split;[exact Hrun|].
 split;[exact Hargin|]. split;[change(stdout arg++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR);now rewrite Hout|].
 split.
 - unfold NativeMalformedTagLaterCommand.final. apply meta_store_same. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
 - unfold NativeMalformedTagLaterCommand.final. rewrite store_meta_length. cbn [memory withOutput]. unfold NativeMalformedTagLaterCommand.failed. rewrite store_meta_length. lia.
Qed.
End NativeTagLaterByteErrorCommand.
