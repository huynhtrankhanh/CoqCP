From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ReadNatInvalid ReadNatOverflow NativeByteNumber NativeByteBadDigit NativeByteOverflowEOF NativeByteReadNumber ReadTokenPendingLeading NativePendingSeparatorTooLong NativeMissingNumberEOF NativePendingWhitespaceEOF ByteLexErrors ByteLexDecompose NativePendingSeparatorEOF NativePendingSeparatorTokenInfo.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativePendingSeparatorNumber.
Import IndexExecution SipHashExecution ReadTokenExecution NativeByteReadNumber.
Theorem token_run native bs ns ch chars prefix sep tail observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> 0<=ch<256 -> TokenByteExecution.separator ch -> (0<length chars<=1024)%nat ->
 Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars ->
 Forall TokenByteExecution.separator prefix -> TokenByteExecution.separator sep ->
 stdin native=prefix++chars++sep::tail ->
 exists after,execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 reports (match ByteProtocol.decode_number chars with
  | ByteProtocol.number value=>ByteProtocol.number_token value tail false
  | ByteProtocol.number_error_result error=>ByteProtocol.number_invalid error tail false end) after.
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hchsep Hlength Hbytes Hprefix Hsep Hinput.
 destruct(NativePendingSeparatorTokenInfo.generated native ch chars prefix sep tail Hmeta Htoken Hpending Herror Hch Hchsep Hlength Hbytes Hprefix Hsep Hinput)
  as(Hreader & Htargetmeta & Hvalid & Hcount & Hcapacity & Hentries & Hclear & Htail).
 set(target:=ReadTokenPendingLeading.pending_separator_result native chars tail) in *.
 destruct(ByteProtocol.decode_number chars) as [value|reason] eqn:Hdecode.
 - pose proof(NativeByteNumber.decode_ascii chars value Hdecode) as Hdigits.
   destruct(ByteProtocol.decode_number_value chars value Hdecode) as [_ Hvalue].
   pose proof(ByteProtocol.decode_number_bounded chars value Hdecode) as Hbounded.
   assert(Hnumber:value=ReadNatExecution.number_from 0 chars) by (rewrite NativeByteNumber.number_from_fold;exact Hvalue).
   set(after:=ReadNatExecution.token_number target chars).
   assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
   { unfold after. apply(ReadNatExecution.generated_readNat_from_token native bs ns target chars);try assumption.
     rewrite <-Hnumber. unfold ByteProtocol.maximum,IndexExecution.maximum in *. lia. }
   exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. cbn [reports].
   unfold after,ReadNatExecution.token_number. split.
   + rewrite meta_store_other by lia. exact Hvalid.
   + split;[rewrite meta_store_same by lia;now symmetry|]. split;[rewrite meta_store_other by lia;exact Hclear|exact Htail].
 - assert(Hnonempty:chars<>[]) by (destruct chars;[cbn in Hlength;lia|discriminate]).
   destruct reason.
   + destruct(NativeByteBadDigit.decode_bad_prefix chars Hdecode Hnonempty) as(pre & bad & post & Hchars & Hdigits & Hbound & Hbad).
     assert(Hbadbyte:0<=bad<256).
     { subst chars. apply Forall_forall with (x:=bad) in Hbytes;[tauto|]. apply list_elem_of_In,in_or_app. right. now left. }
     set(after:=store_meta(store_meta target 14 0)11(ReadNatExecution.number_from 0 pre)).
     assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
     { unfold after. rewrite Hchars in Hcount,Hcapacity,Hentries.
       exact(ReadNatInvalid.generated_readNat_nondigit native bs ns target pre bad post Hreader Htargetmeta Hvalid Hcount Hcapacity Hentries Hdigits Hbound Hbadbyte Hbad). }
     exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. cbn [reports].
     unfold after. split;[rewrite meta_store_other by lia;apply meta_store_same;lia|]. split.
     * rewrite !meta_store_other by lia. exact Hclear.
     * exact Htail.
   + destruct(NativeByteOverflowEOF.decode_overflow_prefix chars Hdecode Hnonempty) as(pre & bad & post & Hchars & Hdigits & Hbound & Hbad & Hoverflow).
     set(after:=store_meta(store_meta target 14 0)11(ReadNatExecution.number_from 0 pre)).
     assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
     { unfold after. rewrite Hchars in Hcount,Hcapacity,Hentries.
       exact(ReadNatOverflow.generated_readNat_overflow native bs ns target pre bad post Hreader Htargetmeta Hvalid Hcount Hcapacity Hentries Hdigits Hbound Hbad Hoverflow). }
     exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. cbn [reports].
     unfold after. split;[rewrite meta_store_other by lia;apply meta_store_same;lia|]. split.
     * rewrite !meta_store_other by lia. exact Hclear.
     * exact Htail.
Qed.
Theorem token_run_eof native bs ns ch chars prefix observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> 0<=ch<256 -> TokenByteExecution.separator ch -> (0<length chars<=1024)%nat ->
 Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars ->
 Forall TokenByteExecution.separator prefix -> stdin native=prefix++chars ->
 exists after,execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 reports (match ByteProtocol.decode_number chars with
  | ByteProtocol.number value=>ByteProtocol.number_token value [] true
  | ByteProtocol.number_error_result error=>ByteProtocol.number_invalid error [] true end) after.
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hchsep Hlength Hbytes Hprefix Hinput.
 destruct(NativePendingSeparatorTokenInfo.generated_eof native ch chars prefix Hmeta Htoken Hpending Herror Hch Hchsep Hlength Hbytes Hprefix Hinput)
  as(Hreader & Htargetmeta & Hvalid & Hcount & Hcapacity & Hentries & Hclear & Htail).
 set(target:=NativePendingSeparatorEOF.eof_result native chars) in *.
 destruct(ByteProtocol.decode_number chars) as [value|reason] eqn:Hdecode.
 - pose proof(NativeByteNumber.decode_ascii chars value Hdecode) as Hdigits.
   destruct(ByteProtocol.decode_number_value chars value Hdecode) as [_ Hvalue].
   pose proof(ByteProtocol.decode_number_bounded chars value Hdecode) as Hbounded.
   assert(Hnumber:value=ReadNatExecution.number_from 0 chars) by (rewrite NativeByteNumber.number_from_fold;exact Hvalue).
   set(after:=ReadNatExecution.token_number target chars).
   assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
   { unfold after. apply(ReadNatExecution.generated_readNat_from_token native bs ns target chars);try assumption.
     rewrite <-Hnumber. unfold ByteProtocol.maximum,IndexExecution.maximum in *. lia. }
   exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. cbn [reports].
   unfold after,ReadNatExecution.token_number. split.
   + rewrite meta_store_other by lia. exact Hvalid.
   + split;[rewrite meta_store_same by lia;now symmetry|]. split;[rewrite meta_store_other by lia;exact Hclear|exact Htail].
 - assert(Hnonempty:chars<>[]) by (destruct chars;[cbn in Hlength;lia|discriminate]).
   destruct reason.
   + destruct(NativeByteBadDigit.decode_bad_prefix chars Hdecode Hnonempty) as(pre & bad & post & Hchars & Hdigits & Hbound & Hbad).
     assert(Hbadbyte:0<=bad<256).
     { subst chars. apply Forall_forall with (x:=bad) in Hbytes;[tauto|]. apply list_elem_of_In,in_or_app. right. now left. }
     set(after:=store_meta(store_meta target 14 0)11(ReadNatExecution.number_from 0 pre)).
     assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
     { unfold after. rewrite Hchars in Hcount,Hcapacity,Hentries.
       exact(ReadNatInvalid.generated_readNat_nondigit native bs ns target pre bad post Hreader Htargetmeta Hvalid Hcount Hcapacity Hentries Hdigits Hbound Hbadbyte Hbad). }
     exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. cbn [reports].
     unfold after. split;[rewrite meta_store_other by lia;apply meta_store_same;lia|]. split.
     * rewrite !meta_store_other by lia. exact Hclear.
     * exact Htail.
   + destruct(NativeByteOverflowEOF.decode_overflow_prefix chars Hdecode Hnonempty) as(pre & bad & post & Hchars & Hdigits & Hbound & Hbad & Hoverflow).
     set(after:=store_meta(store_meta target 14 0)11(ReadNatExecution.number_from 0 pre)).
     assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
     { unfold after. rewrite Hchars in Hcount,Hcapacity,Hentries.
       exact(ReadNatOverflow.generated_readNat_overflow native bs ns target pre bad post Hreader Htargetmeta Hvalid Hcount Hcapacity Hentries Hdigits Hbound Hbad Hoverflow). }
     exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. cbn [reports].
     unfold after. split;[rewrite meta_store_other by lia;apply meta_store_same;lia|]. split.
     * rewrite !meta_store_other by lia. exact Hclear.
     * exact Htail.
Qed.
Theorem too_long native bs ns initial prefix chars ch tail observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=initial+1 -> meta_value native 8=0 -> 0<=initial<256 -> TokenByteExecution.separator initial -> length chars=1024%nat ->
 Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars -> 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 Forall TokenByteExecution.separator prefix -> stdin native=prefix++chars++ch::tail ->
 exists after,execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 meta_value after 14=0 /\ meta_value after 8=1 /\ stdin after=tail.
Proof.
 intros Hmeta Htoken Hpending Herror Hinitial Hsep Hlength Hbytes Hch Hnosep Hprefix Hinput.
 set(tokenstate:=NativePendingSeparatorTooLong.result native chars tail).
 assert(Hreader:exec(funcdef_0__readToken (fun _=>false)(fun _=>0))native=Some(tt,tokenstate)).
 { unfold tokenstate. exact(NativePendingSeparatorTooLong.generated_readToken native (fun _=>false)(fun _=>0) initial prefix chars ch tail Hmeta Htoken Hpending Herror Hinitial Hsep Hlength Hbytes Hch Hnosep Hprefix Hinput). }
 assert(Hstate_meta:(17<length(memory tokenstate arraydef_0__meta))%nat).
 { unfold tokenstate,NativePendingSeparatorTooLong.result. change(17<length(memory(store_meta(put_many(ReadTokenPendingLeading.pending_base native)0 chars)8 (1%Z))arraydef_0__meta))%nat.
   rewrite store_meta_length,put_many_meta_length,ReadTokenPendingLeading.pending_base_length. exact Hmeta. }
 assert(Hvalid:meta_value tokenstate 14=0).
 { unfold tokenstate,NativePendingSeparatorTooLong.result. change(meta_value(store_meta(put_many(ReadTokenPendingLeading.pending_base native)0 chars)8 1)14=0).
   rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. rewrite ReadTokenPendingLeading.pending_base_meta by (try exact Hmeta;lia). reflexivity. }
 assert(Hfatal:meta_value tokenstate 8=1).
 { unfold tokenstate,NativePendingSeparatorTooLong.result. change(meta_value(store_meta(put_many(ReadTokenPendingLeading.pending_base native)0 chars)8 1)8=1).
   apply meta_store_same. rewrite put_many_meta_length,ReadTokenPendingLeading.pending_base_length. lia. }
 set(after:=store_meta tokenstate 11 0).
 assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
 { unfold funcdef_0__readNat. rewrite exec_eliminate,ReadNatExecution.actual_body.
   rewrite(NativeMissingNumberEOF.invalid_composition funcdef_0__readToken ReadNatExecution.digit_loop {|machine:=native;bools:=bs;nums:=ns|} tokenstate Hreader ltac:(lia) Hvalid). reflexivity. }
 exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. split.
 - unfold after. now rewrite meta_store_other by lia.
 - split.
   + unfold after. now rewrite meta_store_other by lia.
   + reflexivity.
Qed.
Theorem generated native bs ns ch observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> 0<=ch<256 -> TokenByteExecution.separator ch -> ByteProtocol.byte_stream(stdin native) ->
 exists after,execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 reports (ByteProtocol.read_number(stdin native)) after.
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hchsep Hrange.
 destruct(ByteProtocol.read_token(stdin native)) as [|chars tail ended|tail] eqn:Hlex.
 - assert(Hprefix:Forall TokenByteExecution.separator (stdin native)).
   { apply separators. now apply ByteLexErrors.missing. }
   destruct(NativePendingWhitespaceEOF.generated_number native bs ns ch (stdin native) observations
      Hmeta Htoken Hpending Herror Hch Hchsep Hprefix eq_refl) as(Hrun & Hinvalid & Hvalue & _ & _ & _ & Hin & _).
   set(after:=NativePendingWhitespaceEOF.number_result native) in *.
   exists after. split;[exact Hrun|]. unfold ByteProtocol.read_number. rewrite Hlex. cbn [reports]. split;assumption.
 - destruct(ByteLexDecompose.token (stdin native) chars tail ended Hlex)
    as(prefix & payload & Hprefix & Hchars & Hnosep & Hnonempty & Hending). subst payload.
   assert(Hprefix':Forall TokenByteExecution.separator prefix) by now apply separators.
   destruct(ByteProtocol.read_token_valid _ _ _ _ Hlex) as [_ Hlength].
   assert(Hlength':(0<length chars<=1024)%nat) by (split;[destruct chars;[contradiction|cbn;lia]|exact Hlength]).
   destruct Hending as [[Hended [Htail Hinput]]|[Hended [sep [Hsep Hinput]]]].
   + subst ended tail.
     assert(Hbody:Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars).
     { apply(body_bytes prefix chars []);[|exact Hnosep]. rewrite app_nil_r. now rewrite <-Hinput. }
     destruct(token_run_eof native bs ns ch chars prefix observations Hmeta Htoken Hpending Herror Hch Hchsep Hlength' Hbody Hprefix' Hinput) as(after & Hrun & Hreport).
     exists after. split;[exact Hrun|]. unfold ByteProtocol.read_number. rewrite Hlex.
     destruct(ByteProtocol.decode_number chars);exact Hreport.
   + subst ended. apply ByteProtocol.separator_spec in Hsep.
     assert(Hbody:Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars).
     { apply(body_bytes prefix chars (sep::tail));[|exact Hnosep]. now rewrite <-Hinput. }
     destruct(token_run native bs ns ch chars prefix sep tail observations Hmeta Htoken Hpending Herror Hch Hchsep Hlength' Hbody Hprefix' Hsep Hinput) as(after & Hrun & Hreport).
     exists after. split;[exact Hrun|]. unfold ByteProtocol.read_number. rewrite Hlex.
     destruct(ByteProtocol.decode_number chars);exact Hreport.
 - destruct(ByteLexErrors.too_long (stdin native) tail Hlex) as(prefix & chars & bad & Hinput & Hprefix & Hlength & Hnosep & Hbad).
   assert(Hprefix':Forall TokenByteExecution.separator prefix) by now apply separators.
   assert(Hbody:Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars).
   { apply(body_bytes prefix chars (bad::tail));[|exact Hnosep]. now rewrite <-Hinput. }
   assert(Hbadbyte:0<=bad<256).
   { unfold ByteProtocol.byte_stream in Hrange. rewrite Hinput,!Forall_app in Hrange.
     destruct Hrange as [Hfirst [Hsecond Hlast]]. inversion Hlast;assumption. }
   assert(Hbadsep:~TokenByteExecution.separator bad).
   { intro Hseparator. apply ByteProtocol.separator_spec in Hseparator. congruence. }
   destruct(too_long native bs ns ch prefix chars bad tail observations Hmeta Htoken Hpending Herror Hch Hchsep
      Hlength Hbody Hbadbyte Hbadsep Hprefix' Hinput) as(after & Hrun & Hinvalid & Hfatal & Hin).
   exists after. split;[exact Hrun|]. unfold ByteProtocol.read_number. rewrite Hlex. cbn [reports]. repeat split;assumption.
Qed.
Theorem generated_with_pending native bs ns ch observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> 0<=ch<256 -> TokenByteExecution.separator ch ->
 ByteProtocol.byte_stream(stdin native) ->
 exists after,execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 reports (ByteProtocol.read_number(ch::stdin native)) after.
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hsep Hstream.
 destruct(generated native bs ns ch observations Hmeta Htoken Hpending Herror Hch Hsep Hstream) as(after & Hrun & Hreports).
 exists after. split;[exact Hrun|].
 assert(Hsep':ByteProtocol.separator ch=true) by (apply ByteProtocol.separator_spec;exact Hsep).
 unfold ByteProtocol.read_number, ByteProtocol.read_token. cbn [ByteProtocol.scan_token]. rewrite Hsep'. exact Hreports.
Qed.
End NativePendingSeparatorNumber.
