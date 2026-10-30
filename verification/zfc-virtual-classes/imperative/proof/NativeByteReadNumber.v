From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat ReadNatInvalid ReadNatOverflow NativeByteNumber NativeByteBadDigit NativeByteOverflowEOF NativeByteTokenInfo ByteLexDecompose ByteLexErrors NativeReadTokenLeadingMissing NativeTooLongLeadingNumber.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeByteReadNumber.
Import IndexExecution SipHashExecution.
Definition reports result after := match result with
 | ByteProtocol.number_missing=>meta_value after 14=0 /\ stdin after=[]
 | ByteProtocol.number_too_long tail=>meta_value after 14=0 /\ meta_value after 8=1 /\ stdin after=tail
 | ByteProtocol.number_invalid _ tail _=>meta_value after 14=0 /\ meta_value after 8=0 /\ stdin after=tail
 | ByteProtocol.number_token value tail _=>meta_value after 14<>0 /\ meta_value after 11=value /\ meta_value after 8=0 /\ stdin after=tail
 end.
Lemma separators prefix : Forall(fun ch=>ByteProtocol.separator ch=true)prefix -> Forall TokenByteExecution.separator prefix.
Proof.
 intro H. induction H as [|ch tail Hch Htail IH];[constructor|]. constructor;[|exact IH].
 apply ByteProtocol.separator_spec in Hch. exact Hch.
Qed.
Lemma body_bytes prefix chars suffix : ByteProtocol.byte_stream(prefix++chars++suffix) ->
 Forall(fun ch=>ByteProtocol.separator ch=false)chars ->
 Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars.
Proof.
 unfold ByteProtocol.byte_stream. intro Hrange. rewrite !Forall_app in Hrange.
 destruct Hrange as [Hprefix [Hchars Hsuffix]]. intro Hnot.
 induction Hchars as [|ch tail Hch Hrest IH] in Hnot|-*;[constructor|].
 inversion Hnot as [|ch' tail' Hsep Hnottail];subst ch' tail'. constructor;[|now apply IH].
 split;[exact Hch|]. intro Hseparator. apply ByteProtocol.separator_spec in Hseparator. congruence.
Qed.
Theorem token_run native bs ns chars prefix sep tail (ended:bool) observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> (0<length chars<=1024)%nat ->
 Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars ->
 Forall TokenByteExecution.separator prefix -> TokenByteExecution.separator sep ->
 (if ended then stdin native=prefix++chars /\ tail=[] else stdin native=prefix++chars++sep::tail) ->
 exists after,execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 reports (match ByteProtocol.decode_number chars with
  | ByteProtocol.number value=>ByteProtocol.number_token value tail ended
  | ByteProtocol.number_error_result error=>ByteProtocol.number_invalid error tail ended end) after.
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hprefix Hsep Hinput.
 destruct(NativeByteTokenInfo.generated native chars prefix sep tail ended Hmeta Htoken Hpending Herror Hlength Hbytes Hprefix Hsep Hinput)
  as(Hreader & Htargetmeta & Hvalid & Hcount & Hcapacity & Hentries & Hclear & Htail).
 set(target:=NativeByteTokenInfo.state native chars sep tail ended) in *.
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
(** Complete native readNat refinement of ByteProtocol.read_number for any
    byte stream, with the natural finite-buffer and clean-reader premises. *)
Theorem generated native bs ns observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> ByteProtocol.byte_stream(stdin native) ->
 exists after,execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 reports (ByteProtocol.read_number(stdin native)) after.
Proof.
 intros Hmeta Htoken Hpending Herror Hrange.
 destruct(ByteProtocol.read_token(stdin native)) as [|chars tail ended|tail] eqn:Hlex.
 - assert(Hprefix:Forall TokenByteExecution.separator (stdin native)).
   { apply separators. now apply ByteLexErrors.missing. }
   destruct(NativeReadTokenLeadingMissing.generated_number native bs ns (stdin native) observations
      Hmeta Htoken Hpending Herror Hprefix eq_refl) as(after & Hrun & Hinvalid & Hvalue & Hin).
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
     destruct(token_run native bs ns chars prefix 32 [] true observations Hmeta Htoken Hpending Herror Hlength' Hbody Hprefix'
       ltac:(unfold TokenByteExecution.separator;tauto) ltac:(cbn;split;[exact Hinput|reflexivity])) as(after & Hrun & Hreport).
     exists after. split;[exact Hrun|]. unfold ByteProtocol.read_number. rewrite Hlex.
     destruct(ByteProtocol.decode_number chars);exact Hreport.
   + subst ended. apply ByteProtocol.separator_spec in Hsep.
     assert(Hbody:Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars).
     { apply(body_bytes prefix chars (sep::tail));[|exact Hnosep]. now rewrite <-Hinput. }
     destruct(token_run native bs ns chars prefix sep tail false observations Hmeta Htoken Hpending Herror Hlength' Hbody Hprefix' Hsep Hinput) as(after & Hrun & Hreport).
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
   destruct(NativeTooLongLeadingNumber.generated_number native bs ns prefix chars bad tail observations Hmeta Htoken Hpending Herror
      Hlength Hbody Hbadbyte Hbadsep Hprefix' Hinput) as(after & Hrun & Hinvalid & Hfatal & Hin).
   exists after. split;[exact Hrun|]. unfold ByteProtocol.read_number. rewrite Hlex. cbn [reports]. repeat split;assumption.
Qed.
End NativeByteReadNumber.
