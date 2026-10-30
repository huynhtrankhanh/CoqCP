From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat ReadNatInvalid ReadNatOverflow NativeByteNumber NativeByteBadDigit NativeByteOverflowEOF NativeByteReadNumber NativePendingByteTokenInfo ByteLexErrors ByteLexDecompose NativePendingTooLongNat NativePendingTooLong ReadToken.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativePendingByteReadNumber.
Import IndexExecution SipHashExecution.
Import NativeByteReadNumber.
Theorem token_run native bs ns ch chars sep tail (ended:bool) observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 (S(length chars)<=1024)%nat -> Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars -> TokenByteExecution.separator sep ->
 (if ended then stdin native=chars /\ tail=[] else stdin native=chars++sep::tail) ->
 exists after,execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 reports (match ByteProtocol.decode_number (ch::chars) with
  | ByteProtocol.number value=>ByteProtocol.number_token value tail ended
  | ByteProtocol.number_error_result error=>ByteProtocol.number_invalid error tail ended end) after.
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hsep Hinput.
 destruct(NativePendingByteTokenInfo.generated native ch chars sep tail ended Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hsep Hinput)
  as(Hreader & Htargetmeta & Hvalid & Hcount & Hcapacity & Hentries & Hclear & Htail).
 set(target:=NativePendingByteTokenInfo.state native ch chars tail ended) in *.
 destruct(ByteProtocol.decode_number (ch::chars)) as [value|reason] eqn:Hdecode.
 - pose proof(NativeByteNumber.decode_ascii (ch::chars) value Hdecode) as Hdigits.
   destruct(ByteProtocol.decode_number_value (ch::chars) value Hdecode) as [_ Hvalue].
   pose proof(ByteProtocol.decode_number_bounded (ch::chars) value Hdecode) as Hbounded.
   assert(Hnumber:value=ReadNatExecution.number_from 0 (ch::chars)) by (rewrite NativeByteNumber.number_from_fold;exact Hvalue).
   set(after:=ReadNatExecution.token_number target (ch::chars)).
   assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
   { unfold after. apply(ReadNatExecution.generated_readNat_from_token native bs ns target (ch::chars));try assumption.
     rewrite <-Hnumber. unfold ByteProtocol.maximum,IndexExecution.maximum in *. lia. }
   exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. cbn [reports].
   unfold after,ReadNatExecution.token_number. split.
   + rewrite meta_store_other by lia. exact Hvalid.
   + split;[rewrite meta_store_same by lia;now symmetry|]. split;[rewrite meta_store_other by lia;exact Hclear|exact Htail].
 - assert(Hnonempty:ch::chars<>[]) by discriminate.
   destruct reason.
   + destruct(NativeByteBadDigit.decode_bad_prefix (ch::chars) Hdecode Hnonempty) as(pre & bad & post & Hchars & Hdigits & Hbound & Hbad).
     assert(Hbadbyte:0<=bad<256).
     { assert(Hall:Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)(ch::chars)) by (constructor;[split;assumption|exact Hbytes]). rewrite Hchars in Hall. apply Forall_forall with (x:=bad) in Hall;[tauto|]. apply list_elem_of_In,in_or_app. right. now left. }
     set(after:=store_meta(store_meta target 14 0)11(ReadNatExecution.number_from 0 pre)).
     assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
     { unfold after. change (meta_value target 6=Z.of_nat(length(ch::chars))) in Hcount.
       change (length(ch::chars)<=length(memory target arraydef_0__token))%nat in Hcapacity.
       change (forall i,(i<length(ch::chars))%nat -> List.nth i(memory target arraydef_0__token)0=List.nth i(ch::chars)0) in Hentries.
       rewrite Hchars in Hcount,Hcapacity,Hentries.
       exact(ReadNatInvalid.generated_readNat_nondigit native bs ns target pre bad post Hreader Htargetmeta Hvalid Hcount Hcapacity Hentries Hdigits Hbound Hbadbyte Hbad). }
     exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. cbn [reports].
     unfold after. split;[rewrite meta_store_other by lia;apply meta_store_same;lia|]. split.
     * rewrite !meta_store_other by lia. exact Hclear.
     * exact Htail.
   + destruct(NativeByteOverflowEOF.decode_overflow_prefix (ch::chars) Hdecode Hnonempty) as(pre & bad & post & Hchars & Hdigits & Hbound & Hbad & Hoverflow).
     set(after:=store_meta(store_meta target 14 0)11(ReadNatExecution.number_from 0 pre)).
     assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
     { unfold after. change (meta_value target 6=Z.of_nat(length(ch::chars))) in Hcount.
       change (length(ch::chars)<=length(memory target arraydef_0__token))%nat in Hcapacity.
       change (forall i,(i<length(ch::chars))%nat -> List.nth i(memory target arraydef_0__token)0=List.nth i(ch::chars)0) in Hentries.
       rewrite Hchars in Hcount,Hcapacity,Hentries.
       exact(ReadNatOverflow.generated_readNat_overflow native bs ns target pre bad post Hreader Htargetmeta Hvalid Hcount Hcapacity Hentries Hdigits Hbound Hbad Hoverflow). }
     exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. cbn [reports].
     unfold after. split;[rewrite meta_store_other by lia;apply meta_store_same;lia|]. split.
     * rewrite !meta_store_other by lia. exact Hclear.
     * exact Htail.
Qed.
(** Full numeric-reader refinement for a pending, nonseparator first byte.
    The byte model sees the pending byte prepended to the remaining tape. *)
Theorem generated native bs ns ch observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 ByteProtocol.byte_stream(stdin native) ->
 exists after,execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 reports (ByteProtocol.read_number(ch::stdin native)) after.
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hnosep Hrange.
 assert(Hsep:ByteProtocol.separator ch=false).
 { destruct(ByteProtocol.separator ch) eqn:Hvalue;[|reflexivity]. apply ByteProtocol.separator_spec in Hvalue. contradiction. }
 assert(Hlexical:ByteProtocol.read_token(ch::stdin native)=ByteProtocol.scan_token [ch](stdin native)).
 { unfold ByteProtocol.read_token. cbn [ByteProtocol.scan_token]. now rewrite Hsep. }
 destruct(ByteProtocol.read_token(ch::stdin native)) as [|full tail ended|tail] eqn:Hlex.
 - exfalso. symmetry in Hlexical. exact(ByteLexErrors.started_not_missing [ch](stdin native) ltac:(discriminate) Hlexical).
 - assert(Hstarted:ByteProtocol.scan_token [ch](stdin native)=ByteProtocol.token full tail ended) by (symmetry;exact Hlexical).
   destruct(ByteLexDecompose.started_token [ch](stdin native) full tail ended ltac:(discriminate) Hstarted)
    as(chars & Hfull & Hnoseps & Hending). cbn [rev app] in Hfull. subst full.
   destruct(ByteProtocol.read_token_valid _ _ _ _ Hlex) as [_ Hlength]. cbn [length] in Hlength.
   destruct Hending as [[Hended [Htail Hinput]]|[Hended [sep [Hseparator Hinput]]]].
   + subst ended tail.
     assert(Hbytes:Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars).
     { apply(NativeByteReadNumber.body_bytes [] chars []);[|exact Hnoseps]. cbn [app]. rewrite app_nil_r. now rewrite <-Hinput. }
     destruct(token_run native bs ns ch chars 32 [] true observations Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes
      ltac:(unfold TokenByteExecution.separator;tauto) ltac:(cbn;split;[exact Hinput|reflexivity])) as(after & Hrun & Hreport).
     exists after. split;[exact Hrun|]. unfold ByteProtocol.read_number. rewrite Hlex. destruct(ByteProtocol.decode_number(ch::chars));exact Hreport.
   + subst ended. apply ByteProtocol.separator_spec in Hseparator.
     assert(Hbytes:Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars).
     { apply(NativeByteReadNumber.body_bytes [] chars (sep::tail));[|exact Hnoseps]. cbn [app]. now rewrite <-Hinput. }
     destruct(token_run native bs ns ch chars sep tail false observations Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hseparator Hinput) as(after & Hrun & Hreport).
     exists after. split;[exact Hrun|]. unfold ByteProtocol.read_number. rewrite Hlex. destruct(ByteProtocol.decode_number(ch::chars));exact Hreport.
 - assert(Hstarted:ByteProtocol.scan_token [ch](stdin native)=ByteProtocol.token_too_long tail) by (symmetry;exact Hlexical).
   destruct(ByteLexErrors.started_long [ch](stdin native) tail ltac:(discriminate) Hstarted)
    as(chars & extra & Hinput & Hnoseps & Hbad & Hlength).
   cbn [length] in Hlength. assert(Hlen:length chars=1023%nat) by lia.
   assert(Hbytes:Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars).
   { apply(NativeByteReadNumber.body_bytes [] chars (extra::tail));[|exact Hnoseps]. cbn [app]. now rewrite <-Hinput. }
   assert(Hextra:0<=extra<256).
   { unfold ByteProtocol.byte_stream in Hrange. rewrite Hinput,Forall_app in Hrange.
     destruct Hrange as [Hfirst Hlast]. inversion Hlast;assumption. }
   assert(Hbadsep:~TokenByteExecution.separator extra).
   { intro Hseparator. apply ByteProtocol.separator_spec in Hseparator. congruence. }
   set(result:=store_meta(NativePendingTooLong.result native ch chars tail)11 0).
   assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,result)).
   { unfold result. exact(NativePendingTooLongNat.generated native bs ns ch chars extra tail Hmeta Htoken Hpending Herror Hch Hnosep Hlen Hbytes Hextra Hbadsep Hinput). }
   assert(Htargetmeta:(17<length(memory(NativePendingTooLong.result native ch chars tail)arraydef_0__meta))%nat).
   { unfold NativePendingTooLong.result. change(17<length(memory(store_meta(ReadTokenExecution.put_many(ReadTokenExecution.started native ch)1 chars)8 (1%Z))arraydef_0__meta))%nat.
     rewrite store_meta_length,ReadTokenExecution.put_many_meta_length,ReadTokenExecution.started_length. exact Hmeta. }
   exists result. split;[now apply ReadNatExecution.generated_readNat_observed|]. unfold ByteProtocol.read_number. rewrite Hlex. cbn [reports].
   unfold result. split.
   + rewrite meta_store_other by lia. unfold NativePendingTooLong.result.
     change(meta_value(store_meta(ReadTokenExecution.put_many(ReadTokenExecution.started native ch)1 chars)8 1)14=0).
     rewrite meta_store_other by lia. rewrite ReadTokenExecution.put_many_meta_other by lia.
     unfold ReadTokenExecution.started. rewrite meta_store_other by lia. rewrite TokenByteExecution.put_byte_meta_other by lia.
     rewrite ReadTokenExecution.reset_meta by exact Hmeta. reflexivity.
   + split.
     * rewrite meta_store_other by lia. unfold NativePendingTooLong.result.
       change(meta_value(store_meta(ReadTokenExecution.put_many(ReadTokenExecution.started native ch)1 chars)8 1)8=1).
       apply meta_store_same. rewrite ReadTokenExecution.put_many_meta_length,ReadTokenExecution.started_length. lia.
     * reflexivity.
Qed.
End NativePendingByteReadNumber.
