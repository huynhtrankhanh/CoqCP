From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash ReadNat ReadNatOverflow ReadToken TokenByte NativeByteOverflowEOF.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeByteOverflow.
Import IndexExecution SipHashExecution.
Theorem generated_bad_number native bs ns chars sep tail observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 ->
 ByteProtocol.read_token (chars++sep::tail)=ByteProtocol.token chars tail false ->
 ByteProtocol.decode_number chars=ByteProtocol.number_error_result ByteProtocol.overflow ->
 Forall(fun byte=>0<=byte<256 /\ ~TokenByteExecution.separator byte)chars ->
 TokenByteExecution.separator sep -> stdin native=chars++sep::tail ->
 exists prefix bad suffix after,
 chars=prefix++bad::suffix /\
 execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 meta_value after 14=0 /\ stdin after=tail.
Proof.
 intros Hmeta Htoken Hpending Herror Hlex Hdecode Hbytes Hsep Hinput.
 destruct(ByteProtocol.read_token_valid _ _ _ _ Hlex) as [Hnonempty Hlength].
 destruct(NativeByteOverflowEOF.decode_overflow_prefix chars Hdecode Hnonempty) as(prefix & bad & suffix & Hchars & Hprefix & Hbound & Hbad & Hoverflow).
 subst chars. set(result:=store_meta(store_meta(ReadTokenExecution.read_result native (prefix++bad::suffix) tail)14 0)11(ReadNatExecution.number_from 0 prefix)).
 assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,result)).
 { unfold result. exact(ReadNatOverflow.generated_overflow_token native bs ns prefix bad suffix sep tail Hmeta Htoken Hpending Herror Hlength Hbytes Hsep Hinput Hprefix Hbound Hbad Hoverflow). }
 exists prefix,bad,suffix,result. split;[reflexivity|]. split.
 - exact(ReadNatExecution.generated_readNat_observed native bs ns result observations Hrun).
 - split.
   + unfold result. rewrite meta_store_other by lia. apply meta_store_same.
     rewrite ReadTokenExecution.result_meta_length. lia.
   + reflexivity.
Qed.
End NativeByteOverflow.
