From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadNat DecimalInput CommandArgs NativeArgumentWhitespace.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeValidNumericReader.
Import IndexExecution SipHashExecution.
Theorem generated s bs ns value prefix sep tail observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 -> Z.of_nat value<=maximum ->
 TokenByteExecution.separator sep -> Forall TokenByteExecution.separator prefix ->
 stdin s=prefix++decimalBytes value++sep::tail ->
 let after:=DecimalInput.encoded_result s value tail in
 execObserved(funcdef_0__readNat bs ns)(s,observations)=Some(tt,(after,observations)) /\
 (17<length(memory after arraydef_0__meta))%nat /\ (1024<=length(memory after arraydef_0__token))%nat /\
 meta_value after 15=0 /\ meta_value after 8=0 /\ meta_value after 14=1 /\ meta_value after 11=Z.of_nat value /\
 stdin after=tail /\ stdout after=stdout s.
Proof.
 intros Hmeta Htoken Hpending Herror Hvalue Hsep Hprefix Hinput. cbn zeta.
 pose proof(NativeArgumentWhitespace.read s bs ns value prefix sep tail observations Hmeta Htoken Hpending Herror Hvalue Hsep Hprefix) as Hrun.
 rewrite <-Hinput in Hrun. destruct s as [arrays input output];cbn [withInput stdin] in Hrun|-*.
 split;[exact Hrun|].
 split;[now rewrite DecimalInput.encoded_meta_length|]. split;[now rewrite DecimalInput.encoded_token_length|].
 split;[rewrite DecimalInput.encoded_meta_other by (try exact Hmeta;lia);exact Hpending|].
 split;[rewrite DecimalInput.encoded_meta_other by (try exact Hmeta;lia);exact Herror|].
 split;[now apply CommandArgs.encoded_valid|].
 exact(DecimalInput.encoded_result_correct {|memory:=arrays;stdin:=input;stdout:=output|} value tail Hmeta Hvalue).
Qed.
End NativeValidNumericReader.
