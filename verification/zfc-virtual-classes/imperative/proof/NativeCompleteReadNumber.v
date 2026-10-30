From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte NativeByteReadNumber NativePendingByteReadNumber NativePendingSeparatorNumber.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeCompleteReadNumber.
Import IndexExecution SipHashExecution NativeByteReadNumber.
Theorem generated native bs ns pending observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 8=0 -> ByteProtocol.byte_stream(stdin native) ->
 (match pending with None=>meta_value native 15=0 | Some ch=>meta_value native 15=ch+1 /\ 0<=ch<256 end) ->
 exists after, execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 reports(ByteProtocol.read_number(match pending with None=>stdin native | Some ch=>ch::stdin native end))after.
Proof.
 intros Hmeta Htoken Herror Hbytes Hpending. destruct pending as [ch|].
 - destruct Hpending as [Hpending Hch]. destruct(decide (TokenByteExecution.separator ch)) as [Hsep|Hnonsep].
   + destruct(NativePendingSeparatorNumber.generated native bs ns ch observations Hmeta Htoken Hpending Herror Hch Hsep Hbytes) as(after & Hrun & Hreport).
     exists after. split;[exact Hrun|].
     assert(Hbool:ByteProtocol.separator ch=true) by (apply ByteProtocol.separator_spec;exact Hsep).
     unfold ByteProtocol.read_number,ByteProtocol.read_token in *. cbn [ByteProtocol.scan_token]. rewrite Hbool. exact Hreport.
   + exact(NativePendingByteReadNumber.generated native bs ns ch observations Hmeta Htoken Hpending Herror Hch Hnonsep Hbytes).
 - exact(NativeByteReadNumber.generated native bs ns observations Hmeta Htoken Hpending Herror Hbytes).
Qed.
End NativeCompleteReadNumber.
