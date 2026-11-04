From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte ByteLexDecompose NativeByteReadNumber NativeValidByteNumericReader.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeValidByteModelReader.
Import IndexExecution SipHashExecution.
Theorem generated s bs ns value tail ended observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 -> ByteProtocol.byte_stream(stdin s) ->
 ByteProtocol.read_number(stdin s)=ByteProtocol.number_token value tail ended ->
 exists after, execObserved(funcdef_0__readNat bs ns)(s,observations)=Some(tt,(after,observations)) /\
 (17<length(memory after arraydef_0__meta))%nat /\ (1024<=length(memory after arraydef_0__token))%nat /\
 meta_value after 15=0 /\ meta_value after 8=0 /\ meta_value after 14=1 /\ meta_value after 11=value /\
 stdin after=tail /\ stdout after=stdout s.
Proof.
 intros Hmeta Htoken Hpending Herror Hrange Hnumber.
 set(input:=stdin s) in *.
 unfold ByteProtocol.read_number in Hnumber.
 destruct(ByteProtocol.read_token input) as [|chars remaining eof|remaining] eqn:Hlex;try discriminate.
 destruct(ByteProtocol.decode_number chars) as [decoded|reason] eqn:Hdecode;try discriminate.
 inversion Hnumber;subst decoded remaining eof.
 destruct(ByteLexDecompose.token input chars tail ended Hlex)
  as(prefix & payload & Hprefix & Hchars & Hnosep & Hnonempty & Hending). subst payload.
 pose proof(ByteProtocol.read_token_valid _ _ _ _ Hlex) as [_ Hlength].
 assert(Hlength':(0<length chars<=1024)%nat) by (split;[destruct chars;[contradiction|cbn;lia]|exact Hlength]).
 apply NativeByteReadNumber.separators in Hprefix.
 destruct Hending as [[Hended [Htail Hinput]]|[Hended [sep [Hsep Hinput]]]].
 - subst ended tail.
   assert(Hbody:Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars).
   { apply(NativeByteReadNumber.body_bytes prefix chars []);[|exact Hnosep]. rewrite app_nil_r. now rewrite <-Hinput. }
   exact(NativeValidByteNumericReader.generated s bs ns chars prefix 32 [] true value observations
     Hmeta Htoken Hpending Herror Hlength' Hbody Hprefix ltac:(unfold TokenByteExecution.separator;tauto)
     ltac:(cbn;split;[exact Hinput|reflexivity]) Hdecode).
 - subst ended. apply ByteProtocol.separator_spec in Hsep.
   assert(Hbody:Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars).
   { apply(NativeByteReadNumber.body_bytes prefix chars (sep::tail));[|exact Hnosep]. now rewrite <-Hinput. }
   exact(NativeValidByteNumericReader.generated s bs ns chars prefix sep tail false value observations
     Hmeta Htoken Hpending Herror Hlength' Hbody Hprefix Hsep Hinput Hdecode).
Qed.
End NativeValidByteModelReader.
