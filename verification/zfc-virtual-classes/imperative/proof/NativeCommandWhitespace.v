From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ReadTokenPendingLeading ReadNatPendingLeading
 NativeCommandReaderCongruence NativeCommandReaderPointwise PendingWhitespaceEquivalence MachinePointwise SeedSeparator.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeCommandWhitespace.
Import IndexExecution SipHashExecution ReadTokenExecution ReadNatExecution.
Definition canonical native digit digits sep tail :=
 store_meta (withInput native (digits++sep::tail)) 15 (digit+1).
Definition spaced native ch prefix digit digits sep tail :=
 store_meta (withInput native (prefix++(digit::digits)++sep::tail)) 15 (ch+1).
Lemma canonical_result_input native input1 input2 digit digits tail :
 pending_result (store_meta(withInput native input1)15(digit+1)) digit digits tail =
 pending_result (store_meta(withInput native input2)15(digit+1)) digit digits tail.
Proof.
 unfold pending_result,started,reset. repeat rewrite SeedSeparator.store_input.
 repeat first [rewrite ReadTokenExecution.put_many_input | rewrite TokenByteExecution.put_byte_input | rewrite SeedSeparator.store_input].
 cbn [withInput]. reflexivity.
Qed.
Theorem generated native bs ns ch prefix digit digits sep tail observations final trace :
 (17<length(memory native arraydef_0__meta))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat -> meta_value native 8=0 ->
 0<=ch<256 -> TokenByteExecution.separator ch -> Forall TokenByteExecution.separator prefix ->
 (S(length digits)<=1024)%nat -> Forall(fun c=>48<=c<=57)(digit::digits) ->
 number_from 0 (digit::digits)<=maximum -> TokenByteExecution.separator sep ->
 execObserved (funcdef_0__command bs ns) (canonical native digit digits sep tail,observations)=Some(tt,(final,trace)) ->
 exists target,execObserved (funcdef_0__command bs ns) (spaced native ch prefix digit digits sep tail,observations)=Some(tt,(target,trace)) /\ MachinePointwise.same final target.
Proof.
 intros Hmeta Htoken Herr Hch Hchsep Hprefix Hlength Hdigits Hvalue Hsep Hrun.
 set (first:=canonical native digit digits sep tail).
 set (second:=spaced native ch prefix digit digits sep tail).
 set (parsed1:=token_number(pending_result first digit digits tail)(digit::digits)).
 set (parsed2:=token_number(ReadTokenPendingLeading.pending_separator_result second (digit::digits) tail)(digit::digits)).
 assert (Hfirst:execObserved NativeCommandReaderCongruence.reader (first,observations)=Some(tt,(parsed1,observations))).
 { apply generated_readNat_observed. unfold parsed1,first,canonical.
   apply generated_readNat_pending with (ch:=digit)(chars:=digits)(sep:=sep).
   - rewrite store_meta_length. exact Hmeta.
   - rewrite store_meta_other by discriminate. exact Htoken.
   - apply meta_store_same. cbn [memory withInput]. lia.
   - rewrite meta_store_other by lia. exact Herr.
   - exact Hlength.
   - exact Hdigits.
   - exact Hvalue.
   - exact Hsep.
   - reflexivity. }
 assert (Hsecond:execObserved NativeCommandReaderCongruence.reader (second,observations)=Some(tt,(parsed2,observations))).
 { apply generated_readNat_observed. unfold parsed2,second,spaced.
   apply ReadNatPendingLeading.generated_readNat_pending_leading with (ch:=ch)(prefix:=prefix)(sep:=sep).
   - rewrite store_meta_length. exact Hmeta.
   - rewrite store_meta_other by discriminate. exact Htoken.
   - apply meta_store_same. cbn [memory withInput]. lia.
   - rewrite meta_store_other by lia. exact Herr.
   - exact Hch.
   - exact Hchsep.
   - cbn [length]. lia.
   - exact Hdigits.
   - exact Hvalue.
   - exact Hsep.
   - exact Hprefix.
   - reflexivity. }
 apply (NativeCommandReaderPointwise.command_same_reader_pointwise bs ns first second parsed1 parsed2 observations final trace Hfirst Hsecond);[|exact Hrun].
 unfold parsed1,parsed2,first,second,canonical,spaced.
 rewrite (canonical_result_input native (digits++sep::tail) (prefix++(digit::digits)++sep::tail) digit digits tail).
 destruct (PendingWhitespaceEquivalence.number_results_same native (prefix++(digit::digits)++sep::tail) ch digit digits tail) as (Hin & Hout & Hmemory).
 split;[symmetry;exact Hin|]. split;[symmetry;exact Hout|]. intro name. symmetry. apply Hmemory.
Qed.
End NativeCommandWhitespace.
