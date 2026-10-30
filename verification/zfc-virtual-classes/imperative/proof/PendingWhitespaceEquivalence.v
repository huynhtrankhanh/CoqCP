From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash InternTail TokenByte ReadToken ReadNat ReadTokenPendingLeading MachinePointwise SeedSeparator.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module PendingWhitespaceEquivalence.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution ReadTokenPendingLeading.
Lemma put_byte_meta s size ch :
 memory (put_byte s size ch) arraydef_0__meta = <[6%nat:=Z.of_nat(S size)]> (memory s arraydef_0__meta).
Proof.
 unfold put_byte,store_meta. cbn [memory withMemory]. rewrite modify_meta. change (<[6%nat:=Z.of_nat(S size)]> (modifyArray (memory s) arraydef_0__token size ch arraydef_0__meta)=<[6%nat:=Z.of_nat(S size)]> (memory s arraydef_0__meta)).
 rewrite InternTailExecution.modify_other by discriminate. reflexivity.
Qed.
Lemma store_meta_array s slot value : memory(store_meta s slot value) arraydef_0__meta=<[slot:=value]>(memory s arraydef_0__meta).
Proof. unfold store_meta. cbn [memory withMemory]. apply modify_meta. Qed.
Lemma initial_same native input whitespace digit :
 MachinePointwise.same
  (put_byte(pending_base(store_meta(withInput native input)15(whitespace+1)))0 digit)
  (started (store_meta(withInput native input)15(digit+1)) digit).
Proof.
 split;[reflexivity|]. split;[reflexivity|]. intro watched.
 destruct (decide(watched=arraydef_0__meta)) as [->|Hnotmeta].
 - rewrite put_byte_meta. unfold pending_base,reset,started.
   repeat rewrite store_meta_array. rewrite put_byte_meta. unfold reset. repeat rewrite store_meta_array. cbn [memory withInput].
   rewrite (list_insert_insert_ne _ 6 15) by lia.
   repeat first [rewrite (list_insert_insert_ne _ 15 6) by lia | rewrite (list_insert_insert_ne _ 15 17) by lia | rewrite (list_insert_insert_ne _ 15 14) by lia].
   repeat rewrite list_insert_insert_eq. reflexivity.
 - destruct (decide(watched=arraydef_0__token)) as [->|Hnottoken].
   + unfold started. rewrite store_meta_other by discriminate. rewrite !put_byte_token.
     unfold pending_base,reset. repeat rewrite store_meta_other by discriminate. reflexivity.
   + unfold started. rewrite store_meta_other by exact Hnotmeta.
     unfold put_byte. repeat rewrite store_meta_other by exact Hnotmeta.
     cbn [memory withMemory]. repeat rewrite InternTailExecution.modify_other by exact Hnottoken.
     unfold pending_base,reset. repeat rewrite store_meta_other by exact Hnotmeta. reflexivity.
Qed.

Lemma same_store s t slot value : MachinePointwise.same s t ->
 MachinePointwise.same (store_meta s slot value) (store_meta t slot value).
Proof. intro H. unfold store_meta. now apply MachinePointwise.same_modify. Qed.
Lemma same_put_byte s t size ch : MachinePointwise.same s t -> MachinePointwise.same (put_byte s size ch) (put_byte t size ch).
Proof. intro H. unfold put_byte. apply same_store. now apply MachinePointwise.same_modify. Qed.
Lemma same_put_many s t size chars : MachinePointwise.same s t -> MachinePointwise.same (put_many s size chars) (put_many t size chars).
Proof. induction chars as [|ch chars IH] in s,t,size|-*;intro H;[exact H|]. cbn [put_many]. apply IH. now apply same_put_byte. Qed.
Theorem token_results_same native input whitespace digit digits tail :
 MachinePointwise.same
  (pending_separator_result (store_meta(withInput native input)15(whitespace+1)) (digit::digits) tail)
  (pending_result (store_meta(withInput native input)15(digit+1)) digit digits tail).
Proof.
 unfold pending_separator_result,pending_result. cbn [put_many].
 apply same_store. apply MachinePointwise.same_input. apply same_store. apply same_put_many. apply initial_same.
Qed.
Theorem number_results_same native input whitespace digit digits tail :
 MachinePointwise.same
  (ReadNatExecution.token_number (pending_separator_result (store_meta(withInput native input)15(whitespace+1)) (digit::digits) tail) (digit::digits))
  (ReadNatExecution.token_number (pending_result (store_meta(withInput native input)15(digit+1)) digit digits tail) (digit::digits)).
Proof. unfold ReadNatExecution.token_number. apply same_store. apply token_results_same. Qed.

Lemma pending_result_input_independent native input1 input2 value chars tail :
 pending_separator_result (store_meta(withInput native input1)15 value) chars tail =
 pending_separator_result (store_meta(withInput native input2)15 value) chars tail.
Proof.
 unfold pending_separator_result,pending_base,reset.
 repeat rewrite SeedSeparator.store_input. repeat rewrite put_many_input.
 repeat rewrite SeedSeparator.store_input. cbn [withInput]. reflexivity.
Qed.
End PendingWhitespaceEquivalence.
