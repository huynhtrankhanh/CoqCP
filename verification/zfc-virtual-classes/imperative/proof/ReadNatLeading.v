From CoqCP Require Import Options Imperative Execution DecimalEncoding.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ReadTokenLeading DecimalInput.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module ReadNatLeading.
Import IndexExecution SipHashExecution ReadNatExecution.
Theorem generated_readNat_leading s bs ns prefix chars sep tail :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = 0 -> meta_value s 8 = 0 ->
  (0 < length chars <= 1024)%nat ->
  Forall (fun ch => 48 <= ch <= 57) chars -> number_from 0 chars <= maximum ->
  TokenByteExecution.separator sep -> Forall TokenByteExecution.separator prefix -> stdin s = prefix ++ chars ++ sep :: tail ->
  exec (funcdef_0__readNat bs ns) s = Some (tt,token_number (ReadTokenExecution.read_result s chars tail) chars).
Proof.
  intros Hmeta Htoken Hpending Herror Hlength Hdigits Hlimit Hsep Hprefix Hin.
  assert (Hbytes : Forall (fun ch => 0 <= ch < 256 /\ ~ TokenByteExecution.separator ch) chars).
  { apply Forall_impl with (P := fun ch => 48 <= ch <= 57); [|exact Hdigits].
    intros ch Hch. split; [lia|unfold TokenByteExecution.separator; lia]. }
  apply generated_readNat_from_token.
  - now apply (ReadTokenLeading.generated_readToken_leading s (fun _ => false) (fun _ => 0) prefix chars sep tail).
  - now rewrite ReadTokenExecution.result_meta_length.
  - rewrite ReadTokenExecution.result_valid by exact Hmeta. discriminate.
  - now apply ReadTokenExecution.result_count.
  - unfold ReadTokenExecution.read_result. rewrite store_meta_other by discriminate.
    change (length chars <= length (memory (store_meta (ReadTokenExecution.put_many (ReadTokenExecution.reset s) 0 chars) 17 1%Z) arraydef_0__token))%nat.
    rewrite store_meta_other by discriminate. rewrite ReadTokenExecution.put_many_token_length, ReadTokenExecution.reset_token. lia.
  - intros i Hi. apply (ReadTokenExecution.result_token_entry s chars tail i); [exact Hi|exact (Nat.le_trans _ _ _ (proj2 Hlength) Htoken)].
  - exact Hdigits.
  - exact Hlimit.
Qed.

Theorem generated_encoded s bs ns value prefix sep tail :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 -> Z.of_nat value<=maximum ->
 TokenByteExecution.separator sep -> Forall TokenByteExecution.separator prefix ->
 stdin s=prefix++decimalBytes value++sep::tail ->
 exec (funcdef_0__readNat bs ns) s=Some(tt,DecimalInput.encoded_result s value tail).
Proof.
 intros Hmeta Htoken Hpending Herror Hword Hsep Hprefix Hin.
 destruct (DecimalInput.decimal_word value Hword) as [Hnumber [Hdigits Hlength]].
 unfold DecimalInput.encoded_result. apply (generated_readNat_leading s bs ns prefix (decimalBytes value) sep tail);
 try assumption; lia.
Qed.
End ReadNatLeading.
