From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ReadTokenPendingLeading.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module ReadNatPendingLeading.
Import IndexExecution SipHashExecution ReadNatExecution.
Theorem generated_readNat_pending_leading s bs ns ch prefix chars sep tail :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 -> 0<=ch<256 -> TokenByteExecution.separator ch ->
  (0 < length chars <= 1024)%nat ->
  Forall (fun ch => 48 <= ch <= 57) chars -> number_from 0 chars <= maximum ->
  TokenByteExecution.separator sep -> Forall TokenByteExecution.separator prefix -> stdin s = prefix ++ chars ++ sep :: tail ->
  exec (funcdef_0__readNat bs ns) s = Some (tt,token_number (ReadTokenPendingLeading.pending_separator_result s chars tail) chars).
Proof.
  intros Hmeta Htoken Hpending Herror Hch Hchsep Hlength Hdigits Hlimit Hsep Hprefix Hin.
  assert (Hbytes : Forall (fun ch => 0 <= ch < 256 /\ ~ TokenByteExecution.separator ch) chars).
  { apply Forall_impl with (P := fun ch => 48 <= ch <= 57); [|exact Hdigits].
    intros digit Hdigit. split; [lia|unfold TokenByteExecution.separator; lia]. }
  apply generated_readNat_from_token.
  - now apply (ReadTokenPendingLeading.generated_pending_leading s (fun _ => false) (fun _ => 0) ch prefix chars sep tail).
  - now rewrite ReadTokenPendingLeading.result_meta_length.
  - rewrite ReadTokenPendingLeading.result_valid by exact Hmeta. discriminate.
  - now apply ReadTokenPendingLeading.result_count.
  - rewrite ReadTokenPendingLeading.result_token_length. lia.
  - intros i Hi. apply (ReadTokenPendingLeading.result_token_entry s chars tail i); [exact Hi|exact (Nat.le_trans _ _ _ (proj2 Hlength) Htoken)].
  - exact Hdigits.
  - exact Hlimit.
Qed.
End ReadNatPendingLeading.
