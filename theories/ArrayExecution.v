From CoqCP Require Import Options Imperative Execution.
From stdpp Require Import numbers list.

Lemma insert_at_prefix {A} (prefix : list A) zero suffixLength value :
  <[length prefix := value]>(prefix ++ repeat zero (S suffixLength)) =
  (prefix ++ [value]) ++ repeat zero suffixLength.
Proof.
  rewrite insert_app_r_alt; [| lia]. rewrite Nat.sub_diag. cbn [repeat insert].
  rewrite <- app_assoc. reflexivity.
Qed.

(* Array access and unsigned arithmetic facts for every imperative program. *)
Section Arrays.
Context {I : Type} {T : I -> Type} `{EqDecision I}.

Definition readArray (name : I) (index : Z) :=
  Dispatch (WithArrays I T) withArraysReturnValue _
    (Retrieve _ _ name index) (fun value => Done _ _ _ value).
Definition writeArray (name : I) (index : Z) (value : T name) :=
  Dispatch (WithArrays I T) withArraysReturnValue _
    (Store _ _ name index value) (fun _ => Done _ _ _ tt).

Lemma execRead {R} name index zero
  (next : T name -> Action (WithArrays I T) withArraysReturnValue R)
  s (h : (index < length (memory s name))%nat) :
  exec (readArray name (Z.of_nat index) >>= next) s =
  exec (next (nth index (memory s name) zero)) s.
Proof.
  unfold readArray. cbn [bind exec step optionBind]. rewrite Nat2Z.id.
  destruct (decide (Nat.lt index (length (memory s name)))) as [bound | bad]; [| lia].
  rewrite (nth_lt_default _ _ _ zero). reflexivity.
Qed.
Lemma execWrite name index value s
  (h : (index < length (memory s name))%nat) :
  exec (writeArray name (Z.of_nat index) value) s =
  Some (tt, withMemory s (modifyArray (memory s) name index value)).
Proof.
  unfold writeArray. cbn [bind exec step optionBind]. rewrite Nat2Z.id.
  destruct (decide (Nat.lt index (length (memory s name)))) as [bound | bad]; [reflexivity | lia].
Qed.
End Arrays.

Lemma coerce_nat64 value (h : (value < 2^64)%nat) : coerceInt (Z.of_nat value) 64 = Z.of_nat value.
Proof.
  unfold coerceInt. apply Z.mod_small. split; [lia |].
  assert (power : Z.of_nat (2^64)%nat = (2^64)%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  rewrite <- power. lia.
Qed.
Lemma coerce_nat32 value (h : (value < 2^32)%nat) : coerceInt (Z.of_nat value) 32 = Z.of_nat value.
Proof.
  unfold coerceInt. apply Z.mod_small. split; [lia |].
  assert (power : Z.of_nat (2^32)%nat = (2^32)%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  rewrite <- power. lia.
Qed.
