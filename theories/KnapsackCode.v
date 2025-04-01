From stdpp Require Import numbers list.
From CoqCP Require Import Options Imperative Knapsack.
From Generated Require Import Knapsack.

Definition state : BlockchainState := fun address =>
  if decide (address = repeat (0%Z) 20) then
    BlockchainContract arrayIndex0 _ (arrayType _ environment0) (arrays _ environment0) 100000%Z (funcdef_0__main (fun x => false) (fun x => 0%Z) (fun x => repeat 0%Z 20))
  else ExternallyOwned 0%Z.

Definition stateAfterInteractions arrays money : BlockchainState := fun address =>
  if decide (address = repeat (0%Z) 20) then
    BlockchainContract arrayIndex0 _ (arrayType _ environment0) arrays (100000%Z - money) (funcdef_0__main (fun x => false) (fun x => 0%Z) (fun x => repeat 0%Z 20))
  else if decide (address = repeat (1%Z) 20) then ExternallyOwned money else ExternallyOwned 0%Z.

Definition to32 (x : nat) := [Z.of_nat (x / (2^24)); Z.of_nat (x / (2^16) mod 256); Z.of_nat (x / (2^8) mod 256); Z.of_nat (x mod 256)].

Lemma to32Length (x : nat) : length (to32 x) = 4%nat.
Proof. unfold to32. easy. Qed.

Fixpoint serializeWeights (items : list (nat * nat)) : list Z :=
  match items with
  | [] => []
  | (weight, _) :: rest => to32 weight ++ serializeWeights rest
  end.

Lemma serializeWeightsLength (items : list (nat * nat)) : (length (serializeWeights items) = 4 * length items)%nat.
Proof.
  induction items as [| head tail IH]. { easy. }
  rewrite (ltac:(easy) : length (head :: tail) = (1 + length tail)%nat).
  destruct head as [a b]. simpl. lia.
Qed.

Fixpoint serializeValues (items : list (nat * nat)) : list Z :=
  match items with
  | [] => []
  | (_, value) :: rest => to32 value ++ serializeValues rest
  end.

Lemma serializeValuesLength (items : list (nat * nat)) : (length (serializeValues items) = 4 * length items)%nat.
Proof.
  induction items as [| head tail IH]. { easy. }
  rewrite (ltac:(easy) : length (head :: tail) = (1 + length tail)%nat).
  destruct head as [a b]. simpl. lia.
Qed.

Definition generateData (items : list (nat * nat)) (limit : nat) : list Z := serializeWeights items ++ serializeValues items ++ to32 limit.

Lemma dataLength (items : list (nat * nat)) (limit : nat) : (length (generateData items limit) = 8 * length items + 4%nat)%nat.
Proof.
  unfold generateData. rewrite -> !app_length, to32Length, serializeValuesLength, serializeWeightsLength. lia.
Qed.

Definition start items limit := invokeContract (repeat (1%Z) 20) (repeat (0%Z) 20) 0 state state (generateData items limit) 1.

Definition extractAnswer (x : option (list Z * BlockchainState)) : Z :=
  match x with
  | Some (answer, _) => nth 0 answer 0 * (2^56) + nth 1 answer 0 * (2^48) + nth 2 answer 0 * (2^40) + nth 3 answer 0 * (2^32) + nth 4 answer 0 * (2^24) + nth 5 answer 0 * (2^16) + nth 6 answer 0 * (2^8) + nth 7 answer 0
  | None => 0
  end.
