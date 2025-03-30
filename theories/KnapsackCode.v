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