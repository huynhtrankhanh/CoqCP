From CoqCP Require Import Options Imperative.
From Generated Require Import DisjointSetUnion.
From stdpp Require Import numbers list.

Definition state : BlockchainState := fun address =>
  if decide (address = repeat (0%Z) 20) then
    BlockchainContract arrayIndex0 _ (arrayType _ environment0) (arrays _ environment0) 100000%Z (funcdef_0__main (fun x => false) (fun x => 0%Z) (fun x => repeat 0%Z 20))
  else ExternallyOwned 0%Z.

Fixpoint interact (state : BlockchainState) (interaction : list (Z * Z)) :=
  match interaction with
  | [] => getBalance (state (repeat 1%Z 20))
  | (a, b) :: tail =>
    match invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0%Z state state [a; b] 1 with
    | Some (_, changedState) => interact changedState tail
    | None => 0%Z
    end
  end.

Definition optimalInteraction (x : list (Z * Z)) := forall x', Z.le (interact state x') (interact state x).
