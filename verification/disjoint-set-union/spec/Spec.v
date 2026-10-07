From CoqCP Require Import Options Imperative Execution UnionFindModel DisjointSetUnion.
From Generated Require Import DisjointSetUnion.
From stdpp Require Import numbers list.

Definition dsuArrays (dsu : list Slot) : forall name, list (arrayType _ environment2 name) :=
  fun name => match name with
  | arraydef_0_DSU_dsu => convertToArray dsu
  | arraydef_0_DSU_hasBeenInitialized => [1%Z]
  | arraydef_0_DSU_result => [0%Z]
  end.

Definition mergeAction (a b : Z) :=
  funcdef_0_DSU_unite (fun _ => false)
    (fun name => match name with
      | vardef_0_DSU_unite_u => a
      | vardef_0_DSU_unite_v => b
      | vardef_0_DSU_unite_z => 0%Z
      end) >>= fun _ =>
  Dispatch (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit
    (Store _ _ arraydef_0_DSU_result 0%Z 0%Z) (fun _ => Done _ _ _ tt).

Definition modelScore (interactions : list (Z * Z)) := dsuScore (dsuFromInteractions (repeat (Ancestor Unit) 100) (map (fun (x : Z * Z) => let (a, b) := x in (Z.to_nat a, Z.to_nat b)) interactions)).

Definition Program := Z -> Z -> Action
  (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit.

(* Generated union operation; the byte-stream frontend is not certified. *)
Definition required (program : Program) : Prop :=
  program = mergeAction /\
  forall dsu, length dsu = 100 -> Z.to_nat (dsuLeafCount dsu) = length dsu ->
    noIllegalIndices dsu -> withoutCyclesN dsu (length dsu) ->
    forall a b, (0 <= a < 100)%Z -> (0 <= b < 100)%Z ->
      runProgram (dsuArrays dsu) (program a b) [] =
        Some (dsuArrays (unite dsu (Z.to_nat a) (Z.to_nat b)), [], []).
Definition scoreBound := forall interactions : list (Z * Z),
  (forall a b, In (a, b) interactions ->
    (0 <= a < 256)%Z /\ (0 <= b < 256)%Z) -> (modelScore interactions <= 5049)%Z.
Definition scoreAttainable :=
  modelScore (map (fun x => (0%Z, Z.of_nat x)) (seq 1 99)) = 5049%Z.

Module Type SOLUTION.
  Parameter program : Program.
  Parameter correct : required program.
  Parameter score_max : scoreBound.
  Parameter score_attainable : scoreAttainable.
End SOLUTION.
