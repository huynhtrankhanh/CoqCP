From CoqCP Require Import Options Imperative Execution.
From UniformInternFixture Require Import UniformInternProgram UniformInternModel.
From Stdlib Require Import Lists.List ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* Artificial buckets deliberately force a collision independently of the
   actual SipHash output. This fixture does not assert bucket-index validity. *)
Definition collision_memory : forall a, list (arrayType _ environment1 a) := fun a =>
 match a as a' return list (arrayType _ environment1 a') with
 | arraydef_0__meta => repeat 0 20 ++ [1024] ++ repeat 0 11
 | arraydef_0__uniformState => [(2,1024)]
 | arraydef_0__uniformNodes => [(1,2,3);(1,2,4)]
 | arraydef_0__uniformLinks => [0;1]
 | arraydef_0__uniformBuckets => repeat 2 1024
 | a' => arrays _ environment1 a'
 end.
Definition collision_machine := {| memory := collision_memory; stdin := []; stdout := [] |}.
Definition intern_arguments (v : varsfuncdef_0__uniformIntern) :=
 match v with
 | vardef_0__uniformIntern_tag => 1
 | vardef_0__uniformIntern_a => 2
 | vardef_0__uniformIntern_b => 3
 | _ => 0
 end.

(* The head differs only in its final field. The implementation must compare
   the complete tuple and continue to the matching earlier node. *)
Example generated_interner_collision_matches_model :
 (match exec (funcdef_0__uniformIntern (fun _ => false) intern_arguments) collision_machine with
  | Some (_, result) => nth_error (memory result arraydef_0__meta) 0
  | None => None end) =
 option_map Z.of_nat
   (UniformInternModel.lookup [(1%nat,2%nat,3%nat);(1%nat,2%nat,4%nat)]
     (UniformInternModel.rehash [(1%nat,2%nat,3%nat);(1%nat,2%nat,4%nat)] (fun _ => 0%nat))
     (fun _ => 0%nat) (1%nat,2%nat,3%nat)).
Proof. vm_compute. reflexivity. Qed.

(* A hit reuses the existing identifier and does not append a symbolic node. *)
Example generated_collision_hit_keeps_node_count :
 (match exec (funcdef_0__uniformIntern (fun _ => false) intern_arguments) collision_machine with
  | Some (_, result) => nth_error (memory result arraydef_0__uniformState) 0
  | None => None end) = Some (2,1024).
Proof. vm_compute. reflexivity. Qed.

Definition missing_arguments (v : varsfuncdef_0__uniformIntern) :=
 match v with
 | vardef_0__uniformIntern_tag => 9
 | vardef_0__uniformIntern_a => 9
 | vardef_0__uniformIntern_b => 9
 | _ => 0
 end.

(* A miss after traversing both colliding entries appends once and reports the
   new ID. The bucket contents are artificial, so this remains a concrete
   execution check rather than a theorem about all valid hash tables. *)
Example generated_collision_miss_appends :
 (match exec (funcdef_0__uniformIntern (fun _ => false) missing_arguments) collision_machine with
  | Some (_, result) => (nth_error (memory result arraydef_0__meta) 0,
                          nth_error (memory result arraydef_0__uniformState) 0,
                          nth_error (memory result arraydef_0__uniformNodes) 2)
  | None => (None,None,None) end) = (Some 2,Some (3,1024),Some (9,9,9)).
Proof. vm_compute. reflexivity. Qed.
