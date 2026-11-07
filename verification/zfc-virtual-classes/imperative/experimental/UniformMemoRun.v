From CoqCP Require Import Options Imperative Execution.
From UniformMemoFixture Require Import UniformMemoProgram UniformMemoChains.
From Stdlib Require Import Lists.List ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.
Definition test_memory : forall a, list (arrayType _ environment1 a) := fun a =>
 match a as a' return list (arrayType _ environment1 a') with
 | arraydef_0__meta => repeat 0 20 ++ [1024] ++ repeat 0 11
 | arraydef_0__uniformMemoState => [(2,1024,0,0)]
 | arraydef_0__uniformMemoBuckets => repeat 2 1024
 | arraydef_0__uniformMemoEntries => [(1,1,77,0);(2,2,88,1)]
 | a' => arrays _ environment1 a'
 end.
Definition test_machine := {| memory := test_memory; stdin := []; stdout := [] |}.
Definition empty_machine := {| memory := arrays _ environment1; stdin := []; stdout := [] |}.
Definition get_arguments node depth (v : varsfuncdef_0__uniformMemoGet) :=
 match v with
 | vardef_0__uniformMemoGet_node => node
 | vardef_0__uniformMemoGet_depth => depth
 | _ => 0
 end.
Example uninitialized_table_reports_error node depth :
 match exec (funcdef_0__uniformMemoGet (fun _ => false) (get_arguments node depth)) empty_machine with
 | Some (_,result) => nth_error (memory result arraydef_0__meta) 8
 | None => None
 end = Some 1.
Proof. vm_compute. reflexivity. Qed.

(* The zero-bucket error path neither hashes nor traverses entries.  Its
   result is independent of the input keys and of the previous cache status. *)
Definition zero_size_memory (count found value : Z) : forall a, list (arrayType _ environment1 a) := fun a =>
 match a as a' return list (arrayType _ environment1 a') with
 | arraydef_0__meta => repeat 0 32
 | arraydef_0__uniformMemoState => [(count,0,found,value)]
 | a' => arrays _ environment1 a'
 end.
Theorem zero_size_resets_status_and_reports_error node depth count found value :
 let m := {| memory := zero_size_memory count found value; stdin := []; stdout := [] |} in
 match exec (funcdef_0__uniformMemoGet (fun _ => false) (get_arguments node depth)) m with
 | Some (_,result) =>
     (nth_error (memory result arraydef_0__meta) 8,
      nth_error (memory result arraydef_0__uniformMemoState) 0)
 | None => (None,None)
 end = (Some 1,Some (count,0,0,0)).
Proof. vm_compute. reflexivity. Qed.
Definition single_memory (v link : Z) : forall a, list (arrayType _ environment1 a) := fun a =>
 match a as a' return list (arrayType _ environment1 a') with
 | arraydef_0__meta => repeat 0 20 ++ [1024] ++ repeat 0 11
 | arraydef_0__uniformMemoState => [(1,1024,0,0)]
 | arraydef_0__uniformMemoBuckets => repeat 1 1024
 | arraydef_0__uniformMemoEntries => [(1,1,v,link)]
 | a' => arrays _ environment1 a'
 end.
Example real_code_returns_arbitrary_payload v link :
 let m := {| memory := single_memory v link; stdin := []; stdout := [] |} in
 match exec (funcdef_0__uniformMemoGet (fun _ => false) (get_arguments 1 1)) m with
 | Some (_,result) => nth_error (memory result arraydef_0__uniformMemoState) 0
 | None => None
 end = Some (1,1024,1,v).
Proof. vm_compute. reflexivity. Qed.
(* Every bucket deliberately points at the same two-entry chain. This forces a
   collision regardless of the actual SipHash output; it is a lookup fixture,
   not an example of a valid fully populated hash table. *)
Example real_code_scans_collision :
 match exec (funcdef_0__uniformMemoGet (fun _ => false) (fun _ => 1)) test_machine with
 | Some (_,result) => nth_error (memory result arraydef_0__uniformMemoState) 0
 | None => None
 end = Some (2,1024,1,77).
Proof. vm_compute. reflexivity. Qed.
Example real_code_rejects_absent_collision :
 match exec (funcdef_0__uniformMemoGet (fun _ => false) (fun _ => 3)) test_machine with
 | Some (_,result) => nth_error (memory result arraydef_0__uniformMemoState) 0
 | None => None
 end = Some (2,1024,0,0).
Proof. vm_compute. reflexivity. Qed.

Definition collision_memory (v head_depth head_value target_link : nat) : forall a, list (arrayType _ environment1 a) := fun a =>
 match a as a' return list (arrayType _ environment1 a') with
 | arraydef_0__meta => repeat 0 20 ++ [1024] ++ repeat 0 11
 | arraydef_0__uniformMemoState => [(2,1024,0,0)]
 | arraydef_0__uniformMemoBuckets => repeat 2 1024
 | arraydef_0__uniformMemoEntries =>
     [(1,1,Z.of_nat v,Z.of_nat target_link);(2,Z.of_nat head_depth,Z.of_nat head_value,1)]
 | a' => arrays _ environment1 a'
 end.
Definition collision_model (v head_depth head_value target_link i : nat) : UniformMemoChains.entry :=
 match i with
 | O => UniformMemoChains.Entry 1 1 v target_link
 | S _ => UniformMemoChains.Entry 2 head_depth head_value 1
 end.
(* A parameterized refinement instance: the implementation follows a
   colliding head and returns the same arbitrary payload as the pure scan. *)
Theorem generated_collision_refines_scan v head_depth head_value target_link :
 let m := {| memory := collision_memory v head_depth head_value target_link; stdin := []; stdout := [] |} in
 (match exec (funcdef_0__uniformMemoGet (fun _ => false) (get_arguments 1 1)) m with
  | Some (_,result) =>
      match nth_error (memory result arraydef_0__uniformMemoState) 0 with
      | Some (_,_,found,value) => if Z.eqb found 1 then Some value else None
      | None => None end
  | None => None end) =
 option_map Z.of_nat (UniformMemoChains.scan (collision_model v head_depth head_value target_link) 2 2 1 1).
Proof. vm_compute. reflexivity. Qed.

Theorem generated_absent_collision_refines_scan v head_depth head_value :
 let m := {| memory := collision_memory v head_depth head_value 0; stdin := []; stdout := [] |} in
 (match exec (funcdef_0__uniformMemoGet (fun _ => false) (get_arguments 3 3)) m with
  | Some (_,result) =>
      match nth_error (memory result arraydef_0__uniformMemoState) 0 with
      | Some (_,_,found,value) => if Z.eqb found 1 then Some value else None
      | None => None end
  | None => None end) =
 option_map Z.of_nat (UniformMemoChains.scan (collision_model v head_depth head_value 0) 2 2 3 3).
Proof. vm_compute. reflexivity. Qed.
