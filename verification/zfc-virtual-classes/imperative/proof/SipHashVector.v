From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith.
Open Scope Z_scope.
Module SipHashVector.
Import IndexExecution.
Definition initial := store_meta (store_meta (store_meta
  {| memory := arrays _ environment1; stdin := []; stdout := [] |}
  20 1024) 26 506097522914230528) 27 1084818905618843912.
Definition arguments := update (update (update (fun _ => 0)
  vardef_0__formulaHash_tag 506097522914230528)
  vardef_0__formulaHash_a 1084818905618843912)
  vardef_0__formulaHash_b 1663540288323457296.
(* Reference SipHash-2-4 vector for the 24 bytes 00,01,...,17 and key 00,...,0f. *)
Example official_vector_24 : option_map
  (fun response => List.nth 28 (memory (snd response) arraydef_0__meta) 0)
  (exec (funcdef_0__formulaHash (fun _ => false) arguments) initial) =
  Some 13307381289415454612.
Proof. vm_compute. reflexivity. Qed.
End SipHashVector.
