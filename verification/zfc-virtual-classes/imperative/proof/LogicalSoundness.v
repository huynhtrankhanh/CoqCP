From CoqCP Require Import Options.
From Trusted Require Export Guarantees.
(* The mathematical guarantees belong to the standalone specification.
   Retain the native proof namespace for existing audit entries. *)
Module LogicalSoundness := Guarantees.
