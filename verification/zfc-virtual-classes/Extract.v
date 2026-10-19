From CoqCP Require Import Options.
From Stdlib Require Import Arith.PeanoNat extraction.Extraction extraction.ExtrOcamlBasic
  extraction.ExtrOcamlNatBigInt.
From Submission Require Import Candidate.
Unset Mangle Names.

(* Indices stay arbitrary precision. In particular, inserting binders must
   never overflow a machine integer and accidentally capture a variable. *)
Extract Constant Nat.eq_dec => "Big_int_Z.eq_big_int".
Extraction "checker.ml" Implementation.program.
