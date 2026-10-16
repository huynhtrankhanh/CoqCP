From CoqCP Require Import Options.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat extraction.Extraction extraction.ExtrOcamlBasic
  extraction.ExtrOcamlNatInt extraction.ExtrOcamlZBigInt.
From Submission Require Import Candidate Tree.
Unset Mangle Names.

(* Signed values, decimal arithmetic, and the 64-bit EOF sentinel retain
   arbitrary precision. Only bounded counts/indices use machine naturals. *)
Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Constant capacity => "(fun h -> 1 lsl h)".
Extract Constant Z.of_nat => "Big_int_Z.big_int_of_int".
Extract Constant Z.to_nat =>
  "(fun x -> if Big_int_Z.sign_big_int x <= 0 then 0 else Big_int_Z.int_of_big_int x)".

Extraction "solver.ml" Implementation.program.
