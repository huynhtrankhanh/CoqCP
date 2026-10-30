From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash MachinePointwise NativeBasicSession NativeSetSchemaSession NativeSchemaFlat
 NativeNameCompact FormulaTopology HashTable ClassLookup.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSetPointwiseState.
Theorem extra s t logical : MachinePointwise.same s t -> NativeSetSchemaSession.extra s logical -> NativeSetSchemaSession.extra t logical.
Proof.
 intros Hsame [Hbasic [Hflat Hsets]]. pose proof Hsame as (_ & _ & Hmemory).
 destruct Hbasic as [Hmeta Hsip Hsafe Htop Hfalse Hclasses Hunique Hcompact]. split.
 - constructor.
   + now rewrite <-Hmemory.
   + now rewrite <-Hmemory.
   + exact Hsafe.
   + apply (FormulaTopology.same s t);[exact Htop|]. intros parent Hparent. unfold HashTableInvariant.tuple_at. now rewrite <-Hmemory.
   + exact Hfalse.
   + apply (ClassLookup.transport s t);[symmetry;apply Hmemory|exact Hclasses].
   + exact Hunique.
   + unfold NativeNameCompact.compact,NativeNameCompact.compact_bindings in *. now rewrite <-Hmemory.
 - split;[eapply NativeSchemaFlat.frame;[symmetry;apply Hmemory|exact Hflat]|exact Hsets].
Qed.
End NativeSetPointwiseState.
