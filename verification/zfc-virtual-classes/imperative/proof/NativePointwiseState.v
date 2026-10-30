From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash MachinePointwise NativeState NativeBasicSession NativeGeneralSession NativeDialogueComposition
 ArenaFrame HashTable ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation FormulaTopology ClassLookup NativeNameCompact NativeSchemaFieldBounds.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativePointwiseState.
Import IndexExecution SipHashExecution.
Lemma meta s t i : MachinePointwise.same s t -> meta_value t i=meta_value s i.
Proof. intros (_ & _ & Hmemory). unfold meta_value. now rewrite Hmemory. Qed.
Lemma storage s t : MachinePointwise.same s t -> ArenaFrame.storage s t.
Proof.
 intro Hsame. destruct Hsame as (_ & _ & Hmemory).
 split;[now rewrite Hmemory|]. split;[intros;symmetry;apply Hmemory|].
 repeat split;unfold meta_value;now rewrite Hmemory.
Qed.
Theorem represents s t logical : MachinePointwise.same s t -> NativeState.represents s logical -> NativeState.represents t logical.
Proof.
 intros Hsame Hstate. pose proof Hsame as (_ & _ & Hmemory).
 constructor.
 - exact (ArenaFrame.storage_arena s t _ (storage s t Hsame) (NativeState.formula_representation _ _ Hstate)).
 - unfold ClassStorage.represents in *. rewrite (meta s t 2 Hsame),<-Hmemory. exact (NativeState.class_representation _ _ Hstate).
 - unfold HistoryRefinement.represents in *. rewrite (meta s t 3 Hsame),<-Hmemory. exact (NativeState.history_representation _ _ Hstate).
 - unfold NameRepresentation.represents in *. rewrite (meta s t 4 Hsame),(meta s t 5 Hsame). repeat rewrite <-Hmemory. exact (NativeState.name_representation _ _ Hstate).
 - eapply SchemaRepresentation.transport;[exact (NativeState.schema_representation _ _ Hstate)|apply meta;exact Hsame|symmetry;apply Hmemory|reflexivity|reflexivity|reflexivity].
Qed.
Theorem boundary s t logical : MachinePointwise.same s t -> NativeDialogueComposition.boundary s logical -> NativeDialogueComposition.boundary t logical.
Proof.
 intros Hsame [Hstate Htoken Hprint Herror Hrun]. pose proof Hsame as (_ & _ & Hmemory).
 constructor;[exact (represents s t logical Hsame Hstate)|now rewrite <-Hmemory|now rewrite <-Hmemory|now rewrite (meta s t 8 Hsame)|now rewrite (meta s t 9 Hsame)].
Qed.
Theorem extra s t logical argument_cap : MachinePointwise.same s t -> NativeGeneralSession.extra argument_cap s logical -> NativeGeneralSession.extra argument_cap t logical.
Proof.
 intros Hsame [Hextra Hfields]. destruct Hextra as [Hmeta Hsip Hsafe Htop Hfalse Hclasses Hunique Hcompact].
 pose proof Hsame as (_ & _ & Hmemory). split.
 - constructor.
   + now rewrite <-Hmemory.
   + now rewrite <-Hmemory.
   + exact Hsafe.
   + apply (FormulaTopology.same s t);[exact Htop|]. intros parent Hparent. unfold HashTableInvariant.tuple_at. now rewrite <-Hmemory.
   + exact Hfalse.
   + apply (ClassLookup.transport s t);[symmetry;apply Hmemory|exact Hclasses].
   + exact Hunique.
   + unfold NativeNameCompact.compact,NativeNameCompact.compact_bindings in *. now rewrite <-Hmemory.
 - apply (NativeSchemaFieldBounds.fields_frame s t);[symmetry;apply Hmemory|exact Hfields].
Qed.
End NativePointwiseState.
