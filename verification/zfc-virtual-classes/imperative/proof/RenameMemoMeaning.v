From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index RenameStack FormulaEncoding Representation RenameMemoTable.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoMeaning.
Import IndexExecution.
Definition entry_meaning fs rho (key : RenameMemoTable.key) value :=
  word (fst key) /\ word (snd key) /\ word value /\ exists source,
    nth_error fs (Z.to_nat (fst key))=Some source /\
    nth_error fs (Z.to_nat value)=Some (RenameStack.renamed rho (Z.to_nat (snd key)) source).
Lemma extends fs extra rho key value : entry_meaning fs rho key value -> entry_meaning (fs++extra) rho key value.
Proof.
  intros [Hnode [Hdepth [Hvalue [source [Hsource Hresult]]]]]. split; [exact Hnode|]. split; [exact Hdepth|]. split; [exact Hvalue|].
  exists source. split; now apply FormulaEncoding.nth_error_extend.
Qed.
Theorem table_extends table count fs extra rho : RenameMemoTable.represents table count (entry_meaning fs rho) ->
  RenameMemoTable.represents table count (entry_meaning (fs++extra) rho).
Proof. intros Hmeaning index Hindex Hoccupied. apply extends. now apply Hmeaning. Qed.
Theorem falsity fs rho root depth : word root -> word depth ->
  nth_error fs (Z.to_nat root)=Some SetTheory.falsity -> nth_error fs 0=Some SetTheory.falsity ->
  entry_meaning fs rho (root,depth) 0.
Proof.
  intros Hroot Hdepth Hsource Hzero. split; [exact Hroot|]. split; [exact Hdepth|]. split.
  - unfold word,maximum. lia.
  - exists SetTheory.falsity. split; [exact Hsource|exact Hzero].
Qed.
Theorem falsity_value fs rho root depth value : FormulaEncoding.unique fs ->
  nth_error fs (Z.to_nat root)=Some SetTheory.falsity -> nth_error fs 0=Some SetTheory.falsity ->
  entry_meaning fs rho (root,depth) value -> value=0.
Proof.
  intros Hunique Hfalse Hzero [_ [_ [Hvalue [source [Hsource Hresult]]]]]. cbn [fst snd] in *.
  rewrite Hfalse in Hsource. injection Hsource as <-.
  change (nth_error fs (Z.to_nat value)=Some SetTheory.falsity) in Hresult.
  apply FormulaEncoding.natural_index_injective; [exact Hvalue|unfold word,maximum; lia|].
  exact (Hunique (Z.to_nat value) 0%nat SetTheory.falsity Hresult Hzero).
Qed.
Theorem result fs rho root depth value source : entry_meaning fs rho (root,Z.of_nat depth) value ->
  nth_error fs (Z.to_nat root)=Some source ->
  nth_error fs (Z.to_nat value)=Some (RenameStack.renamed rho depth source).
Proof.
  intros [_ [_ [_ [stored [Hsource Hresult]]]]] Hsource'. cbn [fst snd] in *.
  rewrite Hsource' in Hsource. injection Hsource as <-. now rewrite Nat2Z.id in Hresult.
Qed.
Theorem below_sentinel s fs rho key value : NativeRepresentation.canonical_arena s fs ->
  entry_meaning fs rho key value -> value<maximum.
Proof.
  intros [Htable _] [_ [_ [Hword [source [Hsource Hresult]]]]].
  pose proof (proj1 Htable) as [_ [_ [_ [_ [_ [_ Hlimit]]]]]].
  assert (Hindex : (Z.to_nat value<length fs)%nat) by (apply nth_error_Some; congruence).
  pose proof (Z2Nat.id value (proj1 Hword)). lia.
Qed.
End RenameMemoMeaning.
