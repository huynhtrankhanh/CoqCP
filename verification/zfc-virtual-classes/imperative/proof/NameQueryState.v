From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ReadName CommandInput ArenaFrame NameRepresentation ClassStorage HistoryRefinement.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Module NameQueryState.
Import IndexExecution SipHashExecution.
Lemma storage s ch chars name sep tail : (17 < length (memory s arraydef_0__meta))%nat ->
  ArenaFrame.storage s (ReadName.name_state s ch chars name sep tail).
Proof.
  intro Hmeta. unfold ReadName.name_state. eapply ArenaFrame.storage_trans; [apply CommandInput.parsed_storage|].
  apply ReadName.storage. now rewrite ReadName.opcode_meta_length.
Qed.
Lemma bindings s ch chars name sep tail bs : (17 < length (memory s arraydef_0__meta))%nat ->
  NameRepresentation.represents s bs -> NameRepresentation.represents (ReadName.name_state s ch chars name sep tail) bs.
Proof.
  intros Hmeta [Hcount [Hbytes [Hlimit [Hspan Hentries]]]]. unfold NameRepresentation.represents.
  rewrite (ReadName.name_other s ch chars name sep tail arraydef_0__names ltac:(discriminate) ltac:(discriminate)),
    (ReadName.name_other s ch chars name sep tail arraydef_0__bindings ltac:(discriminate) ltac:(discriminate)).
  rewrite !ReadName.name_meta_other by (try exact Hmeta; lia). repeat split; assumption.
Qed.
Lemma classes s ch chars name sep tail fs cs : (17 < length (memory s arraydef_0__meta))%nat ->
  ClassStorage.represents s fs cs -> ClassStorage.represents (ReadName.name_state s ch chars name sep tail) fs cs.
Proof.
  intros Hmeta [Hcount Hclasses]. split.
  - rewrite ReadName.name_meta_other by (try exact Hmeta; lia). exact Hcount.
  - rewrite ReadName.name_other by discriminate. exact Hclasses.
Qed.
Lemma history s ch chars name sep tail logical : (17 < length (memory s arraydef_0__meta))%nat ->
  HistoryRefinement.represents s logical -> HistoryRefinement.represents (ReadName.name_state s ch chars name sep tail) logical.
Proof.
  intros Hmeta [Hcount Hhistory]. split.
  - rewrite ReadName.name_meta_other by (try exact Hmeta; lia). exact Hcount.
  - rewrite ReadName.name_other by discriminate. exact Hhistory.
Qed.
End NameQueryState.
