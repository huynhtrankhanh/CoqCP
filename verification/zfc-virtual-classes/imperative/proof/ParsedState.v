From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ReadOne ReadTwo ClassStorage HistoryRefinement.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.

Module ParsedState.
Import IndexExecution SipHashExecution.
Lemma one_classes s fs cs ch chars value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> ClassStorage.represents s fs cs ->
  ClassStorage.represents (ReadOne.argument_state s ch chars value sep tail) fs cs.
Proof.
  intros Hmeta [Hcount Hclasses]. split.
  - rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount.
  - rewrite ReadOne.argument_other by discriminate. exact Hclasses.
Qed.
Lemma one_history s logical ch chars value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> HistoryRefinement.represents s logical ->
  HistoryRefinement.represents (ReadOne.argument_state s ch chars value sep tail) logical.
Proof.
  intros Hmeta [Hcount Hprefix]. split.
  - rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount.
  - rewrite ReadOne.argument_other by discriminate. exact Hprefix.
Qed.
Lemma two_classes s fs cs ch chars a middle b last tail :
  (17 < length (memory s arraydef_0__meta))%nat -> ClassStorage.represents s fs cs ->
  ClassStorage.represents (ReadTwo.second_state s ch chars a middle b last tail) fs cs.
Proof.
  intros Hmeta [Hcount Hclasses]. split.
  - rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hcount.
  - rewrite ReadTwo.second_other by discriminate. exact Hclasses.
Qed.
Lemma two_history s logical ch chars a middle b last tail :
  (17 < length (memory s arraydef_0__meta))%nat -> HistoryRefinement.represents s logical ->
  HistoryRefinement.represents (ReadTwo.second_state s ch chars a middle b last tail) logical.
Proof.
  intros Hmeta [Hcount Hprefix]. split.
  - rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hcount.
  - rewrite ReadTwo.second_other by discriminate. exact Hprefix.
Qed.
End ParsedState.
