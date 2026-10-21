From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash Intern FormulaEncoding Representation ClassStorage HistoryRefinement ReplyOK.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module SemanticFrames.
Import IndexExecution SipHashExecution.
Lemma lookup_nth_error {A} (xs : list A) i : xs !! i = nth_error xs i.
Proof. induction i as [|i IH] in xs |- *; destruct xs; cbn; try reflexivity; apply IH. Qed.
Lemma unique_NoDup meaning : FormulaEncoding.unique meaning -> NoDup meaning.
Proof. intros Hunique. apply NoDup_alt. intros i j p Hi Hj.
  rewrite lookup_nth_error in Hi,Hj. exact (Hunique i j p Hi Hj). Qed.
Lemma arena_NoDup s meaning : NativeRepresentation.canonical_arena s meaning -> NoDup meaning.
Proof. intros [_ [_ [Hunique _]]]. now apply unique_NoDup. Qed.
Lemma classes_extend s t meaning extra classes :
  meta_value t 2 = meta_value s 2 -> memory t arraydef_0__classes = memory s arraydef_0__classes ->
  ClassStorage.represents s meaning classes -> ClassStorage.represents t (meaning ++ extra) classes.
Proof.
  intros Hcount Harrays [Hnumber Hclasses]. split; [now rewrite Hcount|]. rewrite Harrays.
  eapply Forall2_impl; [exact Hclasses|]. intros entry cls Hdecode. now apply ClassStorage.decode_extend.
Qed.
Lemma intern_classes s t meaning extra classes : InternExecution.logical_frame s t ->
  ClassStorage.represents s meaning classes -> ClassStorage.represents t (meaning ++ extra) classes.
Proof. intros [Harrays [Hcells _]] Hclasses. eapply classes_extend; [apply Hcells; lia|apply Harrays; discriminate|exact Hclasses]. Qed.
Lemma history_transport s t logical :
  meta_value t 3 = meta_value s 3 -> memory t arraydef_0__theorems = memory s arraydef_0__theorems ->
  HistoryRefinement.represents s logical -> HistoryRefinement.represents t logical.
Proof. intros Hcount Harrays [Hnumber Hprefix]. split; [now rewrite Hcount|now rewrite Harrays]. Qed.
Lemma intern_history s t logical : InternExecution.logical_frame s t ->
  HistoryRefinement.represents s logical -> HistoryRefinement.represents t logical.
Proof. intros [Harrays [Hcells _]] Hhistory. eapply history_transport; [apply Hcells; lia|apply Harrays; discriminate|exact Hhistory]. Qed.
Lemma reply_classes s meaning classes value : ClassStorage.represents s meaning classes ->
  ClassStorage.represents (ReplyOKExecution.reply_state s value) meaning classes.
Proof. intros [Hcount Hclasses]. split.
  - unfold meta_value. now rewrite ReplyOKExecution.reply_other by discriminate.
  - now rewrite ReplyOKExecution.reply_other by discriminate.
Qed.
Lemma reply_history s logical value : HistoryRefinement.represents s logical ->
  HistoryRefinement.represents (ReplyOKExecution.reply_state s value) logical.
Proof. intro Hhistory. eapply history_transport; [|now rewrite ReplyOKExecution.reply_other by discriminate|exact Hhistory].
  unfold meta_value. now rewrite ReplyOKExecution.reply_other by discriminate. Qed.
End SemanticFrames.
