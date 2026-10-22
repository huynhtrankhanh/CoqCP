From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash HashTable FormulaTopology ArenaFrame ReadTwo
  RenameMemoInput RenameMemoCallers RenameMemoClassEqual.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoParseDomain.
Import IndexExecution SipHashExecution.
Theorem indices_same s t count : memory t arraydef_0__formulas=memory s arraydef_0__formulas ->
  RenameMemoInput.indices_max t count=RenameMemoInput.indices_max s count.
Proof.
  intro Hsame. induction count as [|count IH]; [reflexivity|]. cbn [RenameMemoInput.indices_max].
  rewrite IH. unfold HashTableInvariant.tuple_at. now rewrite Hsame.
Qed.
Theorem predicate_ready s t fs index shift arg : ArenaFrame.storage s t ->
  RenameMemoCallers.predicate_ready s fs index shift arg -> RenameMemoCallers.predicate_ready t fs index shift arg.
Proof.
  intros [_ [Ha _]]. unfold RenameMemoCallers.predicate_ready.
  rewrite Ha by discriminate.
  destruct (nth_error (memory s arraydef_0__classes) index) as [[tag value]|]; try exact (fun H=>H).
  destruct tag as [|positive|positive]; try (destruct positive); try exact (fun H=>H).
  rewrite (indices_same s t) by (apply Ha; discriminate). exact (fun H=>H).
Qed.
Theorem growth_same s t index : ArenaFrame.storage s t ->
  RenameMemoCallers.predicate_growth t index=RenameMemoCallers.predicate_growth s index.
Proof. intros [_ [Ha _]]. unfold RenameMemoCallers.predicate_growth. now rewrite Ha by discriminate. Qed.
Theorem topology s t count : ArenaFrame.storage s t -> FormulaTopology.ordered s count -> FormulaTopology.ordered t count.
Proof.
  intros [_ [Ha _]] Hordered parent child Hparent Hchild. apply Hordered; [exact Hparent|].
  unfold HashTableInvariant.tuple_at in *. now rewrite Ha in Hchild by discriminate.
Qed.
Definition ready s (fs : list SetTheory.formula) :=
  (31<length (memory s arraydef_0__meta))%nat /\ (0<length (memory s arraydef_0__sipState))%nat /\
  0<meta_value s 20 /\ meta_value s 8=0 /\ FormulaTopology.ordered s (length fs).
Theorem second_ready s fs ch chars a middle b last tail : ready s fs ->
  ready (ReadTwo.second_state s ch chars a middle b last tail) fs.
Proof.
  intros [Hmeta [Hsip [Hpositive [Herror Hordered]]]]. unfold ready. split.
  - now rewrite ReadTwo.second_meta_length.
  - split; [now rewrite ReadTwo.second_other by discriminate|]. split.
    + rewrite ReadTwo.second_meta_other by lia. exact Hpositive.
    + split; [rewrite ReadTwo.second_meta_other by lia; exact Herror|].
      eapply topology; [apply ReadTwo.second_storage; lia|exact Hordered].
Qed.
Theorem second_predicate s fs ch chars a middle b last tail index shift arg :
  (17<length (memory s arraydef_0__meta))%nat -> RenameMemoCallers.predicate_ready s fs index shift arg ->
  RenameMemoCallers.predicate_ready (ReadTwo.second_state s ch chars a middle b last tail) fs index shift arg.
Proof. intros Hmeta Hready. eapply predicate_ready; [now apply ReadTwo.second_storage|exact Hready]. Qed.
Theorem equal_ready s t fs a b cls_a cls_b : ArenaFrame.storage s t ->
  RenameMemoClassEqual.ready s fs a b cls_a cls_b -> RenameMemoClassEqual.ready t fs a b cls_a cls_b.
Proof.
  intros Hframe Hready. destruct cls_a,cls_b; cbn [RenameMemoClassEqual.ready] in *; [exact I| | |].
  all: destruct Hready as [Ha Hb]; split; eapply predicate_ready; eassumption.
Qed.
Theorem equal_work s t a b cls_a cls_b : ArenaFrame.storage s t ->
  RenameMemoClassEqual.work t a b cls_a cls_b=RenameMemoClassEqual.work s a b cls_a cls_b.
Proof.
  intro Hframe. destruct cls_a,cls_b; cbn [RenameMemoClassEqual.work]; [reflexivity| | |].
  all: now rewrite (growth_same s t a Hframe),(growth_same s t b Hframe).
Qed.
End RenameMemoParseDomain.
