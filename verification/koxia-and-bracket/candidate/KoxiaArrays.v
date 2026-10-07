From CoqCP Require Import Options Imperative Execution.

From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.

Section ArrayFacts.
Context {I : Type} {T : I -> Type} `{EqDecision I}.
Lemma modifyArray_same (values : forall name, list (T name)) name index value :
  modifyArray values name index value name = <[index:=value]>(values name).
Proof.
  unfold modifyArray. destruct (decide (name=name)) as [equal|impossible]; [|congruence].
  replace equal with (@eq_refl I name) by apply proof_irrel. reflexivity.
Qed.
Lemma modifyArray_other (values : forall name, list (T name)) name index value other :
  other<>name -> modifyArray values name index value other=values other.
Proof. intro different. unfold modifyArray. destruct (decide (other=name)); [congruence|reflexivity]. Qed.
Lemma modifyArray_length (values : forall name, list (T name)) name index value other :
  length (modifyArray values name index value other)=length (values other).
Proof.
  destruct (decide (other=name)) as [->|different].
  - rewrite modifyArray_same, length_insert. reflexivity.
  - rewrite modifyArray_other by exact different. reflexivity.
Qed.
Lemma withMemory_twice (state : @Machine I T) before after :
  withMemory (withMemory state before) after=withMemory state after.
Proof. reflexivity. Qed.
Lemma execStore {R} (state : @Machine I T) name index value
  (continuation : unit -> Action (WithArrays I T) withArraysReturnValue R) :
  (index < length (memory state name))%nat ->
  exec (Dispatch _ _ _ (Store _ _ name (Z.of_nat index) value) continuation) state =
  exec (continuation tt) (withMemory state (modifyArray (memory state) name index value)).
Proof.
  intro bound. cbn [exec step optionBind]. rewrite Nat2Z.id, decide_True by exact bound. reflexivity.
Qed.
Lemma execRetrieve {R} (state : @Machine I T) name index zero
  (continuation : T name -> Action (WithArrays I T) withArraysReturnValue R) :
  (index < length (memory state name))%nat ->
  exec (Dispatch _ _ _ (Retrieve _ _ name (Z.of_nat index)) continuation) state =
  exec (continuation (nth index (memory state name) zero)) state.
Proof.
  intro bound. cbn [exec step optionBind]. rewrite Nat2Z.id.
  destruct (decide (Nat.lt index (length (memory state name)))) as [valid|invalid]; [|lia].
  cbn [optionBind fst snd].
  rewrite (nth_lt_default _ _ _ zero). reflexivity.
Qed.
Definition replaceArray (values : forall name, list (T name)) name replacement other :=
  match decide (other=name) with
  | left same => eq_rect name (fun i => list (T i)) replacement other (eq_sym same)
  | right _ => values other
  end.
Definition withArray (state : @Machine I T) name replacement :=
  withMemory state (replaceArray (memory state) name replacement).
Lemma replaceArray_same values name replacement : replaceArray values name replacement name=replacement.
Proof.
  unfold replaceArray. destruct (decide (name=name)) as [same|impossible]; [|congruence].
  replace same with (@eq_refl I name) by apply proof_irrel. reflexivity.
Qed.
Lemma replaceArray_other values name replacement other : other<>name ->
  replaceArray values name replacement other=values other.
Proof. intro different. unfold replaceArray. destruct (decide (other=name)); [congruence|reflexivity]. Qed.
Lemma replaceArray_twice values name before after :
  replaceArray (replaceArray values name before) name after=replaceArray values name after.
Proof.
  apply functional_extensionality_dep. intro other. destruct (decide (other=name)) as [->|different].
  - rewrite !replaceArray_same. reflexivity.
  - rewrite !replaceArray_other by exact different. reflexivity.
Qed.
Lemma modifyArray_replace values name replacement index value :
  modifyArray (replaceArray values name replacement) name index value=
    replaceArray values name (<[index:=value]>replacement).
Proof.
  apply functional_extensionality_dep. intro other. destruct (decide (other=name)) as [->|different].
  - rewrite modifyArray_same,!replaceArray_same. reflexivity.
  - rewrite modifyArray_other,!replaceArray_other by exact different. reflexivity.
Qed.
Lemma withArray_self state name : withArray state name (memory state name)=state.
Proof.
  unfold withArray. assert (selfMemory : replaceArray (memory state) name (memory state name)=memory state).
  { apply functional_extensionality_dep. intro other. destruct (decide (other=name)) as [->|different].
    - apply replaceArray_same.
    - apply replaceArray_other. exact different. }
  rewrite selfMemory. destruct state. reflexivity.
Qed.
Lemma withArray_twice state name before after :
  withArray (withArray state name before) name after=withArray state name after.
Proof. unfold withArray,withMemory. cbn [memory]. rewrite replaceArray_twice. reflexivity. Qed.
Lemma execStoreArray {R} state name values index value
  (continuation : unit -> Action (WithArrays I T) withArraysReturnValue R) :
  (index<length values)%nat ->
  exec (Dispatch _ _ _ (Store _ _ name (Z.of_nat index) value) continuation) (withArray state name values)=
  exec (continuation tt) (withArray state name (<[index:=value]>values)).
Proof.
  intro bound. rewrite execStore by (cbn [withArray withMemory memory]; rewrite replaceArray_same; exact bound).
  unfold withArray,withMemory. cbn [memory stdin stdout]. rewrite modifyArray_replace. reflexivity.
Qed.
Lemma execReadArray {R} state name values index zero
  (continuation : T name -> Action (WithArrays I T) withArraysReturnValue R) :
  (index<length values)%nat ->
  exec (Dispatch _ _ _ (Retrieve _ _ name (Z.of_nat index)) continuation) (withArray state name values)=
  exec (continuation (nth index values zero)) (withArray state name values).
Proof.
  intro bound. rewrite (execRetrieve _ _ _ zero) by (cbn [withArray withMemory memory]; rewrite replaceArray_same; exact bound).
  cbn [withArray withMemory memory]. rewrite replaceArray_same. reflexivity.
Qed.

Lemma modifyArray_replace_other values name replacement other index value : name<>other ->
  modifyArray (replaceArray values name replacement) other index value=
    replaceArray (modifyArray values other index value) name replacement.
Proof.
  intro different. apply functional_extensionality_dep. intro query.
  destruct (decide (query=name)) as [->|notName].
  - rewrite modifyArray_other by exact different. rewrite !replaceArray_same. reflexivity.
  - destruct (decide (query=other)) as [->|notOther].
    + rewrite replaceArray_other by congruence. rewrite !modifyArray_same.
      rewrite replaceArray_other by congruence. reflexivity.
    + rewrite !replaceArray_other by exact notName. rewrite !modifyArray_other by exact notOther. rewrite replaceArray_other by exact notName. reflexivity.
Qed.
Lemma withArray_store_other state name replacement other index value : name<>other ->
  withMemory (withArray state name replacement)
    (modifyArray (memory (withArray state name replacement)) other index value)=
  withArray (withMemory state (modifyArray (memory state) other index value)) name replacement.
Proof.
  intro different. unfold withArray,withMemory. cbn [memory stdin stdout].
  rewrite modifyArray_replace_other by exact different. reflexivity.
Qed.

End ArrayFacts.
