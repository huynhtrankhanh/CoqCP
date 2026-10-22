From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash FormulaEncoding RenameStack RenameMemoWork RenameMemoSchedule
  RenameMemoScheduleRelation RenameMemoNativeEvent RenameMemoLookup RenameMemoContents RenameMemoAccounting RenameMemoScheduleResources.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
Import ListNotations.
Open Scope Z_scope.
Module RenameMemoEventSchedule.
Import SetTheory IndexExecution SipHashExecution RenameMemoScheduleRelation.
Definition key (query : RenameMemoSchedule.key) := (Z.of_nat (fst query),Z.of_nat (snd query)).
Definition covered s count completed := forall query, In query completed ->
  RenameMemoContents.has (RenameMemoLookup.table s) count (key query).
Record coupled source_fs root s (fs : list formula) count typed model initial_length : Prop := {
  stack_related : relates source_fs root (RenameMemoSchedule.stack model) typed;
  completed_covered : covered s count (RenameMemoSchedule.completed model);
  occupancy_bound : meta_value s 30<=Z.of_nat (length (RenameMemoSchedule.completed model));
  allocation_bound : (length fs+length (RenameMemoSchedule.active (RenameMemoSchedule.stack model))<=
    initial_length+length (RenameMemoSchedule.visited model))%nat
}.
Theorem accounting source_fs root s fs count typed model initial_length :
  coupled source_fs root s fs count typed model initial_length ->
  RenameMemoScheduleResources.accounting s fs typed model initial_length.
Proof.
  intros [Hrel Hcovered Hlive Halloc]. constructor; try assumption.
  symmetry. now apply relates_length with (fs:=source_fs) (root:=root).
Qed.
Definition source_prefix (source_fs fs : list formula) := forall node p,
  nth_error source_fs node=Some p -> nth_error fs node=Some p.
Lemma source_prefix_extend source_fs fs extra : source_prefix source_fs fs -> source_prefix source_fs (fs++extra).
Proof. intros Hprefix node p Hlookup. apply FormulaEncoding.nth_error_extend. now apply Hprefix. Qed.
Lemma node_word root node : word (Z.of_nat root) -> (node<=root)%nat -> word (Z.of_nat node).
Proof. unfold word. intros. lia. Qed.
Lemma miss_absent s fs count source_fs root completed node depth p :
  source_prefix source_fs fs -> word (Z.of_nat root) -> (node<=root)%nat -> nth_error source_fs node=Some p ->
  RenameMemoLookup.indexed s count -> covered s count completed ->
  RenameMemoNativeEvent.misses s fs count p depth -> ~In (node,depth) completed.
Proof.
  intros Hprefix Hroot Hnode Hlookup Hindexed Hcovered Hmiss Hin.
  pose proof (Hmiss (Z.of_nat node) (node_word root node Hroot Hnode)) as Hnone.
  rewrite Nat2Z.id in Hnone. specialize (Hnone (Hprefix node p Hlookup)).
  destruct (RenameMemoContents.lookup_present s count (key (node,depth)) Hindexed (Hcovered (node,depth) Hin)) as [value Hsome].
  unfold key in Hsome. cbn [fst snd] in Hsome. congruence.
Qed.
Lemma completed_key s fs count t size source_fs root node depth p :
  source_prefix source_fs fs -> word (Z.of_nat root) -> (node<=root)%nat -> nth_error source_fs node=Some p ->
  RenameMemoNativeEvent.completes s fs count t size p depth -> RenameMemoAccounting.completed s count t size (key (node,depth)).
Proof.
  intros Hprefix Hroot Hnode Hlookup Hcomplete. unfold key. cbn [fst snd].
  apply Hcomplete; [now apply node_word with (root:=root)|]. rewrite Nat2Z.id. now apply Hprefix.
Qed.
Lemma passive_accounting s t count size done : RenameMemoAccounting.passive s t -> size=count ->
  covered s count done -> meta_value s 30<=Z.of_nat (length done) ->
  covered t size done /\ meta_value t 30<=Z.of_nat (length done).
Proof.
  intros Hpassive -> Hcovered Hlive. split.
  - intros query Hin. apply (RenameMemoAccounting.passive_covers s t count Hpassive). now apply Hcovered.
  - destruct Hpassive as [_ [_ Hsame]]. now rewrite Hsame.
Qed.
Lemma complete_accounting s t count size done query : RenameMemoAccounting.completed s count t size (key query) ->
  covered s count done -> meta_value s 30<=Z.of_nat (length done) ->
  covered t size (query::done) /\ meta_value t 30<=Z.of_nat (length (query::done)).
Proof.
  intros [Hcovers [Hnew Hupper]] Hcovered Hlive. split.
  - intros other [<-|Hin]; [exact Hnew|]. apply Hcovers. now apply Hcovered.
  - cbn [length]. lia.
Qed.

Theorem event_preserves source_fs root graph s fs count t next_fs size typed next_typed model initial_length :
  coherent source_fs root graph -> RenameMemoWork.older graph -> source_prefix source_fs fs ->
  word (Z.of_nat root) -> RenameMemoLookup.indexed s count ->
  coupled source_fs root s fs count typed model initial_length ->
  RenameMemoNativeEvent.event s fs count t next_fs size typed next_typed ->
  exists next_model, RenameMemoSchedule.move graph model next_model /\
    coupled source_fs root t next_fs size next_typed next_model initial_length.
Proof.
  intros Hcoherent Hgraph Hprefix Hroot Hindexed [Hrel Hcovered Hlive Halloc] Hevent.
  destruct model as [visited done indexed hits returns]. cbn [RenameMemoSchedule.stack RenameMemoSchedule.completed RenameMemoSchedule.visited] in *.
  destruct Hevent as [p depth tail Hpassive Hsize Hlength|
    p depth tail Hatomic Hmiss Hcomplete Hlength|p q depth tail Hmiss Hpassive Hsize Hlength|
    p depth tail Hmiss Hpassive Hsize Hlength|p q depth tail left_value Hpassive Hsize Hlength|
    p q depth tail left_value Hcomplete Hlength|p depth tail Hcomplete Hlength].
  - destruct (relates_visit _ _ _ _ _ _ Hrel) as [node [indices [-> [Hnode [Hlookup Htail]]]]].
    destruct (passive_accounting _ _ _ _ _ Hpassive Hsize Hcovered Hlive) as [Hcover' Hlive'].
    eexists. split; [apply RenameMemoSchedule.hit|]. constructor; cbn [RenameMemoSchedule.stack RenameMemoSchedule.completed RenameMemoSchedule.visited RenameMemoSchedule.active length] in *; try assumption. lia.
  - destruct (relates_visit _ _ _ _ _ _ Hrel) as [node [indices [-> [Hnode [Hlookup Htail]]]]].
    pose proof (miss_absent _ _ _ _ _ _ _ _ _ Hprefix Hroot Hnode Hlookup Hindexed Hcovered Hmiss) as Habsent.
    pose proof (completed_key _ _ _ _ _ _ _ _ _ _ Hprefix Hroot Hnode Hlookup Hcomplete) as Hkey.
    destruct (complete_accounting _ _ _ _ _ _ Hkey Hcovered Hlive) as [Hcover' Hlive'].
    assert (Hshape : graph node=RenameMemoWork.leaf).
    { pose proof (Hcoherent node p Hnode Hlookup) as Hshape. destruct p; cbn [RenameMemoNativeEvent.atomic] in Hatomic; try contradiction; exact Hshape. }
    eexists. split; [now apply RenameMemoSchedule.leaf|]. constructor; cbn [RenameMemoSchedule.stack RenameMemoSchedule.completed RenameMemoSchedule.visited RenameMemoSchedule.active length] in *; try assumption. lia.
  - destruct (relates_visit _ _ _ _ _ _ Hrel) as [node [indices [-> [Hnode [Hlookup Htail]]]]].
    pose proof (miss_absent _ _ _ _ _ _ _ _ _ Hprefix Hroot Hnode Hlookup Hindexed Hcovered Hmiss) as Habsent.
    destruct (Hcoherent node (implies p q) Hnode Hlookup) as [lhs [rhs [Hg [Hl Hr]]]].
    destruct (passive_accounting _ _ _ _ _ Hpassive Hsize Hcovered Hlive) as [Hcover' Hlive'].
    eexists. split; [now apply RenameMemoSchedule.binary with (lhs:=lhs) (rhs:=rhs)|].
    constructor; cbn [RenameMemoSchedule.stack RenameMemoSchedule.completed RenameMemoSchedule.visited RenameMemoSchedule.active length] in *; try assumption; [|lia].
    constructor; [|constructor; [now constructor|exact Htail]]. constructor; [|exact Hl].
    apply child_bound with (graph:=graph) (node:=node); [exact Hgraph|exact Hnode|left; exists rhs; now left].
  - destruct (relates_visit _ _ _ _ _ _ Hrel) as [node [indices [-> [Hnode [Hlookup Htail]]]]].
    pose proof (miss_absent _ _ _ _ _ _ _ _ _ Hprefix Hroot Hnode Hlookup Hindexed Hcovered Hmiss) as Habsent.
    destruct (Hcoherent node (all p) Hnode Hlookup) as [child [Hg Hchild]].
    destruct (passive_accounting _ _ _ _ _ Hpassive Hsize Hcovered Hlive) as [Hcover' Hlive'].
    eexists. split; [now apply RenameMemoSchedule.binder with (body:=child)|].
    constructor; cbn [RenameMemoSchedule.stack RenameMemoSchedule.completed RenameMemoSchedule.visited RenameMemoSchedule.active length] in *; try assumption; [|lia].
    constructor; [|constructor; [now constructor|exact Htail]]. constructor; [|exact Hchild].
    apply child_bound with (graph:=graph) (node:=node); [exact Hgraph|exact Hnode|now right].
  - destruct (relates_left _ _ _ _ _ _ _ Hrel) as [node [indices [-> [Hnode [Hlookup Htail]]]]].
    destruct (Hcoherent node (implies p q) Hnode Hlookup) as [lhs [rhs [Hg [Hl Hr]]]].
    destruct (passive_accounting _ _ _ _ _ Hpassive Hsize Hcovered Hlive) as [Hcover' Hlive'].
    eexists. split; [now apply RenameMemoSchedule.next with (lhs:=lhs) (rhs:=rhs)|].
    constructor; cbn [RenameMemoSchedule.stack RenameMemoSchedule.completed RenameMemoSchedule.visited RenameMemoSchedule.active length] in *; try assumption; [|lia].
    constructor; [|constructor; [now constructor|exact Htail]]. constructor; [|exact Hr].
    apply child_bound with (graph:=graph) (node:=node); [exact Hgraph|exact Hnode|left; exists lhs; now right].
  - destruct (relates_right _ _ _ _ _ _ _ _ Hrel) as [node [indices [-> [Hnode [Hlookup Htail]]]]].
    pose proof (completed_key _ _ _ _ _ _ _ _ _ _ Hprefix Hroot Hnode Hlookup Hcomplete) as Hkey.
    destruct (complete_accounting _ _ _ _ _ _ Hkey Hcovered Hlive) as [Hcover' Hlive'].
    eexists. split; [apply RenameMemoSchedule.join|]. constructor; cbn [RenameMemoSchedule.stack RenameMemoSchedule.completed RenameMemoSchedule.visited RenameMemoSchedule.active length] in *; try assumption. lia.
  - destruct (relates_body _ _ _ _ _ _ Hrel) as [node [indices [-> [Hnode [Hlookup Htail]]]]].
    pose proof (completed_key _ _ _ _ _ _ _ _ _ _ Hprefix Hroot Hnode Hlookup Hcomplete) as Hkey.
    destruct (complete_accounting _ _ _ _ _ _ Hkey Hcovered Hlive) as [Hcover' Hlive'].
    eexists. split; [apply RenameMemoSchedule.close|]. constructor; cbn [RenameMemoSchedule.stack RenameMemoSchedule.completed RenameMemoSchedule.visited RenameMemoSchedule.active length] in *; try assumption. lia.
Qed.
End RenameMemoEventSchedule.
