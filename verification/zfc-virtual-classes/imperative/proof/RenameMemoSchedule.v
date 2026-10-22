From CoqCP Require Import Options.
From NativeProof Require Import RenameMemoBounds RenameMemoWork.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.
Module RenameMemoSchedule.
Definition key := (nat*nat)%type.
Inductive frame := visit (node depth : nat) | waiting_left (node depth : nat)
  | waiting_right (node depth : nat) | waiting_body (node depth : nat).
Definition source task : key := match task with visit n d | waiting_left n d | waiting_right n d | waiting_body n d=>(n,d) end.
Fixpoint active stack := match stack with []=>[] | visit _ _::tail=>active tail | task::tail=>source task::active tail end.
Fixpoint calls stack := match stack with []=>0 | visit _ _::tail | waiting_left _ _::tail=>S (calls tail) | _::tail=>calls tail end.
Fixpoint returns_owed stack := match stack with []=>0 | visit _ _::tail=>returns_owed tail
  | waiting_left _ _::tail=>2+returns_owed tail | _::tail=>S (returns_owed tail) end.
Fixpoint ordered stack := match stack with []=>True | task::tail=>Forall (fun below=>fst (source task)<fst (source below)) tail /\ ordered tail end.
Record state := config { visited : list key; completed : list key; stack : list frame; hits : nat; returns : nat }.
Inductive move (graph : nat->RenameMemoWork.shape) : state->state->Prop :=
| hit v d tail n depth h r :
    move graph (config v d (visit n depth::tail) h r) (config v d tail (S h) r)
| leaf v d tail n depth h r : graph n=RenameMemoWork.leaf -> ~In (n,depth) d ->
    move graph (config v d (visit n depth::tail) h r) (config ((n,depth)::v) ((n,depth)::d) tail h r)
| binary v d tail n depth lhs rhs h r : graph n=RenameMemoWork.binary lhs rhs -> ~In (n,depth) d ->
    move graph (config v d (visit n depth::tail) h r)
      (config ((n,depth)::v) d (visit lhs depth::waiting_left n depth::tail) h r)
| binder v d tail n depth body h r : graph n=RenameMemoWork.binder body -> ~In (n,depth) d ->
    move graph (config v d (visit n depth::tail) h r)
      (config ((n,depth)::v) d (visit body (S depth)::waiting_body n depth::tail) h r)
| next v d tail n depth lhs rhs h r : graph n=RenameMemoWork.binary lhs rhs ->
    move graph (config v d (waiting_left n depth::tail) h r)
      (config v d (visit rhs depth::waiting_right n depth::tail) h (S r))
| join v d tail n depth h r :
    move graph (config v d (waiting_right n depth::tail) h r) (config v ((n,depth)::d) tail h (S r))
| close v d tail n depth h r :
    move graph (config v d (waiting_body n depth::tail) h r) (config v ((n,depth)::d) tail h (S r)).
Definition bounded root base query := RenameMemoWork.bounded root base query.
Record invariant root base s : Prop := {
  stack_ordered : ordered (stack s);
  stack_bounded : Forall (fun task=>bounded root base (source task)) (stack s);
  visited_distinct : NoDup (visited s);
  visited_bounded : Forall (bounded root base) (visited s);
  visited_covered : incl (visited s) (completed s++active (stack s));
  hit_account : hits s+calls (stack s)<=length (visited s)+1;
  return_account : returns s+returns_owed (stack s)<=2*length (visited s);
  put_account : length (completed s)+length (active (stack s))<=length (visited s)
}.
Lemma active_in_stack task_stack query : In query (active task_stack) -> exists task, In task task_stack /\ source task=query.
Proof.
  induction task_stack as [|task tail IH]; [contradiction|]. destruct task; cbn [active source]; intro Hin.
  - destruct (IH Hin) as [task [Htask Hsource]]. exists task. split; [now right|exact Hsource].
  - destruct Hin as [<-|Hin]; [eexists; split; [now left|reflexivity]|]. destruct (IH Hin) as [task [Htask Hsource]]. exists task. split; [now right|exact Hsource].
  - destruct Hin as [<-|Hin]; [eexists; split; [now left|reflexivity]|]. destruct (IH Hin) as [task [Htask Hsource]]. exists task. split; [now right|exact Hsource].
  - destruct Hin as [<-|Hin]; [eexists; split; [now left|reflexivity]|]. destruct (IH Hin) as [task [Htask Hsource]]. exists task. split; [now right|exact Hsource].
Qed.
Lemma miss_fresh v done tail node depth : ordered (visit node depth::tail) ->
  incl v (done++active tail) -> ~In (node,depth) done -> ~In (node,depth) v.
Proof.
  intros [Hordered _] Hcovered Hmiss Hin. apply Hcovered in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [contradiction|].
  destruct (active_in_stack tail (node,depth) Hin) as [task [Htask Hsource]].
  apply Forall_forall with (x:=task) in Hordered; [|exact Htask]. rewrite Hsource in Hordered. cbn in Hordered. lia.
Qed.
Lemma ordered_replace old new tail : source old=source new -> ordered (old::tail) -> ordered (new::tail).
Proof. intros Hsame [Htail Hordered]. split; [now rewrite <-Hsame|exact Hordered]. Qed.
Lemma ordered_push parent child wait tail : source parent=source wait ->
  fst (source child)<fst (source parent) -> ordered (parent::tail) -> ordered (child::wait::tail).
Proof.
  intros Hsame Hchild [Htail Hordered]. split.
  - constructor; [now rewrite <-Hsame|]. eapply Forall_impl; [|exact Htail]. intros task Htask. exact (Nat.lt_trans _ _ _ Hchild Htask).
  - now apply ordered_replace with (old:=parent).
Qed.
Lemma bounded_child root base node depth child binders : bounded root base (node,depth) -> child<node -> binders<=1 ->
  bounded root base (child,depth+binders).
Proof. unfold bounded,RenameMemoWork.bounded. cbn. intros. lia. Qed.
Theorem initial root base : invariant root base (config [] [] [visit root base] 0 0).
Proof.
  constructor; cbn [stack visited completed hits returns active calls returns_owed ordered length].
  - split; [constructor|exact I].
  - constructor; [apply RenameMemoWork.bounded_root|constructor].
  - constructor.
  - constructor.
  - intros query Hin. contradiction.
  - lia.
  - lia.
  - lia.
Qed.
Theorem preserves graph root base before after : RenameMemoWork.older graph -> invariant root base before ->
  move graph before after -> invariant root base after.
Proof.
  intros Hgraph Hinv Hmove. destruct Hinv as [Hordered Hstack Hdistinct Hbound Hcovered Hhits Hreturns Hputs].
  destruct Hmove as [v done tail n depth h r|v done tail n depth h r Hg Hmiss|
    v done tail n depth lhs rhs h r Hg Hmiss|v done tail n depth body h r Hg Hmiss|
    v done tail n depth lhs rhs h r Hg|v done tail n depth h r|v done tail n depth h r];
    cbn [stack visited completed hits returns active calls returns_owed length] in *.
  all: try (pose proof (miss_fresh _ _ _ _ _ Hordered Hcovered Hmiss) as Hfresh).
  all: try (pose proof (Hgraph n) as Hchildren; rewrite Hg in Hchildren; cbn in Hchildren).
  all: inversion Hstack as [|task tail' Htop Htail]; subst task tail'; clear Hstack.
  - constructor; cbn [stack visited completed hits returns active calls returns_owed length]; try assumption; [exact (proj2 Hordered)|lia].
  - constructor; cbn [stack visited completed hits returns active calls returns_owed length]; try assumption.
    + exact (proj2 Hordered).
    + now constructor.
    + now constructor.
    + intros query [<-|Hin]; apply in_or_app; [left; now left|].
      specialize (Hcovered query Hin). apply in_app_or in Hcovered. destruct Hcovered; [left; now right|now right].
    + lia.
    + lia.
    + lia.
  - destruct Hchildren as [Hlhs Hrhs]. constructor; cbn [stack visited completed hits returns active calls returns_owed length]; try assumption.
    + now apply ordered_push with (parent:=visit n depth).
    + constructor; [|constructor; assumption]. change (bounded root base (lhs,depth)). replace depth with (depth+0) at 1 by lia.
      apply bounded_child with (node:=n); [exact Htop|exact Hlhs|lia].
    + now constructor.
    + now constructor.
    + intros query [<-|Hin]; [apply in_or_app; right; now left|].
      specialize (Hcovered query Hin). apply in_app_or in Hcovered. destruct Hcovered; apply in_or_app; [now left|right; now right].
    + lia.
    + lia.
    + cbn [length]. lia.
  - constructor; cbn [stack visited completed hits returns active calls returns_owed length]; try assumption.
    + now apply ordered_push with (parent:=visit n depth).
    + constructor; [|constructor; assumption]. change (bounded root base (body,S depth)).
      replace (S depth) with (depth+1) by lia. apply bounded_child with (node:=n); [exact Htop|exact Hchildren|lia].
    + now constructor.
    + now constructor.
    + intros query [<-|Hin]; [apply in_or_app; right; now left|].
      specialize (Hcovered query Hin). apply in_app_or in Hcovered. destruct Hcovered; apply in_or_app; [now left|right; now right].
    + lia.
    + lia.
    + cbn [length]. lia.
  - destruct Hchildren as [Hlhs Hrhs]. constructor; cbn [stack visited completed hits returns active calls returns_owed length]; try assumption.
    + now apply ordered_push with (parent:=waiting_left n depth).
    + constructor; [|constructor; assumption]. change (bounded root base (rhs,depth)). replace depth with (depth+0) at 1 by lia.
      apply bounded_child with (node:=n); [exact Htop|exact Hrhs|lia].
    + lia.
  - constructor; cbn [stack visited completed hits returns active calls returns_owed length]; try assumption.
    + exact (proj2 Hordered).
    + intros query Hin. specialize (Hcovered query Hin). clear Hin. apply in_app_or in Hcovered.
      destruct Hcovered as [Hin|[<-|Hin]]; apply in_or_app; [left; now right|left; now left|now right].
    + lia.
    + cbn [length] in Hputs. lia.
  - constructor; cbn [stack visited completed hits returns active calls returns_owed length]; try assumption.
    + exact (proj2 Hordered).
    + intros query Hin. specialize (Hcovered query Hin). clear Hin. apply in_app_or in Hcovered.
      destruct Hcovered as [Hin|[<-|Hin]]; apply in_or_app; [left; now right|left; now left|now right].
    + lia.
    + cbn [length] in Hputs. lia.
Qed.

Definition elapsed s := length (visited s)+hits s+returns s.
Lemma move_elapsed graph before after : move graph before after -> elapsed after=S (elapsed before).
Proof. intro Hmove. destruct Hmove; unfold elapsed; cbn; lia. Qed.
Inductive reached graph root base : nat->state->Prop :=
| reached_initial : reached graph root base 0 (config [] [] [visit root base] 0 0)
| reached_step steps before after : reached graph root base steps before -> move graph before after ->
    reached graph root base (S steps) after.
Theorem reached_invariant graph root base steps s : RenameMemoWork.older graph -> reached graph root base steps s -> invariant root base s.
Proof. intros Hgraph Hreached. induction Hreached as [|steps before after Hreach IH Hmove]; [apply initial|now apply preserves with (graph:=graph) (before:=before)]. Qed.
Theorem reached_elapsed graph root base steps s : reached graph root base steps s -> elapsed s=steps.
Proof. intro Hreached. induction Hreached as [|steps before after Hreach IH Hmove]; [reflexivity|]. rewrite (move_elapsed _ _ _ Hmove),IH. reflexivity. Qed.
Theorem fresh_bound root base s : invariant root base s -> length (visited s)<=S root*S root.
Proof.
  intro Hinv. apply (RenameMemoBounds.distinct_pairs_from base (S root) (visited s) (visited_distinct _ _ _ Hinv)).
  eapply Forall_impl; [|exact (visited_bounded _ _ _ Hinv)]. intros [node depth] Hbound.
  unfold bounded,RenameMemoWork.bounded in Hbound. cbn in *. lia.
Qed.
Theorem accounting_bound root base s : invariant root base s ->
  elapsed s<=4*(S root*S root)+1 /\
  length (completed s)+length (active (stack s))<=S root*S root.
Proof.
  intro Hinv. pose proof (fresh_bound _ _ _ Hinv).
  pose proof (hit_account _ _ _ Hinv). pose proof (return_account _ _ _ Hinv). pose proof (put_account _ _ _ Hinv).
  unfold elapsed. split; lia.
Qed.
Lemma ordered_distinct tasks : ordered tasks -> NoDup (map (fun task=>fst (source task)) tasks).
Proof.
  induction tasks as [|task tail IH]; [constructor|]. intros [Hhead Htail]. cbn [map]. constructor; [|now apply IH].
  intro Hin. apply in_map_iff in Hin. destruct Hin as [other [Hsame Hin]].
  apply Forall_forall with (x:=other) in Hhead; [|exact Hin]. rewrite Hsame in Hhead. lia.
Qed.
Theorem stack_bound root base s : invariant root base s -> length (stack s)<=S root.
Proof.
  intro Hinv. pose proof (ordered_distinct _ (stack_ordered _ _ _ Hinv)) as Hdistinct.
  assert (Hincluded : incl (map (fun task=>fst (source task)) (stack s)) (seq 0 (S root))).
  { intros node Hin. apply in_map_iff in Hin. destruct Hin as [task [<- Hin]].
    pose proof (stack_bounded _ _ _ Hinv) as Hbounds. apply Forall_forall with (x:=task) in Hbounds; [|exact Hin].
    unfold bounded,RenameMemoWork.bounded in Hbounds. apply in_seq. lia. }
  pose proof (NoDup_incl_length Hdistinct Hincluded) as Hlength. now rewrite length_map,length_seq in Hlength.
Qed.
Theorem polynomial_trace graph root base steps s : RenameMemoWork.older graph -> reached graph root base steps s ->
  steps<=4*(S root*S root)+1 /\ steps<RenameMemoBounds.fuel root /\
  length (completed s)+length (active (stack s))<=S root*S root /\ length (stack s)<=S root.
Proof.
  intros Hgraph Hreach. pose proof (reached_invariant _ _ _ _ _ Hgraph Hreach) as Hinv.
  destruct (accounting_bound _ _ _ Hinv) as [Hwork Hdone]. rewrite (reached_elapsed _ _ _ _ _ Hreach) in Hwork.
  split; [exact Hwork|]. split; [unfold RenameMemoBounds.fuel; nia|]. split; [exact Hdone|now apply stack_bound with (base:=base)].
Qed.
End RenameMemoSchedule.
