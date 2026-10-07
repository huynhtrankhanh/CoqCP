From CoqCP Require Import Options.
From Submission Require Import KoxiaPolynomial KoxiaArena.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Lia.
Local Open Scope Z_scope.
Definition prefixFlags (values : list Z) start (events : list bool) := forall offset,
  (offset<length events)%nat ->
  nth (start+offset+1) values 0-nth (start+offset) values 0=flag (nth offset events false).
Lemma prefixFlags_head values start event events : prefixFlags values start (event::events) ->
  nth (S start) values 0-nth start values 0=flag event.
Proof.
  intro flags. pose proof (flags 0%nat ltac:(cbn [length]; lia)) as headFlag. cbn [nth] in headFlag.
  replace (start+0)%nat with start in headFlag by lia. replace (start+1)%nat with (S start) in headFlag by lia. exact headFlag.
Qed.
Lemma prefixFlags_tail values start event events : prefixFlags values start (event::events) ->
  prefixFlags values (S start) events.
Proof.
  intros flags offset room. pose proof (flags (S offset) ltac:(cbn [length]; lia)) as tailFlag.
  cbn [nth] in tailFlag. replace (start+S offset)%nat with (S start+offset)%nat in tailFlag by lia. exact tailFlag.
Qed.
Theorem prefixFlags_difference values start events : prefixFlags values start events ->
  nth (start+length events) values 0-nth start values 0=Z.of_nat (specialCount events).
Proof.
  rewrite <-specialCount_agrees. induction events as [|event events IH] in start |- *.
  - intros flags. cbn [length specials]. replace (start+0)%nat with start by lia. lia.
  - intro flags. pose proof (prefixFlags_head values start event events flags) as headFlag.
    pose proof (IH (S start) (prefixFlags_tail values start event events flags)) as tailFlag.
    cbn [length specials]. replace (start+S (length events))%nat with (S start+length events)%nat by lia. lia.
Qed.
Lemma firstn_nth_bool events cut index : (index<cut)%nat ->
  nth index (firstn cut events) false=nth index events false.
Proof.
  induction cut as [|cut IH] in events,index |- *; [lia|].
  intros room. destruct events as [|event events]; [destruct index; reflexivity|].
  destruct index as [|index]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma skipn_nth_bool events cut index : nth index (skipn cut events) false=nth (cut+index) events false.
Proof.
  induction cut as [|cut IH] in events |- *; [reflexivity|].
  destruct events as [|event events]; [destruct index; reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.
Theorem prefixFlags_split values start events cut : (cut<=length events)%nat -> prefixFlags values start events ->
  prefixFlags values start (firstn cut events) /\ prefixFlags values (start+cut) (skipn cut events).
Proof.
  intros cutBound flags. split.
  - intros offset room. rewrite length_firstn,Nat.min_l in room by exact cutBound.
    rewrite firstn_nth_bool by exact room. apply flags. lia.
  - intros offset room. rewrite length_skipn in room. rewrite skipn_nth_bool.
    replace (start+cut+offset)%nat with (start+(cut+offset))%nat by lia. apply flags. lia.
Qed.
Fixpoint prefixTotals events total := match events with
  | [] => [total]
  | event::events => total::prefixTotals events (total+flag event)
  end.
Lemma prefixTotals_length events total : length (prefixTotals events total)=S (length events).
Proof. induction events as [|event events IH] in total |- *; [reflexivity|cbn [prefixTotals length]; rewrite IH; reflexivity]. Qed.
Lemma prefixTotals_head events total : nth 0 (prefixTotals events total) 0=total.
Proof. destruct events; reflexivity. Qed.
Theorem prefixTotals_flags events total : prefixFlags (prefixTotals events total) 0 events.
Proof.
  induction events as [|event events IH] in total |- *.
  - intros offset room. cbn [length] in room. lia.
  - intros offset room. destruct offset as [|offset].
    + cbn [prefixTotals nth Nat.add]. rewrite prefixTotals_head. lia.
    + cbn [prefixTotals nth Nat.add]. pose proof (IH (total+flag event) offset ltac:(cbn [length] in room; lia)) as nextFlag.
      replace (0+offset)%nat with offset in nextFlag by lia. exact nextFlag.
Qed.
