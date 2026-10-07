From CoqCP Require Import Options Imperative Execution SwapUpdate.
From Submission Require Import KoxiaPolynomial KoxiaModular KoxiaFourier KoxiaIntegers KoxiaArrays KoxiaTables KoxiaTableLoops KoxiaArrayLoops KoxiaPolynomialBuffers KoxiaLeaf KoxiaLeafEvents.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Existing Instance congruent_equivalence.
Local Existing Instance congruent_add.
Fixpoint ordinaryCount (events : list bool) := match events with [] => 0%nat | event::events =>
  ((if event then 0 else 1)+ordinaryCount events)%nat end.
Fixpoint runBuffers events values len : list Z*nat := match events with
  | [] => (values,len)
  | event::events => runBuffers events (eventBuffer event values len) (eventLength event len)
  end.
Lemma ordinaryCount_bound events : (ordinaryCount events<=length events)%nat.
Proof. induction events as [|event events IH]; cbn [ordinaryCount length]; [lia|destruct event; lia]. Qed.
Lemma eventBuffer_length event values len : length (eventBuffer event values len)=length values.
Proof. destruct event; cbn [eventBuffer]; [apply specialBuffer_length|apply ordinaryBuffer_length]. Qed.
Lemma runBuffers_length events values len : length (fst (runBuffers events values len))=length values.
Proof.
  induction events as [|event events IH] in values,len |- *; [reflexivity|].
  cbn [runBuffers]. rewrite IH,eventBuffer_length. reflexivity.
Qed.
Lemma runBuffers_active events values len : snd (runBuffers events values len)=(len+ordinaryCount events)%nat.
Proof.
  induction events as [|event events IH] in values,len |- *.
  - cbn [runBuffers ordinaryCount snd]. lia.
  - cbn [runBuffers ordinaryCount]. rewrite IH. destruct event; cbn [eventLength]; lia.
Qed.
Lemma runBuffers_canonical events values len : (len+length events<=length values)%nat -> tableCanonical values ->
  tableCanonical (fst (runBuffers events values len)).
Proof.
  induction events as [|event events IH] in values,len |- *; [intros; assumption|].
  intros room canonical. cbn [runBuffers]. apply IH.
  - rewrite eventBuffer_length. destruct event; cbn [eventLength] in *; cbn [length] in room; lia.
  - destruct event; cbn [eventBuffer]; [apply specialBuffer_canonical; exact canonical|apply ordinaryBuffer_canonical; [cbn [length] in room; lia|exact canonical]].
Qed.
Lemma boundaryStep_congruent event p q : (forall j, congruent (p j) (q j)) ->
  forall j, congruent (boundaryStep event p j) (boundaryStep event q j).
Proof.
  intros same j. unfold boundaryStep,unrestrictedStep.
  destruct (j <? 0); [reflexivity|]. destruct event; apply congruent_add; apply same.
Qed.
Lemma run_congruent events p q : (forall j, congruent (p j) (q j)) -> forall j, congruent (run events p j) (run events q j).
Proof.
  induction events as [|event events IH] in p,q |- *; [intros same; exact same|].
  intros same j. cbn [run]. apply IH,boundaryStep_congruent. exact same.
Qed.
Theorem runBuffers_correct events values len : (len+length events<=length values)%nat -> forall j,
  congruent (activeCoefficient (fst (runBuffers events values len)) (snd (runBuffers events values len)) j)
    (run events (activeCoefficient values len) j).
Proof.
  induction events as [|event events IH] in values,len |- *; [intros; reflexivity|].
  intros room j. cbn [runBuffers run].
  transitivity (run events (activeCoefficient (eventBuffer event values len) (eventLength event len)) j).
  - apply IH. rewrite eventBuffer_length. destruct event; cbn [eventLength]; cbn [length] in room; lia.
  - apply run_congruent. intro index. destruct event; cbn [eventBuffer eventLength].
    + apply specialBuffer_correct. cbn [length] in room; lia.
    + apply ordinaryBuffer_correct. cbn [length] in room; lia.
Qed.

Theorem generated_leaf_loop_execution b nums fuel total start events state values len continuation :
  length events=fuel -> (fuel<=total)%nat ->
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_length=Z.of_nat len ->
  (start+total<length (memory state arraydef_0__prefix))%nat ->
  Z.of_nat (start+total+1)<18446744073709551616 ->
  (forall offset, (offset<fuel)%nat ->
    nth (start+(total-fuel)+offset+1) (memory state arraydef_0__prefix) 0-
    nth (start+(total-fuel)+offset) (memory state arraydef_0__prefix) 0=
    (if nth offset events false then 1 else 0)) ->
  (len+fuel<=length values)%nat -> Z.of_nat (len+fuel)<koxiaModulus -> tableCanonical values ->
  exists final,
    exec (eliminateLocalVariables b nums (loop fuel (leafEventBody (Z.of_nat total)) >>= continuation))
      (withArray state arraydef_0__poly values)=
    exec (eliminateLocalVariables b final (continuation tt))
      (withArray state arraydef_0__poly (fst (runBuffers events values len))) /\
    final vardef_0__solve_length=Z.of_nat (snd (runBuffers events values len)) /\
    (forall name, name<>vardef_0__solve_value -> name<>vardef_0__solve_previous -> name<>vardef_0__solve_length -> name<>vardef_0__solve_flag -> final name=nums name).
Proof.
  induction fuel as [|fuel IH] in nums,events,values,len |- *.
  - intros eventsLength fuelBound leftEq lengthEq prefixRoom addressesFit flags room lengthBound canonical.
    destruct events as [|event events]; [|cbn [length] in eventsLength; lia].
    exists nums. split; [reflexivity|]. split; [exact lengthEq|intros; reflexivity].
  - intros eventsLength fuelBound leftEq lengthEq prefixRoom addressesFit flags room lengthBound canonical.
    destruct events as [|event events]; [cbn [length] in eventsLength; lia|].
    assert (eventRoom : (S len<=length values)%nat) by lia.
    assert (eventPrefixRoom : (start+(total-fuel-1)+1<length (memory state arraydef_0__prefix))%nat) by lia.
    assert (eventFlag : nth (start+(total-fuel-1)+1) (memory state arraydef_0__prefix) 0-
      nth (start+(total-fuel-1)) (memory state arraydef_0__prefix) 0=(if event then 1 else 0)).
    { pose proof (flags 0%nat ltac:(lia)) as headFlag. cbn [nth] in headFlag.
      replace (start+(total-S fuel)+0)%nat with (start+(total-fuel-1))%nat in headFlag by lia. exact headFlag. }
    rewrite loop_S,<-bindAssoc,leafEventNormalized with (start:=start) (len:=len)
      by (try assumption; lia). rewrite exec_bind.
    destruct (leafEventAction_execution start (total-fuel-1) len nums state values event lengthEq eventPrefixRoom eventFlag
      eventRoom ltac:(lia) canonical) as [finished [eventExecution [finishedLength preserved]]].
    rewrite eventExecution. cbn [optionBind fst snd].
    assert (finishedLeft : finished vardef_0__solve_l=Z.of_nat start).
    { rewrite preserved by congruence. exact leftEq. }
    assert (tailFlags : forall offset, (offset<fuel)%nat ->
      nth (start+(total-fuel)+offset+1) (memory state arraydef_0__prefix) 0-
      nth (start+(total-fuel)+offset) (memory state arraydef_0__prefix) 0=
      (if nth offset events false then 1 else 0)).
    { intros offset indexBound. pose proof (flags (S offset) ltac:(lia)) as tailFlag. cbn [nth] in tailFlag.
      replace (start+(total-S fuel)+S offset)%nat with (start+(total-fuel)+offset)%nat in tailFlag by lia. exact tailFlag. }
    assert (tailRoom : (eventLength event len+fuel<=length (eventBuffer event values len))%nat).
    { rewrite eventBuffer_length. destruct event; cbn [eventLength]; lia. }
    assert (tailBound : Z.of_nat (eventLength event len+fuel)<koxiaModulus).
    { destruct event; cbn [eventLength]; lia. }
    assert (stepCanonical : tableCanonical (eventBuffer event values len)).
    { destruct event; cbn [eventBuffer]; [apply specialBuffer_canonical; exact canonical|apply ordinaryBuffer_canonical; assumption]. }
    destruct (IH finished events (eventBuffer event values len) (eventLength event len)
      ltac:(cbn [length] in eventsLength; lia) ltac:(lia) finishedLeft finishedLength prefixRoom addressesFit tailFlags tailRoom tailBound stepCanonical)
      as [final [execution [finalLength others]]].
    exists final. split; [exact execution|]. split; [exact finalLength|].
    intros name notValue notPrevious notLength notFlag. rewrite others,preserved by assumption. reflexivity.
Qed.
