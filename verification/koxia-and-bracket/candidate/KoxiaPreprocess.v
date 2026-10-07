From CoqCP Require Import Options Imperative Execution SwapUpdate.
From Submission Require Import KoxiaIntegers KoxiaArrays KoxiaArrayLoops KoxiaTables KoxiaTableLoops KoxiaSolveProgram KoxiaConvolution KoxiaFrameStores KoxiaPolynomial KoxiaLeafRun KoxiaArena KoxiaPrefixFlags KoxiaPaths KoxiaWorkspace KoxiaMemoryPreservation.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque funcdef_0__convolve funcdef_0__ntt.

Definition prepReadAddress (nums : varsfuncdef_0__solve->Z) (reverse : bool) (total : Z) (remaining : nat) :=
  let index:=total-Z.of_nat remaining-1 in
  if reverse then coerceInt (coerceInt (nums vardef_0__solve_end-index) 64-1) 64
  else coerceInt (nums vardef_0__solve_begin+index) 64.

Definition prepClosingNums (nums : varsfuncdef_0__solve->Z) :=
  let balance:=coerceInt (nums vardef_0__solve_balance-1) 64 in
  let prepared:=update (update nums vardef_0__solve_balance balance) vardef_0__solve_flag 0 in
  if bool_decide (toSigned balance 64<toSigned (nums vardef_0__solve_minimum) 64)
  then update (update prepared vardef_0__solve_minimum balance) vardef_0__solve_flag 1
  else prepared.

Definition prepCharacterAction (nums : varsfuncdef_0__solve->Z) :
  Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue (varsfuncdef_0__solve->Z) :=
  if bool_decide (nums vardef_0__solve_ch=40)
  then Done _ _ _ (update nums vardef_0__solve_balance (coerceInt (nums vardef_0__solve_balance+1) 64))
  else let adjusted:=prepClosingNums nums in
    tableRead arraydef_0__prefix (nums vardef_0__solve_count) >>= fun previous =>
    tableWrite arraydef_0__prefix (coerceInt (nums vardef_0__solve_count+1) 64)
      (coerceInt (previous+adjusted vardef_0__solve_flag) 64) >>= fun _ =>
    Done _ _ _ (update adjusted vardef_0__solve_count (coerceInt (nums vardef_0__solve_count+1) 64)).

#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 : koxia_table_steps.
Ltac normalize_prep := repeat progress
  (normalize_table_loop; repeat first [rewrite lookupSame|rewrite lookupDifferent by congruence]).

Theorem prepStepNormalized b nums total remaining continuation :
  eliminateLocalVariables b nums (solvePrepBody total remaining >>= continuation)=
  tableRead arraydef_0__sequence (prepReadAddress nums (b vardef_0__solve_reverse) total remaining) >>= fun stored =>
  prepCharacterAction (update nums vardef_0__solve_ch
    (if b vardef_0__solve_reverse then Z.lxor (coerceInt stored 64) 1 else coerceInt stored 64)) >>= fun finished =>
  eliminateLocalVariables b finished (continuation KeepGoing).
Proof.
  unfold solvePrepBody,numberLocalGet,numberLocalSet,booleanLocalGet,addInt,subInt,xorBits,retrieve,store.
  normalize_prep. destruct (b vardef_0__solve_reverse) eqn:reverse; normalize_prep.
  all: unfold prepReadAddress,tableRead; cbn [bind];
    apply f_equal; apply functional_extensionality; intro stored; normalize_prep.
  all: unfold prepCharacterAction,prepClosingNums; normalize_prep.
  all: repeat (case_bool_decide; normalize_prep; try reflexivity; try congruence).
Qed.

Definition prepInput (state : @Machine arrayIndex1 (arrayType _ environment1))
  (nums : varsfuncdef_0__solve->Z) (reverse : bool) (total : Z) (word : list bool) :=
  forall offset, (offset<length word)%nat ->
    let address:=prepReadAddress nums reverse total (length word-S offset) in
    0<=address /\ (Z.to_nat address<length (memory state arraydef_0__sequence))%nat /\
    nth (Z.to_nat address) (memory state arraydef_0__sequence) 0=
      (if reverse then if negb (nth offset word false) then 40 else 41
       else if nth offset word false then 40 else 41).

Lemma prepInput_transfer before after nums finished reverse total word :
  prepInput before nums reverse total word ->
  memory after arraydef_0__sequence=memory before arraydef_0__sequence ->
  finished vardef_0__solve_begin=nums vardef_0__solve_begin ->
  finished vardef_0__solve_end=nums vardef_0__solve_end ->
  prepInput after finished reverse total word.
Proof.
  intros input same beginEq endEq offset range.
  unfold prepReadAddress. rewrite beginEq,endEq,same.
  exact (input offset range).
Qed.

Lemma prepInput_tail state nums reverse total opening word :
  prepInput state nums reverse total (opening::word) -> prepInput state nums reverse total word.
Proof.
  intros input offset range. pose proof (input (S offset) ltac:(cbn [length]; lia)) as atNext.
  cbn [length nth] in atNext.
  replace (S (length word)-S (S offset))%nat with (length word-S offset)%nat in atNext by lia.
  exact atNext.
Qed.

Fixpoint preprocessAction fuel total b (nums : varsfuncdef_0__solve->Z) :
  Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue (varsfuncdef_0__solve->Z) :=
  match fuel with
  | O=>Done _ _ _ nums
  | S fuel=>tableRead arraydef_0__sequence (prepReadAddress nums (b vardef_0__solve_reverse) total fuel) >>= fun stored =>
      prepCharacterAction (update nums vardef_0__solve_ch
        (if b vardef_0__solve_reverse then Z.lxor (coerceInt stored 64) 1 else coerceInt stored 64)) >>= fun finished=>
      preprocessAction fuel total b finished
  end.

Theorem prepLoopNormalized b nums fuel total continuation :
  eliminateLocalVariables b nums (loop fuel (solvePrepBody total) >>= continuation)=
  preprocessAction fuel total b nums >>= fun finished=>eliminateLocalVariables b finished (continuation tt).
Proof.
  induction fuel as [|fuel IH] in nums |- *; [reflexivity|].
  rewrite loop_S,<-bindAssoc,prepStepNormalized. cbn [preprocessAction].
  rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intro stored.
  rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intro finished.
  apply IH.
Qed.

Definition nextPrepOrigin (origin : Z) (height : nat) (opening : bool) := if opening then origin else
  match height with O=>origin-1 | S _=>origin end.
Definition nextPrepHeight (height : nat) (opening : bool) := if opening then S height else Nat.pred height.
Definition nextPrepCount (count : nat) (opening : bool) := if opening then count else S count.
Definition prepCharacterNums (nums : varsfuncdef_0__solve->Z) (opening : bool) :=
  if opening then update nums vardef_0__solve_balance (coerceInt (nums vardef_0__solve_balance+1) 64)
  else update (prepClosingNums nums) vardef_0__solve_count (coerceInt (nums vardef_0__solve_count+1) 64).
Definition prepCharacterMemory (state : @Machine arrayIndex1 (arrayType _ environment1)) (count height : nat) (opening : bool) :=
  if opening then state else withArray state arraydef_0__prefix
    (<[S count:=(nth count (memory state arraydef_0__prefix) 0+(if Nat.eqb height 0 then 1 else 0))]>
      (memory state arraydef_0__prefix)).

Lemma prepClosingNums_greedy nums origin height :
  nums vardef_0__solve_balance=coerceInt (origin+Z.of_nat height) 64 ->
  nums vardef_0__solve_minimum=coerceInt origin 64 ->
  -500000<=origin<=0 -> origin+Z.of_nat height<=500000 ->
  prepClosingNums nums vardef_0__solve_balance=coerceInt
    (nextPrepOrigin origin height false+Z.of_nat (nextPrepHeight height false)) 64 /\
  prepClosingNums nums vardef_0__solve_minimum=coerceInt (nextPrepOrigin origin height false) 64 /\
  prepClosingNums nums vardef_0__solve_flag=(if Nat.eqb height 0 then 1 else 0).
Proof.
  intros balanceEq minimumEq originBound balanceBound.
  unfold prepClosingNums. rewrite balanceEq,minimumEq,coerce64_sub.
  rewrite !signed64_coerce by lia.
  destruct height as [|height].
  - rewrite bool_decide_true by lia. cbn [nextPrepOrigin nextPrepHeight Nat.pred Nat.eqb Z.of_nat].
    repeat split; repeat first [rewrite lookupSame|rewrite lookupDifferent by congruence]; f_equal; lia.
  - rewrite bool_decide_false by (rewrite Nat2Z.inj_succ; lia).
    cbn [nextPrepOrigin nextPrepHeight Nat.pred Nat.eqb].
    repeat split; repeat first [rewrite lookupSame|rewrite lookupDifferent by congruence]; try reflexivity.
    all: f_equal; rewrite ?Nat2Z.inj_succ; lia.
Qed.

Lemma prepClosingNums_other nums name : name<>vardef_0__solve_balance -> name<>vardef_0__solve_minimum ->
  name<>vardef_0__solve_flag -> prepClosingNums nums name=nums name.
Proof.
  intros. unfold prepClosingNums. destruct (bool_decide _);
    repeat first [rewrite lookupSame|rewrite lookupDifferent by congruence]; reflexivity.
Qed.

Lemma prepCharacterNums_other nums opening name : name<>vardef_0__solve_balance -> name<>vardef_0__solve_minimum ->
  name<>vardef_0__solve_count -> name<>vardef_0__solve_flag -> prepCharacterNums nums opening name=nums name.
Proof.
  intros. unfold prepCharacterNums. destruct opening; rewrite lookupDifferent by congruence; [reflexivity|].
  apply prepClosingNums_other; assumption.
Qed.

Theorem prepCharacter_execution (state : @Machine arrayIndex1 (arrayType _ environment1))
  (nums : varsfuncdef_0__solve->Z) (opening : bool) (origin : Z) (height count : nat) :
  nums vardef_0__solve_ch=(if opening then 40 else 41) ->
  nums vardef_0__solve_balance=coerceInt (origin+Z.of_nat height) 64 ->
  nums vardef_0__solve_minimum=coerceInt origin 64 -> nums vardef_0__solve_count=Z.of_nat count ->
  -500000<=origin<=0 -> origin+Z.of_nat height<=500000 -> Z.of_nat count<=500000 ->
  (S count<length (memory state arraydef_0__prefix))%nat ->
  0<=nth count (memory state arraydef_0__prefix) 0<=500000 ->
  exec (prepCharacterAction nums) state=Some (prepCharacterNums nums opening,prepCharacterMemory state count height opening) /\
  prepCharacterNums nums opening vardef_0__solve_balance=coerceInt
    (nextPrepOrigin origin height opening+Z.of_nat (nextPrepHeight height opening)) 64 /\
  prepCharacterNums nums opening vardef_0__solve_minimum=coerceInt (nextPrepOrigin origin height opening) 64 /\
  prepCharacterNums nums opening vardef_0__solve_count=Z.of_nat (nextPrepCount count opening).
Proof.
  intros charEq balanceEq minimumEq countEq originBound balanceBound countBound prefixRoom prefixBound.
  destruct opening.
  - unfold prepCharacterAction. rewrite charEq,bool_decide_true by reflexivity.
    cbn [prepCharacterNums prepCharacterMemory nextPrepOrigin nextPrepHeight nextPrepCount exec].
    split; [reflexivity|]. split.
    + rewrite lookupSame,balanceEq,coerce64_add. f_equal. rewrite Nat2Z.inj_succ. lia.
    + split; rewrite lookupDifferent by congruence; assumption.
  - unfold prepCharacterAction. rewrite charEq,bool_decide_false by lia.
    pose proof (prepClosingNums_greedy nums origin height balanceEq minimumEq originBound balanceBound)
      as [newBalance [newMinimum newFlag]].
    rewrite countEq,exec_bind,tableRead_execution by (try congruence; lia).
    cbn [optionBind fst snd intValue]. rewrite newFlag.
    rewrite (coerce64_small (Z.of_nat count+1)); [|change (0<=Z.of_nat count+1<18446744073709551616); lia].
    replace (Z.of_nat count+1) with (Z.of_nat (S count)) by lia.
    rewrite coerce64_small by (destruct (Nat.eqb height 0); lia).
    rewrite tableStore_execution by exact prefixRoom.
    split.
    { cbn [prepCharacterNums prepCharacterMemory exec]. rewrite countEq,coerce64_small by lia.
      replace (Z.of_nat count+1) with (Z.of_nat (S count)) by lia. reflexivity. }
    cbn [prepCharacterNums nextPrepCount].
    split; [rewrite lookupDifferent by congruence; exact newBalance|].
    split; [rewrite lookupDifferent by congruence; exact newMinimum|].
    rewrite lookupSame,countEq,coerce64_small by lia. f_equal. lia.
Qed.

Lemma prefixFlags_extend values events event :
  (S (length events)<length values)%nat -> prefixFlags values 0 events ->
  prefixFlags (<[S (length events):=nth (length events) values 0+flag event]>values) 0 (events++[event]).
Proof.
  intros room flags index range. rewrite length_app in range. cbn [length] in range.
  destruct (Nat.lt_ge_cases index (length events)) as [before|last].
  - rewrite app_nth1 by exact before. unfold prefixFlags in flags.
    rewrite !nthUpdateExcept by lia. apply flags. exact before.
  - assert (lastEq : index=length events) by lia. subst index.
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    replace (0+length events+1)%nat with (S (length events)) by lia.
    replace (0+length events)%nat with (length events) by lia.
    rewrite nthUpdate by exact room. rewrite nthUpdateExcept by lia. lia.
Qed.

Definition prepEventsAppend (events : list bool) (opening : bool) (height : nat) :=
  if opening then events else events++[Nat.eqb height 0].

Lemma prepCharacterMemory_other state count height opening name : name<>arraydef_0__prefix ->
  memory (prepCharacterMemory state count height opening) name=memory state name.
Proof. intro different. unfold prepCharacterMemory. destruct opening; [reflexivity|apply withArray_preserve_other; exact different]. Qed.

Lemma prepCharacterMemory_length state count height opening :
  length (memory (prepCharacterMemory state count height opening) arraydef_0__prefix)=
  length (memory state arraydef_0__prefix).
Proof. unfold prepCharacterMemory. destruct opening; [reflexivity|rewrite withArray_preserve_same,length_insert; reflexivity]. Qed.

Lemma prepCharacterMemory_zero state count height opening :
  (S count<length (memory state arraydef_0__prefix))%nat ->
  nth 0 (memory (prepCharacterMemory state count height opening) arraydef_0__prefix) 0=
  nth 0 (memory state arraydef_0__prefix) 0.
Proof.
  intro room. unfold prepCharacterMemory. destruct opening; [reflexivity|].
  rewrite withArray_preserve_same,nthUpdateExcept by lia. reflexivity.
Qed.

Lemma prepCharacterMemory_flags state events height opening :
  (S (length events)<length (memory state arraydef_0__prefix))%nat ->
  prefixFlags (memory state arraydef_0__prefix) 0 events ->
  prefixFlags (memory (prepCharacterMemory state (length events) height opening) arraydef_0__prefix)
    0 (prepEventsAppend events opening height).
Proof.
  intros room flags. unfold prepCharacterMemory,prepEventsAppend. destruct opening; [exact flags|].
  rewrite withArray_preserve_same. change (prefixFlags
    (<[S (length events):=nth (length events) (memory state arraydef_0__prefix) 0+flag (Nat.eqb height 0)]>
      (memory state arraydef_0__prefix)) 0 (events++[Nat.eqb height 0])).
  apply prefixFlags_extend; assumption.
Qed.

Lemma prepEventsAppend_length events opening height :
  length (prepEventsAppend events opening height)=nextPrepCount (length events) opening.
Proof. unfold prepEventsAppend,nextPrepCount. destruct opening; [reflexivity|rewrite length_app; cbn [length]; lia]. Qed.

Lemma prepEventsAppend_suffix events opening height word :
  prepEventsAppend events opening height++eventsFrom word (nextPrepHeight height opening)=
  events++eventsFrom (opening::word) height.
Proof.
  unfold prepEventsAppend,nextPrepHeight. destruct opening; [reflexivity|].
  destruct height; cbn [Nat.pred Nat.eqb eventsFrom]; rewrite <-app_assoc; reflexivity.
Qed.

Theorem preprocessAction_execution (word : list bool) b total nums state origin height events n :
  (length events+length word<=n)%nat -> Z.of_nat n<=500000 ->
  nums vardef_0__solve_balance=coerceInt (origin+Z.of_nat height) 64 ->
  nums vardef_0__solve_minimum=coerceInt origin 64 -> nums vardef_0__solve_count=Z.of_nat (length events) ->
  Z.of_nat (length word)-500000<=origin<=0 -> Z.of_nat (height+length word)<=500000 ->
  @List.length Z (memory state arraydef_0__prefix)=S n -> nth 0 (memory state arraydef_0__prefix) 0=0 ->
  prefixFlags (memory state arraydef_0__prefix) 0 events -> prepInput state nums (b vardef_0__solve_reverse) total word ->
  exists finished final,
    exec (preprocessAction (length word) total b nums) state=Some (finished,final) /\
    finished vardef_0__solve_count=Z.of_nat (length (events++eventsFrom word height)) /\
    prefixFlags (memory final arraydef_0__prefix) 0 (events++eventsFrom word height) /\
    @List.length Z (memory final arraydef_0__prefix)=S n /\ nth 0 (memory final arraydef_0__prefix) 0=0 /\
    stdin final=stdin state /\ stdout final=stdout state /\
    (forall name, name<>arraydef_0__prefix -> memory final name=memory state name) /\
    (forall name, name<>vardef_0__solve_balance -> name<>vardef_0__solve_minimum ->
      name<>vardef_0__solve_count -> name<>vardef_0__solve_flag -> name<>vardef_0__solve_ch -> finished name=nums name).
Proof.
  induction word as [|opening word IH] in nums,state,origin,height,events |- *.
  - intros room nBound balanceEq minimumEq countEq originBound heightBound prefixLength zero flags input.
    exists nums,state. cbn [length preprocessAction eventsFrom]. rewrite app_nil_r.
    repeat split; try assumption; reflexivity.
  - intros room nBound balanceEq minimumEq countEq originBound heightBound prefixLength zero flags input.
    pose proof (input 0%nat ltac:(cbn [length]; lia)) as headInput.
    cbn [length nth] in headInput. replace (S (length word)-1)%nat with (length word) in headInput by lia.
    destruct headInput as [addressNonnegative [sourceRoom sourceCharacter]].
    pose (character := if opening then 40 else 41).
    pose (prepared := update nums vardef_0__solve_ch character).
    assert (loadedCharacter :
      (if b vardef_0__solve_reverse
       then Z.lxor (coerceInt (nth (Z.to_nat (prepReadAddress nums (b vardef_0__solve_reverse) total (length word)))
         (memory state arraydef_0__sequence) 0) 64) 1
       else coerceInt (nth (Z.to_nat (prepReadAddress nums (b vardef_0__solve_reverse) total (length word)))
         (memory state arraydef_0__sequence) 0) 64)=character).
    { rewrite sourceCharacter. unfold character. destruct (b vardef_0__solve_reverse),opening; reflexivity. }
    assert (prefixRoom : (S (length events)<length (memory state arraydef_0__prefix))%nat).
    { change (S (length events)<@List.length Z (memory state arraydef_0__prefix))%nat.
      rewrite prefixLength. cbn [length] in room. lia. }
    assert (prefixBound : 0<=nth (length events) (memory state arraydef_0__prefix) 0<=500000).
    { change (0<=@List.nth Z (length events) (memory state arraydef_0__prefix) 0<=500000).
      pose proof (prefixFlags_difference _ _ _ flags) as totalFlags.
      change (@List.nth Z 0 (memory state arraydef_0__prefix) 0=0) in zero.
      rewrite zero in totalFlags.
      cbn [Nat.add] in totalFlags. pose proof (specialCount_bound events). lia. }
    destruct (@prepCharacter_execution state prepared opening origin height (length events)
      ltac:(unfold prepared,character; apply lookupSame)
      ltac:(unfold prepared; rewrite lookupDifferent by congruence; exact balanceEq)
      ltac:(unfold prepared; rewrite lookupDifferent by congruence; exact minimumEq)
      ltac:(unfold prepared; rewrite lookupDifferent by congruence; exact countEq)
      ltac:(cbn [length] in originBound; lia) ltac:(cbn [length] in heightBound; lia) ltac:(lia)
      prefixRoom prefixBound) as [stepExecution [stepBalance [stepMinimum stepCount]]].
    pose (nextNums := prepCharacterNums prepared opening).
    pose (nextState := prepCharacterMemory state (length events) height opening).
    pose (nextEvents := prepEventsAppend events opening height).
    assert (nextInput : prepInput nextState nextNums (b vardef_0__solve_reverse) total word).
    { apply prepInput_transfer with (before:=state) (nums:=nums).
      - apply prepInput_tail with (opening:=opening). exact input.
      - apply prepCharacterMemory_other. congruence.
      - unfold nextNums. rewrite prepCharacterNums_other by congruence. unfold prepared. apply lookupDifferent. congruence.
      - unfold nextNums. rewrite prepCharacterNums_other by congruence. unfold prepared. apply lookupDifferent. congruence. }
    assert (nextOriginBound : Z.of_nat (length word)-500000<=nextPrepOrigin origin height opening<=0).
    { unfold nextPrepOrigin. destruct opening; [cbn [length] in originBound; lia|].
      destruct height; cbn [length] in originBound; lia. }
    assert (nextHeightBound : Z.of_nat (nextPrepHeight height opening+length word)<=500000).
    { unfold nextPrepHeight. destruct opening; [cbn [length] in heightBound; lia|].
      destruct height; cbn [length Nat.pred] in *; lia. }
    destruct (IH nextNums nextState (nextPrepOrigin origin height opening) (nextPrepHeight height opening) nextEvents
      ltac:(unfold nextEvents; rewrite prepEventsAppend_length; unfold nextPrepCount; destruct opening; cbn [length] in room; lia)
      nBound stepBalance stepMinimum ltac:(unfold nextEvents; rewrite prepEventsAppend_length; exact stepCount)
      nextOriginBound nextHeightBound
      ltac:(unfold nextState; rewrite prepCharacterMemory_length; exact prefixLength)
      ltac:(unfold nextState; rewrite prepCharacterMemory_zero by exact prefixRoom; exact zero)
      ltac:(apply prepCharacterMemory_flags; assumption) nextInput)
      as [finished [final [execution [finalCount [finalFlags [finalLength [finalZero [finalInput [finalOutput [finalArrays finalNums]]]]]]]]]].
    assert (eventsEq : nextEvents++eventsFrom word (nextPrepHeight height opening)=events++eventsFrom (opening::word) height).
    { apply prepEventsAppend_suffix. }
    rewrite eventsEq in finalCount,finalFlags.
    exists finished,final. split.
    { cbn [length preprocessAction]. rewrite exec_bind.
      replace (prepReadAddress nums (b vardef_0__solve_reverse) total (length word)) with
        (Z.of_nat (Z.to_nat (prepReadAddress nums (b vardef_0__solve_reverse) total (length word))))
        at 1 by (rewrite Z2Nat.id by exact addressNonnegative; reflexivity).
      rewrite tableRead_execution by (try congruence; exact sourceRoom).
      cbn [optionBind fst snd intValue]. rewrite loadedCharacter.
      fold character prepared. rewrite exec_bind,stepExecution.
      cbn [optionBind fst snd]. exact execution. }
    split; [exact finalCount|]. split; [exact finalFlags|]. split; [exact finalLength|]. split; [exact finalZero|].
    split; [rewrite finalInput; unfold nextState,prepCharacterMemory; destruct opening; reflexivity|].
    split; [rewrite finalOutput; unfold nextState,prepCharacterMemory; destruct opening; reflexivity|].
    split.
    + intros name different. rewrite finalArrays by exact different. apply prepCharacterMemory_other. exact different.
    + intros name notBalance notMinimum notCount notFlag notChar.
      rewrite finalNums by assumption. unfold nextNums. rewrite prepCharacterNums_other by assumption.
      unfold prepared. apply lookupDifferent. congruence.
Qed.

Lemma workspace_preprocess_transfer before after n stage : SolverWorkspace before n stage ->
  @List.length Z (memory after arraydef_0__prefix)=@List.length Z (memory before arraydef_0__prefix) ->
  (forall name, name<>arraydef_0__prefix -> memory after name=memory before name) ->
  SolverWorkspace after n stage.
Proof.
  intros workspace prefixLength same. apply workspace_transfer with (before:=before).
  - exact workspace.
  - intro name. destruct (decide (name=arraydef_0__prefix)) as [->|different]; [exact prefixLength|].
    rewrite same by exact different. reflexivity.
  - apply same; congruence.
  - apply same; congruence.
  - apply same; congruence.
  - rewrite same by congruence. exact (workspace_work_canonical _ _ _ workspace).
  - rewrite same by congruence. exact (workspace_other_canonical _ _ _ workspace).
  - rewrite same by congruence. exact (workspace_roots_canonical _ _ _ workspace).
  - rewrite same by congruence. exact (workspace_poly_canonical _ _ _ workspace).
  - rewrite same by congruence. exact (workspace_arena_canonical _ _ _ workspace).
Qed.

Theorem generated_preprocess_loop b nums total state word n stage : SolverWorkspace state n stage ->
  (length word<=n)%nat ->
  nums vardef_0__solve_balance=0 -> nums vardef_0__solve_minimum=0 -> nums vardef_0__solve_count=0 ->
  nth 0 (memory state arraydef_0__prefix) 0=0 ->
  prepInput state nums (b vardef_0__solve_reverse) total word ->
  exists finished final,
    (forall continuation, exec (eliminateLocalVariables b nums
      (loop (length word) (solvePrepBody total) >>= continuation)) state=
      exec (eliminateLocalVariables b finished (continuation tt)) final) /\
    finished vardef_0__solve_count=Z.of_nat (length (eventsFrom word 0)) /\
    prefixFlags (memory final arraydef_0__prefix) 0 (eventsFrom word 0) /\
    SolverWorkspace final n stage /\ stdin final=stdin state /\ stdout final=stdout state /\
    (forall name, name<>arraydef_0__prefix -> memory final name=memory state name) /\
    (forall name, name<>vardef_0__solve_balance -> name<>vardef_0__solve_minimum ->
      name<>vardef_0__solve_count -> name<>vardef_0__solve_flag -> name<>vardef_0__solve_ch -> finished name=nums name).
Proof.
  intros workspace wordRoom balanceEq minimumEq countEq zero input.
  pose proof (workspace_input_bound _ _ _ workspace) as inputBound.
  pose proof (workspace_prefix_length _ _ _ workspace) as prefixLength.
  change (@List.length Z (memory state arraydef_0__prefix)=S n) in prefixLength.
  destruct (@preprocessAction_execution word b total nums state 0 0 [] n
    ltac:(cbn [length]; exact wordRoom) ltac:(lia) balanceEq minimumEq countEq ltac:(lia) ltac:(cbn [Nat.add]; lia)
    prefixLength zero ltac:(intros index range; cbn [length] in range; lia) input)
    as [finished [final [execution [finalCount [flags [finalLength [finalZero [finalInput [finalOutput [arrays numsPreserved]]]]]]]]]].
  exists finished,final. split.
  - intro continuation. rewrite prepLoopNormalized,exec_bind,execution. reflexivity.
  - split; [exact finalCount|]. split; [exact flags|]. split.
    + apply workspace_preprocess_transfer with (before:=state); [exact workspace|congruence|exact arrays].
    + split; [exact finalInput|]. split; [exact finalOutput|]. split; assumption.
Qed.
