From CoqCP Require Import Options Imperative Execution SwapUpdate.
From Submission Require Import KoxiaModular KoxiaArrays KoxiaTables.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.

Fixpoint fillValues count (values : list Z) start (value : nat -> Z) :=
  match count with O => values | S count => <[(start+count)%nat:=value count]>(fillValues count values start value) end.
Lemma fillValues_length count values start value : length (fillValues count values start value)=length values.
Proof. induction count as [|count IH]; cbn [fillValues]; rewrite ?length_insert,?IH; reflexivity. Qed.
Theorem fillValues_lookup count values start value index : (start+count<=length values)%nat ->
  nth index (fillValues count values start value) 0=
    if bool_decide ((start<=index<start+count)%nat) then value (index-start)%nat else nth index values 0.
Proof.
  induction count as [|count IH]; [intros; rewrite bool_decide_false by lia; reflexivity|].
  intro room. cbn [fillValues]. destruct (Nat.eq_dec index ((start+count)%nat)) as [new|old].
  - subst index. rewrite nthUpdate by (rewrite fillValues_length; lia).
    rewrite bool_decide_true by lia. replace (start+count-start)%nat with count by lia. reflexivity.
  - rewrite nthUpdateExcept by (rewrite ?fillValues_length; lia). rewrite IH by lia.
    destruct (bool_decide ((start<=index<start+count)%nat)) eqn:inside.
    + apply bool_decide_eq_true in inside. rewrite bool_decide_true by lia. reflexivity.
    + apply bool_decide_eq_false in inside. rewrite bool_decide_false by lia. reflexivity.
Qed.
Lemma fillValues_canonical count values start value : tableCanonical values ->
  (forall index, (index<count)%nat -> 0<=value index<koxiaModulus) ->
  tableCanonical (fillValues count values start value).
Proof.
  induction count as [|count IH]; [intros; assumption|]. intros canonical range. cbn [fillValues].
  unfold tableCanonical. apply Forall_insert; [apply IH; [exact canonical|intros; apply range; lia]|apply range; lia].
Qed.
Lemma integerWrite_execution name state values index value : name<>arraydef_0__frames ->
  (index<length values)%nat ->
  exec (tableWrite name (Z.of_nat index) (intValue name value)) (withArray state name (intValues name values))=
  Some (tt,withArray state name (intValues name (<[index:=value]>values))).
Proof.
  intros notFrames. destruct name; try contradiction.
  all: intro room; unfold tableWrite,intValue,intValues.
  all: rewrite execStoreArray by exact room; reflexivity.
Qed.
Fixpoint fillAction fuel total name start value : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  match fuel with O => Done _ _ _ tt | S fuel =>
    let index := (total-fuel-1)%nat in
    tableWrite name (Z.of_nat (start+index)) (intValue name (value index)) >>= fun _ =>
    fillAction fuel total name start value
  end.
Theorem fillAction_execution fuel count total name state values start value :
  name<>arraydef_0__frames -> (count+fuel=total)%nat -> (start+total<=length values)%nat ->
  exec (fillAction fuel total name start value)
    (withArray state name (intValues name (fillValues count values start value)))=
  Some (tt,withArray state name (intValues name (fillValues total values start value))).
Proof.
  induction fuel as [|fuel IH] in count |- *.
  - intros notFrames countFuel room. assert (count=total) by lia. subst count. reflexivity.
  - intros notFrames countFuel room. cbn [fillAction]. replace (total-fuel-1)%nat with count by lia.
    rewrite exec_bind,integerWrite_execution; [|exact notFrames|rewrite fillValues_length; lia].
    cbn [optionBind fst snd]. apply (IH (S count)); [exact notFrames|lia|exact room].
Qed.

Definition copyValue (source : list Z) offset count index :=
  if bool_decide ((index<count)%nat) then nth (offset+index) source 0 else 0.
Fixpoint copyAction fuel total target source offset count : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  match fuel with
  | O => Done _ _ _ tt
  | S fuel => let index := (total-fuel-1)%nat in
    tableWrite target (Z.of_nat index) (intValue target 0) >>= fun _ =>
    (if bool_decide ((index<count)%nat) then
      tableRead source (Z.of_nat (offset+index)) >>= fun value =>
      tableWrite target (Z.of_nat index) (intValue target (fromIntArray source value))
     else Done _ _ _ tt) >>= fun _ => copyAction fuel total target source offset count
  end.
Lemma intValues_length name values : name<>arraydef_0__frames -> length (intValues name values)=length values.
Proof. intros different. destruct name; try contradiction; reflexivity. Qed.
Lemma fromIntArray_nth name values index : name<>arraydef_0__frames ->
  fromIntArray name (nth index (intValues name values) (intValue name 0))=nth index values 0.
Proof. intros different. destruct name; try contradiction; reflexivity. Qed.

Theorem copyAction_execution fuel count total target source state values sourceValues offset sourceCount :
  target<>arraydef_0__frames -> source<>arraydef_0__frames -> target<>source ->
  memory state source=intValues source sourceValues ->
  (count+fuel=total)%nat -> (total<=length values)%nat -> (offset+sourceCount<=length sourceValues)%nat ->
  exec (copyAction fuel total target source offset sourceCount)
    (withArray state target (intValues target (fillValues count values 0 (copyValue sourceValues offset sourceCount))))=
  Some (tt,withArray state target (intValues target (fillValues total values 0 (copyValue sourceValues offset sourceCount)))).
Proof.
  induction fuel as [|fuel IH] in count |- *.
  - intros targetInteger sourceInteger different sourceEq countFuel room sourceRoom.
    assert (count=total) by lia. subst count. reflexivity.
  - intros targetInteger sourceInteger different sourceEq countFuel room sourceRoom.
    cbn [copyAction]. replace (total-fuel-1)%nat with count by lia.
    rewrite exec_bind,integerWrite_execution.
    2: exact targetInteger.
    2: rewrite fillValues_length; lia.
    cbn [optionBind fst snd].
    destruct (bool_decide ((count<sourceCount)%nat)) eqn:copy.
    + apply bool_decide_eq_true in copy.
      assert (readArray : memory
        (withArray state target (intValues target (<[count:=0]>(fillValues count values 0 (copyValue sourceValues offset sourceCount))))) source=
        intValues source sourceValues).
      { cbn [withArray withMemory memory]. rewrite replaceArray_other by congruence. exact sourceEq. }
      unfold tableRead at 1. cbn [bind].
      rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
        (withArray state target (intValues target (<[count:=0]>(fillValues count values 0 (copyValue sourceValues offset sourceCount)))))
        source (offset+count) (intValue source 0))
        by (rewrite readArray,intValues_length by exact sourceInteger; lia).
      rewrite readArray,fromIntArray_nth by exact sourceInteger.
      rewrite exec_bind,integerWrite_execution.
      2: exact targetInteger.
      2: rewrite length_insert,fillValues_length; lia.
      cbn [optionBind fst snd]. rewrite list_insert_insert,decide_True by reflexivity.
      pose proof (IH (S count) targetInteger sourceInteger different sourceEq ltac:(lia) room sourceRoom) as finish.
      cbn [fillValues] in finish. unfold copyValue at 1 in finish.
      rewrite bool_decide_true in finish by exact copy. cbn [Nat.add] in finish. exact finish.
    + apply bool_decide_eq_false in copy.
      cbn [bind].
      pose proof (IH (S count) targetInteger sourceInteger different sourceEq ltac:(lia) room sourceRoom) as finish.
      cbn [fillValues] in finish. unfold copyValue at 1 in finish.
      rewrite bool_decide_false in finish by exact copy. cbn [Nat.add] in finish. exact finish.
Qed.
Lemma copyValue_canonical source offset count index : tableCanonical source ->
  (offset+count<=length source)%nat -> 0<=copyValue source offset count index<koxiaModulus.
Proof.
  intros canonical room. unfold copyValue. destruct (bool_decide ((index<count)%nat)) eqn:copy.
  - apply bool_decide_eq_true in copy. apply tableCanonical_nth; [exact canonical|lia].
  - unfold koxiaModulus; lia.
Qed.

Section ArrayCommutation.
Context {I : Type} {T : I -> Type} `{EqDecision I}.
Lemma replaceArray_commute (values : forall name : I, list (T name)) left leftValues right rightValues : left<>right ->
  replaceArray (replaceArray values left leftValues) right rightValues=
  replaceArray (replaceArray values right rightValues) left leftValues.
Proof.
  intro different. apply functional_extensionality_dep. intro query.
  destruct (decide (query=left)) as [->|notLeft].
  - rewrite replaceArray_other by exact different. rewrite !replaceArray_same. reflexivity.
  - destruct (decide (query=right)) as [->|notRight].
    + rewrite replaceArray_same. rewrite replaceArray_other by congruence. rewrite replaceArray_same. reflexivity.
    + rewrite !replaceArray_other by assumption. reflexivity.
Qed.
Lemma withArray_commute (state : @Machine I T) left leftValues right rightValues : left<>right ->
  withArray (withArray state left leftValues) right rightValues=
  withArray (withArray state right rightValues) left leftValues.
Proof.
  intro different. unfold withArray,withMemory. cbn [memory stdin stdout].
  rewrite replaceArray_commute by exact different. reflexivity.
Qed.
Lemma withArray_preserve_other (state : @Machine I T) name values other : other<>name ->
  memory (withArray state name values) other=memory state other.
Proof. intro different. cbn [withArray withMemory memory]. apply replaceArray_other. exact different. Qed.
Lemma withArray_length (state : @Machine I T) name values : length (memory (withArray state name values) name)=length values.
Proof. cbn [withArray withMemory memory]. rewrite replaceArray_same. reflexivity. Qed.
End ArrayCommutation.

Fixpoint copyReplaceAction fuel total target source replacement : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  match fuel with
  | O => Done _ _ _ tt
  | S fuel => let index := (total-fuel-1)%nat in
    tableRead source (Z.of_nat index) >>= fun value =>
    tableWrite target (Z.of_nat index) (intValue target (fromIntArray source value)) >>= fun _ =>
    tableWrite source (Z.of_nat index) (intValue source (replacement index)) >>= fun _ =>
    copyReplaceAction fuel total target source replacement
  end.

Theorem copyReplaceAction_execution fuel count total target source state targetValues sourceValues replacement :
  target<>arraydef_0__frames -> source<>arraydef_0__frames -> target<>source ->
  (count+fuel=total)%nat -> (total<=length targetValues)%nat -> (total<=length sourceValues)%nat ->
  exec (copyReplaceAction fuel total target source replacement)
    (withArray (withArray state source (intValues source (fillValues count sourceValues 0 replacement)))
      target (intValues target (fillValues count targetValues 0 (fun index => nth index sourceValues 0))))=
  Some (tt,withArray (withArray state source (intValues source (fillValues total sourceValues 0 replacement)))
      target (intValues target (fillValues total targetValues 0 (fun index => nth index sourceValues 0)))).
Proof.
  induction fuel as [|fuel IH] in count |- *.
  - intros targetInteger sourceInteger different countFuel targetRoom sourceRoom.
    assert (count=total) by lia. subst count. reflexivity.
  - intros targetInteger sourceInteger different countFuel targetRoom sourceRoom.
    cbn [copyReplaceAction]. replace (total-fuel-1)%nat with count by lia.
    assert (readArray : memory
      (withArray (withArray state source (intValues source (fillValues count sourceValues 0 replacement)))
        target (intValues target (fillValues count targetValues 0 (fun index => nth index sourceValues 0)))) source=
      intValues source (fillValues count sourceValues 0 replacement)).
    { rewrite withArray_preserve_other by congruence. cbn [withArray withMemory memory]. apply replaceArray_same. }
    unfold tableRead at 1. cbn [bind].
    rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
      (withArray (withArray state source (intValues source (fillValues count sourceValues 0 replacement)))
        target (intValues target (fillValues count targetValues 0 (fun index => nth index sourceValues 0))))
      source count (intValue source 0))
      by (rewrite readArray,intValues_length by exact sourceInteger; rewrite fillValues_length; lia).
    rewrite readArray,fromIntArray_nth by exact sourceInteger.
    rewrite fillValues_lookup,bool_decide_false by lia.
    rewrite exec_bind,integerWrite_execution; [|exact targetInteger|rewrite fillValues_length; lia].
    cbn [optionBind fst snd]. rewrite withArray_commute by congruence.
    rewrite exec_bind,integerWrite_execution; [|exact sourceInteger|rewrite fillValues_length; lia].
    cbn [optionBind fst snd]. rewrite withArray_commute by exact different.
    pose proof (IH (S count) targetInteger sourceInteger different ltac:(lia) targetRoom sourceRoom) as finish.
    cbn [fillValues Nat.add] in finish. exact finish.
Qed.

Definition copyIntoStep index target source start offset :=
  tableRead source (Z.of_nat (offset+index)) >>= fun value =>
  tableWrite target (Z.of_nat (start+index)) (intValue target (fromIntArray source value)).
Fixpoint copyIntoAction fuel total target source start offset : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  match fuel with O => Done _ _ _ tt | S fuel =>
    copyIntoStep (total-fuel-1) target source start offset >>= fun _ =>
    copyIntoAction fuel total target source start offset
  end.
Theorem copyIntoAction_execution fuel count total target source state values sourceValues start offset :
  target<>arraydef_0__frames -> source<>arraydef_0__frames -> target<>source ->
  memory state source=intValues source sourceValues ->
  (count+fuel=total)%nat -> (start+total<=length values)%nat -> (offset+total<=length sourceValues)%nat ->
  exec (copyIntoAction fuel total target source start offset)
    (withArray state target (intValues target (fillValues count values start (fun index => nth (offset+index) sourceValues 0))))=
  Some (tt,withArray state target (intValues target (fillValues total values start (fun index => nth (offset+index) sourceValues 0)))).
Proof.
  induction fuel as [|fuel IH] in count |- *.
  - intros targetInteger sourceInteger different sourceEq countFuel room sourceRoom.
    assert (count=total) by lia. subst count. reflexivity.
  - intros targetInteger sourceInteger different sourceEq countFuel room sourceRoom.
    cbn [copyIntoAction]. replace (total-fuel-1)%nat with count by lia.
    unfold copyIntoStep,tableRead. cbn [bind].
    assert (readArray : memory
      (withArray state target (intValues target (fillValues count values start (fun index => nth (offset+index) sourceValues 0)))) source=
      intValues source sourceValues).
    { rewrite withArray_preserve_other by congruence. exact sourceEq. }
    rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
      (withArray state target (intValues target (fillValues count values start (fun index => nth (offset+index) sourceValues 0))))
      source (offset+count) (intValue source 0))
      by (rewrite readArray,intValues_length by exact sourceInteger; lia).
    rewrite readArray,fromIntArray_nth by exact sourceInteger.
    rewrite exec_bind,integerWrite_execution; [|exact targetInteger|rewrite fillValues_length; lia].
    cbn [optionBind fst snd]. apply (IH (S count)); [exact targetInteger|exact sourceInteger|exact different|exact sourceEq|lia|exact room|exact sourceRoom].
Qed.
