From CoqCP Require Import Options.
From stdpp Require Import strings.
Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.
Require Import ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Logic.FunctionalExtensionality.
Open Scope Z_scope.

Record Environment (arrayIndex : Type) := { arrayType: arrayIndex -> Type; arrays: forall (name : arrayIndex), list (arrayType name) }.

Record Locals (variableIndex : Type) := { numbers: variableIndex -> Z; booleans: variableIndex -> bool }.

Inductive Action (effectType : Type) (effectResponse : effectType -> Type) (returnType : Type) :=
| Done (returnValue : returnType)
| Dispatch (effect : effectType) (continuation : effectResponse effect -> Action effectType effectResponse returnType).

Fixpoint bind {effectType effectResponse A B} (a : Action effectType effectResponse A) (f : A -> Action effectType effectResponse B) : Action effectType effectResponse B :=
  match a with
  | Done _ _ _ value => f value
  | Dispatch _ _ _ effect continuation => Dispatch _ _ _ effect (fun response => bind (continuation response) f)
  end.

Notation "x >>= f" := (bind x f) (at level 50, left associativity).

Lemma bindDispatch {effectType effectResponse A B} effect (continuation : effectResponse effect -> Action effectType effectResponse A) (f : A -> Action effectType effectResponse B) : Dispatch _ _ _ effect continuation >>= f = Dispatch _ _ _ effect (fun response => continuation response >>= f).
Proof. easy. Qed.

Lemma leftIdentity {effectType effectResponse A B} (x : A) (f : A -> Action effectType effectResponse B) : bind (Done _ _ _ x) f = f x.
Proof. easy. Qed.

Lemma rightIdentity {effectType effectResponse A} (x : Action effectType effectResponse A) : bind x (Done _ _ _) = x.
Proof.
  induction x as [| a next IH]; try easy; simpl.
  assert (h : (λ _0 : effectResponse a, next _0 >>= Done effectType effectResponse A) = next).
  { apply functional_extensionality. assumption. }
  now rewrite h.
Qed.

Lemma bindAssoc {effectType effectResponse A B C} (x : Action effectType effectResponse A) (f : A -> Action effectType effectResponse B) (g : B -> Action effectType effectResponse C) : (bind x (fun x => bind (f x) g)) = (bind (bind x f) g).
Proof.
  induction x as [| a next IH]; try easy; simpl.
  assert (h : (λ _0 : effectResponse a, next _0 >>= λ _1 : A, f _1 >>= g) = (λ _0 : effectResponse a, next _0 >>= f >>= g)).
  { apply functional_extensionality. assumption. }
  now rewrite h.
Qed.

Definition shortCircuitAnd {effectType effectResponse} (a b : Action effectType effectResponse bool) := bind a (fun x => match x with
  | false => Done _ _ _ false
  | true => b
  end).

Definition shortCircuitOr {effectType effectResponse} (a b : Action effectType effectResponse bool) := bind a (fun x => match x with
  | true => Done _ _ _ true
  | false => b
  end).

Inductive BasicEffect :=
| Trap
| Flush
| ReadChar
| WriteChar (value : Z).

#[export] Instance basicEffectEqualityDecidable : EqDecision BasicEffect := ltac:(solve_decision).

Definition basicEffectReturnValue (effect : BasicEffect): Type :=
  match effect with
  | Trap => False
  | Flush => unit
  | ReadChar => Z
  | WriteChar _ => unit
  end.

(* Unfold lemmas for each constructor *)
Lemma unfold_Trap :
  basicEffectReturnValue Trap = False.
Proof. reflexivity. Qed.

Lemma unfold_Flush :
  basicEffectReturnValue Flush = unit.
Proof. reflexivity. Qed.

Lemma unfold_ReadChar :
  basicEffectReturnValue ReadChar = Z.
Proof. reflexivity. Qed.

Lemma unfold_WriteChar c :
  basicEffectReturnValue (WriteChar c) = unit.
Proof. reflexivity. Qed.

(* Autorewrite database *)
Create HintDb basicEffectReturnValue_unfold.

Hint Rewrite unfold_Trap : basicEffectReturnValue_unfold.
Hint Rewrite unfold_Flush : basicEffectReturnValue_unfold.
Hint Rewrite unfold_ReadChar : basicEffectReturnValue_unfold.
Hint Rewrite unfold_WriteChar : basicEffectReturnValue_unfold.

Inductive WithArrays (arrayIndex : Type) (arrayType : arrayIndex -> Type) :=
| DoBasicEffect (effect : BasicEffect)
| Retrieve (arrayName : arrayIndex) (index : Z)
| Store (arrayName : arrayIndex) (index : Z) (value : arrayType arrayName)
| Grow (arrayName : arrayIndex) (minimumLength : Z) (zero : arrayType arrayName).

#[export] Instance withArraysEqualityDecidable {arrayIndex : Type} {arrayType : arrayIndex -> Type} (hIndexEq : EqDecision arrayIndex) (hArrayType : forall name, EqDecision (arrayType name)) : EqDecision (WithArrays arrayIndex arrayType).
Proof.
  intros a b.
  destruct a as [e | a i | a i v | a i v]; destruct b as [e1 | a1 i1 | a1 i1 v1 | a1 i1 v1]; try ((left; easy) || (right; easy)).
  - destruct (decide (e = e1)) as [h | h]; try subst e1.
    { now left. } { right; intro x; now inversion x. }
  - destruct (decide (a = a1)) as [h | h]; try subst a1; destruct (decide (i = i1)) as [h1 | h1]; try subst i1; try now left.
    all: right; intro x; now inversion x.
  - destruct (decide (a = a1)) as [h | h]; try subst a1; destruct (decide (i = i1)) as [h1 | h1]; try subst i1; try (right; intro x; now inversion x).
    destruct (hArrayType a v v1) as [h | h]; try (subst v1; now left). right. intro x. inversion x as [x1]. apply inj_pair2_eq_dec in x1; try easy.
  - destruct (decide (a = a1)) as [h | h]; try subst a1; destruct (decide (i = i1)) as [h1 | h1]; try subst i1; try (right; intro x; now inversion x).
    destruct (hArrayType a v v1) as [h | h]; try (subst v1; now left). right. intro x. inversion x as [x1]. apply inj_pair2_eq_dec in x1; try easy.
Qed.

Definition withArraysReturnValue {arrayIndex} {arrayType : arrayIndex -> Type} (effect : WithArrays arrayIndex arrayType) : Type :=
  match effect with
  | DoBasicEffect _ _ effect => basicEffectReturnValue effect
  | Retrieve _ _ arrayName _ => arrayType arrayName
  | Store _ _ _ _ _ => unit
  | Grow _ _ _ _ _ => unit
  end.

(* Unfold lemmas for each constructor *)
Lemma unfold_DoBasicEffect arrayIndex arrayType effect1 :
  @withArraysReturnValue arrayIndex arrayType (DoBasicEffect _ _ effect1) =
  basicEffectReturnValue effect1.
Proof. reflexivity. Qed.

Lemma unfold_Retrieve arrayIndex arrayType arrayName b :
  @withArraysReturnValue arrayIndex arrayType (Retrieve _ _ arrayName b) =
  arrayType arrayName.
Proof. reflexivity. Qed.

Lemma unfold_Store arrayIndex arrayType c d e :
  @withArraysReturnValue arrayIndex arrayType (Store _ _ c d e) =
  unit.
Proof. reflexivity. Qed.

Lemma unfold_Grow arrayIndex arrayType name minimumLength zero :
  @withArraysReturnValue arrayIndex arrayType (Grow _ _ name minimumLength zero) = unit.
Proof. reflexivity. Qed.

(* Autorewrite database *)
Create HintDb withArraysReturnValue_unfold.

Hint Rewrite unfold_DoBasicEffect : withArraysReturnValue_unfold.
Hint Rewrite unfold_Retrieve : withArraysReturnValue_unfold.
Hint Rewrite unfold_Grow : withArraysReturnValue_unfold.
Hint Rewrite unfold_Store :
 withArraysReturnValue_unfold.

Inductive WithLocalVariables (arrayIndex : Type) (arrayType : arrayIndex -> Type) (variableIndex : Type) :=
| DoWithArrays (effect : WithArrays arrayIndex arrayType)
| BooleanLocalGet (name : variableIndex)
| BooleanLocalSet (name : variableIndex) (value : bool)
| NumberLocalGet (name : variableIndex)
| NumberLocalSet (name : variableIndex) (value : Z).

#[export] Instance withLocalVariablesEqualityDecidable {arrayIndex arrayType variableIndex} (hArrayIndex : EqDecision arrayIndex) (hArrayType : forall name, EqDecision (arrayType name)) (hVariableIndex : EqDecision variableIndex) : EqDecision (WithLocalVariables arrayIndex arrayType variableIndex) := ltac:(solve_decision).

Definition withLocalVariablesReturnValue {arrayIndex arrayType variableIndex} (effect : WithLocalVariables arrayIndex arrayType variableIndex) : Type :=
  match effect with
  | DoWithArrays _ _ _ effect => withArraysReturnValue effect
  | BooleanLocalGet _ _ _ _ => bool
  | BooleanLocalSet _ _ _ _ _ => unit
  | NumberLocalGet _ _ _ _ => Z
  | NumberLocalSet _ _ _ _ _ => unit
  end.

(* Unfold lemmas for each constructor *)
Lemma unfold_DoWithArrays arrayIndex arrayType variableIndex effect :
  @withLocalVariablesReturnValue arrayIndex arrayType variableIndex (DoWithArrays _ _ _ effect) =
  withArraysReturnValue effect.
Proof. reflexivity. Qed.

Lemma unfold_BooleanLocalGet arrayIndex arrayType variableIndex d :
  @withLocalVariablesReturnValue arrayIndex arrayType variableIndex (BooleanLocalGet _ _ _ d) =
  bool.
Proof. reflexivity. Qed.

Lemma unfold_BooleanLocalSet arrayIndex arrayType variableIndex d e :
  @withLocalVariablesReturnValue arrayIndex arrayType variableIndex (BooleanLocalSet _ _ _ d e) =
  unit.
Proof. reflexivity. Qed.

Lemma unfold_NumberLocalGet arrayIndex arrayType variableIndex d :
  @withLocalVariablesReturnValue arrayIndex arrayType variableIndex (NumberLocalGet _ _ _ d) =
  Z.
Proof. reflexivity. Qed.

Lemma unfold_NumberLocalSet arrayIndex arrayType variableIndex d e :
  @withLocalVariablesReturnValue arrayIndex arrayType variableIndex (NumberLocalSet _ _ _ d e) =
  unit.
Proof. reflexivity. Qed.

(* Autorewrite database *)
Create HintDb withLocalVariablesReturnValue_unfold.

Hint Rewrite unfold_DoWithArrays : withLocalVariablesReturnValue_unfold.
Hint Rewrite unfold_BooleanLocalGet : withLocalVariablesReturnValue_unfold.
Hint Rewrite unfold_BooleanLocalSet : withLocalVariablesReturnValue_unfold.
Hint Rewrite unfold_NumberLocalGet : withLocalVariablesReturnValue_unfold.
Hint Rewrite unfold_NumberLocalSet : withLocalVariablesReturnValue_unfold.

(* To automatically rewrite using these lemmas, you can use: *)

(* autorewrite with withLocalVariablesReturnValue_unfold. *)

(* Combined autorewrite database *)
Create HintDb combined_unfold.

Hint Rewrite unfold_DoWithArrays : combined_unfold.
Hint Rewrite unfold_BooleanLocalGet : combined_unfold.
Hint Rewrite unfold_BooleanLocalSet : combined_unfold.
Hint Rewrite unfold_NumberLocalGet : combined_unfold.
Hint Rewrite unfold_NumberLocalSet : combined_unfold.

Hint Rewrite unfold_DoBasicEffect : combined_unfold.
Hint Rewrite unfold_Retrieve : combined_unfold.
Hint Rewrite unfold_Store : combined_unfold.

Hint Rewrite unfold_Trap : combined_unfold.
Hint Rewrite unfold_Flush : combined_unfold.
Hint Rewrite unfold_ReadChar : combined_unfold.
Hint Rewrite unfold_WriteChar : combined_unfold.

(* To automatically rewrite using all the lemmas, use: *)
(* autorewrite with combined_unfold. *)

Inductive LoopOutcome :=
| KeepGoing
| Stop.

Inductive WithinLoop arrayIndex arrayType variableIndex :=
| DoWithLocalVariables (effect : WithLocalVariables arrayIndex arrayType variableIndex)
| DoContinue
| DoBreak.

#[export] Instance withinLoopEqualityDecidable {arrayIndex arrayType variableIndex} (hArrayType : forall name, EqDecision (arrayType name)) (hArrayIndex : EqDecision arrayIndex) (hVariableIndex : EqDecision variableIndex): EqDecision (WithinLoop arrayIndex arrayType variableIndex) := ltac:(solve_decision).

Definition withinLoopReturnValue {arrayIndex arrayType variableIndex} (effect : WithinLoop arrayIndex arrayType variableIndex) : Type :=
  match effect with
  | DoWithLocalVariables _ _ _ effect => withLocalVariablesReturnValue effect
  | DoContinue _ _ _ => false
  | DoBreak _ _ _ => false
  end.

Lemma dropWithinLoop {arrayIndex arrayType variableIndex} (action : Action (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue ()) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue LoopOutcome.
Proof.
  induction action as [| effect continuation IH].
  - exact (Done _ _ _ KeepGoing).
  - destruct effect as [effect | |].
    + exact (Dispatch _ _ _ effect IH).
    + exact (Done _ _ _ KeepGoing).
    + exact (Done _ _ _ Stop).
Defined.

Lemma dropWithinLoop_1 arrayIndex arrayType variableIndex : dropWithinLoop (Done (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue () tt) = Done _ _ _ KeepGoing.
Proof. easy. Qed.

Lemma dropWithinLoop_2 arrayIndex arrayType variableIndex effect continuation : dropWithinLoop (Dispatch (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue () (DoWithLocalVariables _ _ _ effect) continuation) = Dispatch _ _ _ effect (fun x => dropWithinLoop (continuation x)).
Proof. easy. Qed.

Lemma dropWithinLoop_2' arrayIndex arrayType variableIndex effect continuation : dropWithinLoop (Dispatch (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue _ (DoWithLocalVariables _ _ _ effect) (fun x => Done _ _ _ x) >>= continuation) = Dispatch _ _ _ effect (fun x => dropWithinLoop (continuation x)).
Proof. easy. Qed.

Lemma dropWithinLoop_3 arrayIndex arrayType variableIndex continuation : dropWithinLoop (Dispatch (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue () (DoContinue _ _ _) continuation) = Done _ _ _ KeepGoing.
Proof. easy. Qed.

Lemma dropWithinLoop_4 arrayIndex arrayType variableIndex continuation : dropWithinLoop (Dispatch (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue () (DoBreak _ _ _) continuation) = Done _ _ _ Stop.
Proof. easy. Qed.

Fixpoint loop (n : nat) {arrayIndex arrayType variableIndex} (body : nat -> Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue LoopOutcome) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue unit :=
  match n with
  | O => Done _ _ unit tt
  | S n => bind (body n) (fun outcome => match outcome with
    | KeepGoing => loop n body
    | Stop => Done _ _ unit tt
    end)
  end.

Lemma loop_S (n : nat) {arrayIndex arrayType variableIndex} (body : nat -> Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue LoopOutcome) : loop (S n) body = bind (body n) (fun outcome => match outcome with | KeepGoing => loop n body | Stop => Done _ _ unit tt end).
Proof. easy. Qed.

Fixpoint loopString (s : string) {arrayIndex arrayType variableIndex} (body : Z -> Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue LoopOutcome) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue unit :=
  match s with
  | EmptyString => Done _ _ unit tt
  | String x tail => bind (body (Z.of_N (N_of_ascii x))) (fun outcome =>
    match outcome with
    | KeepGoing => loopString tail body
    | Stop => Done _ _ unit tt
    end)
  end.

Definition update {indexType : Type} {A} (map : indexType -> A) (key : indexType) (value : A) `{EqDecision indexType} := fun x => if decide (x = key) then value else map x.

Lemma lookupSame {indexType : Type} {A} (map : indexType -> A) (key : indexType) (value : A) `{EqDecision indexType} : update map key value key = value.
Proof. unfold update. case_decide; easy. Qed.

Lemma lookupDifferent {indexType : Type} {A} (map : indexType -> A) (key key' : indexType) (hdiff : key <> key') (value : A) `{EqDecision indexType} : update map key value key' = map key'.
Proof. unfold update. case_decide as f; [| easy]. exfalso. exact (hdiff ltac:(symmetry; exact f)). Qed.

Lemma updateSame {indexType : Type} {A} (map : indexType -> A) (key : indexType) (value value' : A) `{EqDecision indexType} : update (update map key value) key value' = update map key value'.
Proof.
  unfold update. apply functional_extensionality_dep.
  intro x. case_decide as r; reflexivity.
Qed.

Lemma updateDifferent {indexType : Type} {A} (map : indexType -> A) (key key' : indexType) (value value' : A) (hDiff : key <> key') `{EqDecision indexType} : update (update map key value) key' value' = update (update map key' value') key value.
Proof.
  unfold update. apply functional_extensionality_dep.
  intro x. case_decide as r; case_decide as s; try easy.
  rewrite s in r. exfalso. exact (hDiff r).
Qed.

Lemma eliminateLocalVariables {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (action : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue unit) : Action (WithArrays arrayIndex arrayType) withArraysReturnValue unit.
Proof.
  induction action as [x | effect continuation IH] in bools, numbers |- *;
  [exact (Done _ _ _ x) |].
  destruct effect as [effect | name | name value | name | name value].
  - apply (Dispatch (WithArrays arrayIndex arrayType) withArraysReturnValue unit effect).
    simpl in IH, continuation. intro value. exact (IH value bools numbers ).
  - simpl in IH, continuation. exact (IH (bools name) bools numbers ).
  - simpl in IH, continuation. exact (IH tt (update bools name value) numbers ).
  - simpl in IH, continuation. exact (IH (numbers name) bools numbers ).
  - simpl in IH, continuation. exact (IH tt bools (update numbers name value) ).
Defined.

Lemma pushDispatch {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) effect continuation : eliminateLocalVariables bools numbers (Dispatch _ _ _ (DoWithArrays arrayIndex arrayType _ effect) continuation) = Dispatch _ _ _ effect (fun x => eliminateLocalVariables bools numbers (continuation x)).
Proof. easy. Qed.

Lemma pushDispatch2 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) effect continuation : eliminateLocalVariables bools numbers ((Dispatch _ _ _ (DoWithArrays arrayIndex arrayType _ effect) (fun x => Done _ _ _ x)) >>= continuation) = Dispatch _ _ _ effect (fun x => eliminateLocalVariables bools numbers (continuation x)).
Proof. easy. Qed.

Lemma pushDispatch3 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) effect continuation : eliminateLocalVariables bools numbers ((Dispatch _ _ _ (DoWithArrays arrayIndex arrayType _ effect) (fun x => dropWithinLoop (Done _ _ _ tt))) >>= continuation) = Dispatch _ _ _ effect (fun x => eliminateLocalVariables bools numbers (continuation KeepGoing)).
Proof. easy. Qed.

Lemma pushBooleanGet {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) name continuation : eliminateLocalVariables bools numbers (Dispatch _ _ _ (BooleanLocalGet arrayIndex arrayType _ name) continuation) = eliminateLocalVariables bools numbers (continuation (bools name)).
Proof. easy. Qed.

Lemma pushBooleanGet2 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) name continuation : eliminateLocalVariables bools numbers ((Dispatch _ _ _ (BooleanLocalGet arrayIndex arrayType _ name) (fun x => Done _ _ _ x)) >>= continuation) = eliminateLocalVariables bools numbers (continuation (bools name)).
Proof. easy. Qed.

Lemma pushNumberGet {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) name continuation : eliminateLocalVariables bools numbers (Dispatch _ _ _ (NumberLocalGet arrayIndex arrayType _ name) continuation) = eliminateLocalVariables bools numbers (continuation (numbers name)).
Proof. easy. Qed.

Lemma pushNumberGet2 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) name continuation : eliminateLocalVariables bools numbers ((Dispatch _ _ _ (NumberLocalGet arrayIndex arrayType _ name) (fun x => Done _ _ _ x)) >>= continuation) = eliminateLocalVariables bools numbers (continuation (numbers name)).
Proof. easy. Qed.

Lemma pushBooleanSet {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) name value continuation : eliminateLocalVariables bools numbers (Dispatch _ _ _ (BooleanLocalSet arrayIndex arrayType _ name value) continuation) = eliminateLocalVariables (update bools name value) numbers (continuation tt).
Proof. easy. Qed.

Lemma pushBooleanSet2 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) name value continuation : eliminateLocalVariables bools numbers ((Dispatch _ _ _ (BooleanLocalSet arrayIndex arrayType _ name value) (fun x => Done _ _ _ x)) >>= continuation) = eliminateLocalVariables (update bools name value) numbers (continuation tt).
Proof. easy. Qed.

Lemma pushNumberSet {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) name value continuation : eliminateLocalVariables bools numbers (Dispatch _ _ _ (NumberLocalSet arrayIndex arrayType _ name value) continuation) = eliminateLocalVariables bools (update numbers name value) (continuation tt).
Proof. easy. Qed.

Lemma pushNumberSet2 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) name value continuation : eliminateLocalVariables bools numbers ((Dispatch _ _ _ (NumberLocalSet arrayIndex arrayType _ name value) (fun x => Done _ _ _ x)) >>= continuation) = eliminateLocalVariables bools (update numbers name value) (continuation tt).
Proof. easy. Qed.

Definition readChar arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z (DoWithArrays _ _ _ (DoBasicEffect _ _ ReadChar)) (fun x => Done _ _ Z x).

Definition writeChar arrayIndex arrayType variableIndex x := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ (WriteChar x))) (fun x => Done _ _ _ x).

Definition flush arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ Flush)) (fun x => Done _ _ _ x).

Definition trap arrayIndex arrayType variableIndex returnType := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue returnType (DoWithArrays _ _ _ (DoBasicEffect _ _ Trap)) (fun x => False_rect _ x).

Definition booleanLocalSet arrayIndex arrayType variableIndex name value := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (BooleanLocalSet _ _ _ name value) (fun x => Done _ _ _ x).

Definition booleanLocalGet arrayIndex arrayType variableIndex name := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (BooleanLocalGet _ _ _ name) (fun x => Done _ _ _ x).

Definition numberLocalSet arrayIndex arrayType variableIndex name value := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (NumberLocalSet _ _ _ name value) (fun x => Done _ _ _ x).

Definition numberLocalGet arrayIndex arrayType variableIndex name := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (NumberLocalGet _ _ _ name) (fun x => Done _ _ _ x).

Definition retrieve arrayIndex arrayType variableIndex name index := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (Retrieve arrayIndex arrayType name index)) (fun x => Done _ _ _ x).

Definition store arrayIndex arrayType variableIndex name index (value : arrayType name) := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (Store _ _ name index value)) (fun x => Done _ _ _ x).

Definition grow arrayIndex arrayType variableIndex name minimumLength (zero : arrayType name) := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (Grow _ _ name minimumLength zero)) (fun x => Done _ _ _ x).

Definition growList {A} (values : list A) (minimumLength : nat) (zero : A) :=
  values ++ repeat zero (minimumLength - length values).

Lemma growList_length {A} (values : list A) minimumLength zero :
  length (growList values minimumLength zero) = Nat.max (length values) minimumLength.
Proof. unfold growList. rewrite app_length, repeat_length. lia. Qed.

Lemma growList_preserves {A} (values : list A) minimumLength zero :
  take (length values) (growList values minimumLength zero) = values.
Proof. unfold growList. apply take_app_length. Qed.

Lemma growList_no_shrink {A} (values : list A) minimumLength zero (h : (minimumLength <= length values)%nat) :
  growList values minimumLength zero = values.
Proof. unfold growList. rewrite (proj2 (Nat.sub_0_le _ _) h). simpl. apply app_nil_r. Qed.

Definition continue arrayIndex arrayType variableIndex := Dispatch (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue () (DoContinue _ _ _) (fun x => Done _ _ _ tt).

Lemma dropWithinLoop_continue arrayIndex arrayType variableIndex continuation : dropWithinLoop (continue arrayIndex arrayType variableIndex >>= continuation) = Done _ _ _ KeepGoing.
Proof. easy. Qed.

Definition break arrayIndex arrayType variableIndex := Dispatch (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue () (DoBreak _ _ _) (fun x => Done _ _ _ tt).

Lemma dropWithinLoop_break arrayIndex arrayType variableIndex continuation : dropWithinLoop (break arrayIndex arrayType variableIndex >>= continuation) = Done _ _ _ Stop.
Proof. easy. Qed.

Definition divIntUnsigned {arrayIndex arrayType variableIndex} (a b : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (a / b))).
Definition modIntUnsigned {arrayIndex arrayType variableIndex} (a b : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (a mod b))).

(* Bitwise operations for any bit width *)
Definition andBits {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (Z.land a b))).
Definition orBits {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (Z.lor a b))).
Definition xorBits {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (Z.lxor a b))).

(* Operations for specified bit width *)
Definition shiftLeft {arrayIndex arrayType variableIndex} (bitWidth : Z) (a amount : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z :=
  bind a (fun a => bind amount (fun amount =>
    if decide (amount >= bitWidth) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (Z.land (Z.shiftl a amount) (Z.ones bitWidth))
  )).

Definition shiftRight {arrayIndex arrayType variableIndex} (bitWidth : Z) (a amount : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z :=
  bind a (fun a => bind amount (fun amount =>
    if decide (amount >= bitWidth) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (Z.land (Z.shiftr a amount) (Z.ones bitWidth))
  )).

Definition notBits {u v} (bitWidth : Z) (a : Action u v Z) : Action u v Z := bind a (fun a => Done _ _ _ (Z.land (Z.lnot a) (Z.ones bitWidth))).

Definition coerceBool {u v} (a : Action u v bool) : Action u v Z := bind a (fun a =>
  if a then Done _ _ _ 1 else Done _ _ _ 0
).

(* Generic coercion function based on bit width *)
Definition coerceInt (n bitWidth : Z) : Z :=
  n mod (2 ^ bitWidth).

(* Helper function for signed conversion based on bit width *)
Definition toSigned (n bitWidth : Z) : Z :=
  let half := 2 ^ (bitWidth - 1) in
  if decide (n < half) then n else n - 2 ^ bitWidth.

(* Generic arithmetic operations *)
Definition addInt {u v} (bitWidth : Z) (a b : Action u v Z) : Action u v Z :=
  bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt (a + b) bitWidth))).

Definition subInt {u v} (bitWidth : Z) (a b : Action u v Z) : Action u v Z :=
  bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt (a - b) bitWidth))).

Definition multInt {u v} (bitWidth : Z) (a b : Action u v Z) : Action u v Z :=
  bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt (a * b) bitWidth))).

Definition divIntSigned {arrayIndex arrayType variableIndex} (bitWidth : Z) (a b : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z :=
  bind a (fun a => bind b (fun b =>
    let signedA := toSigned a bitWidth in
    let signedB := toSigned b bitWidth in
    if decide (b = 0) then trap arrayIndex arrayType variableIndex Z
    else if decide (signedA = - (2 ^ (bitWidth - 1)) /\ signedB = -1) then trap arrayIndex arrayType variableIndex Z
    else Done _ _ _ (coerceInt (a / b) bitWidth))).

Fixpoint liftToWithLocalVariables {arrayIndex arrayType variableIndex r} (x : Action (WithArrays arrayIndex arrayType) withArraysReturnValue r) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue r :=
  match x with
  | Done _ _ _ x => Done _ _ _ x
  | Dispatch _ _ _ effect continuation => Dispatch _ _ _ (DoWithArrays _ _ _ effect) (fun x => liftToWithLocalVariables (continuation x))
  end.

Lemma eliminateLift {arrayIndex arrayType variableIndex returnType} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (action : Action (WithArrays arrayIndex arrayType) withArraysReturnValue returnType) continuation : eliminateLocalVariables bools numbers (liftToWithLocalVariables action >>= continuation) = action >>= fun x => eliminateLocalVariables bools numbers (continuation x).
Proof.
  induction action as [a | a b IH]. { easy. }
  change (Dispatch (WithArrays arrayIndex arrayType) withArraysReturnValue
  () a
  (λ _1 : withArraysReturnValue a,
  eliminateLocalVariables bools numbers (liftToWithLocalVariables (b _1) >>= continuation)) =
Dispatch (WithArrays arrayIndex arrayType) withArraysReturnValue
  () a
  (λ _1 : withArraysReturnValue a,
  b _1 >>=
λ _2 : returnType,
  eliminateLocalVariables bools numbers (continuation _2))). rewrite (functional_extensionality_dep _ _ IH). reflexivity.
Qed.

Fixpoint liftToWithinLoop {arrayIndex arrayType variableIndex r} (x : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue r) : Action (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue r :=
  match x with
  | Done _ _ _ x => Done _ _ _ x
  | Dispatch _ _ _ effect continuation => Dispatch _ _ _ (DoWithLocalVariables _ _ _ effect) (fun x => liftToWithinLoop (continuation x))
  end.

Lemma liftToWithinLoopBind {arrayIndex arrayType variableIndex r1 r2} (x : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue r1) (continuation : r1 -> Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue r2) : liftToWithinLoop (x >>= continuation) = liftToWithinLoop x >>= fun t => liftToWithinLoop (continuation t).
Proof.
  induction x as [g | g g1 IH]. { easy. }
  change (Dispatch (WithinLoop arrayIndex arrayType variableIndex)
  withinLoopReturnValue r2
  (DoWithLocalVariables arrayIndex arrayType variableIndex g)
  (λ _0 : withLocalVariablesReturnValue g,
  liftToWithinLoop (g1 _0 >>= continuation)) =
Dispatch (WithinLoop arrayIndex arrayType variableIndex)
  withinLoopReturnValue r2
  (DoWithLocalVariables arrayIndex arrayType variableIndex g)
  (λ _0 : withLocalVariablesReturnValue g,
  liftToWithinLoop (g1 _0) >>=
λ _1 : r1, liftToWithinLoop (continuation _1))). rewrite (functional_extensionality_dep _ _ IH). reflexivity.
Qed.

Lemma dropWithinLoopLiftToWithinLoop {arrayIndex arrayType variableIndex r} (x : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue r) (continuation : r -> Action (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue ()) : dropWithinLoop (liftToWithinLoop x >>= continuation) = x >>= fun v => dropWithinLoop (continuation v).
Proof.
  induction x as [x | x x1 IH]. { easy. }
  change (Dispatch (WithLocalVariables arrayIndex arrayType variableIndex)
  withLocalVariablesReturnValue LoopOutcome x
  (λ _0 : withLocalVariablesReturnValue x,
  dropWithinLoop (liftToWithinLoop (x1 _0) >>= continuation)) =
Dispatch (WithLocalVariables arrayIndex arrayType variableIndex)
  withLocalVariablesReturnValue LoopOutcome x
  (λ _0 : withLocalVariablesReturnValue x,
  x1 _0 >>= λ _1 : r, dropWithinLoop (continuation _1))). rewrite (functional_extensionality_dep _ _ IH). reflexivity.
Qed.

Lemma nth_lt {A} (l : list A) (n : nat) (isLess : Nat.lt n (length l)) : A.
Proof.
  destruct l as [| head tail]; simpl in *; (lia || exact (nth n (head :: tail) head)).
Defined.

Lemma nth_lt_default {A} (l : list A) (n : nat) (isLess : Nat.lt n (length l)) (default : A) : nth_lt l n isLess = nth n l default.
Proof.
  destruct l as [| head tail]; simpl in *. { lia. }
  destruct n as [| n]. { reflexivity. }
  rewrite (nth_indep _ _ default). { reflexivity. } lia.
Qed.

Lemma nthTrap {A arrayIndex arrayType variableIndex} (l : list A) (n : Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue A.
Proof.
  destruct (decide (Nat.lt (Z.to_nat n) (length l))) as [h |].
  - exact (Done _ _ _ (nth_lt l (Z.to_nat n) h)).
  - exact (trap _ _ _ _).
Defined.

Fixpoint getArray {arrayIndex} {arrayType : arrayIndex -> Type} {variableIndex} (arrayName : arrayIndex) (length : nat) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue (list (arrayType arrayName)) :=
  match length with
  | O => Done _ _ _ []
  | S length => retrieve _ _ _ arrayName (Z.of_nat length) >>= fun x => getArray arrayName length >>= fun y => Done _ _ _ (y ++ [x])
  end.

Fixpoint applyArray {arrayIndex} {arrayType : arrayIndex -> Type} {variableIndex} (arrayName : arrayIndex) (l : list (arrayType arrayName)) (startIndex : Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue () :=
  match l with
  | [] => Done _ _ _ tt
  | head :: tail => store _ _ _ arrayName startIndex head >>= fun x => applyArray arrayName tail (startIndex + 1)
  end.

Definition modifyArray {arrayIndex} `{EqDecision arrayIndex} {arrayType : arrayIndex -> Type} (values : forall name, list (arrayType name)) (name : arrayIndex) index (value : arrayType name) :=
  fun currentName => match decide (currentName = name) with
  | left h => eq_rect_r (fun name => list (arrayType name)) (<[index:=value]>(values name)) h
  | right _ => values currentName
  end.


Definition growArrays {arrayIndex} `{EqDecision arrayIndex} {arrayType : arrayIndex -> Type}
  (values : forall name, list (arrayType name)) (name : arrayIndex) minimumLength (zero : arrayType name) :=
  fun currentName => match decide (currentName = name) with
  | left h => ltac:(subst name; exact (growList (values currentName) minimumLength zero))
  | right _ => values currentName
  end.

Fixpoint getNewArrays {arrayIndex arrayType} `{EqDecision arrayIndex}
  (code : Action (WithArrays arrayIndex arrayType) withArraysReturnValue unit)
  (values : forall name, list (arrayType name)) : Action BasicEffect basicEffectReturnValue (forall name, list (arrayType name)) :=
  match code with
  | Done _ _ _ _ => Done _ _ _ values
  | Dispatch _ _ _ (DoBasicEffect _ _ effect) next =>
      Dispatch _ _ _ effect (fun x => getNewArrays (next x) values)
  | Dispatch _ _ _ (Retrieve _ _ name index) next =>
      match decide (Nat.lt (Z.to_nat index) (length (values name))) with
      | left h => getNewArrays (next (nth_lt (values name) (Z.to_nat index) h)) values
      | right _ => Dispatch _ _ _ Trap (fun _ => Done _ _ _ values)
      end
  | Dispatch _ _ _ (Store _ _ name index value) next =>
      match decide (Nat.lt (Z.to_nat index) (length (values name))) with
      | left _ => getNewArrays (next tt) (modifyArray values name (Z.to_nat index) value)
      | right _ => Dispatch _ _ _ Trap (fun _ => Done _ _ _ values)
      end
  | Dispatch _ _ _ (Grow _ _ name minimumLength zero) next =>
      getNewArrays (next tt) (growArrays values name (Z.to_nat minimumLength) zero)
  end.


Lemma withArraysReturnValueDoBasicEffectArrayType arrayIndex1 arrayIndex2 arrayType1 arrayType2 (effect : BasicEffect) : withArraysReturnValue (DoBasicEffect arrayIndex1 arrayType1 effect) = withArraysReturnValue (DoBasicEffect arrayIndex2 arrayType2 effect).
Proof. reflexivity. Defined.

Lemma translateArrays {arrayIndex1 arrayIndex2 arrayType R} (x : Action (WithArrays arrayIndex1 arrayType) withArraysReturnValue R) (destinationArrayType : arrayIndex2 -> Type) (mapping : arrayIndex1 -> arrayIndex2) (hCongruent : forall x, arrayType x = destinationArrayType (mapping x)) : Action (WithArrays arrayIndex2 destinationArrayType) withArraysReturnValue R.
Proof.
  induction x as [x | effect continuation IH].
  - exact (Done _ _ _ x).
  - destruct effect as [effect | arrayName index | arrayName index value | arrayName minimumLength zero].
    + rewrite (withArraysReturnValueDoBasicEffectArrayType arrayIndex1 arrayIndex2 arrayType destinationArrayType) in IH. exact (Dispatch _ _ _ (DoBasicEffect _ destinationArrayType effect) IH).
    + assert (h : withArraysReturnValue (Retrieve arrayIndex1 arrayType arrayName index) = withArraysReturnValue (Retrieve arrayIndex2 destinationArrayType (mapping arrayName) index)). { simpl; auto. }
      rewrite h in IH.
      exact (Dispatch _ _ _ (Retrieve _ destinationArrayType (mapping arrayName) index) IH).
    + assert (h : withArraysReturnValue (Store arrayIndex1 arrayType arrayName index value) = withArraysReturnValue (Store _ destinationArrayType (mapping arrayName) index ltac:(rewrite <- hCongruent; exact value))). { simpl; auto. }
      rewrite h in IH.
      exact (Dispatch _ _ _ (Store _ destinationArrayType (mapping arrayName) index ltac:(rewrite <- hCongruent; exact value)) IH).
    + assert (h : withArraysReturnValue (Grow arrayIndex1 arrayType arrayName minimumLength zero) = withArraysReturnValue (Grow _ destinationArrayType (mapping arrayName) minimumLength ltac:(rewrite <- hCongruent; exact zero))). { reflexivity. }
      rewrite h in IH.
      exact (Dispatch _ _ _ (Grow _ destinationArrayType (mapping arrayName) minimumLength ltac:(rewrite <- hCongruent; exact zero)) IH).
Defined.



Lemma getAllCharacters {arrayIndex arrayType} (x : Action (WithArrays arrayIndex arrayType) withArraysReturnValue ()) (captured : list Z) : Action (WithArrays arrayIndex arrayType) withArraysReturnValue (list Z).
Proof.
  induction x as [x | effect continuation IH] in captured |- *.
  - exact (Done _ _ _ captured).
  - destruct effect as [effect | arrayName index | arrayName index value | arrayName minimumLength zero].
    + destruct effect as [| | | x].
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => IH returnValue captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Flush) (fun returnValue => IH returnValue captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ ReadChar) (fun returnValue => IH returnValue captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ (WriteChar x)) (fun returnValue => IH returnValue (captured ++ [x]))).
    + exact (Dispatch _ _ _ (Retrieve _ arrayType arrayName index) (fun x => IH x captured)).
    + exact (Dispatch _ _ _ (Store _ arrayType arrayName index value) (fun x => IH x captured)).
    + exact (Dispatch _ _ _ (Grow _ arrayType arrayName minimumLength zero) (fun x => IH x captured)).
Defined.


(* Competitive execution consumes stdin bytes, collects stdout, and returns the
   final arrays. Array-only proofs can use runArrays to leave I/O abstract. *)
Definition runArrays arrayIndex (indexEquality : EqDecision arrayIndex) arrayType
  (values : forall name, list (arrayType name))
  (code : Action (WithArrays arrayIndex arrayType) withArraysReturnValue unit) :=
  @getNewArrays arrayIndex arrayType indexEquality code values.

Lemma runArrays_done arrayIndex indexEquality arrayType values :
  runArrays arrayIndex indexEquality arrayType values (Done _ _ _ tt) = Done _ _ _ values.
Proof. reflexivity. Qed.

Lemma runArrays_retrieve arrayIndex indexEquality arrayType values name index continuation :
  runArrays arrayIndex indexEquality arrayType values (Dispatch _ _ _ (Retrieve _ _ name index) continuation) =
  match decide (Nat.lt (Z.to_nat index) (length (values name))) with
  | left h => runArrays arrayIndex indexEquality arrayType values (continuation (nth_lt (values name) (Z.to_nat index) h))
  | right _ => Dispatch _ _ _ Trap (fun _ => Done _ _ _ values)
  end.
Proof. reflexivity. Qed.

Lemma runArrays_store arrayIndex indexEquality arrayType values name index value continuation :
  runArrays arrayIndex indexEquality arrayType values (Dispatch _ _ _ (Store _ _ name index value) continuation) =
  match decide (Nat.lt (Z.to_nat index) (length (values name))) with
  | left h => runArrays arrayIndex indexEquality arrayType (fun currentName => match decide (currentName = name) with
    | left h => eq_rect_r (fun name => list (arrayType name)) (<[Z.to_nat index:=value]>(values name)) h
    | right _ => values currentName
    end) (continuation tt)
  | right _ => Dispatch _ _ _ Trap (fun _ => Done _ _ _ values)
  end.
Proof. reflexivity. Qed.

Fixpoint runIO {R} (code : Action BasicEffect basicEffectReturnValue R)
  (input output : list Z) : option (R * list Z * list Z) :=
  match code with
  | Done _ _ _ value => Some (value, input, output)
  | Dispatch _ _ _ Trap _ => None
  | Dispatch _ _ _ Flush next => runIO (next tt) input output
  | Dispatch _ _ _ ReadChar next =>
      match input with
      | [] => runIO (next (2^64 - 1)) [] output
      | head :: tail => runIO (next head) tail output
      end
  | Dispatch _ _ _ (WriteChar value) next => runIO (next tt) input (output ++ [value])
  end.

Definition runProgram {arrayIndex arrayType} `{EqDecision arrayIndex}
  (values : forall name, list (arrayType name))
  (code : Action (WithArrays arrayIndex arrayType) withArraysReturnValue unit)
  (input : list Z) := runIO (getNewArrays code values) input [].

Create HintDb advance_program.
Hint Rewrite runArrays_done runArrays_retrieve runArrays_store : advance_program.
Hint Rewrite @pushDispatch @pushDispatch2 @pushBooleanGet @pushBooleanGet2
  @pushNumberGet @pushNumberGet2 @pushBooleanSet @pushBooleanSet2
  @pushNumberSet @pushNumberSet2 : advance_program.

Lemma runArrays_grow arrayIndex indexEquality arrayType values name minimumLength zero continuation :
  runArrays arrayIndex indexEquality arrayType values (Dispatch _ _ _ (Grow _ _ name minimumLength zero) continuation) =
  runArrays arrayIndex indexEquality arrayType (growArrays values name (Z.to_nat minimumLength) zero) (continuation tt).
Proof. reflexivity. Qed.

Lemma growArrays_same {arrayIndex} `{EqDecision arrayIndex} {arrayType : arrayIndex -> Type}
  values (name : arrayIndex) minimumLength (zero : arrayType name) :
  growArrays values name minimumLength zero name = growList (values name) minimumLength zero.
Proof. unfold growArrays. destruct (decide (name = name)) as [h | h]; [| easy]. rewrite (UIP_dec (fun x y : arrayIndex => decide (x = y)) h eq_refl). reflexivity. Qed.

Lemma growArrays_other {arrayIndex} `{EqDecision arrayIndex} {arrayType : arrayIndex -> Type}
  values (name other : arrayIndex) minimumLength (zero : arrayType name) (h : other <> name) :
  growArrays values name minimumLength zero other = values other.
Proof. unfold growArrays. case_decide; easy. Qed.
