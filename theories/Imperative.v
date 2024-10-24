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
| WriteChar (value : Z)
| Donate (money : Z) (address : list Z)
| Invoke (money : Z) (address : list Z) (array : list Z)
| GetSender
| GetMoney
| GetCommunicationSize
| ReadByte (index : Z)
| SetByte (index value : Z).

#[export] Instance basicEffectEqualityDecidable : EqDecision BasicEffect := ltac:(solve_decision).

Definition basicEffectReturnValue (effect : BasicEffect): Type :=
  match effect with
  | Trap => False
  | Flush => unit
  | ReadChar => Z
  | WriteChar _ => unit
  | Donate _ _ => unit
  | Invoke _ _ _ => list Z
  | GetSender => list Z
  | GetMoney => Z
  | GetCommunicationSize => Z
  | ReadByte _ => Z
  | SetByte _ _ => unit
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

Lemma unfold_Donate a b :
  basicEffectReturnValue (Donate a b) = unit.
Proof. reflexivity. Qed.

Lemma unfold_Invoke a b c :
  basicEffectReturnValue (Invoke a b c) = list Z.
Proof. reflexivity. Qed.

Lemma unfold_GetSender :
  basicEffectReturnValue GetSender = list Z.
Proof. reflexivity. Qed.

Lemma unfold_GetMoney :
  basicEffectReturnValue GetMoney = Z.
Proof. reflexivity. Qed.

Lemma unfold_GetCommunicationSize :
  basicEffectReturnValue GetCommunicationSize = Z.
Proof. reflexivity. Qed.

Lemma unfold_ReadByte b :
  basicEffectReturnValue (ReadByte b) = Z.
Proof. reflexivity. Qed.

Lemma unfold_SetByte a b :
  basicEffectReturnValue (SetByte a b) = unit.
Proof. reflexivity. Qed.

(* Autorewrite database *)
Create HintDb basicEffectReturnValue_unfold.

Hint Rewrite unfold_Trap : basicEffectReturnValue_unfold.
Hint Rewrite unfold_Flush : basicEffectReturnValue_unfold.
Hint Rewrite unfold_ReadChar : basicEffectReturnValue_unfold.
Hint Rewrite unfold_WriteChar : basicEffectReturnValue_unfold.
Hint Rewrite unfold_Donate : basicEffectReturnValue_unfold.
Hint Rewrite unfold_Invoke : basicEffectReturnValue_unfold.
Hint Rewrite unfold_GetSender : basicEffectReturnValue_unfold.
Hint Rewrite unfold_GetMoney : basicEffectReturnValue_unfold.
Hint Rewrite unfold_GetCommunicationSize : basicEffectReturnValue_unfold.
Hint Rewrite unfold_ReadByte : basicEffectReturnValue_unfold.
Hint Rewrite unfold_SetByte : basicEffectReturnValue_unfold.

Inductive WithArrays (arrayIndex : Type) (arrayType : arrayIndex -> Type) :=
| DoBasicEffect (effect : BasicEffect)
| Retrieve (arrayName : arrayIndex) (index : Z)
| Store (arrayName : arrayIndex) (index : Z) (value : arrayType arrayName).

#[export] Instance withArraysEqualityDecidable {arrayIndex : Type} {arrayType : arrayIndex -> Type} (hIndexEq : EqDecision arrayIndex) (hArrayType : forall name, EqDecision (arrayType name)) : EqDecision (WithArrays arrayIndex arrayType).
Proof.
  intros a b.
  destruct a as [e | a i | a i v]; destruct b as [e1 | a1 i1 | a1 i1 v1]; try ((left; easy) || (right; easy)).
  - destruct (decide (e = e1)) as [h | h]; try subst e1.
    { now left. } { right; intro x; now inversion x. }
  - destruct (decide (a = a1)) as [h | h]; try subst a1; destruct (decide (i = i1)) as [h1 | h1]; try subst i1; try now left.
    all: right; intro x; now inversion x.
  - destruct (decide (a = a1)) as [h | h]; try subst a1; destruct (decide (i = i1)) as [h1 | h1]; try subst i1; try (right; intro x; now inversion x).
    destruct (hArrayType a v v1) as [h | h]; try (subst v1; now left). right. intro x. inversion x as [x1]. apply inj_pair2_eq_dec in x1; try easy.
Qed.

Definition withArraysReturnValue {arrayIndex} {arrayType : arrayIndex -> Type} (effect : WithArrays arrayIndex arrayType) : Type :=
  match effect with
  | DoBasicEffect _ _ effect => basicEffectReturnValue effect
  | Retrieve _ _ arrayName _ => arrayType arrayName
  | Store _ _ _ _ _ => unit
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

(* Autorewrite database *)
Create HintDb withArraysReturnValue_unfold.

Hint Rewrite unfold_DoBasicEffect : withArraysReturnValue_unfold.
Hint Rewrite unfold_Retrieve : withArraysReturnValue_unfold.
Hint Rewrite unfold_Store :
 withArraysReturnValue_unfold.

Inductive WithLocalVariables (arrayIndex : Type) (arrayType : arrayIndex -> Type) (variableIndex : Type) :=
| DoWithArrays (effect : WithArrays arrayIndex arrayType)
| BooleanLocalGet (name : variableIndex)
| BooleanLocalSet (name : variableIndex) (value : bool)
| NumberLocalGet (name : variableIndex)
| NumberLocalSet (name : variableIndex) (value : Z)
| AddressLocalGet (name : variableIndex)
| AddressLocalSet (name : variableIndex) (value : list Z).

#[export] Instance withLocalVariablesEqualityDecidable {arrayIndex arrayType variableIndex} (hArrayIndex : EqDecision arrayIndex) (hArrayType : forall name, EqDecision (arrayType name)) (hVariableIndex : EqDecision variableIndex) : EqDecision (WithLocalVariables arrayIndex arrayType variableIndex) := ltac:(solve_decision).

Definition withLocalVariablesReturnValue {arrayIndex arrayType variableIndex} (effect : WithLocalVariables arrayIndex arrayType variableIndex) : Type :=
  match effect with
  | DoWithArrays _ _ _ effect => withArraysReturnValue effect
  | BooleanLocalGet _ _ _ _ => bool
  | BooleanLocalSet _ _ _ _ _ => unit
  | NumberLocalGet _ _ _ _ => Z
  | NumberLocalSet _ _ _ _ _ => unit
  | AddressLocalGet _ _ _ _ => list Z
  | AddressLocalSet _ _ _ _ _ => unit
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

Lemma unfold_AddressLocalGet arrayIndex arrayType variableIndex d :
  @withLocalVariablesReturnValue arrayIndex arrayType variableIndex (AddressLocalGet _ _ _ d) =
  list Z.
Proof. reflexivity. Qed.

Lemma unfold_AddressLocalSet arrayIndex arrayType variableIndex d e :
  @withLocalVariablesReturnValue arrayIndex arrayType variableIndex (AddressLocalSet _ _ _ d e) =
  unit.
Proof. reflexivity. Qed.

(* Autorewrite database *)
Create HintDb withLocalVariablesReturnValue_unfold.

Hint Rewrite unfold_DoWithArrays : withLocalVariablesReturnValue_unfold.
Hint Rewrite unfold_BooleanLocalGet : withLocalVariablesReturnValue_unfold.
Hint Rewrite unfold_BooleanLocalSet : withLocalVariablesReturnValue_unfold.
Hint Rewrite unfold_NumberLocalGet : withLocalVariablesReturnValue_unfold.
Hint Rewrite unfold_NumberLocalSet : withLocalVariablesReturnValue_unfold.
Hint Rewrite unfold_AddressLocalGet : withLocalVariablesReturnValue_unfold.
Hint Rewrite unfold_AddressLocalSet : withLocalVariablesReturnValue_unfold.

(* To automatically rewrite using these lemmas, you can use: *)

(* autorewrite with withLocalVariablesReturnValue_unfold. *)

(* Combined autorewrite database *)
Create HintDb combined_unfold.

Hint Rewrite unfold_DoWithArrays : combined_unfold.
Hint Rewrite unfold_BooleanLocalGet : combined_unfold.
Hint Rewrite unfold_BooleanLocalSet : combined_unfold.
Hint Rewrite unfold_NumberLocalGet : combined_unfold.
Hint Rewrite unfold_NumberLocalSet : combined_unfold.
Hint Rewrite unfold_AddressLocalGet : combined_unfold.
Hint Rewrite unfold_AddressLocalSet : combined_unfold.

Hint Rewrite unfold_DoBasicEffect : combined_unfold.
Hint Rewrite unfold_Retrieve : combined_unfold.
Hint Rewrite unfold_Store : combined_unfold.

Hint Rewrite unfold_Trap : combined_unfold.
Hint Rewrite unfold_Flush : combined_unfold.
Hint Rewrite unfold_ReadChar : combined_unfold.
Hint Rewrite unfold_WriteChar : combined_unfold.
Hint Rewrite unfold_Donate : combined_unfold.
Hint Rewrite unfold_Invoke : combined_unfold.
Hint Rewrite unfold_GetSender : combined_unfold.
Hint Rewrite unfold_GetMoney : combined_unfold.
Hint Rewrite unfold_GetCommunicationSize : combined_unfold.
Hint Rewrite unfold_ReadByte : combined_unfold.
Hint Rewrite unfold_SetByte : combined_unfold.

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

Lemma eliminateLocalVariables {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) (action : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue unit) : Action (WithArrays arrayIndex arrayType) withArraysReturnValue unit.
Proof.
  induction action as [x | effect continuation IH] in bools, numbers, addresses |- *;
  [exact (Done _ _ _ x) |].
  destruct effect as [effect | name | name value | name | name value | name | name value].
  - apply (Dispatch (WithArrays arrayIndex arrayType) withArraysReturnValue unit effect).
    simpl in IH, continuation. intro value. exact (IH value bools numbers addresses).
  - simpl in IH, continuation. exact (IH (bools name) bools numbers addresses).
  - simpl in IH, continuation. exact (IH tt (update bools name value) numbers addresses).
  - simpl in IH, continuation. exact (IH (numbers name) bools numbers addresses).
  - simpl in IH, continuation. exact (IH tt bools (update numbers name value) addresses).
  - simpl in IH, continuation. exact (IH (addresses name) bools numbers addresses).
  - simpl in IH, continuation. exact (IH tt bools numbers (update addresses name value)).
Defined.

Lemma pushDispatch {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) effect continuation : eliminateLocalVariables bools numbers addresses (Dispatch _ _ _ (DoWithArrays arrayIndex arrayType _ effect) continuation) = Dispatch _ _ _ effect (fun x => eliminateLocalVariables bools numbers addresses (continuation x)).
Proof. easy. Qed.

Lemma pushDispatch2 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) effect continuation : eliminateLocalVariables bools numbers addresses ((Dispatch _ _ _ (DoWithArrays arrayIndex arrayType _ effect) (fun x => Done _ _ _ x)) >>= continuation) = Dispatch _ _ _ effect (fun x => eliminateLocalVariables bools numbers addresses (continuation x)).
Proof. easy. Qed.

Lemma pushDispatch3 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) effect continuation : eliminateLocalVariables bools numbers addresses ((Dispatch _ _ _ (DoWithArrays arrayIndex arrayType _ effect) (fun x => dropWithinLoop (Done _ _ _ tt))) >>= continuation) = Dispatch _ _ _ effect (fun x => eliminateLocalVariables bools numbers addresses (continuation KeepGoing)).
Proof. easy. Qed.

Lemma pushBooleanGet {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) name continuation : eliminateLocalVariables bools numbers addresses (Dispatch _ _ _ (BooleanLocalGet arrayIndex arrayType _ name) continuation) = eliminateLocalVariables bools numbers addresses (continuation (bools name)).
Proof. easy. Qed.

Lemma pushBooleanGet2 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) name continuation : eliminateLocalVariables bools numbers addresses ((Dispatch _ _ _ (BooleanLocalGet arrayIndex arrayType _ name) (fun x => Done _ _ _ x)) >>= continuation) = eliminateLocalVariables bools numbers addresses (continuation (bools name)).
Proof. easy. Qed.

Lemma pushNumberGet {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) name continuation : eliminateLocalVariables bools numbers addresses (Dispatch _ _ _ (NumberLocalGet arrayIndex arrayType _ name) continuation) = eliminateLocalVariables bools numbers addresses (continuation (numbers name)).
Proof. easy. Qed.

Lemma pushNumberGet2 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) name continuation : eliminateLocalVariables bools numbers addresses ((Dispatch _ _ _ (NumberLocalGet arrayIndex arrayType _ name) (fun x => Done _ _ _ x)) >>= continuation) = eliminateLocalVariables bools numbers addresses (continuation (numbers name)).
Proof. easy. Qed.

Lemma pushAddressGet {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) name continuation : eliminateLocalVariables bools numbers addresses (Dispatch _ _ _ (AddressLocalGet arrayIndex arrayType _ name) continuation) = eliminateLocalVariables bools numbers addresses (continuation (addresses name)).
Proof. easy. Qed.

Lemma pushAddressGet2 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) name continuation : eliminateLocalVariables bools numbers addresses ((Dispatch _ _ _ (AddressLocalGet arrayIndex arrayType _ name) (fun x => Done _ _ _ x)) >>= continuation) = eliminateLocalVariables bools numbers addresses (continuation (addresses name)).
Proof. easy. Qed.

Lemma pushBooleanSet {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) name value continuation : eliminateLocalVariables bools numbers addresses (Dispatch _ _ _ (BooleanLocalSet arrayIndex arrayType _ name value) continuation) = eliminateLocalVariables (update bools name value) numbers addresses (continuation tt).
Proof. easy. Qed.

Lemma pushBooleanSet2 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) name value continuation : eliminateLocalVariables bools numbers addresses ((Dispatch _ _ _ (BooleanLocalSet arrayIndex arrayType _ name value) (fun x => Done _ _ _ x)) >>= continuation) = eliminateLocalVariables (update bools name value) numbers addresses (continuation tt).
Proof. easy. Qed.

Lemma pushNumberSet {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) name value continuation : eliminateLocalVariables bools numbers addresses (Dispatch _ _ _ (NumberLocalSet arrayIndex arrayType _ name value) continuation) = eliminateLocalVariables bools (update numbers name value) addresses (continuation tt).
Proof. easy. Qed.

Lemma pushNumberSet2 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) name value continuation : eliminateLocalVariables bools numbers addresses ((Dispatch _ _ _ (NumberLocalSet arrayIndex arrayType _ name value) (fun x => Done _ _ _ x)) >>= continuation) = eliminateLocalVariables bools (update numbers name value) addresses (continuation tt).
Proof. easy. Qed.

Lemma pushAddressSet {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) name value continuation : eliminateLocalVariables bools numbers addresses (Dispatch _ _ _ (AddressLocalSet arrayIndex arrayType _ name value) continuation) = eliminateLocalVariables bools numbers (update addresses name value) (continuation tt).
Proof. easy. Qed.

Lemma pushAddressSet2 {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) name value continuation : eliminateLocalVariables bools numbers addresses ((Dispatch _ _ _ (AddressLocalSet arrayIndex arrayType _ name value) (fun x => Done _ _ _ x)) >>= continuation) = eliminateLocalVariables bools numbers (update addresses name value) (continuation tt).
Proof. easy. Qed.

Definition readChar arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z (DoWithArrays _ _ _ (DoBasicEffect _ _ ReadChar)) (fun x => Done _ _ Z x).

Definition writeChar arrayIndex arrayType variableIndex x := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ (WriteChar x))) (fun x => Done _ _ _ x).

Definition flush arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ Flush)) (fun x => Done _ _ _ x).

Definition trap arrayIndex arrayType variableIndex returnType := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue returnType (DoWithArrays _ _ _ (DoBasicEffect _ _ Trap)) (fun x => False_rect _ x).

Definition readByte arrayIndex arrayType variableIndex index := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ (ReadByte index))) (fun x => Done _ _ _ x).

Definition setByte arrayIndex arrayType variableIndex index value := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ (SetByte index value))) (fun x => Done _ _ _ x).

Definition getSender arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ GetSender)) (fun x => Done _ _ _ x).

Definition getMoney arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ GetMoney)) (fun x => Done _ _ _ x).

Definition getCommunicationSize arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ GetCommunicationSize)) (fun x => Done _ _ _ x).

Definition donate arrayIndex arrayType variableIndex money address := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ (Donate money address))) (fun x => Done _ _ _ x).

Definition invoke arrayIndex arrayType variableIndex money address array := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ (Invoke money address array))) (fun x => Done _ _ _ x).

Definition booleanLocalSet arrayIndex arrayType variableIndex name value := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (BooleanLocalSet _ _ _ name value) (fun x => Done _ _ _ x).

Definition booleanLocalGet arrayIndex arrayType variableIndex name := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (BooleanLocalGet _ _ _ name) (fun x => Done _ _ _ x).

Definition addressLocalSet arrayIndex arrayType variableIndex name value := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (AddressLocalSet _ _ _ name value) (fun x => Done _ _ _ x).

Definition addressLocalGet arrayIndex arrayType variableIndex name := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (AddressLocalGet _ _ _ name) (fun x => Done _ _ _ x).

Definition numberLocalSet arrayIndex arrayType variableIndex name value := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (NumberLocalSet _ _ _ name value) (fun x => Done _ _ _ x).

Definition numberLocalGet arrayIndex arrayType variableIndex name := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (NumberLocalGet _ _ _ name) (fun x => Done _ _ _ x).

Definition retrieve arrayIndex arrayType variableIndex name index := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (Retrieve arrayIndex arrayType name index)) (fun x => Done _ _ _ x).

Definition store arrayIndex arrayType variableIndex name index (value : arrayType name) := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (Store _ _ name index value)) (fun x => Done _ _ _ x).

Definition continue arrayIndex arrayType variableIndex := Dispatch (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue () (DoContinue _ _ _) (fun x => Done _ _ _ tt).

Definition break arrayIndex arrayType variableIndex := Dispatch (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue () (DoBreak _ _ _) (fun x => Done _ _ _ tt).

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

Lemma eliminateLift {arrayIndex arrayType variableIndex returnType} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) (action : Action (WithArrays arrayIndex arrayType) withArraysReturnValue returnType) continuation : eliminateLocalVariables bools numbers addresses (liftToWithLocalVariables action >>= continuation) = action >>= fun x => eliminateLocalVariables bools numbers addresses (continuation x).
Proof.
  induction action as [a | a b IH]. { easy. }
  change (Dispatch (WithArrays arrayIndex arrayType) withArraysReturnValue
  () a
  (λ _1 : withArraysReturnValue a,
  eliminateLocalVariables bools numbers addresses
  (liftToWithLocalVariables (b _1) >>= continuation)) =
Dispatch (WithArrays arrayIndex arrayType) withArraysReturnValue
  () a
  (λ _1 : withArraysReturnValue a,
  b _1 >>=
λ _2 : returnType,
  eliminateLocalVariables bools numbers addresses
  (continuation _2))). rewrite (functional_extensionality_dep _ _ IH). reflexivity.
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

Lemma nth_lt {A} (l : list A) (n : nat) (isLess : Nat.lt n (length l)) : A.
Proof.
  destruct l as [| head tail]; simpl in *; (lia || exact (nth n (head :: tail) head)).
Defined.

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

Definition invokeWithArrays {arrayIndex} {arrayType : arrayIndex -> Type} {variableIndex} (money : Z) (address : list Z) (arrayName : arrayIndex) (length : Z) (hEq : arrayType arrayName = Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue () := getArray arrayName (Z.to_nat length) >>= fun array => invoke arrayIndex arrayType variableIndex money address ltac:(rewrite hEq in *; exact array) >>= fun array => applyArray arrayName ltac:(rewrite hEq in *; exact array) 0.

Lemma getNewArrays {arrayIndex arrayType} `{EqDecision arrayIndex} (x : Action (WithArrays arrayIndex arrayType) withArraysReturnValue ()) (arrays : forall x, list (arrayType x)) : (Action BasicEffect basicEffectReturnValue (forall x, list (arrayType x))).
Proof.
  induction x as [x | effect continuation IH] in arrays |- *.
  - exact (Done _ _ _ arrays).
  - destruct effect as [effect | arrayName index | arrayName index value].
    + exact (Dispatch _ _ _ effect (fun x => (IH ltac:(simpl in *; exact x) arrays))).
    + destruct (decide (Nat.lt (Z.to_nat index) (length (arrays arrayName)))) as [H | H].
      * exact (IH ltac:(simpl in *; exact (nth_lt (arrays arrayName) (Z.to_nat index) H)) arrays).
      * exact (Dispatch _ _ _ Trap (fun _ => Done _ _ _ arrays)).
    + destruct (decide (Nat.lt (Z.to_nat index) (length (arrays arrayName)))) as [H | H].
      * exact (IH tt (fun name => ltac:(destruct (decide (name = arrayName)) as [H' |]; [subst arrayName; exact (<[(Z.to_nat index):=value]>(arrays name)) | exact (arrays name)]))).
      * exact (Dispatch _ _ _ Trap (fun _ => Done _ _ _ arrays)).
Defined.

Lemma withArraysReturnValueDoBasicEffectArrayType arrayIndex1 arrayIndex2 arrayType1 arrayType2 (effect : BasicEffect) : withArraysReturnValue (DoBasicEffect arrayIndex1 arrayType1 effect) = withArraysReturnValue (DoBasicEffect arrayIndex2 arrayType2 effect).
Proof. auto. Qed.

Lemma translateArrays {arrayIndex1 arrayIndex2 arrayType} (x : Action (WithArrays arrayIndex1 arrayType) withArraysReturnValue ()) (destinationArrayType : arrayIndex2 -> Type) (mapping : arrayIndex1 -> arrayIndex2) (hCongruent : forall x, arrayType x = destinationArrayType (mapping x)) : Action (WithArrays arrayIndex2 destinationArrayType) withArraysReturnValue ().
Proof.
  induction x as [x | effect continuation IH].
  - exact (Done _ _ _ tt).
  - destruct effect as [effect | arrayName index | arrayName index value].
    + rewrite (withArraysReturnValueDoBasicEffectArrayType arrayIndex1 arrayIndex2 arrayType destinationArrayType) in IH. exact (Dispatch _ _ _ (DoBasicEffect _ destinationArrayType effect) IH).
    + assert (h : withArraysReturnValue (Retrieve arrayIndex1 arrayType arrayName index) = withArraysReturnValue (Retrieve arrayIndex2 destinationArrayType (mapping arrayName) index)). { simpl; auto. }
      rewrite h in IH.
      exact (Dispatch _ _ _ (Retrieve _ destinationArrayType (mapping arrayName) index) IH).
    + assert (h : withArraysReturnValue (Store arrayIndex1 arrayType arrayName index value) = withArraysReturnValue (Store _ destinationArrayType (mapping arrayName) index ltac:(rewrite <- hCongruent; exact value))). { simpl; auto. }
      rewrite h in IH.
      exact (Dispatch _ _ _ (Store _ destinationArrayType (mapping arrayName) index ltac:(rewrite <- hCongruent; exact value)) IH).
Defined.

Lemma modifyArray {arrayIndex} `{EqDecision arrayIndex} {arrayType : arrayIndex -> Type} (arrays : forall x, list (arrayType x)) (toBeModified : arrayIndex) (index : nat) (value : arrayType toBeModified) : forall x, list (arrayType x).
Proof.
  intro arrayName.
  destruct (decide (arrayName = toBeModified)) as [H | H].
  - rewrite <- H in value.
    exact (<[index:=value]>(arrays arrayName)).
  - exact (arrays arrayName).
Defined.

Lemma getAllCharacters {arrayIndex arrayType} (x : Action (WithArrays arrayIndex arrayType) withArraysReturnValue ()) (captured : list Z) : Action (WithArrays arrayIndex arrayType) withArraysReturnValue (list Z).
Proof.
  induction x as [x | effect continuation IH] in captured |- *.
  - exact (Done _ _ _ captured).
  - destruct effect as [effect | arrayName index | arrayName index value].
    + destruct effect as [| | | x | | | | | | |].
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => IH returnValue captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Flush) (fun returnValue => IH returnValue captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ ReadChar) (fun returnValue => IH returnValue captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ (WriteChar x)) (fun returnValue => IH returnValue (captured ++ [x]))).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
    + exact (Dispatch _ _ _ (Retrieve _ arrayType arrayName index) (fun x => IH x captured)).
    + exact (Dispatch _ _ _ (Store _ arrayType arrayName index value) (fun x => IH x captured)).
Defined.

Inductive BlockchainAccount :=
| ExternallyOwned (money : Z)
| BlockchainContract (arrayIndex : Type) (arrayIndexEqualityDecidable : EqDecision arrayIndex) (arrayType : arrayIndex -> Type) (arrays : forall (name : arrayIndex), list (arrayType name)) (money : Z) (code : Action (WithArrays arrayIndex arrayType) withArraysReturnValue ()).

Definition BlockchainState := list Z -> BlockchainAccount.

Definition getBalance (x : BlockchainAccount) : Z :=
  match x with
  | ExternallyOwned money => money
  | BlockchainContract _ _ _ _ balance _ => balance
  end.

Definition updateBalance (x : BlockchainAccount) (newBalance : Z) : BlockchainAccount :=
  match x with
  | ExternallyOwned _ => ExternallyOwned newBalance
  | BlockchainContract a b c d _ e => BlockchainContract a b c d newBalance e
  end.

Definition transferMoney (state : BlockchainState) (sender target : list Z) (money : Z) :=
  let intermediateState := update state sender (updateBalance (state sender) (getBalance (state sender) - money)) in
  update intermediateState target (updateBalance (state target) (getBalance (state target) + money)).

(* this assumes the money has already been transferred before the contract gets invoked *)
(* so initially this function doesn't deduct the balance of the sender and credit the balance of the target *)
(* revertTo: state before the money transfer and the subsequent contract invocation, state: current state *)
Fixpoint invokeContractAux (sender target : list Z) (money : Z) (revertTo state : BlockchainState) (communication : list Z) (fuel : nat) (arrayIndex : Type) (arrayIndexEqualityDecidable : EqDecision arrayIndex) (arrayType : arrayIndex -> Type) (arrays : forall (name : arrayIndex), list (arrayType name)) (originalCode code : Action (WithArrays arrayIndex arrayType) withArraysReturnValue ()): option (list Z * BlockchainState) :=
  match fuel with
  | O => None
  | S fuel => (fix inner (code : Action (WithArrays arrayIndex arrayType) withArraysReturnValue ()) (communication : list Z) (arrays : forall (name : arrayIndex), list (arrayType name)) (state : BlockchainState) :=
    match code with
    | Done _ _ _ _ => Some (communication, update state target (BlockchainContract arrayIndex _ arrayType arrays (getBalance (state target)) originalCode))
    | Dispatch _ _ _ (Retrieve _ _ arrayName index) continuation =>
      match decide (Nat.lt (Z.to_nat index) (length (arrays arrayName))) with
      | left h => inner (continuation (nth_lt (arrays arrayName) (Z.to_nat index) h)) communication arrays state
      | right _ => Some ([], revertTo)
      end
    | Dispatch _ _ _ (Store _ _ arrayName index value) continuation =>
      match decide (Nat.lt (Z.to_nat index) (length (arrays arrayName))) with
      | left h => inner (continuation tt) communication (fun currentName =>
        match decide (currentName = arrayName) with
        | left h => ltac:(rewrite h; exact (<[Z.to_nat index := value]> (arrays arrayName)))
        | right _ => arrays currentName
        end) state
      | right _ => Some ([], revertTo)
      end
      | Dispatch _ _ _ (DoBasicEffect _ _ Trap) continuation => Some ([], revertTo)
      | Dispatch _ _ _ (DoBasicEffect _ _ Flush) continuation => Some ([], revertTo)
      | Dispatch _ _ _ (DoBasicEffect _ _ ReadChar) continuation => Some ([], revertTo)
      | Dispatch _ _ _ (DoBasicEffect _ _ (WriteChar _)) continuation => Some ([], revertTo)
      | Dispatch _ _ _ (DoBasicEffect _ _ (Donate money address)) continuation =>
        if decide (money <= getBalance (state target) /\ 0 <= money /\ money < 2^256) then
          inner (continuation tt) communication arrays (transferMoney state target address money)
        else Some ([], revertTo)
      | Dispatch _ _ _ (DoBasicEffect _ _ (Invoke money address passedArray)) continuation =>
        if decide (money <= getBalance (state target) /\ 0 <= money /\ money < 2^256) then
          let alteredState := update state target (BlockchainContract arrayIndex _ arrayType arrays (getBalance (state target)) originalCode) in
          match (state address) with
          | ExternallyOwned _ => inner (continuation []) communication arrays (transferMoney alteredState target address money)
          | BlockchainContract arrayIndex arrayIndexEqualityDecidable arrayType arrays2 balance code => match invokeContractAux target address money alteredState (transferMoney alteredState target address money) passedArray fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays2 code code with
            | None => None
            | Some (newArray, newState) => inner (continuation newArray) communication arrays newState
            end
          end
        else Some ([], revertTo)
      | Dispatch _ _ _ (DoBasicEffect _ _ GetSender) continuation => inner (continuation sender) communication arrays state
      | Dispatch _ _ _ (DoBasicEffect _ _ GetMoney) continuation => inner (continuation money) communication arrays state
      | Dispatch _ _ _ (DoBasicEffect _ _ GetCommunicationSize) continuation => inner (continuation (Z.of_nat (length communication))) communication arrays state
      | Dispatch _ _ _ (DoBasicEffect _ _ (ReadByte index)) continuation =>
        if decide (Nat.lt (Z.to_nat index) (length communication)) then
          inner (continuation (nth (Z.to_nat index) communication 0)) communication arrays state
        else Some ([], revertTo)
      | Dispatch _ _ _ (DoBasicEffect _ _ (SetByte index value)) continuation =>
        if decide (Nat.lt (Z.to_nat index) (length communication)) then
          inner (continuation tt) (<[Z.to_nat index := value]> communication) arrays state
        else Some ([], revertTo)
      end) code communication arrays state
    end.

Definition invokeContract (sender target : list Z) (money : Z) (revertTo state : BlockchainState) (communication : list Z) (fuel : nat) :=
  match state target with
  | ExternallyOwned _ => Some ([], state)
  | BlockchainContract arrayIndex arrayIndexEqualityDecidable arrayType arrays balance code => invokeContractAux sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays code code
  end.

Lemma unfoldInvoke_0 : 
  forall sender target money revertTo state communication arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode code,
    invokeContractAux sender target money revertTo state communication 0 arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode code = None.
Proof. easy. Qed.

Lemma unfoldInvoke_S_Done : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays returnValue originalCode,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Done _ _ _ returnValue) =
      Some (communication, update state target (BlockchainContract arrayIndex _ arrayType arrays (getBalance (state target)) originalCode)).
Proof. easy. Qed.

Lemma unfoldInvoke_S_Retrieve : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode arrayName index continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (Retrieve _ _ arrayName index) continuation) =
      match decide (Nat.lt (Z.to_nat index) (length (arrays arrayName))) with
      | left h => invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (continuation (nth_lt (arrays arrayName) (Z.to_nat index) h))
      | right _ => Some ([], revertTo)
      end.
Proof. easy. Qed.

Lemma unfoldInvoke_S_Store : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode arrayName index value continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (Store _ _ arrayName index value) continuation) =
      match decide (Nat.lt (Z.to_nat index) (length (arrays arrayName))) with
      | left h =>
          invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType 
            (fun currentName => match decide (currentName = arrayName) with
              | left h => ltac:(rewrite h; exact (<[Z.to_nat index := value]> (arrays arrayName)))
              | right _ => arrays currentName
              end)
            originalCode (continuation tt)
      | right _ => Some ([], revertTo)
      end.
Proof. easy. Qed.

Lemma unfoldInvoke_S_Trap : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (DoBasicEffect _ _ Trap) continuation) = 
      Some ([], revertTo).
Proof. easy. Qed.

Lemma unfoldInvoke_S_Flush : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (DoBasicEffect _ _ Flush) continuation) = 
      Some ([], revertTo).
Proof. easy. Qed.

Lemma unfoldInvoke_S_ReadChar : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (DoBasicEffect _ _ ReadChar) continuation) = 
      Some ([], revertTo).
Proof. easy. Qed.

Lemma unfoldInvoke_S_WriteChar : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode value continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (DoBasicEffect _ _ (WriteChar value)) continuation) = 
      Some ([], revertTo).
Proof. easy. Qed.

Lemma unfoldInvoke_S_Donate : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode donationMoney address continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (DoBasicEffect _ _ (Donate donationMoney address)) continuation) = 
      if decide (donationMoney <= getBalance (state target) /\ 0 <= donationMoney /\ donationMoney < 2^256) then
        invokeContractAux sender target money revertTo (transferMoney state target address donationMoney) communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (continuation tt)
      else Some ([], revertTo).
Proof. easy. Qed.

Lemma unfoldInvoke_S_Invoke : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode invokeMoney address passedArray continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (DoBasicEffect _ _ (Invoke invokeMoney address passedArray)) continuation) = 
      if decide (invokeMoney <= getBalance (state target) /\ 0 <= invokeMoney /\ invokeMoney < 2^256) then
        let alteredState := update state target (BlockchainContract arrayIndex _ arrayType arrays (getBalance (state target)) originalCode) in
        match (state address) with
        | ExternallyOwned _ => invokeContractAux sender target money revertTo (transferMoney alteredState target address invokeMoney) communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (continuation [])
        | BlockchainContract arrayIndex2 arrayIndexEqualityDecidable2 arrayType2 arrays2 _ code =>
          match invokeContractAux target address invokeMoney alteredState (transferMoney alteredState target address invokeMoney) passedArray fuel arrayIndex2 arrayIndexEqualityDecidable2 arrayType2 arrays2 code code with
          | None => None
          | Some (newArray, newState) => invokeContractAux sender target money revertTo newState communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (continuation newArray)
          end
        end
      else Some ([], revertTo).
Proof. easy. Qed.

Lemma unfoldInvoke_S_GetSender : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (DoBasicEffect _ _ GetSender) continuation) = invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (continuation sender).
Proof. easy. Qed.

Lemma unfoldInvoke_S_GetMoney : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (DoBasicEffect _ _ GetMoney) continuation) = invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (continuation money).
Proof. easy. Qed.

Lemma unfoldInvoke_S_GetCommunicationSize : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (DoBasicEffect _ _ GetCommunicationSize) continuation) = invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (continuation (Z.of_nat (length communication))).
Proof. easy. Qed.

Lemma unfoldInvoke_S_ReadByte : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode index continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (DoBasicEffect _ _ (ReadByte index)) continuation) =
    if decide (Nat.lt (Z.to_nat index) (length communication)) then
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (continuation (nth (Z.to_nat index) communication 0))
    else Some ([], revertTo).
Proof. easy. Qed.

Lemma unfoldInvoke_S_SetByte : 
  forall sender target money revertTo state communication fuel arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode index value continuation,
    invokeContractAux sender target money revertTo state communication (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (Dispatch _ _ _ (DoBasicEffect _ _ (SetByte index value)) continuation) =
    if decide (Nat.lt (Z.to_nat index) (length communication)) then
    invokeContractAux sender target money revertTo state (<[Z.to_nat index := value]> communication) (S fuel) arrayIndex arrayIndexEqualityDecidable arrayType arrays originalCode (continuation tt)
    else Some ([], revertTo).
Proof. easy. Qed.

Create HintDb advance_program.
Hint Rewrite unfoldInvoke_0 : advance_program.
Hint Rewrite unfoldInvoke_S_Done : advance_program.
Hint Rewrite unfoldInvoke_S_Retrieve : advance_program.
Hint Rewrite unfoldInvoke_S_Store : advance_program.
Hint Rewrite unfoldInvoke_S_Trap : advance_program.
Hint Rewrite unfoldInvoke_S_Flush : advance_program.
Hint Rewrite unfoldInvoke_S_ReadChar : advance_program.
Hint Rewrite unfoldInvoke_S_WriteChar : advance_program.
Hint Rewrite unfoldInvoke_S_Donate : advance_program.
Hint Rewrite unfoldInvoke_S_Invoke : advance_program.
Hint Rewrite unfoldInvoke_S_GetSender : advance_program.
Hint Rewrite unfoldInvoke_S_GetMoney : advance_program.
Hint Rewrite unfoldInvoke_S_GetCommunicationSize : advance_program.
Hint Rewrite unfoldInvoke_S_ReadByte : advance_program.
Hint Rewrite unfoldInvoke_S_SetByte : advance_program.
Hint Rewrite @pushDispatch : advance_program.
Hint Rewrite @pushDispatch2 : advance_program.
Hint Rewrite @pushBooleanGet : advance_program.
Hint Rewrite @pushBooleanGet2 : advance_program.
Hint Rewrite @pushNumberGet : advance_program.
Hint Rewrite @pushNumberGet2 : advance_program.
Hint Rewrite @pushAddressGet : advance_program.
Hint Rewrite @pushAddressGet2 : advance_program.
Hint Rewrite @pushBooleanSet : advance_program.
Hint Rewrite @pushBooleanSet2 : advance_program.
Hint Rewrite @pushNumberSet : advance_program.
Hint Rewrite @pushNumberSet2 : advance_program.
Hint Rewrite @pushAddressSet : advance_program.
Hint Rewrite @pushAddressSet2 : advance_program.
