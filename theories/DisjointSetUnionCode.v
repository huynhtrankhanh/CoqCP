From CoqCP Require Import Options Imperative DisjointSetUnion ListsEqual.
From Generated Require Import DisjointSetUnion.
From stdpp Require Import numbers list.
Require Import Coq.Logic.FunctionalExtensionality.

Definition state : BlockchainState := fun address =>
  if decide (address = repeat (0%Z) 20) then
    BlockchainContract arrayIndex0 _ (arrayType _ environment0) (arrays _ environment0) 100000%Z (funcdef_0__main (fun x => false) (fun x => 0%Z) (fun x => repeat 0%Z 20))
  else ExternallyOwned 0%Z.

Definition stateAfterInteractions arrays money : BlockchainState := fun address =>
  if decide (address = repeat (0%Z) 20) then
    BlockchainContract arrayIndex0 _ (arrayType _ environment0) arrays (100000%Z - money) (funcdef_0__main (fun x => false) (fun x => 0%Z) (fun x => repeat 0%Z 20))
  else if decide (address = repeat (1%Z) 20) then ExternallyOwned money else ExternallyOwned 0%Z.

Fixpoint interact (state : BlockchainState) (interactions : list (Z * Z)) :=
  match interactions with
  | [] => getBalance (state (repeat 1%Z 20))
  | (a, b) :: tail =>
    match invokeContract (repeat 1%Z 20) (repeat 0%Z 20) 0%Z state state [a; b] 1 with
    | Some (_, changedState) => interact changedState tail
    | None => 0%Z
    end
  end.

Definition optimalInteractions (x : list (Z * Z)) := forall x', Z.le (interact state x') (interact state x).

Inductive Slot :=
| ReferTo (x : nat)
| Ancestor (x : Tree).

Fixpoint convertToArray (x : list Slot) : list Z :=
  match x with
  | [] => []
  | (ReferTo x) :: tail => (Z.of_nat x) :: convertToArray tail
  | (Ancestor x) :: tail => (Z.sub 256%Z (Z.of_nat (leafCount x))) :: convertToArray tail
  end.

Fixpoint ancestor (dsu : list Slot) (fuel : nat) (index : nat) :=
  match fuel with
  | O => index
  | S fuel => match nth index dsu (Ancestor Unit) with
    | ReferTo x => ancestor dsu fuel x
    | Ancestor _ => index
    end
  end.

Fixpoint pathCompress (dsu : list Slot) (fuel : nat) (index ancestor : nat) :=
  match fuel with
  | O => dsu
  | S fuel => match nth index dsu (Ancestor Unit) with
    | ReferTo x => pathCompress (<[index := ReferTo ancestor]> dsu) fuel x ancestor
    | Ancestor _ => dsu
    end
  end.

Definition performMerge (dsu : list Slot) (tree1 tree2 : Tree) (u v : nat) :=
  <[u := ReferTo v]> (<[v := Ancestor (Unite tree2 tree1)]> dsu).

Definition unite (dsu : list Slot) (a b : nat) :=
  if decide (length dsu <= a) then dsu else
  if decide (length dsu <= b) then dsu else
  let u := ancestor dsu (length dsu) a in
  let dsu1 := pathCompress dsu (length dsu) a u in
  let v := ancestor dsu1 (length dsu1) b in
  let dsu2 := pathCompress dsu1 (length dsu1) b v in
  if decide (u = v) then dsu2 else
  match nth u dsu2 (Ancestor Unit) with
  | ReferTo _ => dsu2
  | Ancestor tree1 => match nth v dsu2 (Ancestor Unit) with
    | ReferTo _ => dsu2
    | Ancestor tree2 =>
      if decide (leafCount tree2 < leafCount tree1) then performMerge dsu tree2 tree1 v u else performMerge dsu tree1 tree2 u v
    end
  end.

Fixpoint dsuFromInteractions (dsu : list Slot) (interactions : list (nat * nat)) :=
  match interactions with
  | [] => dsu
  | (a, b)::tail => dsuFromInteractions (unite dsu a b) tail
  end.

Definition dsuScore (dsu : list Slot) := Z.of_nat (list_sum (map (fun x => match x with | ReferTo _ => 0 | Ancestor x => score x end) dsu)).

Definition dsuLeafCount (dsu : list Slot) := Z.of_nat (list_sum (map (fun x => match x with | ReferTo _ => 0 | Ancestor x => leafCount x end) dsu)).

Definition modelScore (interactions : list (Z * Z)) := dsuScore (dsuFromInteractions (repeat (Ancestor Unit) 100) (map (fun (x : Z * Z) => let (a, b) := x in (Z.to_nat a, Z.to_nat b)) interactions)).

Definition getBalanceInvoke (state : BlockchainState) (communication : list Z) :=
  match invokeContract (repeat 1%Z 20) (repeat 0%Z 20) 0 state state communication 1 with
  | Some (a, b) => getBalance (b (repeat 1%Z 20))
  | None => 0%Z
  end.

Lemma initializeArray a b n nextCommands (h : n <= 100) (l : list Z) (hL : length l = 100) : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0
  state state [a; b] 1 arrayIndex0
  arrayIndexEqualityDecidable0
  (arrayType arrayIndex0 environment0) (λ _0 : arrayIndex0,
  match
  _0 as _1
return
  (list
  (arrayType
  arrayIndex0
  environment0
  _1))
with
| arraydef_0__dsu => l
| arraydef_0__hasBeenInitialized =>
    [1%Z]
| arraydef_0__result =>
    [0%Z]
end)
  (funcdef_0__main (λ _ : varsfuncdef_0__main, false)
  (λ _ : varsfuncdef_0__main, 0%Z)
  (λ _ : varsfuncdef_0__main, repeat 0%Z 20))
  (eliminateLocalVariables
  (λ _ : varsfuncdef_0__main, false)
  (λ _ : varsfuncdef_0__main, 0%Z)
  (λ _ : varsfuncdef_0__main, repeat 0%Z 20)
  (loop n
  (λ _0 : nat,
  dropWithinLoop
  (liftToWithinLoop
  (Done
  (WithLocalVariables arrayIndex0
  (arrayType arrayIndex0
  environment0)
  varsfuncdef_0__main)
  withLocalVariablesReturnValue Z
  (100%Z - Z.of_nat _0 - 1)%Z >>=
λ _1 : Z,
  Done
  (WithLocalVariables arrayIndex0
  (arrayType arrayIndex0
  environment0)
  varsfuncdef_0__main)
  withLocalVariablesReturnValue Z
  (coerceInt (coerceInt (- (1)) 64)
  8) >>=
λ _2 : Z,
  Dispatch
  (WithLocalVariables arrayIndex0
  (arrayType arrayIndex0
  environment0)
  varsfuncdef_0__main)
  withLocalVariablesReturnValue
  (withLocalVariablesReturnValue
  (DoWithArrays arrayIndex0
  (arrayType arrayIndex0
  environment0)
  varsfuncdef_0__main
  (Store arrayIndex0
  (arrayType arrayIndex0
  environment0)
  arraydef_0__dsu _1
  _2)))
  (DoWithArrays arrayIndex0
  (arrayType arrayIndex0
  environment0)
  varsfuncdef_0__main
  (Store arrayIndex0
  (arrayType arrayIndex0
  environment0)
  arraydef_0__dsu _1
  _2))
  (λ _3 : withLocalVariablesReturnValue
  (DoWithArrays
  arrayIndex0
  (arrayType
  arrayIndex0
  environment0)
  varsfuncdef_0__main
  (Store arrayIndex0
  (arrayType
  arrayIndex0
  environment0)
  arraydef_0__dsu
  _1
  _2)),
  Done
  (WithLocalVariables
  arrayIndex0
  (arrayType arrayIndex0
  environment0)
  varsfuncdef_0__main)
  withLocalVariablesReturnValue
  (withLocalVariablesReturnValue
  (DoWithArrays
  arrayIndex0
  (arrayType
  arrayIndex0
  environment0)
  varsfuncdef_0__main
  (Store arrayIndex0
  (arrayType
  arrayIndex0
  environment0)
  arraydef_0__dsu _1
  _2)))
  _3)) >>=
λ _ : (),
  Done
  (WithinLoop arrayIndex0
  (arrayType arrayIndex0
  environment0)
  varsfuncdef_0__main)
  withinLoopReturnValue ()
  ())) >>= (fun _ => nextCommands))) = invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0
  state state [a; b] 1 arrayIndex0
  arrayIndexEqualityDecidable0
  (arrayType arrayIndex0 environment0) (λ _0 : arrayIndex0,
  match
  _0 as _1
return
  (list
  (arrayType
  arrayIndex0
  environment0
  _1))
with
| arraydef_0__dsu =>
    take (100 - n) l ++ repeat 255%Z n
| arraydef_0__hasBeenInitialized =>
    [1%Z]
| arraydef_0__result =>
    [0%Z]
end)
  (funcdef_0__main (λ _ : varsfuncdef_0__main, false)
  (λ _ : varsfuncdef_0__main, 0%Z)
  (λ _ : varsfuncdef_0__main, repeat 0%Z 20))
  (eliminateLocalVariables
  (λ _ : varsfuncdef_0__main, false)
  (λ _ : varsfuncdef_0__main, 0%Z)
  (λ _ : varsfuncdef_0__main, repeat 0%Z 20) nextCommands).
Proof.
  induction n as [| n IH] in l, hL, h |- *.
  - unfold loop. rewrite leftIdentity. rewrite (ltac:(easy) : repeat _ 0 = []). rewrite app_nil_r. rewrite (ltac:(lia) : 100 - 0 = 100). rewrite <- hL, firstn_all. reflexivity.
  - rewrite loop_S. rewrite !(ltac:(easy) : (coerceInt (coerceInt (- (1)) 64) 8) = 255%Z). rewrite !leftIdentity. unfold liftToWithinLoop at 1. rewrite <- !bindAssoc. pose proof dropWithinLoop_2' _ _ _ (DoWithArrays arrayIndex0 (arrayType arrayIndex0 environment0) varsfuncdef_0__main (Store arrayIndex0 (arrayType arrayIndex0 environment0) arraydef_0__dsu (100 - Z.of_nat n - 1) 255%Z)) as step. assert (h1 : (λ _1 : withinLoopReturnValue
  (DoWithLocalVariables arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main
  (DoWithArrays arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main
  (Store arrayIndex0
  (arrayType arrayIndex0 environment0)
  arraydef_0__dsu
  (100 - Z.of_nat n - 1)
  255%Z))),
  Done
  (WithinLoop arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main)
  withinLoopReturnValue
  (withinLoopReturnValue
  (DoWithLocalVariables arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main
  (DoWithArrays arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main
  (Store arrayIndex0
  (arrayType arrayIndex0 environment0)
  arraydef_0__dsu
  (100 - Z.of_nat n - 1) 255%Z))))
  _1) =  (λ _1 : unit,
  Done
  (WithinLoop arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main)
  withinLoopReturnValue
  (withinLoopReturnValue
  (DoWithLocalVariables arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main
  (DoWithArrays arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main
  (Store arrayIndex0
  (arrayType arrayIndex0 environment0)
  arraydef_0__dsu
  (100 - Z.of_nat n - 1) 255%Z))))
  _1) ). { apply functional_extensionality_dep. intro x. reflexivity. } rewrite h1 in step. clear h1. rewrite step. clear step. pose proof pushDispatch3 (λ _ : varsfuncdef_0__main, false) (λ _ : varsfuncdef_0__main, 0%Z) (λ _ : varsfuncdef_0__main, repeat 0%Z 20) (Store arrayIndex0 (arrayType arrayIndex0
  environment0)
  arraydef_0__dsu (100 - Z.of_nat n - 1)
  255%Z) as well. rewrite well. clear well. autorewrite with advance_program.
  pose proof IH ltac:(lia) (<[Z.to_nat (100 - Z.of_nat n - 1):=255%Z]> l) ltac:(now rewrite insert_length) as previous. clear IH.

  assert (hh : (λ _0 : arrayIndex0,
  match
  _0 as _1
return
  (list
  (arrayType
  arrayIndex0
  environment0
  _1))
with
| arraydef_0__dsu =>
    <[Z.to_nat
  (100 -
Z.of_nat n -
1):=255%Z]>
  l
| arraydef_0__hasBeenInitialized =>
    [1%Z]
| arraydef_0__result =>
    [0%Z]
end) = (λ _0 : arrayIndex0,
  match
  decide
  (_0 = arraydef_0__dsu)
with
| left _1 =>
  @eq_rect_r arrayIndex0 arraydef_0__dsu
  (fun _2 : arrayIndex0 =>
list (arrayType arrayIndex0 environment0 _2))
  (@insert nat
  (arrayType arrayIndex0 environment0
  arraydef_0__dsu)
  (list
  (arrayType arrayIndex0 environment0
  arraydef_0__dsu))
  (@list_insert
  (arrayType arrayIndex0 environment0
  arraydef_0__dsu))
  (Z.to_nat (Z.sub (Z.sub 100 (Z.of_nat n)) 1))
  255%Z
  l)
  _0
  _1
| right _ =>
    match
  _0 as _2
return
  (list
  (arrayType
  arrayIndex0
  environment0
  _2))
with
| arraydef_0__dsu =>
    l
| arraydef_0__hasBeenInitialized =>
    [1%Z]
| arraydef_0__result =>
    [0%Z]
end
end)). { apply functional_extensionality_dep. intro x. destruct x; simpl; easy. } rewrite <- hh. clear hh. rewrite !(ltac:(cbv; reflexivity) : (coerceInt (coerceInt (Z.opp 1) 64) 8) = 255%Z) in previous. rewrite previous. rewrite insert_take_drop; [| lia]. rewrite (ltac:(lia) : Z.to_nat (100 - Z.of_nat n - 1) = 100 - S n). rewrite (ltac:(intros; listsEqual) : forall a b c, a ++ b :: c = (a ++ [b]) ++ c). pose proof take_app_length (take (100 - S n) l ++ [255%Z]) (drop (S (100 - S n)) l) as step. rewrite app_length in step. rewrite (ltac:(easy) : length [255%Z] = 1) in step. rewrite take_length in step. rewrite (ltac:(lia) : (100 - S n) `min` length l = 100 - S n) in step. rewrite (ltac:(lia) : 100 - S n + 1 = 100 - n) in step. rewrite step. clear step. rewrite (ltac:(intros; listsEqual) : forall a b c, (a ++ [b]) ++ c = a ++ (b :: c)). rewrite (ltac:(easy) : _ :: repeat _ _ = repeat 255%Z (S n)). case_decide as hIf; [reflexivity |]. pose proof (ltac:(lia) : @length (arrayType arrayIndex0 environment0 arraydef_0__dsu) l <= 100 - S n) as step. simpl in step. rewrite hL in step. lia.
Qed.

Lemma firstInteraction (a b : Z) : invokeContract (repeat 1%Z 20) (repeat 0%Z 20) 0%Z state state [a; b] 1 = Some ([a; b], stateAfterInteractions (fun x => match x with | arraydef_0__result => [0%Z] | arraydef_0__hasBeenInitialized => [1%Z] | arraydef_0__dsu => convertToArray (unite (repeat (Ancestor Unit) 100) (Z.to_nat a) (Z.to_nat b)) end) (dsuScore (unite (repeat (Ancestor Unit) 100) (Z.to_nat a) (Z.to_nat b)))).
Proof.
  unfold invokeContract. rewrite (ltac:(easy) : state (repeat 0%Z 20) = BlockchainContract _ _ _ _ _ _). unfold funcdef_0__main at 2. rewrite !leftIdentity. unfold retrieve at 1. rewrite <- !bindAssoc. pose proof pushDispatch2 (λ _ : varsfuncdef_0__main, false) (λ _ : varsfuncdef_0__main, 0%Z) (λ _ : varsfuncdef_0__main, repeat 0%Z 20) (Retrieve arrayIndex0 (arrayType arrayIndex0 environment0) arraydef_0__hasBeenInitialized 0) as step. autorewrite with combined_unfold in step. rewrite step. clear step. autorewrite with advance_program. case_decide as h; simpl in h; [| lia]. rewrite !leftIdentity. case_bool_decide as h1; cbv in h1; [| lia]. unfold store. pose proof pushDispatch2 (λ _ : varsfuncdef_0__main, false) (λ _ : varsfuncdef_0__main, 0%Z) (λ _ : varsfuncdef_0__main, repeat 0%Z 20) (Store arrayIndex0 (arrayType arrayIndex0 environment0) arraydef_0__hasBeenInitialized 0 (coerceInt 1 8)) as step. autorewrite with combined_unfold in *. rewrite <- !bindAssoc, step. clear step. autorewrite with advance_program. assert (hsimp : (λ _0 : arrayIndex0,
  match
  decide
  (_0 =
arraydef_0__hasBeenInitialized)
with
| left _1 =>
    eq_rect_r
  (λ _2 : arrayIndex0,
  list
  (arrayType
  arrayIndex0
  environment0
  _2))
  (@insert nat
  (arrayType
  arrayIndex0
  environment0
  arraydef_0__hasBeenInitialized)
  (list
  (arrayType
  arrayIndex0
  environment0
  arraydef_0__hasBeenInitialized))
  (@list_insert
  (arrayType
  arrayIndex0
  environment0
  arraydef_0__hasBeenInitialized))
  (Z.to_nat Z0)
  (coerceInt
  (Zpos xH)
  (Zpos
  (xO
  (xO
  (xO
  xH))))) (arrays
  arrayIndex0
  environment0
  arraydef_0__hasBeenInitialized))
  _1
| right _ =>
    arrays
  arrayIndex0
  environment0
  _0
end) = fun (x : arrayIndex0) => match x with | arraydef_0__hasBeenInitialized => [1%Z] | arraydef_0__dsu => repeat 0%Z 100 | arraydef_0__result => [0%Z] end). { apply functional_extensionality_dep. intro x. destruct x; cbv; reflexivity. }
  case_decide as hw; simpl in hw; [| lia]. rewrite hsimp. clear hsimp. pose proof (fun x => initializeArray a b 100 x ltac:(lia) (repeat 0%Z 100) ltac:(easy)) as step. rewrite step. clear step. rewrite (ltac:(lia) : 100 - 100 = 0). rewrite (ltac:(easy) : take 0 _ = []). rewrite app_nil_l. rewrite !leftIdentity. unfold readByte. pose proof pushDispatch2 (λ _ : varsfuncdef_0__main, false) (λ _ : varsfuncdef_0__main, 0%Z) (λ _ : varsfuncdef_0__main, repeat 0%Z 20) (DoBasicEffect arrayIndex0 (arrayType arrayIndex0 environment0)
  (ReadByte 0)) as step. autorewrite with combined_unfold in step. rewrite step. clear step. autorewrite with advance_program.  case_decide as h2; [| simpl in h2; lia]. pose proof pushDispatch2 (λ _ : varsfuncdef_0__main, false) (λ _ : varsfuncdef_0__main, 0%Z) (λ _ : varsfuncdef_0__main, repeat 0%Z 20) (DoBasicEffect arrayIndex0 (arrayType arrayIndex0 environment0) (ReadByte 1)) as step. autorewrite with combined_unfold in step. rewrite <- !bindAssoc, step. clear step. autorewrite with advance_program. rewrite !leftIdentity. rewrite (ltac:(easy) : (nth (Z.to_nat 0) [a; b] 0%Z) = a), (ltac:(easy) : (nth (Z.to_nat 1) [a; b] 0%Z) = b). rewrite (ltac:(apply functional_extensionality_dep; intro x; destruct x; easy) : (update (update (λ _ : varsfuncdef_0__unite, 0%Z) vardef_0__unite_u a) vardef_0__unite_v b) = fun x => match x with | vardef_0__unite_u => a | vardef_0__unite_v => b | _ => 0%Z end).
Admitted.

Lemma interactEqualsModelScore (x : list (Z * Z)) : interact state x = modelScore x.
Proof.
Admitted.
