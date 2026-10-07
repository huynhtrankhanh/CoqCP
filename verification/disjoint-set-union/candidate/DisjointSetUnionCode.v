From CoqCP Require Import Options Imperative DisjointSetUnion ListsEqual ExistsInRange SwapUpdate.

From CoqCP Require Export UnionFindModel.
Require Export Trusted.Spec.

From Generated Require Import DisjointSetUnion.
From stdpp Require Import numbers list.
Require Import Stdlib.Logic.FunctionalExtensionality.
From Stdlib Require Import Wellfounded.

Lemma initializeArray n nextCommands (h : n <= 100) (l : list Z) (hL : length l = 100) : runArrays arrayIndex2 arrayIndexEqualityDecidable2 (arrayType arrayIndex2 environment2) (λ _0 : arrayIndex2,
  match
  _0 as _1
return
  (list
  (arrayType
  arrayIndex2
  environment2
  _1))
with
| arraydef_0_DSU_dsu => l
| arraydef_0_DSU_hasBeenInitialized =>
    [1%Z]
| arraydef_0_DSU_result =>
    [0%Z]
end) (eliminateLocalVariables
  (λ _ : varsfuncdef_0_DSU_initialize, false)
  (λ _ : varsfuncdef_0_DSU_initialize, 0%Z)

  (loop n
  (λ _0 : nat,
  dropWithinLoop
  (liftToWithinLoop
  (Done
  (WithLocalVariables arrayIndex2
  (arrayType arrayIndex2
  environment2)
  varsfuncdef_0_DSU_initialize)
  withLocalVariablesReturnValue Z
  (100%Z - Z.of_nat _0 - 1)%Z >>=
λ _1 : Z,
  Done
  (WithLocalVariables arrayIndex2
  (arrayType arrayIndex2
  environment2)
  varsfuncdef_0_DSU_initialize)
  withLocalVariablesReturnValue Z
  (coerceInt (coerceInt (- (1)) 64)
  8) >>=
λ _2 : Z,
  Dispatch
  (WithLocalVariables arrayIndex2
  (arrayType arrayIndex2
  environment2)
  varsfuncdef_0_DSU_initialize)
  withLocalVariablesReturnValue
  (withLocalVariablesReturnValue
  (DoWithArrays arrayIndex2
  (arrayType arrayIndex2
  environment2)
  varsfuncdef_0_DSU_initialize
  (Store arrayIndex2
  (arrayType arrayIndex2
  environment2)
  arraydef_0_DSU_dsu _1
  _2)))
  (DoWithArrays arrayIndex2
  (arrayType arrayIndex2
  environment2)
  varsfuncdef_0_DSU_initialize
  (Store arrayIndex2
  (arrayType arrayIndex2
  environment2)
  arraydef_0_DSU_dsu _1
  _2))
  (λ _3 : withLocalVariablesReturnValue
  (DoWithArrays
  arrayIndex2
  (arrayType
  arrayIndex2
  environment2)
  varsfuncdef_0_DSU_initialize
  (Store arrayIndex2
  (arrayType
  arrayIndex2
  environment2)
  arraydef_0_DSU_dsu
  _1
  _2)),
  Done
  (WithLocalVariables
  arrayIndex2
  (arrayType arrayIndex2
  environment2)
  varsfuncdef_0_DSU_initialize)
  withLocalVariablesReturnValue
  (withLocalVariablesReturnValue
  (DoWithArrays
  arrayIndex2
  (arrayType
  arrayIndex2
  environment2)
  varsfuncdef_0_DSU_initialize
  (Store arrayIndex2
  (arrayType
  arrayIndex2
  environment2)
  arraydef_0_DSU_dsu _1
  _2)))
  _3)) >>=
λ _ : (),
  Done
  (WithinLoop arrayIndex2
  (arrayType arrayIndex2
  environment2)
  varsfuncdef_0_DSU_initialize)
  withinLoopReturnValue ()
  ())) >>= (fun _ => nextCommands))) = runArrays arrayIndex2 arrayIndexEqualityDecidable2 (arrayType arrayIndex2 environment2) (λ _0 : arrayIndex2,
  match
  _0 as _1
return
  (list
  (arrayType
  arrayIndex2
  environment2
  _1))
with
| arraydef_0_DSU_dsu =>
    take (100 - n) l ++ repeat 255%Z n
| arraydef_0_DSU_hasBeenInitialized =>
    [1%Z]
| arraydef_0_DSU_result =>
    [0%Z]
end) (eliminateLocalVariables
  (λ _ : varsfuncdef_0_DSU_initialize, false)
  (λ _ : varsfuncdef_0_DSU_initialize, 0%Z)
   nextCommands).
Proof.
  induction n as [| n IH] in l, hL, h |- *.
  - unfold loop. rewrite leftIdentity. rewrite (ltac:(easy) : repeat _ 0 = []). rewrite app_nil_r. rewrite (ltac:(lia) : 100 - 0 = 100). rewrite <- hL, firstn_all. reflexivity.
  - rewrite loop_S. rewrite !(ltac:(easy) : (coerceInt (coerceInt (- (1)) 64) 8) = 255%Z). rewrite !leftIdentity. unfold liftToWithinLoop at 1. rewrite <- !bindAssoc. pose proof dropWithinLoop_2' _ _ _ (DoWithArrays arrayIndex2 (arrayType arrayIndex2 environment2) varsfuncdef_0_DSU_initialize (Store arrayIndex2 (arrayType arrayIndex2 environment2) arraydef_0_DSU_dsu (100 - Z.of_nat n - 1) 255%Z)) as step. assert (h1 : (λ _1 : withinLoopReturnValue
  (DoWithLocalVariables arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_initialize
  (DoWithArrays arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_initialize
  (Store arrayIndex2
  (arrayType arrayIndex2 environment2)
  arraydef_0_DSU_dsu
  (100 - Z.of_nat n - 1)
  255%Z))),
  Done
  (WithinLoop arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_initialize)
  withinLoopReturnValue
  (withinLoopReturnValue
  (DoWithLocalVariables arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_initialize
  (DoWithArrays arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_initialize
  (Store arrayIndex2
  (arrayType arrayIndex2 environment2)
  arraydef_0_DSU_dsu
  (100 - Z.of_nat n - 1) 255%Z))))
  _1) =  (λ _1 : unit,
  Done
  (WithinLoop arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_initialize)
  withinLoopReturnValue
  (withinLoopReturnValue
  (DoWithLocalVariables arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_initialize
  (DoWithArrays arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_initialize
  (Store arrayIndex2
  (arrayType arrayIndex2 environment2)
  arraydef_0_DSU_dsu
  (100 - Z.of_nat n - 1) 255%Z))))
  _1) ). { apply functional_extensionality_dep. intro x. reflexivity. } rewrite h1 in step. clear h1. rewrite step. clear step. pose proof pushDispatch3 (λ _ : varsfuncdef_0_DSU_initialize, false) (λ _ : varsfuncdef_0_DSU_initialize, 0%Z)  (Store arrayIndex2 (arrayType arrayIndex2
  environment2)
  arraydef_0_DSU_dsu (100 - Z.of_nat n - 1)
  255%Z) as well. rewrite well. clear well. autorewrite with advance_program.
  pose proof IH ltac:(lia) (<[Z.to_nat (100 - Z.of_nat n - 1):=255%Z]> l) ltac:(now rewrite length_insert) as previous. clear IH.

  assert (hh : (λ _0 : arrayIndex2,
  match
  _0 as _1
return
  (list
  (arrayType
  arrayIndex2
  environment2
  _1))
with
| arraydef_0_DSU_dsu =>
    <[Z.to_nat
  (100 -
Z.of_nat n -
1):=255%Z]>
  l
| arraydef_0_DSU_hasBeenInitialized =>
    [1%Z]
| arraydef_0_DSU_result =>
    [0%Z]
end) = (λ _0 : arrayIndex2,
  match
  decide
  (_0 = arraydef_0_DSU_dsu)
with
| left _1 =>
  @eq_rect_r arrayIndex2 arraydef_0_DSU_dsu
  (fun _2 : arrayIndex2 =>
list (arrayType arrayIndex2 environment2 _2))
  (@insert nat
  (arrayType arrayIndex2 environment2
  arraydef_0_DSU_dsu)
  (list
  (arrayType arrayIndex2 environment2
  arraydef_0_DSU_dsu))
  (@list_insert
  (arrayType arrayIndex2 environment2
  arraydef_0_DSU_dsu))
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
  arrayIndex2
  environment2
  _2))
with
| arraydef_0_DSU_dsu =>
    l
| arraydef_0_DSU_hasBeenInitialized =>
    [1%Z]
| arraydef_0_DSU_result =>
    [0%Z]
end
end)). { apply functional_extensionality_dep. intro x. destruct x; simpl; easy. } rewrite <- hh. clear hh. rewrite !(ltac:(cbv; reflexivity) : (coerceInt (coerceInt (Z.opp 1) 64) 8) = 255%Z) in previous. rewrite previous. rewrite insert_take_drop; [| lia]. rewrite (ltac:(lia) : Z.to_nat (100 - Z.of_nat n - 1) = 100 - S n). rewrite (ltac:(intros; listsEqual) : forall a b c, a ++ b :: c = (a ++ [b]) ++ c). pose proof take_app_length (take (100 - S n) l ++ [255%Z]) (drop (S (100 - S n)) l) as step. rewrite length_app in step. rewrite (ltac:(easy) : length [255%Z] = 1) in step. rewrite length_take in step. rewrite (ltac:(lia) : (100 - S n) `min` length l = 100 - S n) in step. rewrite (ltac:(lia) : 100 - S n + 1 = 100 - n) in step. rewrite step. clear step. rewrite (ltac:(intros; listsEqual) : forall a b c, (a ++ [b]) ++ c = a ++ (b :: c)). rewrite (ltac:(easy) : _ :: repeat _ _ = repeat 255%Z (S n)). case_decide as hIf; [reflexivity |]. pose proof (ltac:(lia) : @length (arrayType arrayIndex2 environment2 arraydef_0_DSU_dsu) l <= 100 - S n) as step. simpl in step. rewrite hL in step. lia.
Qed.

Lemma runAncestor1 (dsu : list Slot) (hL : length dsu = 100) (hM : Z.to_nat (dsuLeafCount dsu) = length dsu) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (whatever2 a : Z) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) continuation continuation2 whatever n (hN : n <= 100) : runArrays arrayIndex2 arrayIndexEqualityDecidable2 (arrayType arrayIndex2 environment2) (λ _0 : arrayIndex2,
  match
  _0 as _1
return
  (list
  (arrayType
  arrayIndex2
  environment2
  _1))
with
| arraydef_0_DSU_dsu =>
    convertToArray dsu
| arraydef_0_DSU_hasBeenInitialized =>
    [1%Z]
| arraydef_0_DSU_result =>
    [whatever]
end) (eliminateLocalVariables
  (λ _ : varsfuncdef_0_DSU_ancestor, false) (λ _0 : varsfuncdef_0_DSU_ancestor,
  match _0
with
| vardef_0_DSU_ancestor_vertex =>
    whatever2
| vardef_0_DSU_ancestor_work =>
    a
end)

  (loop n
  (λ _ : nat,
  dropWithinLoop
  (liftToWithinLoop
  (numberLocalGet arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor
  vardef_0_DSU_ancestor_work >>=
λ _0 : withLocalVariablesReturnValue
  (NumberLocalGet arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor
  vardef_0_DSU_ancestor_work),
  Done
  (WithLocalVariables arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor)
  withLocalVariablesReturnValue Z
  (coerceInt _0 64) >>=
λ _1 : Z,
  retrieve arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor arraydef_0_DSU_dsu
  _1 >>=
λ _2 : arrayType arrayIndex2 environment2
  arraydef_0_DSU_dsu,
  Done
  (WithLocalVariables arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor)
  withLocalVariablesReturnValue Z
  (coerceInt 0 8) >>=
λ _3 : Z,
  Done
  (WithLocalVariables arrayIndex2
  (arrayType arrayIndex2
  environment2)
  varsfuncdef_0_DSU_ancestor)
  withLocalVariablesReturnValue bool
  (bool_decide
  (toSigned _2 8 < toSigned _3 8)%Z)) >>=
λ _0 : bool,
  (if _0
then
 break arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor >>=
λ _ : (),
  Done
  (WithinLoop arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor)
  withinLoopReturnValue ()
  ()
else
 Done
  (WithinLoop arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor)
  withinLoopReturnValue ()
  ()) >>=
λ _ : (),
  liftToWithinLoop
  (numberLocalGet arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor
  vardef_0_DSU_ancestor_work >>=
λ _1 : withLocalVariablesReturnValue
  (NumberLocalGet arrayIndex2
  (arrayType arrayIndex2
  environment2)
  varsfuncdef_0_DSU_ancestor
  vardef_0_DSU_ancestor_work),
  Done
  (WithLocalVariables arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor)
  withLocalVariablesReturnValue Z
  (coerceInt _1 64) >>=
λ _2 : Z,
  retrieve arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor
  arraydef_0_DSU_dsu _2 >>=
λ _3 : arrayType arrayIndex2
  environment2 arraydef_0_DSU_dsu,
  numberLocalSet arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor
  vardef_0_DSU_ancestor_work
  _3) >>=
λ _ : (),
  Done
  (WithinLoop arrayIndex2
  (arrayType arrayIndex2 environment2)
  varsfuncdef_0_DSU_ancestor)
  withinLoopReturnValue ()
  ())) >>= continuation) >>= continuation2) = runArrays arrayIndex2 arrayIndexEqualityDecidable2 (arrayType arrayIndex2 environment2) (λ _0 : arrayIndex2,
  match
  _0 as _1
return
  (list
  (arrayType
  arrayIndex2
  environment2
  _1))
with
| arraydef_0_DSU_dsu =>
    convertToArray dsu
| arraydef_0_DSU_hasBeenInitialized =>
    [1%Z]
| arraydef_0_DSU_result =>
    [whatever]
end) (eliminateLocalVariables
  (λ _ : varsfuncdef_0_DSU_ancestor, false) (λ _0 : varsfuncdef_0_DSU_ancestor,
  match _0
with
| vardef_0_DSU_ancestor_vertex =>
    whatever2
| vardef_0_DSU_ancestor_work =>
    Z.of_nat (ancestor dsu n (Z.to_nat a))
end)
   (continuation tt) >>= continuation2).
Proof.
  revert a hLt1 hLe1. induction n as [| n IH]; intros a hLt1 hLe1.
  - rewrite (ltac:(simpl; reflexivity) : loop 0 _ = _), (ltac:(simpl; reflexivity) : ancestor dsu 0 _ = _), Z2Nat.id, leftIdentity; [reflexivity | lia].
  - rewrite (ltac:(simpl; reflexivity) : loop (S _) _ = _). unfold numberLocalGet at 1. rewrite <- !bindAssoc, liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop, <- !bindAssoc. pose proof @pushNumberGet2 arrayIndex2 (arrayType arrayIndex2 environment2) varsfuncdef_0_DSU_ancestor _ (λ _ : varsfuncdef_0_DSU_ancestor, false) (λ _1 : varsfuncdef_0_DSU_ancestor,
  match
  _1
with
| vardef_0_DSU_ancestor_vertex =>
    whatever2
| vardef_0_DSU_ancestor_work =>
    a
end)  as step. rewrite step. clear step.
  assert (step : coerceInt a 64 = a).
  { revert hLe1 hLt1. clear. intros h1 h2. unfold coerceInt. rewrite Z.mod_small. { reflexivity. } lia. }
  rewrite step, !leftIdentity, liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop. unfold retrieve at 1.
  pose proof pushDispatch2 (λ _ : varsfuncdef_0_DSU_ancestor, false)
  (λ _0 : varsfuncdef_0_DSU_ancestor,
     match _0 with
     | vardef_0_DSU_ancestor_vertex => whatever2
     | vardef_0_DSU_ancestor_work => a
     end)  (Retrieve arrayIndex2 (arrayType arrayIndex2 environment2)
     arraydef_0_DSU_dsu a) as step2. rewrite <- !bindAssoc, step2. clear step2.
  rewrite (ltac:(simpl; reflexivity) : forall effect continuation f, bind (Dispatch _ _ _ effect continuation) f = _). autorewrite with advance_program.
  case_decide as hs; [| rewrite lengthConvert in hs; lia].
  rewrite !leftIdentity, (ltac:(easy) : toSigned (coerceInt 0%Z 8) 8 = 0%Z).
  rewrite (ltac:(easy) : @nth_lt (arrayType arrayIndex2 environment2 arraydef_0_DSU_dsu) (convertToArray dsu) (Z.to_nat a) hs = @nth_lt Z (convertToArray dsu) (Z.to_nat a) hs), (nth_lt_default (convertToArray dsu) (Z.to_nat a) hs 0%Z), nthConvert; [| lia].
  remember (nth (Z.to_nat a) dsu (Ancestor Unit)) as g eqn:hg. symmetry in hg.
  destruct g as [g | g]; clear hs.
  + case_bool_decide as hs. { unfold toSigned in hs. pose proof h1 (Z.to_nat a) g hg. case_decide; [| lia]. lia. } rewrite (ltac:(easy) : liftToWithinLoop
  (Done
     (WithLocalVariables arrayIndex2 (arrayType arrayIndex2 environment2)
        varsfuncdef_0_DSU_ancestor) withLocalVariablesReturnValue bool false) = Done _ _ bool false), !leftIdentity.
    rewrite liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite <- !bindAssoc, pushNumberGet2, !step, !leftIdentity, liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop. unfold retrieve at 1. rewrite <- !bindAssoc, pushDispatch2. rewrite (ltac:(simpl; reflexivity) : forall effect continuation f, bind (Dispatch _ _ _ effect continuation) f = _). autorewrite with advance_program. clear hs. case_decide as hs; [| rewrite lengthConvert in hs; lia]. rewrite liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop, <- !bindAssoc. unfold numberLocalSet at 1. pose proof (@pushNumberSet2 arrayIndex2 (arrayType arrayIndex2 environment2) varsfuncdef_0_DSU_ancestor _ (λ _ : varsfuncdef_0_DSU_ancestor, false)
    (λ _0 : varsfuncdef_0_DSU_ancestor,
       match _0 with
       | vardef_0_DSU_ancestor_vertex => whatever2
       | vardef_0_DSU_ancestor_work => a
       end)  vardef_0_DSU_ancestor_work) (nth_lt (convertToArray dsu) (Z.to_nat a) hs) as step3. rewrite step3. clear step3.
    rewrite (ltac:(cbv; reflexivity) : dropWithinLoop
    (Done
       (WithinLoop arrayIndex2 (arrayType arrayIndex2 environment2)
          varsfuncdef_0_DSU_ancestor) withinLoopReturnValue () ())  = _), !leftIdentity.
    assert (step3 : nth_lt (convertToArray dsu) (Z.to_nat a) hs = Z.of_nat g).
    { rewrite (nth_lt_default _ _ _ 0%Z), nthConvert; [| lia]. rewrite hg. reflexivity. } rewrite step3. clear step3.
    assert (step3 : (update
    (λ _0 : varsfuncdef_0_DSU_ancestor,
       match _0 with
       | vardef_0_DSU_ancestor_vertex => whatever2
       | vardef_0_DSU_ancestor_work => a
       end) vardef_0_DSU_ancestor_work (Z.of_nat g)) = fun x => match x with | vardef_0_DSU_ancestor_vertex => whatever2 | vardef_0_DSU_ancestor_work => Z.of_nat g end). { unfold update. apply functional_extensionality_dep. intro aa. destruct aa; easy. } rewrite step3. clear step3.
    pose proof IH ltac:(lia) (Z.of_nat g) ltac:(pose proof h1 (Z.to_nat a) _ hg as ls; lia) ltac:(lia) as step3. rewrite !liftToWithinLoopBind, <- !bindAssoc in step3. rewrite step3, Nat2Z.id.
    clear step3. assert (step3 : ancestor dsu (S n) (Z.to_nat a) = ancestor dsu n g). { simpl. rewrite hg. reflexivity. } rewrite step3. reflexivity.
  + case_bool_decide as hs.
    * rewrite liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop. rewrite <- !bindAssoc, leftIdentity, <- !bindAssoc, dropWithinLoop_break, !leftIdentity.
      assert (step3 : ancestor dsu (S n) (Z.to_nat a) = Z.to_nat a).
      { simpl. rewrite hg. reflexivity. } rewrite step3, Z2Nat.id; [| lia]. reflexivity.
    * unfold toSigned in hs. case_decide as hss. { simpl in hss. rewrite (ltac:(easy) : (2 ^ (8 - 1) = 128)%Z) in hss. pose proof nthLowerBoundConvertAuxStep dsu ltac:(lia) ltac:(lia) (Z.to_nat a) ltac:(lia) g hg. lia. } rewrite (ltac:(easy) : (2 ^ 8 = 256)%Z) in hs. pose proof oneLeqLeafCount g. lia.
Qed.
