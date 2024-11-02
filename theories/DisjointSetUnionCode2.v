From CoqCP Require Import Options Imperative DisjointSetUnion ListsEqual ExistsInRange SwapUpdate DisjointSetUnionCode.
From Generated Require Import DisjointSetUnion.
From stdpp Require Import numbers list.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Wellfounded.
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma runCompressLoop (dsu : list Slot) (hL : length dsu = 100) (hL1 : Z.to_nat (dsuLeafCount dsu) = length dsu) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (a : Z) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) communication (n : nat) (hN : n <= 100) continuation : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state state communication 1 arrayIndex0 arrayIndexEqualityDecidable0
  (arrayType arrayIndex0 environment0)
  (λ _0 : arrayIndex0,
     match
       _0 as _1 return (list (arrayType arrayIndex0 environment0 _1))
     with
     | arraydef_0__dsu => convertToArray dsu
     | arraydef_0__hasBeenInitialized => [1%Z]
     | arraydef_0__result =>
         [Z.of_nat (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]
     end) (funcdef_0__main xpred0 (fun=> 0%Z) (fun=> repeat 0%Z 20))
  (eliminateLocalVariables xpred0
     (λ _0 : varsfuncdef_0__ancestor,
        match _0 with
        | vardef_0__ancestor_vertex | _ => a
        end) (fun=> repeat 0%Z 20)
     (loop n
        (fun=> dropWithinLoop
                 (liftToWithinLoop
                    (numberLocalGet arrayIndex0
                       (arrayType arrayIndex0 environment0)
                       varsfuncdef_0__ancestor vardef_0__ancestor_work >>=
                     λ _0 : withLocalVariablesReturnValue
                              (NumberLocalGet arrayIndex0
                                 (arrayType arrayIndex0 environment0)
                                 varsfuncdef_0__ancestor
                                 vardef_0__ancestor_work),
                       Done
                         (WithLocalVariables arrayIndex0
                            (arrayType arrayIndex0 environment0)
                            varsfuncdef_0__ancestor)
                         withLocalVariablesReturnValue Z 
                         (coerceInt _0 64) >>=
                       λ _1 : Z,
                         retrieve arrayIndex0
                           (arrayType arrayIndex0 environment0)
                           varsfuncdef_0__ancestor arraydef_0__dsu _1 >>=
                         λ _2 : arrayType arrayIndex0 environment0
                                  arraydef_0__dsu,
                           Done
                             (WithLocalVariables arrayIndex0
                                (arrayType arrayIndex0 environment0)
                                varsfuncdef_0__ancestor)
                             withLocalVariablesReturnValue Z 
                             (coerceInt 0 8) >>=
                           λ _3 : Z,
                             Done
                               (WithLocalVariables arrayIndex0
                                  (arrayType arrayIndex0 environment0)
                                  varsfuncdef_0__ancestor)
                               withLocalVariablesReturnValue bool
                               (bool_decide (toSigned _2 8 < toSigned _3 8)%Z)) >>=
                  λ _0 : bool,
                    (if _0
                     then
                      break arrayIndex0 (arrayType arrayIndex0 environment0)
                        varsfuncdef_0__ancestor >>=
                      (fun=> Done
                               (WithinLoop arrayIndex0
                                  (arrayType arrayIndex0 environment0)
                                  varsfuncdef_0__ancestor)
                               withinLoopReturnValue () ())
                     else
                      Done
                        (WithinLoop arrayIndex0
                           (arrayType arrayIndex0 environment0)
                           varsfuncdef_0__ancestor) withinLoopReturnValue ()
                        ()) >>=
                    (fun=> liftToWithinLoop
                             (numberLocalGet arrayIndex0
                                (arrayType arrayIndex0 environment0)
                                varsfuncdef_0__ancestor
                                vardef_0__ancestor_work >>=
                              λ _1 : withLocalVariablesReturnValue
                                       (NumberLocalGet arrayIndex0
                                          (arrayType arrayIndex0 environment0)
                                          varsfuncdef_0__ancestor
                                          vardef_0__ancestor_work),
                                Done
                                  (WithLocalVariables arrayIndex0
                                     (arrayType arrayIndex0 environment0)
                                     varsfuncdef_0__ancestor)
                                  withLocalVariablesReturnValue Z
                                  (coerceInt _1 64) >>=
                                λ _2 : Z,
                                  retrieve arrayIndex0
                                    (arrayType arrayIndex0 environment0)
                                    varsfuncdef_0__ancestor
                                    arraydef_0__result 0 >>=
                                  [eta store arrayIndex0
                                         (arrayType arrayIndex0 environment0)
                                         varsfuncdef_0__ancestor
                                         arraydef_0__dsu _2]) >>=
                           (fun=> liftToWithinLoop
                                    (numberLocalGet arrayIndex0
                                       (arrayType arrayIndex0 environment0)
                                       varsfuncdef_0__ancestor
                                       vardef_0__ancestor_work >>=
                                     λ _1 : withLocalVariablesReturnValue
                                              (NumberLocalGet arrayIndex0
                                                 (arrayType arrayIndex0
                                                 environment0)
                                                 varsfuncdef_0__ancestor
                                                 vardef_0__ancestor_work),
                                       Done
                                         (WithLocalVariables arrayIndex0
                                            (arrayType arrayIndex0
                                               environment0)
                                            varsfuncdef_0__ancestor)
                                         withLocalVariablesReturnValue Z
                                         (coerceInt _1 64) >>=
                                       λ _2 : Z,
                                         retrieve arrayIndex0
                                           (arrayType arrayIndex0
                                              environment0)
                                           varsfuncdef_0__ancestor
                                           arraydef_0__dsu _2 >>=
                                         [eta numberLocalSet arrayIndex0
                                                (arrayType arrayIndex0
                                                 environment0)
                                                varsfuncdef_0__ancestor
                                                vardef_0__ancestor_work]) >>=
                                  (fun=> Done
                                           (WithinLoop arrayIndex0
                                              (arrayType arrayIndex0
                                                 environment0)
                                              varsfuncdef_0__ancestor)
                                           withinLoopReturnValue () ()))))) >>=
      (fun=> Done
               (WithLocalVariables arrayIndex0
                  (arrayType arrayIndex0 environment0)
                  varsfuncdef_0__ancestor) withLocalVariablesReturnValue ()
               ())) >>= continuation) =
invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state state communication 1 arrayIndex0 arrayIndexEqualityDecidable0
  (arrayType arrayIndex0 environment0)
  (λ _0 : arrayIndex0,
     match
       _0 as _1 return (list (arrayType arrayIndex0 environment0 _1))
     with
     | arraydef_0__dsu =>
         convertToArray
           (pathCompress dsu n (Z.to_nat a)
              (ancestor dsu (length dsu) (Z.to_nat a)))
     | arraydef_0__hasBeenInitialized => [1%Z]
     | arraydef_0__result =>
         [Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))]
     end) (funcdef_0__main xpred0 (fun=> 0%Z) (fun=> repeat 0%Z 20))
  (continuation ()).
Proof.
  move : a hLe1 hLt1 dsu h1 hL hL1 h2. elim : n hN.
  { move => hN a hLe1 hLt1. rewrite (ltac:(simpl; reflexivity) : loop 0 _ = _) leftIdentity (ltac:(simpl; reflexivity) : eliminateLocalVariables xpred0
     (λ _0 : varsfuncdef_0__ancestor,
        match _0 with
        | vardef_0__ancestor_vertex | _ => a
        end) (fun=> repeat 0%Z 20)
     (Done
        (WithLocalVariables arrayIndex0 (arrayType arrayIndex0 environment0)
           varsfuncdef_0__ancestor) withLocalVariablesReturnValue () ()) = _) leftIdentity.
    move => dsu h1 hL hL1 h2.
    rewrite (ltac:(intros; simpl; reflexivity) : forall a b c, pathCompress a 0 b c = _) hL. easy. }
  move => n IH hN a hLe1 hLt1 dsu h1 hL hL1 h2. rewrite loop_S -!bindAssoc dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 !leftIdentity.
  have ra : coerceInt a 64 = a.
  { unfold coerceInt. rewrite Z.mod_small; lia. }
  rewrite ra. unfold retrieve at 1. rewrite pushDispatch2 (ltac:(intros; simpl; reflexivity) : forall effect continuation f, Dispatch _ _ _ effect continuation >>= f = _) unfoldInvoke_S_Retrieve. case_decide as xxx; [| rewrite lengthConvert in xxx; lia].
  rewrite (nth_lt_default _ _ _ 0%Z) nthConvert; [lia |]. rewrite (ltac:(easy) : (toSigned (coerceInt 0 8) 8 = 0)%Z).
  have usk : toSigned
                match nth (Z.to_nat a) dsu (Ancestor Unit) with
                | ReferTo _0 => Z.of_nat _0
                | Ancestor _0 => 256 - Z.of_nat (leafCount _0)
                end 8 = match nth (Z.to_nat a) dsu (Ancestor Unit) with | ReferTo x => Z.of_nat x | Ancestor x => -Z.of_nat (leafCount x) end.
  { remember (nth (Z.to_nat a) dsu _) as hh eqn:hhh. symmetry in hhh. unfold toSigned. destruct hh as [hh | hh].
    - pose proof h1 (Z.to_nat a) _ hhh. case_decide; lia.
    - pose proof oneLeqLeafCount hh. case_decide; [| lia]. pose proof nthLowerBoundConvertAuxStep dsu ltac:(lia) ltac:(lia) (Z.to_nat a) ltac:(lia) _ hhh. lia. }
  rewrite usk. clear usk. remember (nth (Z.to_nat a) dsu (Ancestor Unit)) as hh eqn:hhh. symmetry in hhh. case_bool_decide as hs.
  - rewrite dropWithinLoop_4 !leftIdentity.
    destruct hh as [hh | hh]. { lia. }
    have red : pathCompress dsu (S n) (Z.to_nat a)
              (ancestor dsu (length dsu) (Z.to_nat a)) = dsu.
    { simpl. rewrite hhh. reflexivity. }
    rewrite red hL. reflexivity.
  - rewrite !leftIdentity dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 !leftIdentity. unfold retrieve at 1. rewrite pushDispatch2 (ltac:(intros; simpl; reflexivity) : forall effect continuation f, Dispatch _ _ _ effect continuation >>= f = _)  unfoldInvoke_S_Retrieve. case_decide as ppp; [| simpl in ppp; lia]. rewrite pushDispatch2 (ltac:(intros; simpl; reflexivity) : forall effect continuation f, Dispatch _ _ _ effect continuation >>= f = _) unfoldInvoke_S_Store (ltac:(simpl; reflexivity) : nth_lt [_] (Z.to_nat 0) _ = _) ra.
  have gda : (λ _0 : arrayIndex0,
       match decide (_0 = arraydef_0__dsu) with
       | left _1 =>
           eq_rect_r
             (λ _2 : arrayIndex0,
                list (arrayType arrayIndex0 environment0 _2))
             (@insert nat
                (arrayType arrayIndex0 environment0 arraydef_0__dsu)
                (list (arrayType arrayIndex0 environment0 arraydef_0__dsu))
                (@list_insert
                   (arrayType arrayIndex0 environment0 arraydef_0__dsu))
                (Z.to_nat a)
                (Z.of_nat (ancestor dsu (Z.to_nat 100) (Z.to_nat a)))
                (convertToArray dsu)) _1
       | right _ =>
           match
             _0 as _2 return (list (arrayType arrayIndex0 environment0 _2))
           with
           | arraydef_0__dsu => convertToArray dsu
           | arraydef_0__hasBeenInitialized => [1%Z]
           | arraydef_0__result =>
               [Z.of_nat (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]
           end
       end) = fun xx => match xx with | arraydef_0__dsu => (<[Z.to_nat a:=Z.of_nat
                              (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]>
                (convertToArray dsu)) | arraydef_0__hasBeenInitialized => [1%Z]
           | arraydef_0__result =>
               [Z.of_nat (ancestor dsu (Z.to_nat 100) (Z.to_nat a))] end.
  { apply functional_extensionality_dep. intro jak. destruct jak; easy. }
  rewrite gda. clear gda.
  rewrite insertConvertReferTo; [lia | lia |]. rewrite Nat2Z.id dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 ra !leftIdentity. unfold retrieve at 1. rewrite pushDispatch2 (ltac:(intros; simpl; reflexivity) : forall effect continuation f, Dispatch _ _ _ effect continuation >>= f = _) unfoldInvoke_S_Retrieve. clear ppp xxx. case_decide as xxx; [| rewrite lengthConvert in xxx; lia]. case_decide as ppp; [| rewrite lengthConvert in ppp; rewrite insert_length in ppp; lia]. rewrite pushNumberSet2 /update.
  assert (red : forall _0,
           ( match
             @decide (@eq varsfuncdef_0__ancestor _0 vardef_0__ancestor_work)
               (@decide_rel varsfuncdef_0__ancestor varsfuncdef_0__ancestor
                  (@eq varsfuncdef_0__ancestor)
                  variableIndexEqualityDecidablevarsfuncdef_0__ancestor _0
                  vardef_0__ancestor_work)
            with |left _ =>
             @nth_lt (arrayType arrayIndex0 environment0 arraydef_0__dsu)
               (convertToArray
                  (@insert nat Slot (list Slot) (@list_insert Slot)
                     (Z.to_nat a)
                     (ReferTo (ancestor dsu (Z.to_nat 100) (Z.to_nat a))) dsu))
               (Z.to_nat a) ppp
            | right _ => match _0 with
                 | vardef_0__ancestor_vertex | _ => a
                 end end) = match _0 with | vardef_0__ancestor_work => nth_lt
           (convertToArray
              (<[Z.to_nat a:=ReferTo
                               (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]>
                 dsu)) (Z.to_nat a) ppp | _ => a end).
  { intro g. destruct g; easy. }
  have red2 := functional_extensionality_dep _ _ red.
  rewrite red2. clear red red2. rewrite (nth_lt_default _ _ _ 0%Z) nthConvert. { rewrite insert_length. lia. } rewrite nth_lookup list_lookup_insert. { lia. } rewrite (ltac:(simpl; reflexivity) : default _ (Some _) = _).
Admitted.

Lemma runAncestor (dsu : list Slot) (hL : length dsu = 100) (hL1 : Z.to_nat (dsuLeafCount dsu) = length dsu) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (a : Z) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) communication continuation whatever : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state state
  communication 1 arrayIndex0 arrayIndexEqualityDecidable0
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
    convertToArray dsu
| arraydef_0__hasBeenInitialized =>
    [1%Z]
| arraydef_0__result =>
    [whatever]
end)
  (funcdef_0__main (λ _ : varsfuncdef_0__main, false)
  (λ _ : varsfuncdef_0__main, 0%Z)
  (λ _ : varsfuncdef_0__main, repeat 0%Z 20))
  (funcdef_0__ancestor (λ _ : varsfuncdef_0__ancestor, false)
  (update (λ _ : varsfuncdef_0__ancestor, 0%Z)
  vardef_0__ancestor_vertex a)
  (λ _ : varsfuncdef_0__ancestor, repeat 0%Z 20) >>= continuation) = invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state state
  communication 1 arrayIndex0 arrayIndexEqualityDecidable0
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
    convertToArray (pathCompress dsu (length dsu) (Z.to_nat a) (ancestor dsu (length dsu) (Z.to_nat a)))
| arraydef_0__hasBeenInitialized =>
    [1%Z]
| arraydef_0__result =>
    [Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))]
end)
  (funcdef_0__main (λ _ : varsfuncdef_0__main, false)
  (λ _ : varsfuncdef_0__main, 0%Z)
  (λ _ : varsfuncdef_0__main, repeat 0%Z 20))
  (continuation tt).
Proof.
  rewrite /funcdef_0__ancestor. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 pushNumberSet2.
  have : (update (update (fun=> 0%Z) vardef_0__ancestor_vertex a)
        vardef_0__ancestor_work
        (update (fun=> 0%Z) vardef_0__ancestor_vertex a
           vardef_0__ancestor_vertex)) = fun x => match x with | vardef_0__ancestor_vertex => a | vardef_0__ancestor_work => a end.
  { apply functional_extensionality_dep. intro x. destruct x; easy. }
  move => h. rewrite h. clear h. rewrite leftIdentity.
  have av := fun g gg => runAncestor1 dsu hL hL1 h1 h2 a a hLe1 hLt1 communication g gg whatever (Z.to_nat 100%Z) ltac:(lia).
  move : av. rewrite !leftIdentity !rightIdentity. move => av.
  rewrite -bindAssoc av. unfold numberLocalGet at 1. rewrite pushNumberGet2. unfold store at 1. rewrite pushDispatch2. rewrite (ltac:(intros; simpl; reflexivity) : forall effect continuation f, Dispatch _ _ _ effect continuation >>= f = _) unfoldInvoke_S_Store. case_decide as xxx; [| simpl in xxx; lia]; clear xxx.
  have jda : (λ _0 : arrayIndex0,
     match decide (_0 = arraydef_0__result) with
     | left _1 =>
         eq_rect_r
           (λ _2 : arrayIndex0, list (arrayType arrayIndex0 environment0 _2))
           (<[Z.to_nat 0:=Z.of_nat (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]>
              [whatever]) _1
     | right _ =>
         match
           _0 as _2 return (list (arrayType arrayIndex0 environment0 _2))
         with
         | arraydef_0__dsu => convertToArray dsu
         | arraydef_0__hasBeenInitialized => [1%Z]
         | arraydef_0__result => [whatever]
         end
     end) = fun x => match x with | arraydef_0__dsu => convertToArray dsu | arraydef_0__hasBeenInitialized => [1%Z] | arraydef_0__result => [Z.of_nat (ancestor dsu (Z.to_nat 100) (Z.to_nat a))] end.
  { apply functional_extensionality_dep. intro g. destruct g; easy. }
  rewrite jda. clear jda. unfold numberLocalGet at 1. rewrite pushNumberGet2. unfold numberLocalSet at 1. rewrite pushNumberSet2.
  have jda : (update
        (λ _0 : varsfuncdef_0__ancestor,
           match _0 with
           | vardef_0__ancestor_vertex => a
           | vardef_0__ancestor_work =>
               Z.of_nat (ancestor dsu (Z.to_nat 100) (Z.to_nat a))
           end) vardef_0__ancestor_work a) = fun x => match x with | vardef_0__ancestor_vertex => a | vardef_0__ancestor_work => a end.
  { apply functional_extensionality_dep. intro gg. destruct gg; easy. }
  rewrite jda. clear jda.
Admitted.

Lemma runUnite (dsu : list Slot) (hL : length dsu = 100) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (a b : Z) (hLt1 : Z.lt a 100) (hLt2 : Z.lt b 100) : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state
  state [a; b] 1 arrayIndex0 arrayIndexEqualityDecidable0
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
    convertToArray dsu
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
  (liftToWithLocalVariables
  (funcdef_0__unite
  (λ _ : varsfuncdef_0__unite, false) (λ _0 : varsfuncdef_0__unite,
  match _0
with
| vardef_0__unite_u =>
    a
| vardef_0__unite_v =>
    b
| vardef_0__unite_z =>
    0%Z
end)
  (λ _ : varsfuncdef_0__unite, repeat 0%Z 20)) >>=
λ _ : (),
  Dispatch
  (WithLocalVariables arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main)
  withLocalVariablesReturnValue
  (withLocalVariablesReturnValue
  (DoWithArrays arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main
  (Store arrayIndex0
  (arrayType arrayIndex0 environment0)
  arraydef_0__result 0 (coerceInt 0 8))))
  (DoWithArrays arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main
  (Store arrayIndex0
  (arrayType arrayIndex0 environment0)
  arraydef_0__result 0 (coerceInt 0 8)))
  (λ _0 : withLocalVariablesReturnValue
  (DoWithArrays arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main
  (Store arrayIndex0
  (arrayType arrayIndex0
  environment0)
  arraydef_0__result 0
  (coerceInt 0 8))),
  Done
  (WithLocalVariables arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main)
  withLocalVariablesReturnValue
  (withLocalVariablesReturnValue
  (DoWithArrays arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main
  (Store arrayIndex0
  (arrayType arrayIndex0 environment0)
  arraydef_0__result 0 (coerceInt 0 8))))
  _0) >>=
λ _ : (),
  Done
  (WithLocalVariables arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__main)
  withLocalVariablesReturnValue ()
  ())) =
Some
  ([a; b],
stateAfterInteractions (λ _0 : arrayIndex0,
  match
  _0 as _1
return
  (list
  (arrayType arrayIndex0
  environment0 _1))
with
| arraydef_0__dsu =>
    convertToArray
  (unite
  dsu
  (Z.to_nat a)
  (Z.to_nat b))
| arraydef_0__hasBeenInitialized =>
    [1%Z]
| arraydef_0__result => [0%Z]
end)
  (dsuScore
  (unite dsu (Z.to_nat a)
  (Z.to_nat b)))).
Proof.
  unfold funcdef_0__unite. unfold numberLocalGet at 1. rewrite <- !bindAssoc, pushNumberGet2, !leftIdentity, eliminateLift, eliminateLift.
Admitted.

Lemma firstInteraction (a b : Z) (hLt1 : Z.lt a 100) (hLt2 : Z.lt b 100) : invokeContract (repeat 1%Z 20) (repeat 0%Z 20) 0%Z state state [a; b] 1 = Some ([a; b], stateAfterInteractions (fun x => match x with | arraydef_0__result => [0%Z] | arraydef_0__hasBeenInitialized => [1%Z] | arraydef_0__dsu => convertToArray (unite (repeat (Ancestor Unit) 100) (Z.to_nat a) (Z.to_nat b)) end) (dsuScore (unite (repeat (Ancestor Unit) 100) (Z.to_nat a) (Z.to_nat b)))).
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
  case_decide as h3; [| simpl in h3; lia].
Admitted.

Lemma interactEqualsModelScore (x : list (Z * Z)) : interact state x = modelScore x.
Proof.
Admitted.
