From CoqCP Require Import Options Imperative DisjointSetUnion ListsEqual ExistsInRange SwapUpdate DisjointSetUnionCode.
From Generated Require Import DisjointSetUnion.
From stdpp Require Import numbers list.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Wellfounded.
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma runCompressLoop (dsu : list Slot) state1 state2 (hL : length dsu = 100) (hL1 : Z.to_nat (dsuLeafCount dsu) = length dsu) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (a : Z) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) communication whatever (n : nat) (hN : n <= 100) continuation : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state1 state2 communication
  1 arrayIndex0 arrayIndexEqualityDecidable0
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
        | vardef_0__ancestor_vertex => whatever | _ => a
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
                                    varsfuncdef_0__ancestor arraydef_0__dsu
                                    _2 >>=
                                  [eta numberLocalSet arrayIndex0
                                         (arrayType arrayIndex0 environment0)
                                         varsfuncdef_0__ancestor
                                         vardef_0__ancestor_vertex]) >>=
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
                                           arraydef_0__result 0 >>=
                                         [eta store arrayIndex0
                                                (arrayType arrayIndex0
                                                 environment0)
                                                varsfuncdef_0__ancestor
                                                arraydef_0__dsu _2]) >>=
                                  (fun=> liftToWithinLoop
                                           (numberLocalGet arrayIndex0
                                              (arrayType arrayIndex0
                                                 environment0)
                                              varsfuncdef_0__ancestor
                                              vardef_0__ancestor_vertex >>=
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
                                                 withinLoopReturnValue () ())))))) >>=
      (fun=> Done
               (WithLocalVariables arrayIndex0
                  (arrayType arrayIndex0 environment0)
                  varsfuncdef_0__ancestor) withLocalVariablesReturnValue ()
               ())) >>= continuation) =
invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state1 state2 communication 1 arrayIndex0 arrayIndexEqualityDecidable0
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
  move : a hLe1 hLt1 dsu h1 hL hL1 h2 whatever. elim : n hN.
  { move => hN a hLe1 hLt1. rewrite (ltac:(simpl; reflexivity) : loop 0 _ = _) leftIdentity.
    move => dsu h1 hL hL1 h2 whatever.
    rewrite (ltac:(intros; simpl; reflexivity) : forall a b c, pathCompress a 0 b c = _) hL. easy. }
  move => n IH hN a hLe1 hLt1 dsu h1 hL hL1 h2 whatever. rewrite loop_S -!bindAssoc dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 !leftIdentity.
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
  - rewrite !leftIdentity dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 !leftIdentity. unfold retrieve at 1. rewrite pushDispatch2 (ltac:(intros; simpl; reflexivity) : forall effect continuation f, Dispatch _ _ _ effect continuation >>= f = _)  unfoldInvoke_S_Retrieve ra. case_decide as ppp; [| rewrite lengthConvert in ppp; lia]. rewrite pushNumberSet2 dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2. rewrite (ltac:(cbv) : update _ _ _ vardef_0__ancestor_work = a). { easy. } rewrite !leftIdentity. unfold retrieve at 1. rewrite pushDispatch2 (ltac:(intros; simpl; reflexivity) : forall effect continuation f, Dispatch _ _ _ effect continuation >>= f = _) unfoldInvoke_S_Retrieve. case_decide as nnn; [| simpl in nnn; lia]. rewrite pushDispatch2 (ltac:(intros; simpl; reflexivity) : forall effect continuation f, Dispatch _ _ _ effect continuation >>= f = _) unfoldInvoke_S_Store. rewrite (ltac:(simpl; reflexivity) : forall xx, nth_lt [xx] _ nnn = xx) insertConvertReferTo. { rewrite ra. lia. } { lia. } rewrite Nat2Z.id.
  have red: (update
          (λ _0 : varsfuncdef_0__ancestor,
             match _0 with
             | vardef_0__ancestor_vertex => whatever
             | vardef_0__ancestor_work => a
             end) vardef_0__ancestor_vertex
          (nth_lt (convertToArray dsu) (Z.to_nat a) ppp)) = fun x => match x with | vardef_0__ancestor_vertex => nth_lt (convertToArray dsu) (Z.to_nat a) ppp | _ => a end.
  { apply functional_extensionality_dep. intro g. destruct g; easy. }
  rewrite red. clear red.
  rewrite dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2. unfold numberLocalSet at 1. rewrite pushNumberSet2 (nth_lt_default _ _ _ 0%Z).
  destruct hh as [hh | hh]; [| simpl in hhh; pose proof oneLeqLeafCount hh; lia]. clear nnn ppp xxx. rewrite ra lengthConvert. case_decide as mww; [| lia]; clear mww. rewrite (ltac:(easy) : dropWithinLoop (Done _ _ _ _) = Done _ _ _ _) leftIdentity.
  have red : (λ _0 : arrayIndex0,
     match decide (_0 = arraydef_0__dsu) with
     | left _1 =>
         @eq_rect_r arrayIndex0 arraydef_0__dsu
            (fun _2 : arrayIndex0 =>
             list (arrayType arrayIndex0 environment0 _2))
            (convertToArray
               (@insert nat Slot (list Slot) (@list_insert Slot) 
                  (Z.to_nat a)
                  (ReferTo (ancestor dsu (Z.to_nat 100) (Z.to_nat a))) dsu))
            _0 _1
     | right _ =>
         match
           _0 as _2 return (list (arrayType arrayIndex0 environment0 _2))
         with
         | arraydef_0__dsu => convertToArray dsu
         | arraydef_0__hasBeenInitialized => [1%Z]
         | arraydef_0__result =>
             [Z.of_nat (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]
         end
     end) = fun x => match x with | arraydef_0__dsu => convertToArray
              (<[Z.to_nat a:=ReferTo
                               (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]>
                 dsu)
         | arraydef_0__hasBeenInitialized => [1%Z]
         | arraydef_0__result =>
             [Z.of_nat (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]
         end.
  { apply functional_extensionality_dep. intro g. destruct g; easy. }
  rewrite red. clear red.
  rewrite nthConvert. { lia. } rewrite hhh.
  have red : (update
        (λ _0 : varsfuncdef_0__ancestor,
           match _0 with
           | vardef_0__ancestor_vertex => Z.of_nat hh
           | vardef_0__ancestor_work => a
           end) vardef_0__ancestor_work (Z.of_nat hh)) = fun x => match x with
           | vardef_0__ancestor_vertex => Z.of_nat hh
           | vardef_0__ancestor_work => Z.of_nat hh
           end.
  { apply functional_extensionality_dep. intro g. destruct g; easy. }
  rewrite red. clear red.
  have red1 : noIllegalIndices
  (<[Z.to_nat a:=ReferTo (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]> dsu).
  { clear hs. intros a1 a2 a3. destruct (decide (a1 = Z.to_nat a)) as [hs | hs]. { rewrite -> nth_lookup, <- hs, list_lookup_insert in a3; [| lia]. rewrite (ltac:(simpl; reflexivity) : default _ (Some _) = _) in a3. rewrite insert_length. pose proof (ltac:(clear; intros a b h; injection h; easy) : forall a b, ReferTo a = ReferTo b -> a = b) _ _ a3 as a4. rewrite <- a4. apply ancestorLtLength; (assumption || lia). } rewrite insert_length. rewrite nth_lookup list_lookup_insert_ne in a3. { lia. } rewrite <- (nth_lookup _ _ (Ancestor Unit)) in a3. pose proof h1 _ _ a3. lia. }
  have red2 : Z.to_nat
  (dsuLeafCount
     (<[Z.to_nat a:=ReferTo (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]> dsu)) =
length
  (<[Z.to_nat a:=ReferTo (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]> dsu).
  { unfold dsuLeafCount. rewrite Nat2Z.id insert_length insert_take_drop. { lia. } rewrite (ltac:(intros; listsEqual) : forall a b, a :: b = [a] ++ b) !map_app !list_sum_app.
    assert (hst : list_sum
   (map
      (λ _1 : Slot,
         match _1 with
         | ReferTo _ => 0
         | Ancestor _2 => leafCount _2
         end) [ReferTo (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]) = list_sum
   (map
      (λ _1 : Slot,
         match _1 with
         | ReferTo _ => 0
         | Ancestor _2 => leafCount _2
         end) [nth (Z.to_nat a) dsu (Ancestor Unit)])).
    { rewrite hhh. easy. } rewrite hst. clear hst. rewrite -!list_sum_app -!map_app -(ltac:(intros; listsEqual) : forall a b, a :: b = [a] ++ b) nthConsDrop; try lia. { intro cona. rewrite cona in hL; simpl in hL; lia. } rewrite take_drop. unfold dsuLeafCount in hL1. rewrite Nat2Z.id in hL1. exact hL1. }
  have red3 : withoutCyclesN
  (<[Z.to_nat a:=ReferTo (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]> dsu)
  (length
     (<[Z.to_nat a:=ReferTo (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]> dsu)).
  { intros b c. rewrite insert_length in c. rewrite insert_length (ltac:(lia) : Z.to_nat 100%Z = length dsu) -ancestorInsert; try (assumption || lia). { rewrite hhh. easy. }
    destruct (decide (ancestor dsu (length dsu) b = Z.to_nat a)) as [hw | hw].
    - pose proof h2 b c as st. rewrite hw hhh in st. exfalso. exact st.
    - rewrite nth_lookup list_lookup_insert_ne. { lia. } rewrite <- (nth_lookup _ _ (Ancestor Unit)). pose proof h2 b c. assumption. }
  pose proof IH ltac:(lia) (Z.of_nat hh) ltac:(lia) ltac:(pose proof h1 _ _ hhh; lia) (<[Z.to_nat a:=ReferTo (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]> dsu) red1 ltac:(rewrite -> insert_length; lia) red2 red3 (Z.of_nat hh) as ffi.
  rewrite dropWithinLoopLiftToWithinLoop -!bindAssoc in ffi.
  assert (closer : Z.of_nat
            (ancestor
               (<[Z.to_nat a:=ReferTo
                                (ancestor dsu (Z.to_nat 100) (Z.to_nat a))]>
                  dsu) (Z.to_nat 100) (Z.to_nat (Z.of_nat hh))) = Z.of_nat (ancestor dsu (Z.to_nat 100) (Z.to_nat a))).
  { rewrite !(ltac:(lia) : Z.to_nat 100%Z = length dsu) Nat2Z.id -ancestorInsert; try (assumption || lia). { pose proof h1 _ _ hhh. lia. } { rewrite hhh. easy. }
    assert (subtask : ancestor dsu (length dsu) (Z.to_nat a) = ancestor dsu (S (length dsu - 1)) (Z.to_nat a)). { rewrite (ltac:(lia) : S (length dsu - 1) = length dsu). reflexivity. } rewrite subtask. simpl. rewrite hhh.
    pose proof h2 (Z.to_nat a) ltac:(lia) as subtask2. rewrite subtask in subtask2. simpl in subtask2. rewrite hhh in subtask2.
    assert (subtask3 : ancestor dsu (length dsu) hh = ancestor dsu (S (length dsu - 1)) hh). { rewrite (ltac:(lia) : S (length dsu - 1) = length dsu). reflexivity. } rewrite subtask3.
    pose proof h1 (Z.to_nat a) _ hhh as lh.
    pose proof validChainAncestorChain dsu (length dsu - 1) hh ltac:(lia) h1 as mh.
    epose proof validChainAncestorLength dsu (ancestorChain dsu (length dsu - 1) hh) h1 ltac:(split; try assumption; rewrite ancestorEqLastAncestorChain; destruct (nth (ancestor dsu (length dsu - 1) hh) dsu (Ancestor Unit)) as [xx | xx]; try (exfalso; exact subtask2); exists xx; reflexivity) hh ltac:(clear; destruct (length dsu - 1); simpl; try reflexivity; destruct (nth hh dsu (Ancestor Unit)); easy) as nh. rewrite -subtask3 -ancestorEqLastAncestorChain -nh ancestorEqLastAncestorChain. reflexivity. }
  rewrite closer in ffi. rewrite ffi insert_length Nat2Z.id (ltac:(lia) : Z.to_nat 100%Z = length dsu) -ancestorInsert; try (assumption || lia). { pose proof h1 (Z.to_nat a) _ hhh. assumption. } { rewrite hhh. easy. }
  assert (anc : ancestor dsu (length dsu) hh = ancestor dsu (length dsu) (Z.to_nat a)).
  { assert (subtask : ancestor dsu (length dsu) (Z.to_nat a) = ancestor dsu (S (length dsu - 1)) (Z.to_nat a)). { rewrite (ltac:(lia) : S (length dsu - 1) = length dsu). reflexivity. } rewrite subtask. simpl. rewrite hhh.
    pose proof h2 (Z.to_nat a) ltac:(lia) as subtask2. rewrite subtask in subtask2. simpl in subtask2. rewrite hhh in subtask2.
    assert (subtask3 : ancestor dsu (length dsu) hh = ancestor dsu (S (length dsu - 1)) hh). { rewrite (ltac:(lia) : S (length dsu - 1) = length dsu). reflexivity. } rewrite subtask3.
    pose proof h1 (Z.to_nat a) _ hhh as lh.
    pose proof validChainAncestorChain dsu (length dsu - 1) hh ltac:(lia) h1 as mh.
    pose proof validChainAncestorLength dsu (ancestorChain dsu (length dsu - 1) hh) h1 ltac:(split; try assumption; rewrite ancestorEqLastAncestorChain; destruct (nth (ancestor dsu (length dsu - 1) hh) dsu (Ancestor Unit)) as [xx | xx]; try (exfalso; exact subtask2); exists xx; reflexivity) hh ltac:(clear; destruct (length dsu - 1); simpl; try reflexivity; destruct (nth hh dsu (Ancestor Unit)); easy) as nh. rewrite -subtask3 -ancestorEqLastAncestorChain -nh ancestorEqLastAncestorChain. reflexivity. }
  assert (finale : pathCompress dsu (S n) (Z.to_nat a) (ancestor dsu (length dsu) (Z.to_nat a)) = pathCompress (<[Z.to_nat a:=ReferTo (ancestor dsu (length dsu) (Z.to_nat a))]> dsu) n hh (ancestor dsu (length dsu) hh)).
  { simpl. rewrite hhh anc. reflexivity. } rewrite -finale anc. reflexivity.
Qed.

Lemma runAncestor (dsu : list Slot) state1 state2 (hL : length dsu = 100) (hL1 : Z.to_nat (dsuLeafCount dsu) = length dsu) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (a : Z) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) communication continuation whatever : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state1 state2
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
  (λ _ : varsfuncdef_0__ancestor, repeat 0%Z 20) >>= continuation) = invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state1 state2
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
  have av := fun g gg => runAncestor1 dsu state1 state2 hL hL1 h1 h2 a a hLe1 hLt1 communication g gg whatever (Z.to_nat 100%Z) ltac:(lia).
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
  rewrite jda. clear jda. rewrite runCompressLoop; try (assumption || lia). rewrite (ltac:(lia) : Z.to_nat 100 = length dsu). reflexivity.
Qed.

Lemma mergingLogic (dsu : list Slot) (hL : length dsu = 100) (hL1 : Z.to_nat (dsuLeafCount dsu) = length dsu) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (a b : Z) (x y : Z) (hLeX : Z.le 0 x) (hLtX : Z.lt x 100) (hLeY : Z.le 0 y) (hLtY : Z.lt y 100) (hdiff : ancestor dsu (length dsu) (Z.to_nat a) <> ancestor dsu (length dsu) (Z.to_nat b)) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) (hLe2 : Z.le 0 b) (hLt2 : Z.lt b 100) tree1 tree2 (htree1 : nth (ancestor dsu (length dsu) (Z.to_nat a)) (pathCompress (pathCompress dsu (length dsu) (Z.to_nat x) (ancestor dsu (length dsu) (Z.to_nat x))) (length dsu) (Z.to_nat y)
              (ancestor dsu (length dsu) (Z.to_nat y))) (Ancestor Unit) = Ancestor tree1) (htree2 : nth (ancestor dsu (length dsu) (Z.to_nat b)) (pathCompress
              (pathCompress dsu (length dsu) (Z.to_nat x)
                 (ancestor dsu (length dsu) (Z.to_nat x))) 
              (length dsu) (Z.to_nat y)
              (ancestor dsu (length dsu) (Z.to_nat y))) (Ancestor Unit) = Ancestor tree2) whatever whatever2 ignored : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state
  (stateAfterInteractions
     ignored (dsuScore dsu)) [x; y] 1 arrayIndex0
  arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0)
  (λ _0 : arrayIndex0,
     match
       _0 as _1 return (list (arrayType arrayIndex0 environment0 _1))
     with
     | arraydef_0__dsu =>
         convertToArray
           (pathCompress
              (pathCompress dsu (length dsu) (Z.to_nat x)
                 (ancestor dsu (length dsu) (Z.to_nat x))) 
              (length dsu) (Z.to_nat y)
              (ancestor dsu (length dsu) (Z.to_nat y)))
     | arraydef_0__hasBeenInitialized => [1%Z]
     | arraydef_0__result =>
         [whatever2]
     end) (funcdef_0__main xpred0 (fun=> 0%Z) (fun=> repeat 0%Z 20))
  (eliminateLocalVariables xpred0
     (λ _0 : varsfuncdef_0__unite,
        match _0 with
        | vardef_0__unite_u =>
            Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))
        | vardef_0__unite_z => whatever
        | _ => Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b))
        end) (fun=> repeat 0%Z 20)
     (numberLocalGet arrayIndex0 (arrayType arrayIndex0 environment0)
        varsfuncdef_0__unite vardef_0__unite_v >>=
      λ _0 : withLocalVariablesReturnValue
               (NumberLocalGet arrayIndex0
                  (arrayType arrayIndex0 environment0) varsfuncdef_0__unite
                  vardef_0__unite_v),
        Done
          (WithLocalVariables arrayIndex0
             (arrayType arrayIndex0 environment0) varsfuncdef_0__unite)
          withLocalVariablesReturnValue Z (coerceInt _0 64) >>=
        (λ _1 : Z,
           numberLocalGet arrayIndex0 (arrayType arrayIndex0 environment0)
             varsfuncdef_0__unite vardef_0__unite_u >>=
           (λ _2 : withLocalVariablesReturnValue
                     (NumberLocalGet arrayIndex0
                        (arrayType arrayIndex0 environment0)
                        varsfuncdef_0__unite vardef_0__unite_u),
              Done
                (WithLocalVariables arrayIndex0
                   (arrayType arrayIndex0 environment0) varsfuncdef_0__unite)
                withLocalVariablesReturnValue Z (coerceInt _2 64) >>=
              [eta retrieve arrayIndex0 (arrayType arrayIndex0 environment0)
                     varsfuncdef_0__unite arraydef_0__dsu] >>=
              λ _3 : Z,
                numberLocalGet arrayIndex0
                  (arrayType arrayIndex0 environment0) varsfuncdef_0__unite
                  vardef_0__unite_v >>=
                (λ _4 : withLocalVariablesReturnValue
                          (NumberLocalGet arrayIndex0
                             (arrayType arrayIndex0 environment0)
                             varsfuncdef_0__unite vardef_0__unite_v),
                   Done
                     (WithLocalVariables arrayIndex0
                        (arrayType arrayIndex0 environment0)
                        varsfuncdef_0__unite) withLocalVariablesReturnValue Z
                     (coerceInt _4 64) >>=
                   [eta retrieve arrayIndex0
                          (arrayType arrayIndex0 environment0)
                          varsfuncdef_0__unite arraydef_0__dsu]) >>=
                (λ _4 : Z,
                   Done
                     (WithLocalVariables arrayIndex0
                        (arrayType arrayIndex0 environment0)
                        varsfuncdef_0__unite) withLocalVariablesReturnValue Z
                     (coerceInt (_3 + _4) 8)) >>=
                [eta Done
                       (WithLocalVariables arrayIndex0
                          (arrayType arrayIndex0 environment0)
                          varsfuncdef_0__unite) withLocalVariablesReturnValue
                       Z]) >>=
           [eta store arrayIndex0 (arrayType arrayIndex0 environment0)
                  varsfuncdef_0__unite arraydef_0__dsu _1] >>=
           (fun=> numberLocalGet arrayIndex0
                    (arrayType arrayIndex0 environment0) varsfuncdef_0__unite
                    vardef_0__unite_u >>=
                  λ _2 : withLocalVariablesReturnValue
                           (NumberLocalGet arrayIndex0
                              (arrayType arrayIndex0 environment0)
                              varsfuncdef_0__unite vardef_0__unite_u),
                    Done
                      (WithLocalVariables arrayIndex0
                         (arrayType arrayIndex0 environment0)
                         varsfuncdef_0__unite) withLocalVariablesReturnValue
                      Z (coerceInt _2 64) >>=
                    λ _3 : Z,
                      numberLocalGet arrayIndex0
                        (arrayType arrayIndex0 environment0)
                        varsfuncdef_0__unite vardef_0__unite_v >>=
                      [eta Done
                             (WithLocalVariables arrayIndex0
                                (arrayType arrayIndex0 environment0)
                                varsfuncdef_0__unite)
                             withLocalVariablesReturnValue
                             (withLocalVariablesReturnValue
                                (NumberLocalGet arrayIndex0
                                   (arrayType arrayIndex0 environment0)
                                   varsfuncdef_0__unite vardef_0__unite_v))] >>=
                      [eta store arrayIndex0
                             (arrayType arrayIndex0 environment0)
                             varsfuncdef_0__unite arraydef_0__dsu _3] >>=
                      (fun=> getSender arrayIndex0
                               (arrayType arrayIndex0 environment0)
                               varsfuncdef_0__unite >>=
                             λ _4 : withLocalVariablesReturnValue
                                      (DoWithArrays arrayIndex0
                                         (arrayType arrayIndex0 environment0)
                                         varsfuncdef_0__unite
                                         (DoBasicEffect arrayIndex0
                                            (arrayType arrayIndex0
                                               environment0) GetSender)),
                               numberLocalGet arrayIndex0
                                 (arrayType arrayIndex0 environment0)
                                 varsfuncdef_0__unite vardef_0__unite_v >>=
                               (λ _5 : withLocalVariablesReturnValue
                                         (NumberLocalGet arrayIndex0
                                            (arrayType arrayIndex0
                                               environment0)
                                            varsfuncdef_0__unite
                                            vardef_0__unite_v),
                                  Done
                                    (WithLocalVariables arrayIndex0
                                       (arrayType arrayIndex0 environment0)
                                       varsfuncdef_0__unite)
                                    withLocalVariablesReturnValue Z
                                    (coerceInt _5 64) >>=
                                  [eta retrieve arrayIndex0
                                         (arrayType arrayIndex0 environment0)
                                         varsfuncdef_0__unite arraydef_0__dsu] >>=
                                  λ _6 : arrayType arrayIndex0 environment0
                                           arraydef_0__dsu,
                                    Done
                                      (WithLocalVariables arrayIndex0
                                         (arrayType arrayIndex0 environment0)
                                         varsfuncdef_0__unite)
                                      withLocalVariablesReturnValue Z
                                      (coerceInt (- _6) 8) >>=
                                    λ _7 : Z,
                                      Done
                                        (WithLocalVariables arrayIndex0
                                           (arrayType arrayIndex0
                                              environment0)
                                           varsfuncdef_0__unite)
                                        withLocalVariablesReturnValue Z
                                        (coerceInt _7 256)) >>=
                               (donate arrayIndex0
                                  (arrayType arrayIndex0 environment0)
                                  varsfuncdef_0__unite)^~ _4 >>=
                               (fun=> Done
                                        (WithLocalVariables arrayIndex0
                                           (arrayType arrayIndex0
                                              environment0)
                                           varsfuncdef_0__unite)
                                        withLocalVariablesReturnValue () ())))) >>=
        (fun=> Done
                 (WithLocalVariables arrayIndex0
                    (arrayType arrayIndex0 environment0) varsfuncdef_0__unite)
                 withLocalVariablesReturnValue () ())) >>=
   (fun=> Dispatch
            (WithArrays arrayIndex0 (arrayType arrayIndex0 environment0))
            withArraysReturnValue ()
            (Store arrayIndex0 (arrayType arrayIndex0 environment0)
               arraydef_0__result 0 (coerceInt 0 8))
            (fun=> eliminateLocalVariables xpred0 
                     (fun=> 0%Z) (fun=> repeat 0%Z 20)
                     (Done
                        (WithLocalVariables arrayIndex0
                           (arrayType arrayIndex0 environment0)
                           varsfuncdef_0__main) withLocalVariablesReturnValue
                        () ())))) = Some
  ([x; y],
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
  (performMerge
  (pathCompress
              (pathCompress dsu (length dsu) (Z.to_nat x)
                 (ancestor dsu (length dsu) (Z.to_nat x))) 
              (length dsu) (Z.to_nat y)
              (ancestor dsu (length dsu) (Z.to_nat y)))
  tree1 tree2
  (ancestor dsu (length dsu) (Z.to_nat a))
  (ancestor dsu (length dsu) (Z.to_nat b)))
| arraydef_0__hasBeenInitialized =>
    [1%Z]
| arraydef_0__result => [0%Z]
end)
  (dsuScore (performMerge
  (pathCompress
              (pathCompress dsu (length dsu) (Z.to_nat x)
                 (ancestor dsu (length dsu) (Z.to_nat x))) 
              (length dsu) (Z.to_nat y)
              (ancestor dsu (length dsu) (Z.to_nat y)))
  tree1 tree2
  (ancestor dsu (length dsu) (Z.to_nat a))
  (ancestor dsu (length dsu) (Z.to_nat b))))).
Proof.
  pose proof ancestorLtLength dsu h1 (length dsu) (Z.to_nat b) ltac:(lia) as ib1.
  pose proof ancestorLtLength dsu h1 (length dsu) (Z.to_nat a) ltac:(lia) as ib2.
  pose proof ancestorLtLength dsu h1 (length dsu) (Z.to_nat x) ltac:(lia) as arb1.
  pose proof ancestorLtLength dsu h1 (length dsu) (Z.to_nat y) ltac:(lia) as arb2.
  assert (lib1 : (coerceInt (Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b))) 64) = Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b))).
  { unfold coerceInt. rewrite Z.mod_small; [| reflexivity]. lia. }
  assert (lib2 : (coerceInt (Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))) 64) = Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))).
  { unfold coerceInt. rewrite Z.mod_small; [| reflexivity]. lia. }
  unfold numberLocalGet at 1. rewrite pushNumberGet2 lib1 !leftIdentity. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 lib2 !leftIdentity. unfold retrieve at 1. rewrite -!bindAssoc pushDispatch2 bindDispatch unfoldInvoke_S_Retrieve. case_decide as ppp; [| rewrite lengthConvert !pathCompressPreservesLength Nat2Z.id in ppp; lia]. unfold numberLocalGet at 1. rewrite pushNumberGet2 pushDispatch2 bindDispatch unfoldInvoke_S_Retrieve !(nth_lt_default _ _ _ 0%Z) !Nat2Z.id. case_decide as lll; [| rewrite lengthConvert!pathCompressPreservesLength in lll; lia].
  rewrite (nth_lt_default _ _ _ 0%Z) lib1 !nthConvert; try (rewrite !pathCompressPreservesLength; lia). rewrite htree1 Nat2Z.id htree2. clear ppp lll.
  pose proof h2 (Z.to_nat a) ltac:(lia) as g1.
  pose proof h2 (Z.to_nat b) ltac:(lia) as g2.
  remember (nth (ancestor dsu (length dsu) (Z.to_nat a)) dsu (Ancestor Unit)) as a1 eqn:j1. symmetry in j1.
  remember (nth (ancestor dsu (length dsu) (Z.to_nat b)) dsu (Ancestor Unit)) as a2 eqn:j2. symmetry in j2.
  destruct a1 as [a1 | a1]; destruct a2 as [a2 | a2]; try (exfalso; (exact g1) || (exact g2)).
  assert (exx : ((coerceInt
           (256%Z - Z.of_nat (leafCount tree1) +
            (256%Z - Z.of_nat (leafCount tree2))) 8%Z) = 256%Z - Z.of_nat (leafCount tree1) - Z.of_nat (leafCount tree2))%Z).
  { unfold coerceInt. rewrite (ltac:(clear; lia) : ((256 - Z.of_nat (leafCount tree1) + (256 - Z.of_nat (leafCount tree2))) = 512 + -(Z.of_nat (leafCount tree1) + Z.of_nat (leafCount tree2)))%Z). rewrite Z.add_mod; [lia |]. rewrite (ltac:(clear; easy) : (512 `mod` 2^8 = 0)%Z) Z.add_0_l Z.mod_mod; [lia |].
   rewrite !(pathCompressPreservesNth _ _ _ _ _ a1) in htree1; try exact j1.
   rewrite !(pathCompressPreservesNth _ _ _ _ _ a2) in htree2; try exact j2.
   pose proof sumTwoAncestors dsu _ _ hdiff ltac:(apply ancestorLtLength; (assumption || lia)) ltac:(apply ancestorLtLength; (assumption || lia)) _ j1 _ j2 as step.
   pose proof oneLeqLeafCount tree1. pose proof oneLeqLeafCount tree2.
   assert (p1 : tree1 = a1). { rewrite htree1 in j1. injection j1. easy. }
   assert (p2 : tree2 = a2). { rewrite htree2 in j2. injection j2. easy. } subst tree1 tree2.
   rewrite (ltac:(easy) : (2^8 = 256)%Z) Z_mod_nz_opp_full; rewrite Z.mod_small; lia. }
   rewrite exx. unfold store at 1. rewrite pushDispatch2 bindDispatch unfoldInvoke_S_Store.
   assert (p1 : tree1 = a1). { rewrite !(pathCompressPreservesNth _ _ _ _ _ a1) in htree1; try exact j1. rewrite htree1 in j1. injection j1. easy. }
   assert (p2 : tree2 = a2). { rewrite !(pathCompressPreservesNth _ _ _ _ _ a2) in htree2; try exact j2. rewrite htree2 in j2. injection j2. easy. } subst tree1 tree2. rewrite Nat2Z.id lengthConvert !pathCompressPreservesLength. case_decide as lll; [| exfalso; exact (lll ltac:(apply ancestorLtLength; (assumption || lia)))].
   assert (lc : leafCount a1 + leafCount a2 <= length dsu).
   { pose proof sumTwoAncestors dsu _ _ hdiff ltac:(apply ancestorLtLength; (assumption || lia)) ltac:(apply ancestorLtLength; (assumption || lia)) _ j1 _ j2 as step. lia. }
   assert (hsimp : (fun _0 : arrayIndex0 =>
   match
     @decide (@eq arrayIndex0 _0 arraydef_0__dsu)
       (@decide_rel arrayIndex0 arrayIndex0 (@eq arrayIndex0)
          arrayIndexEqualityDecidable0 _0 arraydef_0__dsu)
   with
   | @left _ _ _1 =>
       @eq_rect_r arrayIndex0 arraydef_0__dsu
         (fun _2 : arrayIndex0 =>
          list (arrayType arrayIndex0 environment0 _2))
         (@insert nat (arrayType arrayIndex0 environment0 arraydef_0__dsu)
            (list (arrayType arrayIndex0 environment0 arraydef_0__dsu))
            (@list_insert
               (arrayType arrayIndex0 environment0 arraydef_0__dsu))
            (ancestor dsu (@length Slot dsu) (Z.to_nat b))
            (Z.sub (Z.sub 256 (Z.of_nat (leafCount a1)))
               (Z.of_nat (leafCount a2)))
            (convertToArray
               (pathCompress
                  (pathCompress dsu (@length Slot dsu) 
                     (Z.to_nat x)
                     (ancestor dsu (@length Slot dsu) (Z.to_nat x)))
                  (@length Slot dsu) (Z.to_nat y)
                  (ancestor dsu (@length Slot dsu) (Z.to_nat y))))) _0 _1
   | @right _ _ _ =>
       match
         _0 as _2 return (list (arrayType arrayIndex0 environment0 _2))
       with
       | arraydef_0__dsu =>
           convertToArray
             (pathCompress
                (pathCompress dsu (@length Slot dsu) 
                   (Z.to_nat x)
                   (ancestor dsu (@length Slot dsu) (Z.to_nat x)))
                (@length Slot dsu) (Z.to_nat y)
                (ancestor dsu (@length Slot dsu) (Z.to_nat y)))
       | arraydef_0__hasBeenInitialized => @cons Z 1%Z (@nil Z)
       | arraydef_0__result =>
           @cons Z
             (whatever2)
             (@nil Z)
       end
   end) = (fun _0 => match _0 with | arraydef_0__dsu =>
             (<[ancestor dsu (length dsu) (Z.to_nat b):=
              (256 - Z.of_nat (leafCount a1) - Z.of_nat (leafCount a2))%Z]>
              (convertToArray
                 (pathCompress
                    (pathCompress dsu (length dsu) 
                       (Z.to_nat x) (ancestor dsu (length dsu) (Z.to_nat x)))
                    (length dsu) (Z.to_nat y)
                    (ancestor dsu (length dsu) (Z.to_nat y)))))
         | arraydef_0__hasBeenInitialized => [1%Z]
         | arraydef_0__result =>
             [whatever2]
         end)). { apply functional_extensionality_dep. intro _0. destruct _0; easy. } rewrite hsimp. clear hsimp.
     pose proof insertConvertAncestor
              (pathCompress
                 (pathCompress dsu (length dsu) (Z.to_nat x)
                    (ancestor dsu (length dsu) (Z.to_nat x))) 
                 (length dsu) (Z.to_nat y)
                 (ancestor dsu (length dsu) (Z.to_nat y))) (ancestor dsu (length dsu) (Z.to_nat b)) ltac:(rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia)) (Unite a2 a1) as step2. unfold performMerge.
     assert (step : (256 - Z.of_nat (leafCount (Unite a2 a1)) = 256 - Z.of_nat (leafCount a1) - Z.of_nat (leafCount a2))%Z).
     { simpl. lia. }
     rewrite step in step2. rewrite step2.
     unfold numberLocalGet at 1. rewrite pushNumberGet2 lib2 leftIdentity. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 leftIdentity. unfold store at 1. rewrite pushDispatch2 bindDispatch unfoldInvoke_S_Store. rewrite Nat2Z.id lengthConvert insert_length !pathCompressPreservesLength. case_decide as jel; [| lia].
     rewrite insertConvertReferTo. { rewrite insert_length !pathCompressPreservesLength; lia. } { lia. } rewrite Nat2Z.id.
     assert (hasd: (fun _0 : arrayIndex0 =>
      match
        @decide (@eq arrayIndex0 _0 arraydef_0__dsu)
          (@decide_rel arrayIndex0 arrayIndex0 (@eq arrayIndex0)
             arrayIndexEqualityDecidable0 _0 arraydef_0__dsu)
      with
      | @left _ _ _1 =>
          @eq_rect_r arrayIndex0 arraydef_0__dsu
            (fun _2 : arrayIndex0 =>
             list (arrayType arrayIndex0 environment0 _2))
            (convertToArray
               (@insert nat Slot (list Slot) (@list_insert Slot)
                  (ancestor dsu (@length Slot dsu) (Z.to_nat a))
                  (ReferTo (ancestor dsu (@length Slot dsu) (Z.to_nat b)))
                  (@insert nat Slot (list Slot) (@list_insert Slot)
                     (ancestor dsu (@length Slot dsu) (Z.to_nat b))
                     (Ancestor (Unite a2 a1))
                     (pathCompress
                        (pathCompress dsu (@length Slot dsu) 
                           (Z.to_nat x)
                           (ancestor dsu (@length Slot dsu) (Z.to_nat x)))
                        (@length Slot dsu) (Z.to_nat y)
                        (ancestor dsu (@length Slot dsu) (Z.to_nat y)))))) _0
            _1
      | @right _ _ _ =>
          match
            _0 as _2 return (list (arrayType arrayIndex0 environment0 _2))
          with
          | arraydef_0__dsu =>
              convertToArray
                (@insert nat Slot (list Slot) (@list_insert Slot)
                   (ancestor dsu (@length Slot dsu) (Z.to_nat b))
                   (Ancestor (Unite a2 a1))
                   (pathCompress
                      (pathCompress dsu (@length Slot dsu) 
                         (Z.to_nat x)
                         (ancestor dsu (@length Slot dsu) (Z.to_nat x)))
                      (@length Slot dsu) (Z.to_nat y)
                      (ancestor dsu (@length Slot dsu) (Z.to_nat y))))
          | arraydef_0__hasBeenInitialized => @cons Z 1%Z (@nil Z)
          | arraydef_0__result =>
              @cons Z
                (whatever2)
                (@nil Z)
          end
      end) = (fun _0 => match _0 with | arraydef_0__dsu => convertToArray
              (<[ancestor dsu (length dsu) (Z.to_nat a):=
                 ReferTo (ancestor dsu (length dsu) (Z.to_nat b))]>
                 (<[ancestor dsu (length dsu) (Z.to_nat b):=
                    Ancestor (Unite a2 a1)]>
                    (pathCompress
                       (pathCompress dsu (length dsu) 
                          (Z.to_nat x)
                          (ancestor dsu (length dsu) (Z.to_nat x)))
                       (length dsu) (Z.to_nat y)
                       (ancestor dsu (length dsu) (Z.to_nat y))))) | arraydef_0__hasBeenInitialized => [1%Z]
         | arraydef_0__result =>
             [whatever2]
         end)). { apply functional_extensionality_dep. intro _0. destruct _0; easy. }
     rewrite hasd. clear hasd. unfold getSender. rewrite pushDispatch2 bindDispatch unfoldInvoke_S_GetSender.
     unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 !leftIdentity. unfold retrieve at 1. rewrite pushDispatch2 bindDispatch unfoldInvoke_S_Retrieve.
     case_decide as ppp; [rewrite (nth_lt_default _ _ _ 0%Z) | rewrite lengthConvert !insert_length !pathCompressPreservesLength lib1 in ppp; lia]. clear ppp.
     assert (clu : forall v, coerceInt (coerceInt v 8) 256 = coerceInt v 8).
     { intro v. unfold coerceInt. rewrite Z.mod_small; [| reflexivity]. pose proof (ltac:(intros; lia) : forall (a : Z), (0 <= a < 2^8 -> 0 <= a < 2^256)%Z) as g. apply g. apply Z.mod_pos_bound; lia. }
     rewrite clu nthConvert. { rewrite !insert_length !pathCompressPreservesLength lib1 Nat2Z.id. lia. }
     rewrite nth_lookup !lib1 !Nat2Z.id list_lookup_insert_ne. { lia. } rewrite list_lookup_insert. { rewrite !pathCompressPreservesLength. lia. } rewrite (ltac:(simpl; reflexivity) : default (Ancestor Unit) (Some (Ancestor (Unite a2 a1))) = _).
     assert (solv : (coerceInt (- (256 - Z.of_nat (leafCount (Unite a2 a1)))) 8 = Z.of_nat (leafCount a1) + Z.of_nat (leafCount a2))%Z).
     { simpl. unfold coerceInt. rewrite (ltac:(easy) : (2^8 = 256)%Z). rewrite -(Z.mod_add (- (256 - Z.of_nat (leafCount a2 + leafCount a1))) 1 256 ltac:(lia)). rewrite (ltac:(lia) : ((- (256 - Z.of_nat (leafCount a2 + leafCount a1)) + 1 * 256 = Z.of_nat (leafCount a1 + leafCount a2)))%Z).
     rewrite Z.mod_small; [| lia]. pose proof sumTwoAncestors dsu (ancestor dsu (length dsu) (Z.to_nat a)) (ancestor dsu (length dsu) (Z.to_nat b)) ltac:(assumption) ltac:(apply ancestorLtLength; (assumption || lia)) ltac:(apply ancestorLtLength; (assumption || lia)) a1 ltac:(assumption) a2 ltac:(assumption). lia. } rewrite solv. unfold donate. rewrite pushDispatch2 bindDispatch unfoldInvoke_S_Donate leftIdentity.
     assert (st2 : (getBalance
          (stateAfterInteractions
             ignored (dsuScore dsu) (repeat 0 20)) = 100000 - dsuScore dsu)%Z).
     { easy. } rewrite st2.
     pose proof performMergeScore (pathCompress
                       (pathCompress dsu (length dsu) 
                          (Z.to_nat x)
                          (ancestor dsu (length dsu) (Z.to_nat x)))
                       (length dsu) (Z.to_nat y)
                       (ancestor dsu (length dsu) (Z.to_nat y))) a1 a2 (ancestor dsu (length dsu) (Z.to_nat a)) (ancestor dsu (length dsu) (Z.to_nat b)) ltac:(lia) ltac:(rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia)) ltac:(rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia)) ltac:(rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia)) ltac:(rewrite (pathCompressPreservesNth _ _ _ _ _ a1); try (assumption || lia); rewrite (pathCompressPreservesNth _ _ _ _ _ a1); try (assumption || lia)) ltac:(rewrite (pathCompressPreservesNth _ _ _ _ _ a2); try (assumption || lia); rewrite (pathCompressPreservesNth _ _ _ _ _ a2); try (assumption || lia)) as stp. unfold performMerge in stp.
     rewrite !pathCompressPreservesScore in stp. rewrite stp.
     pose proof maxScore3 dsu as gg. rewrite !hL1 !hL (ltac:(easy): (100 * (100 + 1)) `div` 2 - 1 = Z.to_nat (5049%Z)) in gg.
     assert ((0 <= dsuScore dsu)%Z).
     { unfold dsuScore. lia. }
     assert (hStep : (dsuScore dsu <= 5049)%Z).
     { unfold dsuScore in gg. rewrite Nat2Z.id in gg. unfold dsuScore. lia. }
     case_decide as hs; [| exfalso; exact (hs ltac:(split; lia))].
     rewrite unfoldInvoke_S_Store. clear hs. case_decide as hs; [| exfalso; exact (hs ltac:(simpl; lia))].
     
     assert (hsimp : (fun _1 : arrayIndex0 =>
      match
        @decide (@eq arrayIndex0 _1 arraydef_0__result)
          (@decide_rel arrayIndex0 arrayIndex0 (@eq arrayIndex0)
             arrayIndexEqualityDecidable0 _1 arraydef_0__result)
      with
      | @left _ _ _2 =>
          @eq_rect_r arrayIndex0 arraydef_0__result
            (fun _3 : arrayIndex0 =>
             list (arrayType arrayIndex0 environment0 _3))
            (@insert nat
               (arrayType arrayIndex0 environment0 arraydef_0__result)
               (list (arrayType arrayIndex0 environment0 arraydef_0__result))
               (@list_insert
                  (arrayType arrayIndex0 environment0 arraydef_0__result))
               (Z.to_nat 0) (coerceInt 0 8)
               (@cons Z
                  (Z.of_nat (ancestor dsu (@length Slot dsu) (Z.to_nat b)))
                  (@nil Z))) _1 _2
      | @right _ _ _ =>
          match
            _1 as _3 return (list (arrayType arrayIndex0 environment0 _3))
          with
          | arraydef_0__dsu =>
              convertToArray
                (@insert nat Slot (list Slot) (@list_insert Slot)
                   (ancestor dsu (@length Slot dsu) (Z.to_nat a))
                   (ReferTo (ancestor dsu (@length Slot dsu) (Z.to_nat b)))
                   (@insert nat Slot (list Slot) (@list_insert Slot)
                      (ancestor dsu (@length Slot dsu) (Z.to_nat b))
                      (Ancestor (Unite a2 a1))
                      (pathCompress
                         (pathCompress dsu (@length Slot dsu) 
                            (Z.to_nat x)
                            (ancestor dsu (@length Slot dsu) (Z.to_nat x)))
                         (@length Slot dsu) (Z.to_nat y)
                         (ancestor dsu (@length Slot dsu) (Z.to_nat y)))))
          | arraydef_0__hasBeenInitialized => @cons Z 1%Z (@nil Z)
          | arraydef_0__result =>
              @cons Z
                (whatever2)
                (@nil Z)
          end
      end) = fun _1 => match
           _1 as _3 return (list (arrayType arrayIndex0 environment0 _3))
         with
         | arraydef_0__dsu =>
             convertToArray
               (<[ancestor dsu (length dsu) (Z.to_nat a):=
                  ReferTo (ancestor dsu (length dsu) (Z.to_nat b))]>
                  (<[ancestor dsu (length dsu) (Z.to_nat b):=
                     Ancestor (Unite a2 a1)]>
                     (pathCompress
                        (pathCompress dsu (length dsu) 
                           (Z.to_nat x)
                           (ancestor dsu (length dsu) (Z.to_nat x)))
                        (length dsu) (Z.to_nat y)
                        (ancestor dsu (length dsu) (Z.to_nat y)))))
         | arraydef_0__hasBeenInitialized => [1%Z]
         | arraydef_0__result =>
             [0%Z]
         end). { apply functional_extensionality_dep. intro _1. destruct _1; easy. }
     rewrite hsimp. clear hsimp.
     assert (hsimp : transferMoney
     (stateAfterInteractions
        ignored (dsuScore dsu)) (repeat 0%Z 20) (repeat 1%Z 20)
     (Z.of_nat (leafCount a1) + Z.of_nat (leafCount a2)) = stateAfterInteractions
        ignored (dsuScore dsu + Z.of_nat (leafCount a1) + Z.of_nat (leafCount a2))).
     { apply functional_extensionality_dep. intro _1. unfold stateAfterInteractions. unfold transferMoney. unfold update.
       repeat case_decide; try (exfalso; easy); try reflexivity.
       { subst _1. exfalso. easy. }
       { simpl. rewrite Z.add_assoc. reflexivity. }
       { simpl. rewrite (ltac:(lia) : ((100000 - dsuScore dsu -
   (Z.of_nat (leafCount a1) + Z.of_nat (leafCount a2))) = (100000 -
   (dsuScore dsu + Z.of_nat (leafCount a1) + Z.of_nat (leafCount a2))))%Z). reflexivity. } }
     rewrite hsimp. clear hsimp. simpl.
  apply (ltac:(intros T U mm ma mb mc; subst ma; reflexivity) : forall (T U : Type) (g : T) (a b : U), a = b -> Some (g, a) = Some (g, b)).
  apply functional_extensionality_dep. intro ___1. unfold update. unfold stateAfterInteractions. repeat case_decide; easy.
Qed.

Lemma runUnite (dsu : list Slot) (hL : length dsu = 100) (hL1 : Z.to_nat (dsuLeafCount dsu) = length dsu) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (a b : Z) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) (hLe2 : Z.le 0 b) (hLt2 : Z.lt b 100) ignored : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state
  (stateAfterInteractions ignored
  (dsuScore
  dsu)) [a; b] 1 arrayIndex0 arrayIndexEqualityDecidable0
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
  unfold funcdef_0__unite. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 !leftIdentity eliminateLift eliminateLift -!bindAssoc runAncestor; try (assumption || lia). unfold retrieve at 1. rewrite !pushDispatch2 (ltac:(intros; simpl; reflexivity) : forall effect continuation f, Dispatch _ _ _ effect continuation >>= f = _) unfoldInvoke_S_Retrieve. case_decide as ppp; [| simpl in ppp; lia]. rewrite (ltac:(intros; easy) : forall a c, nth_lt [a] (Z.to_nat 0%Z) c = a). clear ppp. unfold numberLocalSet at 1. rewrite pushNumberSet2.
  assert (le : update
        (λ _0 : varsfuncdef_0__unite,
           match _0 with
           | vardef_0__unite_u => a
           | vardef_0__unite_v => b
           | vardef_0__unite_z => 0%Z
           end) vardef_0__unite_u
        (Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))) = fun x => match x with | vardef_0__unite_u => Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a)) | vardef_0__unite_v => b | vardef_0__unite_z => 0%Z end). { apply functional_extensionality_dep. intro hh. destruct hh; easy. } rewrite le. clear le.
  unfold numberLocalGet at 1. rewrite pushNumberGet2 !leftIdentity eliminateLift.
  rewrite -!bindAssoc runAncestor; try (assumption || lia). { rewrite pathCompressPreservesLength; (assumption || lia). } { rewrite pathCompressPreservesLength; try (assumption || lia). rewrite pathCompressPreservesLeafCount; try (assumption || lia). } { apply pathCompressPreservesNoIllegalIndices; try (assumption || lia). apply ancestorLtLength; try assumption. lia. } { rewrite pathCompressPreservesLength; try (assumption || lia). apply pathCompressPreservesWithoutCycles; try (assumption || lia). } unfold retrieve at 1. rewrite !pushDispatch2 (ltac:(intros; simpl; reflexivity) : forall effect continuation f, Dispatch _ _ _ effect continuation >>= f = _) unfoldInvoke_S_Retrieve. case_decide as ppp; [| simpl in ppp; lia]. rewrite (ltac:(intros; easy) : forall a c, nth_lt [a] (Z.to_nat 0%Z) c = a). clear ppp. unfold numberLocalSet at 1. rewrite pushNumberSet2.
  assert (uwl : update
        (λ _0 : varsfuncdef_0__unite,
           match _0 with
           | vardef_0__unite_u =>
               Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))
           | vardef_0__unite_v => b
           | vardef_0__unite_z => 0%Z
           end) vardef_0__unite_v
        (Z.of_nat
           (ancestor
              (pathCompress dsu (length dsu) (Z.to_nat a)
                 (ancestor dsu (length dsu) (Z.to_nat a)))
              (length
                 (pathCompress dsu (length dsu) (Z.to_nat a)
                    (ancestor dsu (length dsu) (Z.to_nat a)))) 
              (Z.to_nat b))) = fun _0 => match _0 with
           | vardef_0__unite_u =>
               Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))
           | vardef_0__unite_v => Z.of_nat
           (ancestor
              (pathCompress dsu (length dsu) (Z.to_nat a)
                 (ancestor dsu (length dsu) (Z.to_nat a)))
              (length
                 (pathCompress dsu (length dsu) (Z.to_nat a)
                    (ancestor dsu (length dsu) (Z.to_nat a)))) 
              (Z.to_nat b))
           | vardef_0__unite_z => 0%Z
           end). { apply functional_extensionality_dep. intro iw. destruct iw; easy. } rewrite uwl. clear uwl.
  unfold numberLocalGet at 1. rewrite pushNumberGet2. unfold numberLocalGet at 1. rewrite pushNumberGet2. case_bool_decide as hs.
  - unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2.
    assert (ra2 : coerceInt (Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))) 64 = Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))). { unfold coerceInt. rewrite Z.mod_small; [| reflexivity]. pose proof ancestorLtLength dsu h1 (length dsu) (Z.to_nat a) ltac:(lia). lia. } rewrite ra2.
    assert (rb2 : coerceInt (Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b))) 64 = Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b))). { unfold coerceInt. rewrite Z.mod_small; [| reflexivity]. pose proof ancestorLtLength dsu h1 (length dsu) (Z.to_nat b) ltac:(lia). lia. }
    pose proof pathCompressPreservesAncestorLength dsu h1 h2 (length dsu) (Z.to_nat a) (Z.to_nat b) (Z.to_nat a) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) as step. rewrite pathCompressPreservesLength; try (assumption || lia). rewrite step !leftIdentity. unfold retrieve at 1. rewrite -!bindAssoc pushDispatch2 (ltac:(intros; simpl; reflexivity) : forall effect continuation f, Dispatch _ _ _ effect continuation >>= f = _) unfoldInvoke_S_Retrieve. case_decide as ppp; [|rewrite Nat2Z.id lengthConvert !pathCompressPreservesLength in ppp; exfalso; exact (ppp ltac:(apply ancestorLtLength; (assumption || lia)))]. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 !leftIdentity. unfold retrieve at 1. rewrite pushDispatch2 rb2 (ltac:(intros; simpl; reflexivity) : forall effect continuation f, Dispatch _ _ _ effect continuation >>= f = _) unfoldInvoke_S_Retrieve. rewrite Nat2Z.id.
    case_decide as lll; [| rewrite lengthConvert !pathCompressPreservesLength in lll; exfalso; exact (lll ltac:(apply ancestorLtLength; (assumption || lia)))]. rewrite !leftIdentity.
    rewrite !(ltac:(intros; simpl; reflexivity) : forall a b c, @nth_lt (arrayType arrayIndex0 environment0 arraydef_0__dsu) a b c = @nth_lt Z a b c) !(nth_lt_default _ _ _ 0%Z) Nat2Z.id !nthConvert; try (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia)).
    remember (nth (ancestor dsu (length dsu) (Z.to_nat a))
                 (pathCompress
                    (pathCompress dsu (length dsu) 
                       (Z.to_nat a) (ancestor dsu (length dsu) (Z.to_nat a)))
                    (length dsu) (Z.to_nat b)
                    (ancestor dsu (length dsu) (Z.to_nat b))) 
                 (Ancestor Unit)) as lnode eqn:hlnode.
    remember (nth (ancestor dsu (length dsu) (Z.to_nat b))
                 (pathCompress
                    (pathCompress dsu (length dsu) 
                       (Z.to_nat a) (ancestor dsu (length dsu) (Z.to_nat a)))
                    (length dsu) (Z.to_nat b)
                    (ancestor dsu (length dsu) (Z.to_nat b))) 
                 (Ancestor Unit)) as rnode eqn:hrnode.
    pose proof pathCompressPreservesWithoutCycles dsu h2 h1 (length dsu) (Z.to_nat a) ltac:(lia) as steproll1.
    pose proof pathCompressPreservesNoIllegalIndices dsu h1 (length dsu) (Z.to_nat a) (ancestor dsu (length dsu) (Z.to_nat a)) ltac:(lia) ltac:(apply ancestorLtLength; (assumption || lia)) as stepidx1.
    pose proof pathCompressPreservesWithoutCycles (pathCompress dsu (length dsu) (Z.to_nat a)
     (ancestor dsu (length dsu) (Z.to_nat a))) ltac:(rewrite pathCompressPreservesLength; exact steproll1) stepidx1 (length dsu) (Z.to_nat b) ltac:(rewrite pathCompressPreservesLength; lia) as mold.
     pose proof mold (Z.to_nat a) ltac:(rewrite pathCompressPreservesLength; lia) as anca. rewrite !pathCompressPreservesLength !step in anca.
     pose proof mold (Z.to_nat b) ltac:(rewrite pathCompressPreservesLength; lia) as ancb. rewrite !pathCompressPreservesLength !step in ancb.
     pose proof pathCompressPreservesAncestorLength (pathCompress dsu (length dsu) (Z.to_nat a)
             (ancestor dsu (length dsu) (Z.to_nat a))) ltac:(apply pathCompressPreservesNoIllegalIndices; try (assumption || lia); apply ancestorLtLength; (assumption || lia)) ltac:(rewrite pathCompressPreservesLength; apply pathCompressPreservesWithoutCycles; (assumption || lia)) (length dsu) as mold2. rewrite !pathCompressPreservesLength in mold2.
     pose proof (fun a (g1 : a < length dsu) b (g2 : b < length dsu) => mold2 a b a g1 g2 g1 ltac:(reflexivity)) (Z.to_nat b) ltac:(lia) as mold3. clear mold2.
     pose proof (fun xx (hh : xx < length dsu) => pathCompressPreservesAncestorLength dsu h1 h2 (length dsu) (Z.to_nat a) xx (Z.to_nat a) ltac:(lia) hh ltac:(lia) ltac:(reflexivity)) as mold2.
     pose proof mold3 (Z.to_nat a) ltac:(lia) as simpa1.
     pose proof mold2 (Z.to_nat a) ltac:(lia) as simpa2. rewrite simpa2 in simpa1.
     pose proof mold3 (Z.to_nat b) ltac:(lia) as simpb1.
     pose proof mold2 (Z.to_nat b) ltac:(lia) as simpb2. rewrite simpb2 in simpb1, simpa1. rewrite simpa1 -hlnode in anca. rewrite simpb1 -hrnode in ancb. destruct lnode as [lnode | lnode]; destruct rnode as [rnode | rnode]; try (exfalso; (exact anca || exact ancb)).
     pose proof nthLowerBoundConvertAuxStep (pathCompress
     (pathCompress dsu (length dsu) (Z.to_nat a)
        (ancestor dsu (length dsu) (Z.to_nat a))) 
     (length dsu) (Z.to_nat b) (ancestor dsu (length dsu) (Z.to_nat b))) ltac:(rewrite !pathCompressPreservesLength; lia) ltac:(rewrite ! pathCompressPreservesLeafCount; try (assumption || (rewrite -> ? pathCompressPreservesLength; lia))) as mold4. rewrite !pathCompressPreservesLength in mold4. symmetry in hlnode. symmetry in hrnode.
     pose proof mold4 (ancestor dsu (length dsu) (Z.to_nat a)) ltac:(apply ancestorLtLength; (assumption || lia)) _ hlnode as lcl.
     pose proof mold4 (ancestor dsu (length dsu) (Z.to_nat b)) ltac:(apply ancestorLtLength; (assumption || lia)) _ hrnode as lcr. clear ppp lll.
     assert (stepl : toSigned (256 - Z.of_nat (leafCount lnode)) 8 = -Z.of_nat (leafCount lnode)).
     { unfold toSigned. case_decide as ppp; lia. } rewrite stepl. clear stepl.
     assert (stepr : toSigned (256 - Z.of_nat (leafCount rnode)) 8 = -Z.of_nat (leafCount rnode)).
     { unfold toSigned. case_decide as ppp; lia. } rewrite stepr. clear stepr.
     case_bool_decide as hswap.
     + unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2. unfold numberLocalSet at 1. rewrite -!bindAssoc pushNumberSet2.
     assert (hsimp : (update
        (λ _0 : varsfuncdef_0__unite,
           match _0 with
           | vardef_0__unite_u =>
               Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))
           | vardef_0__unite_v =>
               Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b))
           | vardef_0__unite_z => 0%Z
           end) vardef_0__unite_z
        (Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a)))) = (λ _0 : varsfuncdef_0__unite,
           match _0 with
           | vardef_0__unite_u =>
               Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))
           | vardef_0__unite_v =>
               Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b))
           | vardef_0__unite_z => (Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a)))
           end)). { apply functional_extensionality_dep. intro f. destruct f; easy. } rewrite hsimp. clear hsimp.
     unfold numberLocalGet at 1. rewrite pushNumberGet2. unfold numberLocalSet at 1. rewrite -!bindAssoc pushNumberSet2.
     assert (hsimp : (update
        (λ _0 : varsfuncdef_0__unite,
           match _0 with
           | vardef_0__unite_v =>
               Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b))
           | _ => Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))
           end) vardef_0__unite_u
        (Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b)))) = (λ _0 : varsfuncdef_0__unite,
           match _0 with
           | vardef_0__unite_u =>
               Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b))
           | vardef_0__unite_v =>
               Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b))
           | vardef_0__unite_z => (Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a)))
           end)). { apply functional_extensionality_dep. intro f. destruct f; easy. } rewrite hsimp. clear hsimp.
     unfold numberLocalGet at 1. rewrite pushNumberGet2. unfold numberLocalSet at 1. rewrite pushNumberSet2.
     assert (hsimp : (update
        (λ _0 : varsfuncdef_0__unite,
           match _0 with
           | vardef_0__unite_z =>
               Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))
           | _ => Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b))
           end) vardef_0__unite_v
        (Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a)))) = (λ _0 : varsfuncdef_0__unite,
           match _0 with
           | vardef_0__unite_u =>
               Z.of_nat (ancestor dsu (length dsu) (Z.to_nat b))
           | vardef_0__unite_v =>
               Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))
           | vardef_0__unite_z => (Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a)))
           end)). { apply functional_extensionality_dep. intro f. destruct f; easy. } rewrite hsimp. clear hsimp.
     rewrite pathCompressPreservesLength !pathCompressPreservesAncestorLength in hs; try (assumption || lia).
     pose proof mergingLogic hL hL1 h1 h2 (ltac:(lia) : (0 <= a)%Z) ltac:(lia) (ltac:(lia) : (0 <= b)%Z) ltac:(lia) (ltac:(lia) : ancestor dsu (length dsu) (Z.to_nat b) ≠ ancestor dsu (length dsu) (Z.to_nat a)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) hrnode hlnode as st.
     rewrite st. apply (ltac:(intros T U mm ma mb mc; subst ma; reflexivity) : forall (T U : Type) (g : T) (a b : U), a = b -> Some (g, a) = Some (g, b)).
     apply functional_extensionality_dep. intro x. unfold update. unfold stateAfterInteractions. repeat case_decide; try easy.
     { rewrite performMergeScore; try (assumption || lia || (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))).
       rewrite !pathCompressPreservesScore.
       unfold unite. repeat case_decide; try lia; [rewrite -> pathCompressPreservesLength, -> pathCompressPreservesAncestorLength in *; try (assumption || lia || (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))); lia|]. rewrite !pathCompressPreservesLength !pathCompressPreservesAncestorLength; try (assumption || lia || (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))). rewrite hlnode hrnode.
       case_decide; try lia. rewrite performMergeScore; try (assumption || lia || (rewrite ?pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))). rewrite !pathCompressPreservesScore. reflexivity. }
     { rewrite performMergeScore; try (assumption || lia || (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))).
       rewrite !pathCompressPreservesScore.
       unfold unite. repeat case_decide; try lia; [rewrite -> pathCompressPreservesLength, -> pathCompressPreservesAncestorLength in *; try (assumption || lia || (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))); lia|]. rewrite !pathCompressPreservesLength !pathCompressPreservesAncestorLength; try (assumption || lia || (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))). rewrite hlnode hrnode.
       case_decide; try lia. rewrite performMergeScore; try (assumption || lia || (rewrite ?pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))). rewrite !pathCompressPreservesScore. reflexivity. }
   + rewrite -!bindAssoc !leftIdentity.
     rewrite pathCompressPreservesLength !pathCompressPreservesAncestorLength in hs; try (assumption || lia).
     pose proof mergingLogic hL hL1 h1 h2 (ltac:(lia) : (0 <= a)%Z) ltac:(lia) (ltac:(lia) : (0 <= b)%Z) ltac:(lia) (ltac:(lia) : ancestor dsu (length dsu) (Z.to_nat a) ≠ ancestor dsu (length dsu) (Z.to_nat b)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) hlnode hrnode as st.
     rewrite st. apply (ltac:(intros T U mm ma mb mc; subst ma; reflexivity) : forall (T U : Type) (g : T) (a b : U), a = b -> Some (g, a) = Some (g, b)).
     apply functional_extensionality_dep. intro x. unfold update. unfold stateAfterInteractions. repeat case_decide; try easy.
     { rewrite performMergeScore; try (assumption || lia || (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))).
       rewrite !pathCompressPreservesScore.
       unfold unite. repeat case_decide; try lia; [rewrite -> pathCompressPreservesLength, -> pathCompressPreservesAncestorLength in *; try (assumption || lia || (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))); lia|]. rewrite !pathCompressPreservesLength !pathCompressPreservesAncestorLength; try (assumption || lia || (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))). rewrite hlnode hrnode.
       case_decide; try lia. rewrite performMergeScore; try (assumption || lia || (rewrite ?pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))). rewrite !pathCompressPreservesScore. reflexivity. }
     { rewrite performMergeScore; try (assumption || lia || (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))).
       rewrite !pathCompressPreservesScore.
       unfold unite. repeat case_decide; try lia; [rewrite -> pathCompressPreservesLength, -> pathCompressPreservesAncestorLength in *; try (assumption || lia || (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))); lia|]. rewrite !pathCompressPreservesLength !pathCompressPreservesAncestorLength; try (assumption || lia || (rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))). rewrite hlnode hrnode.
       case_decide; try lia. rewrite performMergeScore; try (assumption || lia || (rewrite ?pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia))). rewrite !pathCompressPreservesScore. reflexivity. }
  - rewrite !leftIdentity unfoldInvoke_S_Store. case_decide as ppp; [| simpl in ppp; lia]. clear ppp.
    assert (battle : (λ _0 : arrayIndex0,
     match
       @decide (_0 = arraydef_0__result)
         (@decide_rel arrayIndex0 arrayIndex0 (@eq arrayIndex0)
            arrayIndexEqualityDecidable0 _0 arraydef_0__result)
     with
     | @left _ _ _1 =>
         @eq_rect_r arrayIndex0 arraydef_0__result
           (λ _2 : arrayIndex0, list (arrayType arrayIndex0 environment0 _2))
           (<[Z.to_nat 0:=coerceInt 0 8]>
              [Z.of_nat
                 (ancestor
                    (pathCompress dsu (@length Slot dsu) 
                       (Z.to_nat a)
                       (ancestor dsu (@length Slot dsu) (Z.to_nat a)))
                    (@length Slot
                       (pathCompress dsu (@length Slot dsu) 
                          (Z.to_nat a)
                          (ancestor dsu (@length Slot dsu) (Z.to_nat a))))
                    (Z.to_nat b))]) _0 _1
     | @right _ _ _ =>
         match
           _0 as _2 return (list (arrayType arrayIndex0 environment0 _2))
         with
         | arraydef_0__dsu =>
             convertToArray
               (pathCompress
                  (pathCompress dsu (@length Slot dsu) 
                     (Z.to_nat a)
                     (ancestor dsu (@length Slot dsu) (Z.to_nat a)))
                  (@length Slot
                     (pathCompress dsu (@length Slot dsu) 
                        (Z.to_nat a)
                        (ancestor dsu (@length Slot dsu) (Z.to_nat a))))
                  (Z.to_nat b)
                  (ancestor
                     (pathCompress dsu (@length Slot dsu) 
                        (Z.to_nat a)
                        (ancestor dsu (@length Slot dsu) (Z.to_nat a)))
                     (@length Slot
                        (pathCompress dsu (@length Slot dsu) 
                           (Z.to_nat a)
                           (ancestor dsu (@length Slot dsu) (Z.to_nat a))))
                     (Z.to_nat b)))
         | arraydef_0__hasBeenInitialized => [1%Z]
         | arraydef_0__result =>
             [Z.of_nat
                (ancestor
                   (pathCompress dsu (@length Slot dsu) 
                      (Z.to_nat a)
                      (ancestor dsu (@length Slot dsu) (Z.to_nat a)))
                   (@length Slot
                      (pathCompress dsu (@length Slot dsu) 
                         (Z.to_nat a)
                         (ancestor dsu (@length Slot dsu) (Z.to_nat a))))
                   (Z.to_nat b))]
         end
     end) = fun _0 => match
           _0 as _2 return (list (arrayType arrayIndex0 environment0 _2))
         with
         | arraydef_0__dsu =>
             convertToArray
               (pathCompress
                  (pathCompress dsu (length dsu) (Z.to_nat a)
                     (ancestor dsu (length dsu) (Z.to_nat a)))
                  (length
                     (pathCompress dsu (length dsu) 
                        (Z.to_nat a) (ancestor dsu (length dsu) (Z.to_nat a))))
                  (Z.to_nat b)
                  (ancestor
                     (pathCompress dsu (length dsu) 
                        (Z.to_nat a) (ancestor dsu (length dsu) (Z.to_nat a)))
                     (length
                        (pathCompress dsu (length dsu) 
                           (Z.to_nat a)
                           (ancestor dsu (length dsu) (Z.to_nat a))))
                     (Z.to_nat b)))
         | arraydef_0__hasBeenInitialized => [1%Z]
         | arraydef_0__result =>
             [0%Z]
         end). { apply functional_extensionality_dep. intro dd. destruct dd; easy. } rewrite battle.
  unfold unite. repeat case_decide; try lia. rewrite !pathCompressPreservesScore (ltac:(simpl; reflexivity) : eliminateLocalVariables xpred0 (fun=> 0%Z) (fun=> repeat 0%Z 20)
     (Done
        (WithLocalVariables arrayIndex0 (arrayType arrayIndex0 environment0)
           varsfuncdef_0__main) withLocalVariablesReturnValue () ()) = _) unfoldInvoke_S_Done.
  apply (ltac:(intros T U mm ma mb mc; subst ma; reflexivity) : forall (T U : Type) (g : T) (a b : U), a = b -> Some (g, a) = Some (g, b)).
  apply functional_extensionality_dep. intro x. unfold update. unfold stateAfterInteractions. repeat case_decide; easy.
Qed.

Lemma outOfBoundsInteractionNA (a b : Z) (hOOB : Z.le 100 a) (hUB : Z.lt a 256) (dsu : list Slot) (hL : length dsu = 100) : invokeContract (repeat 1%Z 20) (repeat 0%Z 20) 0%Z state (stateAfterInteractions (fun x => match x with | arraydef_0__result => [0%Z] | arraydef_0__hasBeenInitialized => [1%Z] | arraydef_0__dsu => convertToArray dsu end) (dsuScore dsu)) [a; b] 1 = Some ([], state).
Proof.
  unfold invokeContract. rewrite (ltac:(easy) : stateAfterInteractions _ _ (repeat 0%Z 20) = BlockchainContract _ _ _ _ _ _). unfold funcdef_0__main at 2. rewrite !leftIdentity. unfold retrieve at 1. rewrite <- !bindAssoc. pose proof pushDispatch2 (λ _ : varsfuncdef_0__main, false) (λ _ : varsfuncdef_0__main, 0%Z) (λ _ : varsfuncdef_0__main, repeat 0%Z 20) (Retrieve arrayIndex0 (arrayType arrayIndex0 environment0) arraydef_0__hasBeenInitialized 0) as step. autorewrite with combined_unfold in step. rewrite step. clear step. autorewrite with advance_program. case_decide as h; simpl in h; [| lia]. rewrite !leftIdentity.
  unfold readByte at 1. rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte. case_decide as hs; [| simpl in hs; lia]. clear hs.
  rewrite !leftIdentity.
  unfold readByte at 1. rewrite bindDispatch pushDispatch2 unfoldInvoke_S_ReadByte. case_decide as hs; [| simpl in hs; lia]. rewrite !leftIdentity.
  assert (variableList : (update
              (update (fun=> 0%Z) vardef_0__unite_u
                 (nth (Z.to_nat 0) [a; b] 0%Z)) vardef_0__unite_v
              (nth (Z.to_nat 1) [a; b] 0%Z)) = fun x => match x with | vardef_0__unite_u => a | vardef_0__unite_v => b | _ => 0%Z end).
  { apply functional_extensionality_dep. intro x. destruct x; easy. } rewrite variableList. clear variableList.
  rewrite eliminateLift. unfold funcdef_0__unite. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 !leftIdentity eliminateLift. unfold funcdef_0__ancestor at 1. unfold numberLocalGet at 1. rewrite pushNumberGet2 pushNumberSet2 !leftIdentity loop_S !liftToWithinLoopBind -!bindAssoc dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 (ltac:(easy) : (update (update (fun=> 0%Z) vardef_0__ancestor_vertex a)
                    vardef_0__ancestor_work
                    (update (fun=> 0%Z) vardef_0__ancestor_vertex a
                       vardef_0__ancestor_vertex) vardef_0__ancestor_work) = a) !leftIdentity dropWithinLoopLiftToWithinLoop.
  unfold retrieve at 1. rewrite -!bindAssoc pushDispatch2 bindDispatch unfoldInvoke_S_Retrieve.
  case_decide as ht; [| reflexivity]. exfalso. rewrite lengthConvert hL in ht.
  unfold coerceInt in ht. rewrite Z.mod_small in ht. { lia. } lia.
Qed.

Lemma outOfBoundsInteraction1A (a b : Z) (hOOB : Z.le 100 a) (hUB : Z.lt a 256) : invokeContract (repeat 1%Z 20) (repeat 0%Z 20) 0%Z state state [a; b] 1 = Some ([], state).
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
  (ReadByte 0)) as step. autorewrite with combined_unfold in step. rewrite step. clear step. autorewrite with advance_program.  case_decide as h2; [| simpl in h2; lia]. pose proof pushDispatch2 (λ _ : varsfuncdef_0__main, false) (λ _ : varsfuncdef_0__main, 0%Z) (λ _ : varsfuncdef_0__main, repeat 0%Z 20) (DoBasicEffect arrayIndex0 (arrayType arrayIndex0 environment0) (ReadByte 1)) as step. autorewrite with combined_unfold in step. rewrite <- !bindAssoc, step. clear step. autorewrite with advance_program. rewrite !leftIdentity. rewrite (ltac:(easy) : (nth (Z.to_nat 0) [a; b] 0%Z) = a)  (ltac:(easy) : (nth (Z.to_nat 1) [a; b] 0%Z) = b). rewrite (ltac:(apply functional_extensionality_dep; intro x; destruct x; easy) : (update (update (λ _ : varsfuncdef_0__unite, 0%Z) vardef_0__unite_u a) vardef_0__unite_v b) = fun x => match x with | vardef_0__unite_u => a | vardef_0__unite_v => b | _ => 0%Z end).
  case_decide as h3; [| simpl in h3; lia].
  rewrite eliminateLift. unfold funcdef_0__unite. unfold numberLocalGet at 1. rewrite pushNumberGet2 pushDispatch2 unfoldInvoke_S_Retrieve. case_decide as hs; [| reflexivity]. exfalso. rewrite (ltac:(easy) : (update (update (fun=> 0%Z) vardef_0__ancestor_vertex a)
           vardef_0__ancestor_work
           (update (fun=> 0%Z) vardef_0__ancestor_vertex a
              vardef_0__ancestor_vertex) vardef_0__ancestor_work) = a) in hs.
  simpl in *. unfold coerceInt in hs. rewrite Z.mod_small in hs. { lia. } lia.
Qed.

Lemma outOfBoundsInteractionNB (a b : Z) (hLA : Z.le 0 a) (hUA : Z.lt a 256) (hOOB : Z.le 100 b) (hUB : Z.lt b 256) (dsu : list Slot) (hL : length dsu = 100) (hL1 : Z.to_nat (dsuLeafCount dsu) = length dsu) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) : invokeContract (repeat 1%Z 20) (repeat 0%Z 20) 0%Z state (stateAfterInteractions (fun x => match x with | arraydef_0__result => [0%Z] | arraydef_0__hasBeenInitialized => [1%Z] | arraydef_0__dsu => convertToArray dsu end) (dsuScore dsu)) [a; b] 1 = Some ([], state).
Proof.
  destruct (decide (Z.le 100 a)) as [hy | hy].
  { apply outOfBoundsInteractionNA; assumption. }
  unfold invokeContract. rewrite (ltac:(easy) : stateAfterInteractions _ _ (repeat 0%Z 20) = BlockchainContract _ _ _ _ _ _). unfold funcdef_0__main at 2. rewrite !leftIdentity. unfold retrieve at 1. rewrite <- !bindAssoc. pose proof pushDispatch2 (λ _ : varsfuncdef_0__main, false) (λ _ : varsfuncdef_0__main, 0%Z) (λ _ : varsfuncdef_0__main, repeat 0%Z 20) (Retrieve arrayIndex0 (arrayType arrayIndex0 environment0) arraydef_0__hasBeenInitialized 0) as step. autorewrite with combined_unfold in step. rewrite step. clear step. autorewrite with advance_program. case_decide as h; simpl in h; [| lia]. rewrite !leftIdentity.
  unfold readByte at 1. rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte. case_decide as hs; [| simpl in hs; lia]. clear hs.
  rewrite !leftIdentity.
  unfold readByte at 1. rewrite bindDispatch pushDispatch2 unfoldInvoke_S_ReadByte. case_decide as hs; [| simpl in hs; lia]. rewrite !leftIdentity.
  assert (variableList : (update
              (update (fun=> 0%Z) vardef_0__unite_u
                 (nth (Z.to_nat 0) [a; b] 0%Z)) vardef_0__unite_v
              (nth (Z.to_nat 1) [a; b] 0%Z)) = fun x => match x with | vardef_0__unite_u => a | vardef_0__unite_v => b | _ => 0%Z end).
  { apply functional_extensionality_dep. intro x. destruct x; easy. } rewrite variableList. clear variableList.
  rewrite eliminateLift. unfold funcdef_0__unite. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 !leftIdentity eliminateLift -!bindAssoc runAncestor; try (assumption || lia). unfold retrieve at 1. rewrite pushDispatch2 bindDispatch unfoldInvoke_S_Retrieve.
  case_decide as ht; [| simpl in ht; lia]. unfold numberLocalSet at 1. rewrite pushNumberSet2. unfold numberLocalGet at 1. rewrite pushNumberGet2 !leftIdentity eliminateLift. unfold funcdef_0__ancestor. rewrite (ltac:(easy) : (update
           (λ _0 : varsfuncdef_0__unite,
              match _0 with
              | vardef_0__unite_u => a
              | vardef_0__unite_v => b
              | vardef_0__unite_z => 0%Z
              end) vardef_0__unite_u
           (nth_lt [Z.of_nat (ancestor dsu (length dsu) (Z.to_nat a))]
              (Z.to_nat 0) ht) vardef_0__unite_v) = b).
  unfold numberLocalGet at 1. rewrite pushNumberGet2 pushNumberSet2 !leftIdentity loop_S !liftToWithinLoopBind -!bindAssoc dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 !leftIdentity (ltac:(easy) : (update (update (fun=> 0%Z) vardef_0__ancestor_vertex b)
                    vardef_0__ancestor_work
                    (update (fun=> 0%Z) vardef_0__ancestor_vertex b
                       vardef_0__ancestor_vertex) vardef_0__ancestor_work) = b).
  unfold coerceInt at 1. rewrite Z.mod_small. { lia. }
  rewrite dropWithinLoopLiftToWithinLoop. unfold retrieve at 1. rewrite -!bindAssoc pushDispatch2 unfoldInvoke_S_Retrieve. case_decide as hu; [| reflexivity]. exfalso. rewrite lengthConvert pathCompressPreservesLength in hu. lia.
Qed.

Lemma outOfBoundsInteraction1B (a b : Z) (hLA : Z.le 0 a) (hUA : Z.lt a 256) (hOOB : Z.le 100 b) (hUB : Z.lt b 256) : invokeContract (repeat 1%Z 20) (repeat 0%Z 20) 0%Z state state [a; b] 1 = Some ([], state).
Proof.
  destruct (decide (Z.le 100 a)) as [hy | hy].
  { apply outOfBoundsInteraction1A; lia. }
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
  (ReadByte 0)) as step. autorewrite with combined_unfold in step. rewrite step. clear step. autorewrite with advance_program.  case_decide as h2; [| simpl in h2; lia]. pose proof pushDispatch2 (λ _ : varsfuncdef_0__main, false) (λ _ : varsfuncdef_0__main, 0%Z) (λ _ : varsfuncdef_0__main, repeat 0%Z 20) (DoBasicEffect arrayIndex0 (arrayType arrayIndex0 environment0) (ReadByte 1)) as step. autorewrite with combined_unfold in step. rewrite <- !bindAssoc, step. clear step. autorewrite with advance_program. rewrite !leftIdentity. rewrite (ltac:(easy) : (nth (Z.to_nat 0) [a; b] 0%Z) = a)  (ltac:(easy) : (nth (Z.to_nat 1) [a; b] 0%Z) = b). rewrite (ltac:(apply functional_extensionality_dep; intro x; destruct x; easy) : (update (update (λ _ : varsfuncdef_0__unite, 0%Z) vardef_0__unite_u a) vardef_0__unite_v b) = fun x => match x with | vardef_0__unite_u => a | vardef_0__unite_v => b | _ => 0%Z end).
  case_decide as h3; [| simpl in h3; lia].
  rewrite eliminateLift. unfold funcdef_0__unite.
  unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 !leftIdentity eliminateLift -!bindAssoc.
  assert (hR : repeat 255%Z 100 = convertToArray (repeat (Ancestor Unit) 100)). { reflexivity. } rewrite hR runAncestor; try (reflexivity || lia). { intros x y z. rewrite nth_repeat in z. easy. } { rewrite withoutCyclesNIffWithoutCyclesBool. reflexivity. }
  unfold retrieve at 1. rewrite pushDispatch2 bindDispatch unfoldInvoke_S_Retrieve. case_decide as hv; [| reflexivity].
  rewrite (ltac:(easy) : (nth_lt
           [Z.of_nat
              (ancestor (repeat (Ancestor Unit) 100)
                 (length (repeat (Ancestor Unit) 100)) 
                 (Z.to_nat a))] (Z.to_nat 0) hv) = Z.of_nat
              (ancestor (repeat (Ancestor Unit) 100)
                 (length (repeat (Ancestor Unit) 100)) 
                 (Z.to_nat a))).
  unfold numberLocalSet at 1. rewrite pushNumberSet2. unfold numberLocalGet at 1. rewrite pushNumberGet2 !leftIdentity (ltac:(easy) : (update
                 (λ _0 : varsfuncdef_0__unite,
                    match _0 with
                    | vardef_0__unite_u => a
                    | vardef_0__unite_v => b
                    | vardef_0__unite_z => 0%Z
                    end) vardef_0__unite_u
                 (Z.of_nat
                    (ancestor (repeat (Ancestor Unit) 100)
                       (length (repeat (Ancestor Unit) 100)) 
                       (Z.to_nat a))) vardef_0__unite_v) = b) eliminateLift -!bindAssoc.
  unfold funcdef_0__ancestor. unfold numberLocalGet at 1. rewrite pushNumberGet2 pushNumberSet2 !leftIdentity loop_S !liftToWithinLoopBind -!bindAssoc dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite -!bindAssoc pushNumberGet2 (ltac:(easy) : (update (update (fun=> 0%Z) vardef_0__ancestor_vertex b)
                    vardef_0__ancestor_work
                    (update (fun=> 0%Z) vardef_0__ancestor_vertex b
                       vardef_0__ancestor_vertex) vardef_0__ancestor_work) = b) !leftIdentity.
  rewrite dropWithinLoopLiftToWithinLoop. unfold retrieve at 1. rewrite -!bindAssoc pushDispatch2. unfold coerceInt at 1.
  rewrite Z.mod_small. { lia. }
  rewrite bindDispatch unfoldInvoke_S_Retrieve. case_decide as hm; [| reflexivity]. exfalso. rewrite lengthConvert !pathCompressPreservesLength repeat_length in hm. lia.
Qed.

Lemma firstInteraction (a b : Z) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) (hLe2 : Z.le 0 b) (hLt2 : Z.lt b 100) : invokeContract (repeat 1%Z 20) (repeat 0%Z 20) 0%Z state state [a; b] 1 = Some ([a; b], stateAfterInteractions (fun x => match x with | arraydef_0__result => [0%Z] | arraydef_0__hasBeenInitialized => [1%Z] | arraydef_0__dsu => convertToArray (unite (repeat (Ancestor Unit) 100) (Z.to_nat a) (Z.to_nat b)) end) (dsuScore (unite (repeat (Ancestor Unit) 100) (Z.to_nat a) (Z.to_nat b)))).
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
  (ReadByte 0)) as step. autorewrite with combined_unfold in step. rewrite step. clear step. autorewrite with advance_program.  case_decide as h2; [| simpl in h2; lia]. pose proof pushDispatch2 (λ _ : varsfuncdef_0__main, false) (λ _ : varsfuncdef_0__main, 0%Z) (λ _ : varsfuncdef_0__main, repeat 0%Z 20) (DoBasicEffect arrayIndex0 (arrayType arrayIndex0 environment0) (ReadByte 1)) as step. autorewrite with combined_unfold in step. rewrite <- !bindAssoc, step. clear step. autorewrite with advance_program. rewrite !leftIdentity. rewrite (ltac:(easy) : (nth (Z.to_nat 0) [a; b] 0%Z) = a)  (ltac:(easy) : (nth (Z.to_nat 1) [a; b] 0%Z) = b). rewrite (ltac:(apply functional_extensionality_dep; intro x; destruct x; easy) : (update (update (λ _ : varsfuncdef_0__unite, 0%Z) vardef_0__unite_u a) vardef_0__unite_v b) = fun x => match x with | vardef_0__unite_u => a | vardef_0__unite_v => b | _ => 0%Z end).
  case_decide as h3; [| simpl in h3; lia].
  assert (hR : convertToArray (repeat (Ancestor Unit) 100) = repeat (255%Z) 100).
  { reflexivity. } rewrite -hR.
  pose proof runUnite (ltac:(reflexivity) : length (repeat (Ancestor Unit) 100) = 100) ltac:(reflexivity) ltac:(intros x y z; rewrite nth_repeat in z; easy) ltac:(rewrite withoutCyclesNIffWithoutCyclesBool; easy) hLe1 hLt1 hLe2 hLt2 (arrays _ environment0) as step.
  assert (hS : (stateAfterInteractions (arrays arrayIndex0 environment0)
     (dsuScore (repeat (Ancestor Unit) 100))) = state).
  { apply functional_extensionality_dep. intro x. unfold stateAfterInteractions. unfold state. case_decide. { reflexivity. } case_decide. { reflexivity. } reflexivity. }
  rewrite hS in step. rewrite step. reflexivity.
Qed.

Lemma interactEqualsModelScore (x : list (Z * Z)) (hN : forall a b, In (a, b) x -> Z.le 0 a /\ Z.lt a 256 /\ Z.le 0 b /\ Z.lt b 256) : interact state x = modelScore x.
Proof.
  induction x as [| head tail IH]. { easy. }
  destruct head as [a b].
  pose proof hN a b ltac:(left; reflexivity) as [h1 [h2 [h3 h4]]].
  rewrite (ltac:(intros; simpl; reflexivity) : forall state, interact state ((a, b) :: tail) = _).
  fold (repeat 1%Z 20). fold (repeat 0%Z 20).
  unfold modelScore. rewrite ((ltac:(easy) : forall a b, a :: b = [a] ++ b) (a, b)) map_app (ltac:(easy) : map (λ _0 : Z * Z, let (_1, _2) := _0 in (Z.to_nat _1, Z.to_nat _2))
  [(a, b)] = [(Z.to_nat a, Z.to_nat b)]) -(ltac:(easy) : forall a b, a :: b = [a] ++ b). rewrite (ltac:(simpl; reflexivity) : dsuFromInteractions _ (_ :: _) = _).
  case_decide as hv; rewrite repeat_length in hv.
  - rewrite firstInteraction; try lia. admit.
  - destruct (ltac:(lia) : Z.le 100 a \/ Z.le 100 b) as [h5 | h5].
    + rewrite outOfBoundsInteraction1A; try assumption. apply IH. intros m1 m2 m3. apply hN. right. exact m3.
    + rewrite outOfBoundsInteraction1B; try assumption. apply IH. intros m1 m2 m3. apply hN. right. exact m3.
  (* can't directly do induction here, must use an auxiliary lemma *)
Admitted.
