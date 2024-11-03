From CoqCP Require Import Options Imperative DisjointSetUnion ListsEqual ExistsInRange SwapUpdate DisjointSetUnionCode.
From Generated Require Import DisjointSetUnion.
From stdpp Require Import numbers list.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Wellfounded.
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma runCompressLoop (dsu : list Slot) (hL : length dsu = 100) (hL1 : Z.to_nat (dsuLeafCount dsu) = length dsu) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (a : Z) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) communication whatever (n : nat) (hN : n <= 100) continuation : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state state communication
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
  rewrite jda. clear jda. rewrite runCompressLoop; try (assumption || lia). rewrite (ltac:(lia) : Z.to_nat 100 = length dsu). reflexivity.
Qed.

Lemma runUnite (dsu : list Slot) (hL : length dsu = 100) (hL1 : Z.to_nat (dsuLeafCount dsu) = length dsu) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (a b : Z) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) (hLe2 : Z.le 0 b) (hLt2 : Z.lt b 100) : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state
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
  - admit.
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
