From CoqCP Require Import Options Imperative DisjointSetUnion ListsEqual ExistsInRange.
From Generated Require Import DisjointSetUnion.
From stdpp Require Import numbers list.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Wellfounded.

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

Definition noIllegalIndices (dsu : list Slot) := forall x y, nth x dsu (Ancestor Unit) = ReferTo y -> y < length dsu.

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

Fixpoint ancestorChain (dsu : list Slot) (fuel : nat) (index : nat) :=
  match fuel with
  | O => [index]
  | S fuel => match nth index dsu (Ancestor Unit) with
    | ReferTo x => index :: ancestorChain dsu fuel x
    | Ancestor _ => index :: nil
    end
  end.

Lemma ancesterEqLastAncestorChain dsu fuel index : last (ancestorChain dsu fuel index) = Some (ancestor dsu fuel index).
Proof.
  induction fuel as [| fuel IH] in index |- *. { easy. }
  simpl. remember (nth index dsu (Ancestor Unit)) as x eqn:hX. destruct x as [x | x]; symmetry in hX.
  - rewrite last_cons. pose proof IH x as h. now rewrite h.
  - easy.
Qed.

Definition validChain (dsu : list Slot) (chain : list nat) := chain <> [] /\ nth 0 chain 0 < length dsu /\ forall index, S index < length chain -> nth (nth index chain 0) dsu (Ancestor Unit) = ReferTo (nth (S index) chain 0).

Definition validChainToAncestor (dsu : list Slot) (chain : list nat) := validChain dsu chain /\ exists x, nth (nth (length chain - 1) chain 0) dsu (Ancestor Unit) = Ancestor x.

Lemma pigeonhole (f : nat -> nat) (n : nat) (hImage : forall x, f x < n) : exists i j, i <> j /\ i < S n /\ j < S n /\ f i = f j.
Proof.
  induction n as [| n IH] in f, hImage |- *.
  { pose proof hImage 0. lia. }
  remember (existsInRange (S n) (fun x => bool_decide (f x = f (S n)))) as s eqn:hs. symmetry in hs. destruct s.
  - pose proof proj1 (existsInRangeMeaning _ _) (Is_true_true_2 _ hs) as [w [h1 h2]]. rewrite bool_decide_eq_true in h2. exists w. exists (S n). repeat split; try lia.
  - pose proof proj1 (notExistsInRangeMeaning _ _) (Is_true_false_2 _ hs) as step. unfold notExistsInRangeLogic in step. assert (step2 : forall x, x < S n -> f x <> f (S n)). { intros x h. pose proof step x ltac:(lia) as h2. case_bool_decide as h1. { exfalso. apply h2. easy. } assumption. }
    destruct (decide (n = 0)) as [h1 | h1].
    { pose proof hImage 0 as h2. pose proof hImage 1 as h3. subst n. exists 0, 1. split; lia. }
    pose proof IH (fun x => if decide (f x < f (S n)) then f x else f x - 1) ltac:(intro x; simpl; case_decide as h; [pose proof hImage (S n) as h'; lia | pose proof hImage x as h'; lia]) as [a [b [c [d [e g]]]]]. exists a, b. repeat split; try (assumption || lia). case_decide as h2; case_decide as h3; try assumption.
    + pose proof step2 b e. lia.
    + pose proof step2 a d. lia.
    + pose proof step2 b e. pose proof step2 a d. lia.
Qed.

Lemma pigeonholeOrdered (f : nat -> nat) (n : nat) (hImage : forall x, f x < n) : exists i j, i < j /\ i < S n /\ j < S n /\ f i = f j.
Proof.
  pose proof pigeonhole f n hImage as [a [b [c [d [e g]]]]].
  destruct (ltac:(lia) : a < b \/ b < a) as [h | h].
  - exists a, b. repeat split; assumption.
  - exists b, a. symmetry in g. repeat split; assumption.
Qed.

Lemma commonSubarrays (dsu : list Slot) chain (h2 : validChain dsu chain) (i j delta : nat) (hI : i < length chain) (hJ : j < length chain) (hIDelta : i + delta < length chain) (hJDelta : j + delta < length chain) (hEq : nth i chain 0 = nth j chain 0) : nth (i + delta) chain 0 = nth (j + delta) chain 0.
Proof.
  induction delta as [| delta IH].
  { now rewrite !Nat.add_0_r. }
  pose proof IH ltac:(lia) ltac:(lia) as h.
  pose proof h2 as [a [b c]].
  pose proof c (i + delta) ltac:(lia) as c1. pose proof c (j + delta) ltac:(lia) as c2. rewrite h in c1. symmetry in c1. pose proof eq_trans c1 c2 as c3. injection c3. rewrite !Nat.add_succ_r. intro h3. exact h3.
Qed.

Lemma validChainMaxLength (dsu : list Slot) chain (h1 : noIllegalIndices dsu) (h2 : validChainToAncestor dsu chain) : length chain <= length dsu.
Proof.
  assert (h : forall index, index < length chain -> nth index chain 0 < length dsu).
  { intro index. induction index as [| index IH]; intro h3.
    - pose proof h2 as [[_ [x _]] _]. exact x.
    - apply (h1 (nth index chain 0) (nth (S index) chain 0)). pose proof h2 as [[_ [_ x]] _]. exact (x index h3). }
  destruct (ltac:(lia) : length dsu = 0 \/ 0 < length dsu) as [hs | hs].
  { destruct h2 as [[e [f g]] [b c]]. lia. }
  assert (h3 : forall x : nat, nth x chain 0 < length dsu).
  { intro x. destruct (ltac:(lia) : length chain <= x \/ x < length chain) as [hd | hd]. { rewrite nth_overflow; lia. } apply h. exact hd. }
  pose proof pigeonholeOrdered (fun x => nth x chain 0) (length dsu) h3 as [a [b [c [d [e f]]]]].
  pose proof commonSubarrays dsu chain ltac:(pose proof h2 as [h4 _]; exact h4) a b (length chain - 1 - b) as g.
  pose proof (ltac:(lia) : length chain <= length dsu \/ length dsu < length chain) as [hd | hd]; [exact hd |].
  pose proof g ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) f as i. clear g. rewrite (ltac:(lia) : b + (length chain - 1 - b) = length chain - 1) in i.
  pose proof h2 as [[_ [_ g]] _]. pose proof g (a + (length chain - 1 - b)) ltac:(lia) as g1. rewrite i in g1. pose proof h2 as [_ [x g2]]. rewrite g1 in g2. easy.
Qed.

Lemma validChainLe (dsu : list Slot) chain (h1 : noIllegalIndices dsu) (h2 : validChainToAncestor dsu chain) fuel vertex (h3 : nth 0 chain 0 = vertex) (h4 : length chain <= fuel) : chain = ancestorChain dsu fuel vertex.
Proof.
  revert vertex h3 fuel h4.
  induction chain as [| head tail IH]; intros vertex h3 fuel h4.
  - pose proof h2 as [[e [f g]] [h i]]. exfalso. exact (e ltac:(reflexivity)).
  - pose proof h2 as [[e [f g]] [h i]]. destruct fuel as [| fuel]. { simpl in h4. lia. } simpl.
    destruct (decide (length tail = 0)) as [hs | hs].
    + pose proof nil_length_inv _ hs. subst tail. simpl in *. subst head. rewrite i. reflexivity.
    + pose proof g 0 ltac:(simpl in *; lia) as step. simpl in step. simpl in h3. subst head. rewrite step. pose proof (fun x => IH x (nth 0 tail 0) ltac:(reflexivity) fuel ltac:(simpl in *; lia)) as step2.
      assert (step3 : validChainToAncestor dsu tail).
      { repeat split. { intro step3. subst tail. exact (hs ltac:(reflexivity)). } { admit. } { intros a ha. pose proof g (S a) ltac:(simpl; lia) as step3. simpl in step3. exact step3. } { exists h. rewrite (ltac:(simpl; lia) : length (vertex :: tail) - 1 = S (length tail - 1)) in i. rewrite (ltac:(intros; simpl; reflexivity) : forall a b c d, nth (S a) (b :: c) d = nth a c d) in i. exact i. } }
    now rewrite <- (step2 step3).
Qed.

Lemma validChainTake (dsu : list Slot) chain (h1 : noIllegalIndices dsu) (h2 : validChainToAncestor dsu chain) fuel vertex (h3 : nth 0 chain 0 = vertex) : take (S fuel) chain = ancestorChain dsu fuel vertex.
Proof.
  induction fuel as [| fuel IH].
  { destruct chain as [| head tail].
    - destruct h2 as [[e [f g]] [b c]]. exfalso. exact (e ltac:(reflexivity)).
    - simpl in *. rewrite take_0, h3. reflexivity. }
  pose proof take_S_r chain (S fuel) (nth (S fuel) chain 0) as h4.
  pose proof nth_lookup_or_length chain (S fuel) 0 as [h5 | h5].
  - rewrite (h4 h5), IH. pose proof lookup_lt_Some _ _ _ h5 as h6.
    assert (h7 : forall delta, S fuel + delta < length chain -> ancestorChain dsu fuel (nth delta chain 0) ++ [nth (S fuel + delta) chain 0] = ancestorChain dsu (S fuel) (nth delta chain 0)).
    { revert h2. clear. intro h2. induction fuel as [| fuel IH]; intros delta h7.
      - simpl. pose proof h2 as [[e [f g]] [b c]]. rewrite g; [| lia]. reflexivity.
      - rewrite (ltac:(simpl; reflexivity) : ancestorChain _ (S _) _ = _). pose proof h2 as [[e [f g]] [b c]]. rewrite g; [| lia]. rewrite (ltac:(intros; listsEqual) : forall a b c, (a :: b) ++ [c] = a :: (b ++ [c])), (ltac:(lia) : S (S fuel) + delta = S fuel + S delta), IH; [| lia]. rewrite (ltac:(intro x; simpl; reflexivity) : forall x, ancestorChain _ (S x) (nth delta chain 0) = _). rewrite g; [| lia]. reflexivity. }
    pose proof h7 0 ltac:(lia). rewrite (ltac:(easy) : forall x, x + 0 = x) in *. subst vertex. assumption.
  - rewrite firstn_all2; [| lia].
    
Qed.

Lemma ancestorLtLength dsu (h : noIllegalIndices dsu) n index (h1 : index < length dsu) : ancestor dsu n index < length dsu.
Proof.
  induction n as [| n IH] in h1, index |- *; [easy |].
  simpl. remember (nth index dsu (Ancestor Unit)) as x eqn:hX. symmetry in hX. destruct x as [x | x].
  - pose proof h _ _ hX. apply IH. lia.
  - exact h1.
Qed.

Definition withoutCyclesN (dsu : list Slot) (n : nat) :=
  forall x, x < n -> match nth (ancestor dsu (length dsu) x) dsu (Ancestor Unit) with
  | Ancestor _ => true
  | _ => false
  end.

Fixpoint withoutCyclesBool (dsu : list Slot) (n : nat) : bool :=
  match n with
  | O => true
  | S n => match nth (ancestor dsu (length dsu) n) dsu (Ancestor Unit) with
    | Ancestor _ => withoutCyclesBool dsu n
    | _ => false
    end
  end.

Lemma withoutCyclesNIffWithoutCyclesBool dsu n : withoutCyclesN dsu n <-> withoutCyclesBool dsu n.
Proof.
  induction n as [| n IH].
  - simpl. unfold withoutCyclesN. split; intros; lia.
  - split; intro h.
  { rewrite (ltac:(easy) : withoutCyclesBool dsu (S n) = match nth (ancestor dsu (length dsu) n) dsu (Ancestor Unit) with
    | Ancestor _ => withoutCyclesBool dsu n
    | _ => false
    end).
    pose proof h n ltac:(lia) as step. destruct (nth (ancestor dsu (length dsu) n) dsu (Ancestor Unit)) as [h3 |]; [contradiction; exact h3 |]. rewrite <- IH. intros x y. pose proof h x ltac:(lia). assumption. }
  { rewrite (ltac:(easy) : withoutCyclesBool dsu (S n) = match nth (ancestor dsu (length dsu) n) dsu (Ancestor Unit) with
    | Ancestor _ => withoutCyclesBool dsu n
    | _ => false
    end) in h. intros x y. destruct (ltac:(lia) : x = n \/ x < n) as [h2 | h2]. { rewrite h2. destruct (nth (ancestor dsu (length dsu) n) dsu (Ancestor Unit)) as [h3 | h3]; [assumption |]. easy. } destruct (nth (ancestor dsu (length dsu) n) dsu (Ancestor Unit)) as [h1 |]; [contradiction; exact h1 |]. rewrite <- IH in h. pose proof h x ltac:(lia). assumption. }
Qed.

Lemma ancestorInsert (dsu : list Slot) (fuel : nat) (u x : nat) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (h3 : u < length dsu) (h4 : x < length dsu) (h5 : match nth x dsu (Ancestor Unit) with | ReferTo _ => true | Ancestor _ => false end) : ancestor dsu (length dsu) (ancestor dsu fuel u) = ancestor (<[x:=ReferTo (ancestor dsu (length dsu) x)]> dsu) (length dsu) (ancestor (<[x:=ReferTo (ancestor dsu fuel x)]> dsu) fuel u).
Proof.
Qed.

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

Lemma pathCompressPreservesLength (dsu : list Slot) (n a b : nat) : length (pathCompress dsu n a b) = length dsu.
Proof.
  induction n as [| n IH] in dsu, a |- *; [easy |].
  simpl. destruct (nth a dsu (Ancestor Unit)) as [x | x]; [| easy]. rewrite IH. apply insert_length.
Qed.

Lemma pathCompressPreservesLeafCount (dsu : list Slot) (n a b : nat) : dsuLeafCount (pathCompress dsu n a b) = dsuLeafCount dsu.
Proof.
  induction n as [| n IH] in dsu, a |- *. { easy. }
  simpl. remember (nth a dsu (Ancestor Unit)) as x eqn:hX. symmetry in hX. destruct x as [x | x]; [| reflexivity].
  rewrite (IH (<[a := ReferTo b]> dsu) x). clear IH n. destruct (decide (length dsu <= a)) as [hL | hL]. { rewrite list_insert_ge; lia. } rewrite insert_take_drop; [| lia]. unfold dsuLeafCount. apply inj_eq. rewrite map_app, list_sum_app. simpl. rewrite (ltac:(lia) : forall a b, a + b = a + 0 + b). rewrite (ltac:(easy) : 0 = list_sum (map (fun x => match x with | ReferTo x => 0 | Ancestor x => leafCount x end) [ReferTo x])) at 1. rewrite <- hX, <- !list_sum_app, <- !map_app.
  assert (H1 : forall (T : Type) (l : list T) i default (H : i < length l), take i l ++ [nth i l default] = take (S i) l).
  { clear. intros T l i default H.
    revert H. revert l. induction i as [| i IHi]; intros l H.
    - rewrite take_0. destruct l; simpl in *; try lia. rewrite take_0. reflexivity.
    - destruct l; simpl in H; try lia.
      simpl. rewrite IHi; try lia. reflexivity. }
  rewrite H1; [| lia]. rewrite take_drop. reflexivity.
Qed.

Lemma pathCompressPreservesWithoutCycles (dsu : list Slot) (h : withoutCyclesN dsu (length dsu)) (h1 : noIllegalIndices dsu) (n u : nat) (hU : u < length dsu) : withoutCyclesN (pathCompress dsu n u (ancestor dsu (length dsu) u)) (length dsu).
Proof.
  induction n as [| n IH] in u, dsu, h, hU, h1 |- *. { simpl. assumption. }
  simpl. remember (nth u dsu (Ancestor Unit)) as x eqn:hX. destruct x as [x | x]; [| easy]. pose proof (fun t => IH (<[u:=ReferTo (ancestor dsu (length dsu) u)]> dsu) t ltac:(intros v1 v2; destruct (decide (v1 = u)) as [h2 | h2]; [destruct (decide (length dsu <= u)); [rewrite list_insert_ge; [| lia]; intro h3; rewrite h2 in h3; rewrite <- hX in h3; injection h3; intro h4; subst x; subst u; exact (h1 v1 v2 ltac:(symmetry in hX; exact hX)) | pose proof list_lookup_insert dsu u (ReferTo (ancestor dsu (length dsu) u)) ltac:(lia) as step; pose proof nth_lookup_Some _ _ (Ancestor Unit) _ step as step2; subst u; rewrite step2; pose proof ancestorLtLength dsu h1 (length dsu) v1 ltac:(lia) as step3]; intro h3; injection h3; intro h4; rewrite insert_length | pose proof list_lookup_insert_ne dsu u v1 (ReferTo (ancestor dsu (length dsu) u)) ltac:(lia) as step; pose proof nth_lookup dsu v1 (Ancestor Unit) as step1; pose proof (nth_lookup (<[u:=ReferTo (ancestor dsu (length dsu) u)]> dsu) v1 (Ancestor Unit)) as step2; rewrite step in step2; rewrite <- step1 in step2; rewrite step2; intro step3; rewrite insert_length; exact (h1 v1 v2 step3)]; lia) x ltac:(rewrite insert_length; exact (h1 u x ltac:(symmetry; assumption)))) as step. rewrite !insert_length in step.
  assert (step1 : u < length dsu -> x < length dsu -> ancestor (<[u:=ReferTo (ancestor dsu (length dsu) u)]> dsu) (length dsu) x = ancestor dsu (length dsu) x).
  { clear. }
Qed.

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
