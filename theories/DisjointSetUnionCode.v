From CoqCP Require Import Options Imperative DisjointSetUnion ListsEqual ExistsInRange SwapUpdate.
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

Lemma nthConvert (x : list Slot) (n : nat) (hN : n < length x) : nth n (convertToArray x) (0%Z) = match nth n x (Ancestor Unit) with | ReferTo c => Z.of_nat c | Ancestor c => Z.sub 256%Z (Z.of_nat (leafCount c)) end.
Proof.
  revert n hN. induction x as [| head tail IH]; intros n hN.
  { simpl in hN. lia. }
  destruct n as [| n].
  - simpl. destruct head; reflexivity.
  - rewrite -> (ltac:(destruct head; reflexivity) : nth (S n) (convertToArray (head :: tail)) 0%Z = nth n (convertToArray tail) 0%Z), (ltac:(simpl; reflexivity) : nth (S _) (_ :: _) _ = _). apply IH. simpl in hN. lia.
Qed.

Lemma insertConvertReferTo (x : list Slot) (n : nat) (hN : n < length x) (v : Z) (hU : Z.le 0 v) : <[n := v]> (convertToArray x) = convertToArray (<[n := ReferTo (Z.to_nat v)]> x).
Proof.
  revert n hN. induction x as [| head tail IH]; intros n hN.
  { simpl in hN. lia. }
  destruct n as [| n].
  - simpl. destruct head; simpl; rewrite Z2Nat.id; try lia; reflexivity.
  - simpl. destruct head; simpl; rewrite IH; try reflexivity; simpl in hN; lia.
Qed.

Lemma insertConvertAncestor (x : list Slot) (n : nat) (hN : n < length x) (v : Tree) : <[n := (256 - Z.of_nat (leafCount v))%Z]> (convertToArray x) = convertToArray (<[n := Ancestor v]> x).
Proof.
  revert n hN. induction x as [| head tail IH]; intros n hN. { simpl in hN. lia. }
  destruct n as [| n].
  - simpl. destruct head; simpl; reflexivity.
  - simpl. destruct head; simpl; rewrite IH; try reflexivity; simpl in hN; lia.
Qed.

Lemma lengthConvert (dsu : list Slot) : length (convertToArray dsu) = length dsu.
Proof.
  induction dsu as [| [|] tail IH]; [easy | |]; simpl; now rewrite IH.
Qed.

Lemma nthUpperBoundConvertAux (dsu : list Slot) (h : length dsu < 256) (h1 : forall x y, nth x dsu (Ancestor Unit) = ReferTo y -> y < 256) (n : nat) : Z.lt (nth n (convertToArray dsu) (0%Z)) (256%Z).
Proof.
  revert n. induction dsu as [| [a | a] tail IH]; intro n; [destruct n; easy | |]; destruct n as [| n].
  - simpl. pose proof h1 0 a ltac:(easy). lia.
  - simpl. apply IH. { simpl in h; lia. } intros s t. pose proof h1 (S s) t as step. simpl in step. exact step.
  - simpl. pose proof oneLeqLeafCount a. lia.
  - simpl. apply IH. { simpl in h; lia. } intros s t. pose proof h1 (S s) t as step. simpl in step. exact step.
Qed.

Lemma nthUpperBoundConvert (dsu : list Slot) (h : length dsu < 256) (h1 : noIllegalIndices dsu) (n : nat) : Z.lt (nth n (convertToArray dsu) (0%Z)) (256%Z).
Proof.
  apply nthUpperBoundConvertAux; try assumption.
  intros a b c. pose proof h1 a b c. lia.
Qed.

Definition dsuScore (dsu : list Slot) := Z.of_nat (list_sum (map (fun x => match x with | ReferTo _ => 0 | Ancestor x => score x end) dsu)).

Definition dsuLeafCount (dsu : list Slot) := Z.of_nat (list_sum (map (fun x => match x with | ReferTo _ => 0 | Ancestor x => leafCount x end) dsu)).

Lemma sumTwoAncestors' (dsu : list Slot) (a b : nat) (hAB : a < b) (hB : b < length dsu) u (hA1 : nth a dsu (Ancestor Unit) = Ancestor u) v (hB1 : nth b dsu (Ancestor Unit) = Ancestor v) : leafCount u + leafCount v <= Z.to_nat (dsuLeafCount dsu).
Proof.
  pose proof ListDecomposition.listDecomposition dsu a b hAB hB (Ancestor Unit) as step. rewrite step. unfold dsuLeafCount. rewrite Nat2Z.id, !map_app, hA1, hB1, !list_sum_app. simpl. lia.
Qed.

Lemma sumTwoAncestors (dsu : list Slot) (a b : nat) (hAB : a <> b) (hA : a < length dsu) (hB : b < length dsu) u (hA1 : nth a dsu (Ancestor Unit) = Ancestor u) v (hB1 : nth b dsu (Ancestor Unit) = Ancestor v) : leafCount u + leafCount v <= Z.to_nat (dsuLeafCount dsu).
Proof.
  destruct (ltac:(lia) : a < b \/ b < a) as [hs | hs]; [| rewrite Nat.add_comm].
  - apply (sumTwoAncestors' _ a b); assumption.
  - apply (sumTwoAncestors' _ b a); assumption.
Qed.

Lemma nthLowerBoundConvertAuxStep (dsu : list Slot) (h : length dsu < 256) (h1 : Z.to_nat (dsuLeafCount dsu) < 128) (n : nat) (hn : n < length dsu) x (h2 : nth n dsu (Ancestor Unit) = Ancestor x) : leafCount x < 128.
Proof.
  revert n hn x h2. induction dsu as [| head tail IH].
  { simpl. intro. lia. }
  intros n h2 h3 h4.
  destruct n as [| n].
  - simpl in h4. unfold dsuLeafCount in h1. rewrite -> Nat2Z.id, map_cons, (ltac:(simpl; reflexivity) : list_sum (_ :: _) = _ + list_sum _) in h1. rewrite h4 in h1. lia.
  - exact (IH ltac:(simpl in h; lia) ltac:(unfold dsuLeafCount in h1; rewrite Nat2Z.id in h1; rewrite -> map_cons, (ltac:(simpl; reflexivity) : list_sum (_ :: _) = _ + list_sum _) in h1; unfold dsuLeafCount; rewrite Nat2Z.id; lia) n ltac:(simpl in h2; lia) h3 ltac:(simpl in h4; exact h4)).
Qed.

Lemma nthLowerBoundConvertAux (dsu : list Slot) (h : length dsu < 256) (h1 : Z.to_nat (dsuLeafCount dsu) < 128) (n : nat) : Z.le 0%Z (nth n (convertToArray dsu) (0%Z)).
Proof.
  revert n h1. induction dsu as [| head tail IH].
  { cbv. intros a b. destruct a; easy. }
  intros [| a] b.
  - simpl. destruct head as [x | x]. { simpl. lia. }
    simpl. unfold dsuLeafCount in b. rewrite -> Nat2Z.id, map_cons, (ltac:(simpl; reflexivity) : list_sum (_ :: _) = _ + list_sum _) in b. lia.
  - rewrite (ltac:(simpl; destruct head; easy) : nth (S a) (convertToArray (head :: tail)) (0%Z) = nth a (convertToArray tail) (0%Z)).
    exact (IH ltac:(simpl in h; lia) a ltac:(unfold dsuLeafCount in b; rewrite -> Nat2Z.id, map_cons, (ltac:(simpl; reflexivity) : list_sum (_ :: _) = _ + list_sum _) in b; unfold dsuLeafCount; rewrite Nat2Z.id; lia)).
Qed.

Lemma nthLowerBoundConvert (dsu : list Slot) (h : length dsu < 128) (h1 : Z.to_nat (dsuLeafCount dsu) = length dsu) (n : nat) : Z.le 0%Z (nth n (convertToArray dsu) (0%Z)).
Proof. apply nthLowerBoundConvertAux; try (assumption || lia). Qed.

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

Lemma firstAncestorChain dsu fuel index : nth 0 (ancestorChain dsu fuel index) 0 = index.
Proof.
  destruct fuel as [| fuel]. { easy. }
  simpl. destruct (nth index _ _); easy.
Qed.

Lemma zeroLtLengthAncestorChain dsu fuel index : 0 < length (ancestorChain dsu fuel index).
Proof.
  destruct fuel as [| fuel]. { simpl. lia. }
  simpl. destruct (nth index _ _); cbv; lia.
Qed.


Lemma ancestorEqLastAncestorChain' dsu fuel index : last (ancestorChain dsu fuel index) = Some (ancestor dsu fuel index).
Proof.
  induction fuel as [| fuel IH] in index |- *. { easy. }
  simpl. remember (nth index dsu (Ancestor Unit)) as x eqn:hX. destruct x as [x | x]; symmetry in hX.
  - rewrite last_cons. pose proof IH x as h. now rewrite h.
  - easy.
Qed.

Lemma defaultLast {A : Type} (l : list A) (d : A) : default d (last l) = nth (length l - 1) l d.
Proof.
  induction l as [| head tail IH]. { easy. }
  simpl. rewrite last_cons. rewrite Nat.sub_0_r.
  destruct tail as [| head' tail'].
  { easy. } rewrite -> (ltac:(simpl; reflexivity) : length (_ :: _) = _) in *. rewrite (ltac:(lia) : S (length tail') - 1 = length tail') in IH. rewrite <- IH.
  assert (h : last (head' :: tail') <> None).
  { rewrite last_cons. destruct (last tail'); easy. }
  destruct (last (head' :: tail')) as [x |]. { reflexivity. } easy.
Qed.

Lemma ancestorEqLastAncestorChain dsu fuel index : nth (length (ancestorChain dsu fuel index) - 1) (ancestorChain dsu fuel index) 0 = ancestor dsu fuel index.
Proof.
  pose proof defaultLast (ancestorChain dsu fuel index) 0 as h. rewrite ancestorEqLastAncestorChain' in h. simpl in h. symmetry. exact h.
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

Lemma chainElementsValidIndices (dsu : list Slot) chain (h1 : noIllegalIndices dsu) (h2 : validChainToAncestor dsu chain) index (h3 : index < length chain) : nth index chain 0 < length dsu.
Proof.
  induction index as [| index IH].
  - pose proof h2 as [[_ [x _]] _]. exact x.
  - apply (h1 (nth index chain 0) (nth (S index) chain 0)). pose proof h2 as [[_ [_ x]] _]. exact (x index h3).
Qed.

Lemma validChainPairwiseDifferent (dsu : list Slot) chain (h1 : noIllegalIndices dsu) (h2 : validChainToAncestor dsu chain) (i j : nat) (h4 : i <> j) (h5 : i < length chain) (h3 : j < length chain) : nth i chain 0 <> nth j chain 0.
Proof.
  assert (wlog : forall i j, i < j -> i < length chain -> j < length chain -> nth i chain 0 <> nth j chain 0).
  { revert h1 h2. clear. intros h1 h2 i j h3 h4 h5 h6.
    destruct h2 as [[e [f g]] [b c]].
    pose proof commonSubarrays dsu chain ltac:(repeat split; assumption) i j (length chain - 1 - j) h4 h5 ltac:(lia) ltac:(lia) h6 as step. pose proof (ltac:(destruct chain; simpl in *; lia) : 0 < length chain).
    rewrite (ltac:(lia) : j + (length chain - 1 - j) = length chain - 1) in step. rewrite <- step in c.
    rewrite (g (i + (length chain - 1 - j)) ltac:(lia)) in c. easy. }
  destruct (ltac:(lia) : i < j \/ j < i) as [h | h].
  - apply wlog; assumption.
  - intro g. symmetry in g. revert g. apply wlog; assumption.
Qed.

Lemma validChainMaxLength (dsu : list Slot) chain (h1 : noIllegalIndices dsu) (h2 : validChainToAncestor dsu chain) : length chain <= length dsu.
Proof.
  assert (h : forall index, index < length chain -> nth index chain 0 < length dsu).
  { apply chainElementsValidIndices; assumption. }
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
      { repeat split. { intro step3. subst tail. exact (hs ltac:(reflexivity)). } { pose proof chainElementsValidIndices dsu (vertex :: tail) h1 h2 1 ltac:(simpl; lia) as step3. simpl in step3. exact step3. } { intros a ha. pose proof g (S a) ltac:(simpl; lia) as step3. simpl in step3. exact step3. } { exists h. rewrite (ltac:(simpl; lia) : length (vertex :: tail) - 1 = S (length tail - 1)) in i. rewrite (ltac:(intros; simpl; reflexivity) : forall a b c d, nth (S a) (b :: c) d = nth a c d) in i. exact i. } }
    now rewrite <- (step2 step3).
Qed.

Lemma nthZeroAncestorChain (dsu : list Slot) fuel vertex : nth 0 (ancestorChain dsu fuel vertex) 0 = vertex.
Proof.
  destruct fuel as [| fuel].
  - simpl. reflexivity.
  - rewrite (ltac:(intros; simpl; reflexivity) : forall fuel, ancestorChain dsu (S fuel) vertex = _). destruct (nth vertex dsu (Ancestor Unit)); easy.
Qed.

Lemma validChainAncestorChain (dsu : list Slot) fuel vertex (hVertex : vertex < length dsu) (hDsu : noIllegalIndices dsu) : validChain dsu (ancestorChain dsu fuel vertex).
Proof.
  induction fuel as [| fuel IH] in hVertex, vertex |- *.
  { simpl. repeat split. { easy. } { simpl. lia. } { intros x h. simpl in h. lia. } }
  repeat split.
  - simpl. destruct (nth vertex dsu (Ancestor Unit)); easy.
  - rewrite nthZeroAncestorChain. exact hVertex.
  - intros x h. simpl. remember (nth vertex dsu (Ancestor Unit)) as e eqn:he. symmetry in he. destruct e as [e | e].
    + simpl. destruct x as [| x]. { rewrite nthZeroAncestorChain. exact he. }
      pose proof hDsu _ _ he as hf. pose proof IH _ hf as [g1 [g2 g3]].
      simpl in h. rewrite he in h. simpl in h. exact (g3 x ltac:(lia)).
    + simpl in h. rewrite he in h. simpl in h. lia.
Qed.

Lemma validChainAncestorLength (dsu : list Slot) chain (h1 : noIllegalIndices dsu) (h2 : validChainToAncestor dsu chain) vertex (h3 : nth 0 chain 0 = vertex) : chain = ancestorChain dsu (length dsu) vertex.
Proof. apply validChainLe; try assumption. apply validChainMaxLength; assumption. Qed.

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
    exact (validChainLe dsu chain h1 h2 (S fuel) vertex h3 h5).
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

Lemma ancestorReferTo (dsu : list Slot) (u v : nat) (hU : u < length dsu) (h : noIllegalIndices dsu) (h' : withoutCyclesN dsu (length dsu)) (hR : nth u dsu (Ancestor Unit) = ReferTo v) : ancestor dsu (length dsu) u = ancestor dsu (length dsu) v.
Proof.
  rewrite <- !ancestorEqLastAncestorChain.
  pose proof h u v hR as hV.
  assert (hL : 0 < length dsu).
  { destruct dsu as [| head tail]. { simpl in hR. easy. }
    simpl. lia.  }
  rewrite (ltac:(lia) : length dsu = S (length dsu - 1)) at 1. simpl. rewrite hR. rewrite (ltac:(lia) : length dsu = S (length dsu - 1)) at 2. simpl. rewrite hR, Nat.sub_0_r.
  pose proof h' u hU as hB. rewrite <- ancestorEqLastAncestorChain in hB. rewrite (ltac:(lia) : length dsu = S (length dsu - 1)) in hB. simpl in hB. rewrite hR in hB. simpl in hB. rewrite Nat.sub_0_r in hB.
  pose proof zeroLtLengthAncestorChain dsu (length dsu - 1) v as hA.
  rewrite ((ltac:(lia) : forall a, 0 < a -> a = S (a - 1)) _ hA) in *. simpl. remember (nth
    (nth (length (ancestorChain dsu (length dsu - 1) v) - 1)
       (ancestorChain dsu (length dsu - 1) v) 0) dsu 
    (Ancestor Unit)) as e eqn:he. destruct e as [e | e]. { easy. }
  symmetry in he.
  rewrite (fun i => validChainAncestorLength dsu (ancestorChain dsu (length dsu - 1) v) h i v ltac:(apply firstAncestorChain)). { reflexivity. }
  split.
  - apply validChainAncestorChain; assumption.
  - exists e. exact he.
Qed.

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

Lemma ancestorChainInsertNotPresent (dsu : list Slot) (fuel : nat) (u x : nat) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (h3 : u < length dsu) (h4 : x < length dsu) (h5 : match nth x dsu (Ancestor Unit) with | ReferTo _ => true | Ancestor _ => false end) (hd : ∀ _0 : nat, _0 < length (ancestorChain dsu (length dsu) u) → nth _0 (ancestorChain dsu (length dsu) u) 0 ≠ x) : ancestorChain dsu fuel u = ancestorChain (<[x:=ReferTo (ancestor dsu (length dsu) x)]> dsu) fuel u.
Proof.
  revert h3 hd. revert u. induction fuel as [| fuel IH]; intros u h3 hd. { easy. }
  simpl. pose proof hd 0 ltac:(destruct (length dsu); simpl; destruct (nth u dsu (Ancestor Unit)); simpl; try lia) as step1.
  assert (step2 : nth 0 (ancestorChain dsu (length dsu) u) 0 = u).
  { destruct (length dsu); [reflexivity |]. simpl. destruct (nth u dsu (Ancestor Unit)); easy. }
  rewrite step2 in step1. clear step2. pose proof list_lookup_insert_ne dsu x u (ReferTo (ancestor dsu (length dsu) x)) ltac:(intro hh; subst x; exact (step1 ltac:(reflexivity))) as step2.
  pose proof (ltac:(intros a b h; subst a; reflexivity): forall a b, a = b -> default (Ancestor Unit) a = default (Ancestor Unit) b) _ _ step2 as step3. rewrite <- !nth_lookup in step3. rewrite step3.
  remember (nth u dsu (Ancestor Unit)) as s eqn:hs. symmetry in hs. destruct s as [s | s]; [| reflexivity]. rewrite <- IH. { reflexivity. }
  - exact (h1 u s hs).
  - intros y hy. pose proof hd (S y) as step4. remember (ancestorChain dsu (length dsu) u) as toChop eqn:hC. symmetry in hC. destruct toChop as [| head tail]. { destruct (length dsu); simpl in hC; [easy |]. destruct (nth u dsu (Ancestor Unit)); simpl in hC; easy. }
    assert (hz : head = u). { destruct (length dsu); simpl in hC; [easy |]. destruct (nth u dsu (Ancestor Unit)); simpl in hC; try easy. inversion hC. reflexivity. } subst head. simpl in step4.
    pose proof validChainAncestorChain dsu (length dsu) u h3 h1 as [a [b c]].
    assert (hL : 1 < length dsu).
    { destruct (decide (length dsu = 0)) as [g | g].
      { pose proof nil_length_inv _ g. subst dsu. simpl in *. easy. }
      destruct (decide (length dsu = 1)) as [g1 | g1].
      { destruct dsu as [| head taill]. { simpl in g1. easy. }
        simpl in g1. pose proof nil_length_inv taill ltac:(lia). subst taill.
        pose proof (ltac:(simpl in *; lia) : u = 0). subst u. pose proof h1 0 s hs as g2. simpl in g2.
        pose proof (ltac:(lia) : s = 0). subst s. pose proof h2 0 ltac:(simpl; lia) as g3. simpl in hs. subst head. simpl in g3. exfalso. exact g3. } lia. }
    assert (hA : 1 < length (ancestorChain dsu (length dsu) u)).
    { assert (hS : exists x, length dsu = S (S (x))). { exists (length dsu - 2). lia. }
      destruct hS as [v vv]. rewrite vv. simpl. rewrite hs. destruct (nth s dsu (Ancestor Unit)); simpl; lia. }
    pose proof c 0 hA as hQ. rewrite hC in hQ. simpl in hQ. rewrite hs in hQ. injection hQ. clear hQ. intro hQ.
    pose proof (fun x => validChainAncestorLength dsu tail h1 x s ltac:(symmetry; exact hQ)) as step5.
    assert (hh : 0 < length tail).
    { rewrite hC in hA. simpl in hA. lia. }
    assert (step6 : validChainToAncestor dsu tail).
    { repeat split.
      - rewrite hC in hA. simpl in hA. intro cc. rewrite cc in hA. simpl in hA. lia.
      - rewrite <- hQ. exact (h1 u s hs).
      - intros g1 g2. rewrite hC in c. pose proof c (S g1) as d. simpl in d. apply d. lia.
      - pose proof h2 u h3 as g3. pose proof (ltac:(exists (nth (ancestor dsu (length dsu) u) dsu (Ancestor Unit)); reflexivity) : exists e, nth (ancestor dsu (length dsu) u) dsu (Ancestor Unit) = e) as [[e | e] he]. { rewrite he in g3. exfalso. exact g3. } exists e. rewrite <- ancestorEqLastAncestorChain in he. rewrite hC in he. rewrite (ltac:(simpl; lia) : length (u :: tail) - 1 = length tail) in he. rewrite (ltac:(lia) : length tail = S (length tail - 1)) in he. simpl in he. exact he. }
      pose proof step5 step6 as step7. rewrite <- step7 in *. apply step4. lia.
Qed.

Lemma ancestorChainInsertPresent (dsu : list Slot) chain (u x : nat) (h0 : validChainToAncestor dsu chain) (hV : nth 0 chain 0 = u) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (h3 : u < length dsu) (h4 : x < length dsu) (h5 : match nth x dsu (Ancestor Unit) with | ReferTo _ => true | Ancestor _ => false end) i (hd : i < length chain) (he : nth i chain 0 = x) (t : nat) (hT : nth t chain 0 = ancestor dsu (length dsu) x) (hT1 : i < t) (hT2 : t < length chain) : take (S i) chain ++ drop t chain = ancestorChain (<[x:=ReferTo (ancestor dsu (length dsu) x)]> dsu) (length ((<[x:=ReferTo (ancestor dsu (length dsu) x)]> dsu))) u.
Proof.
  assert (h1' : noIllegalIndices (<[x:=ReferTo (ancestor dsu (length dsu) x)]> dsu)).
  { intros a b c.
    destruct (decide (a = x)) as [h | h].
    - rewrite h in c. rewrite nth_lookup, list_lookup_insert in c; [| lia]. simpl in c. rewrite insert_length. injection c. intro d. subst b. apply ancestorLtLength; assumption.
    - rewrite nth_lookup, list_lookup_insert_ne in c; [| lia]. rewrite <- nth_lookup in c. rewrite insert_length. exact (h1 a b c). }
  pose proof validChainAncestorLength (<[x:=ReferTo (ancestor dsu (length dsu) x)]> dsu) (take (S i) chain ++ drop t chain) h1' as step.
  assert (step1 : nth 0 (take (S i) chain ++ drop t chain) 0 = u).
  { rewrite app_nth1; [| rewrite take_length; lia]. destruct chain as [| head tail].
    - cbv in h0. easy.
    - simpl in *. subst head. reflexivity. }
  assert (step2 : validChainToAncestor (<[x:=ReferTo (ancestor dsu (length dsu) x)]> dsu) (take (S i) chain ++ drop t chain)).
  { repeat split.
    - destruct chain as [| head tail]. { cbv in h0. easy. } easy.
    - destruct chain as [| head tail]. { cbv in h0. easy. } simpl in he. rewrite app_nth1; [| rewrite take_length; lia]. simpl. simpl in hV. subst head. rewrite insert_length. assumption.
    - intros a b. pose proof h0 as [[e [f g]] [l k]]. destruct (ltac:(lia) : a < i \/ a = i \/ i < a) as [hs | [hs | hs]].
      + rewrite !app_nth1; [| rewrite take_length; lia | rewrite take_length; lia]. rewrite <- !nthTake; try lia. pose proof list_lookup_insert_ne dsu x (nth a chain 0) (ReferTo (ancestor dsu (length dsu) x)). pose proof validChainPairwiseDifferent dsu chain h1 h0 a i ltac:(lia) ltac:(lia) ltac:(lia) as step2. rewrite he in step2. pose proof list_lookup_insert_ne dsu x ((nth a chain 0)) (ReferTo (ancestor dsu (length dsu) x)) ltac:(lia) as step3. pose proof (ltac:(clear; intros a b h; subst b; easy) : forall a b, a = b -> default (Ancestor Unit) a = default (Ancestor Unit) b) _ _ step3 as step4. rewrite <- !nth_lookup in step4. rewrite step4. apply g. lia.
      + subst a. rewrite app_nth1; try (rewrite take_length; lia). rewrite app_nth2; try (rewrite take_length; lia). rewrite take_length. rewrite (ltac:(lia) : S i - S i `min` length chain = 0). rewrite <- !nthTake; try lia.
        pose proof lookup_drop chain t 0 as step2. rewrite (ltac:(lia) : t + 0 = t) in step2. pose proof nth_lookup chain t 0 as step3. rewrite <- step2 in step3.
        pose proof nth_lookup (drop t chain) 0 0 as step4. rewrite <- step3 in step4. rewrite step4. rewrite he. rewrite nth_lookup. rewrite list_lookup_insert.
        * rewrite (ltac:(easy) : forall a b, default a (Some b) = b). rewrite hT. reflexivity.
        * lia.
      + rewrite !app_nth2; try (rewrite take_length; lia). rewrite take_length; try lia. rewrite (ltac:(lia) : S i `min` length chain = S i). rewrite !nth_lookup. rewrite !lookup_drop. rewrite (ltac:(lia) : t + (S a - S i) = S (t + (a - S i))). rewrite list_lookup_insert_ne; rewrite <- !nth_lookup.
        * apply g. rewrite app_length, take_length, drop_length, (ltac:(lia) : S i `min` length chain = S i) in b. lia.
        * rewrite <- he. apply (validChainPairwiseDifferent dsu); try (assumption || lia).
          rewrite app_length, take_length, drop_length, (ltac:(lia) : S i `min` length chain = S i) in b. lia.
    - destruct h0 as [[e [f g]] [b c]]. exists b. rewrite app_length. rewrite app_nth2; [| rewrite take_length, drop_length, (ltac:(lia) : S i `min` length chain = S i); lia]. rewrite (ltac:(lia) : length (take (S i) chain) + length (drop t chain) - 1 - length (take (S i) chain) = length (drop t chain) - 1). rewrite (nth_lookup (drop t chain)), drop_length, lookup_drop, <- nth_lookup, (ltac:(lia) : t + (length chain - t - 1) = length chain - 1), nth_lookup, list_lookup_insert_ne; [now rewrite <- nth_lookup |]. intro gg. rewrite <- gg in c. rewrite c in h5. easy. }
      exact (step step2 u step1).
Qed.

Lemma ancestorOfVertexInAncestorChain (dsu : list Slot) chain (u x : nat) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (h3 : u < length dsu) (h4 : x < length dsu) (h5 : match nth x dsu (Ancestor Unit) with | ReferTo _ => true | Ancestor _ => false end) (h6 : validChainToAncestor dsu chain) (h7 : nth 0 chain 0 = u) (s : nat) (h8 : nth s chain 0 = x) (h9 : s < length chain) : ancestor dsu (length dsu) u = ancestor dsu (length dsu) x.
Proof.
  rewrite <- !ancestorEqLastAncestorChain, <- (validChainAncestorLength dsu chain h1 h6 _ h7), <- (validChainAncestorLength dsu (drop s chain) h1).
  - rewrite !nth_lookup, lookup_drop, drop_length, <- !nth_lookup, (ltac:(lia) : s + (length chain - s - 1) = length chain - 1). reflexivity.
  - repeat split.
    + intro h. pose proof (ltac:(rewrite h; reflexivity) : length (drop s chain) = length []) as step1. rewrite drop_length in step1. simpl in step1. lia.
    + rewrite nth_lookup, lookup_drop, Nat.add_0_r, <- nth_lookup, h8. exact h4.
    + intros g i. rewrite drop_length in i. repeat rewrite (nth_lookup (drop _ _)), lookup_drop. rewrite <- !nth_lookup, (ltac:(lia) : s + S g = S (s + g)).
      destruct h6 as [[e [f j]] [b c]]. apply j. lia.
    + repeat rewrite (nth_lookup (drop _ _)), lookup_drop. rewrite <- !nth_lookup, drop_length, (ltac:(lia) : s + (length chain - s - 1) = length chain - 1). destruct h6 as [_ c]. exact c.
  - rewrite nth_lookup, lookup_drop, Nat.add_0_r, <- nth_lookup. exact h8.
Qed.

Lemma ancestorInsert (dsu : list Slot) (u x : nat) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (h3 : u < length dsu) (h4 : x < length dsu) (h5 : match nth x dsu (Ancestor Unit) with | ReferTo _ => true | Ancestor _ => false end) : ancestor dsu (length dsu) u = ancestor (<[x:=ReferTo (ancestor dsu (length dsu) x)]> dsu) (length dsu) u.
Proof.
  pose proof validChainAncestorChain dsu (length dsu) u h3 h1 as step.
  pose proof h2 u h3 as step2.
  remember (existsInRange (length (ancestorChain dsu (length dsu) u)) (fun i => bool_decide (nth i (ancestorChain dsu (length dsu) u) 0 = x))) as s eqn:hs. symmetry in hs. destruct s; [rewrite <- Is_true_true, existsInRangeMeaning in hs | rewrite <- Is_true_false, notExistsInRangeMeaning in hs]; unfold existsInRangeLogic in hs.
  - destruct hs as [s [hb hc]]. rewrite bool_decide_eq_true in hc.
    assert (step3: validChainToAncestor dsu (ancestorChain dsu (length dsu) u)).
    { split. { assumption. } pose proof h2 u h3 as step3.
      remember (nth (ancestor dsu (length dsu) u) dsu (Ancestor Unit)) as g eqn:hg. symmetry in hg. destruct g as [g | g]. { exfalso. exact step3. } exists g. rewrite <- hg, ancestorEqLastAncestorChain. reflexivity. }
    pose proof ancestorChainInsertPresent dsu (ancestorChain dsu (length dsu) u) u x step3 ltac:(destruct (length dsu); simpl; [reflexivity |]; destruct (nth u dsu (Ancestor Unit)); easy) h1 h2 h3 h4 h5 s hb hc (length (ancestorChain dsu (length dsu) u) - 1) as step4. rewrite ancestorEqLastAncestorChain in step4.
    destruct (ltac:(lia) : s = length (ancestorChain dsu (length dsu) u) - 1 \/ s < length (ancestorChain dsu (length dsu) u) - 1) as [step5 | step5].
    { subst s. rewrite <- hc in h5. destruct step3 as [[e [f g]] [b c]]. rewrite c in h5. exfalso. exact h5. }
    pose proof ancestorOfVertexInAncestorChain dsu (ancestorChain dsu (length dsu) u) u x h1 h2 h3 h4 h5 step3 ltac:(destruct (length dsu); simpl; destruct (nth u dsu (Ancestor Unit)); simpl; try lia) s hc hb as step6.
    pose proof step4 step6 step5 ltac:(lia) as step7.
    rewrite <- (ancestorEqLastAncestorChain (<[x:=ReferTo (ancestor dsu (length dsu) x)]> dsu)). rewrite insert_length in step7. rewrite <- step7, app_length, app_nth2, drop_length, take_length, (ltac:(lia) : (S s `min` length (ancestorChain dsu (length dsu) u) = S s)); [| rewrite drop_length; lia]. rewrite (ltac:(lia) : S s + (length (ancestorChain dsu (length dsu) u) - (length (ancestorChain dsu (length dsu) u) - 1)) - 1 - S s = 0), nth_lookup, lookup_drop, Nat.add_0_r, <- nth_lookup, ancestorEqLastAncestorChain. reflexivity.
  - unfold notExistsInRangeLogic in hs. assert (hd : forall i, i < length (ancestorChain dsu (length dsu) u) -> nth i (ancestorChain dsu (length dsu) u) 0 <> x).
    { intros a b. pose proof hs a b as c. case_bool_decide; [exfalso; exact (c ltac:(easy)) | assumption]. }
    rewrite <- (ancestorEqLastAncestorChain dsu (length dsu) u) in step2. pose proof ancestorChainInsertNotPresent dsu (length dsu) u x h1 h2 h3 h4 h5 hd as step3. rewrite <- ancestorEqLastAncestorChain, <- ancestorEqLastAncestorChain, <- !step3. reflexivity.
Qed.

Fixpoint pathCompress (dsu : list Slot) (fuel : nat) (index ancestor : nat) :=
  match fuel with
  | O => dsu
  | S fuel => match nth index dsu (Ancestor Unit) with
    | ReferTo x => pathCompress (<[index := ReferTo ancestor]> dsu) fuel x ancestor
    | Ancestor _ => dsu
    end
  end.

Lemma pathCompressPreservesNth (dsu : list Slot) a b c d e (hd : nth d dsu (Ancestor Unit) = Ancestor e) : nth d (pathCompress dsu a b c) (Ancestor Unit) = nth d dsu (Ancestor Unit).
Proof.
  revert dsu b c d e hd. induction a as [| a IH]. { easy. }
  intros dsu b c d e hd. simpl. remember (nth b dsu (Ancestor Unit)) as x eqn:hx. destruct x as [x | x]; symmetry in hx; [| reflexivity]. pose proof IH (<[b:=ReferTo c]> dsu) x c d e as step. destruct (decide (b = d)) as [hs | hs]. { subst b. rewrite hx in hd. easy. }
  assert (step2: nth d (<[b:=ReferTo c]> dsu) (Ancestor Unit) = nth d dsu (Ancestor Unit)).
  { rewrite nth_lookup, list_lookup_insert_ne; [| exact hs]. rewrite <- nth_lookup. reflexivity. } rewrite step2 in step. rewrite (step hd). reflexivity.
Qed.

Lemma withoutCyclesExtractAncestor (dsu : list Slot) (h2 : withoutCyclesN dsu (length dsu)) (a : nat) (hA : a < length dsu) : exists k, nth (ancestor dsu (length dsu) a) dsu (Ancestor Unit) = Ancestor k.
Proof.
  pose proof h2 a hA as step.
  destruct (nth (ancestor dsu (length dsu) a) dsu (Ancestor Unit)) as [g | g]. { exfalso. exact step. } exists g. reflexivity.
Qed.

Lemma pathCompressNth (dsu : list Slot) (h1 : noIllegalIndices dsu) (fuel : nat) (a b c : nat) (hA : a < length dsu) (hB : b < length dsu) (hC : c < length dsu) : nth c (pathCompress dsu fuel a b) (Ancestor Unit) = nth c dsu (Ancestor Unit) \/ nth c (pathCompress dsu fuel a b) (Ancestor Unit) = ReferTo b.
Proof.
  revert dsu h1 a b c hA hB hC. induction fuel as [| fuel IH];
  intros dsu h1 a b c hA hB hC.
  { simpl. left. reflexivity. }
  simpl. remember (nth a dsu (Ancestor Unit)) as e eqn:he. symmetry in he.
  destruct e as [e | e]; [| left; reflexivity].
  pose proof h1 a _ he as hE.
  epose proof IH (<[a:=ReferTo b]> dsu) _ e b c ltac:(rewrite insert_length; exact hE) ltac:(rewrite insert_length; exact hB) ltac:(rewrite insert_length; exact hC) as hf.
  destruct (decide (c = a)) as [hs | hs].
  - subst c. rewrite (ltac:(rewrite nth_lookup, list_lookup_insert; easy) : nth a (<[a:=ReferTo b]> dsu) (Ancestor Unit) = ReferTo b) in hf. right. destruct hf; assumption.
  - rewrite (ltac:(rewrite !nth_lookup, list_lookup_insert_ne; try lia; reflexivity) : nth c (<[a:=ReferTo b]> dsu) (Ancestor Unit) = nth c dsu (Ancestor Unit)) in hf. exact hf.
  Unshelve.
  intros i j hi. rewrite insert_length. destruct (decide (i = a)) as [hs | hs].
  + subst i. rewrite (ltac:(rewrite nth_lookup, list_lookup_insert; easy) : nth a (<[a:=ReferTo b]> dsu) (Ancestor Unit) = ReferTo b) in hi. injection hi. lia.
  + rewrite (ltac:(rewrite !nth_lookup, list_lookup_insert_ne; try lia; reflexivity) : nth i (<[a:=ReferTo b]> dsu) (Ancestor Unit) = nth i dsu (Ancestor Unit)) in hi.
    assert (hi1 : i < length dsu).
    { destruct (decide (length dsu <= i)) as [ht | ht]; [| lia]. rewrite nth_overflow in hi; [| exact ht]. easy. }
    exact (h1 i _ hi).
Qed.

Lemma doubleBangEqIfNthEq {A} (l l1 : list A) (hL : length l = length l1) d (hnth : forall x, x < length l -> nth x l d = nth x l1 d) n : l !! n = l1 !! n.
Proof.
  remember (l !! n) as target1 eqn:h1.
  remember (l1 !! n) as target2 eqn:h2.
  symmetry in h1. symmetry in h2.
  destruct target1 as [target1 |]; destruct target2 as [target2 |]; try fast_reflexivity; try pose proof lookup_ge_None_1 _ _ h1 as d1; try pose proof lookup_ge_None_1 _ _ h2 as d2; try pose proof lookup_ge_None_2 _ _ (ltac:(lia) : length l <= n); try pose proof lookup_ge_None_2 _ _ (ltac:(lia) : length l1 <= n); try congruence.
  pose proof lookup_lt_Some _ _ _ h1 as s.
  pose proof hnth n s as t.
  rewrite !nth_lookup, h1, h2 in t. simpl in t. congruence.
Qed.

Definition performMerge (dsu : list Slot) (tree1 tree2 : Tree) (u v : nat) :=
  <[u := ReferTo v]> (<[v := Ancestor (Unite tree2 tree1)]> dsu).

Lemma performMergeScore' (dsu : list Slot) (tree1 tree2 : Tree) (u v : nat) (hUV : u < v) (hL : v < length dsu) (hU : nth u dsu (Ancestor Unit) = Ancestor tree1) (hV : nth v dsu (Ancestor Unit) = Ancestor tree2) : (dsuScore (performMerge dsu tree1 tree2 u v) = dsuScore dsu + Z.of_nat (leafCount tree1) + Z.of_nat (leafCount tree2))%Z.
Proof.
  unfold performMerge. rewrite (insert_take_drop dsu); [| exact hL]. rewrite insert_app_l; [| rewrite take_length; lia]. rewrite insert_take_drop, take_take; [| rewrite take_length; lia]. rewrite (ltac:(lia) : u `min` v = u).
  pose proof ListDecomposition.listDecomposition dsu u v hUV hL (Ancestor Unit) as a. rewrite a at 4. rewrite hU, hV, ((ltac:(intros; easy) : forall a b, a :: b = [a] ++ b) (ReferTo _)), ((ltac:(intros; easy) : forall a b, a :: b = [a] ++ b) (Ancestor _)), <- !app_assoc.
  unfold dsuScore. rewrite !map_app, !list_sum_app. simpl. rewrite (ltac:(easy) : _ + 1 = S _), !Nat.add_0_r. lia.
Qed.

Lemma performMergeScore'' (dsu : list Slot) (tree1 tree2 : Tree) (u v : nat) (hUV : v < u) (hL : u < length dsu) (hU : nth u dsu (Ancestor Unit) = Ancestor tree1) (hV : nth v dsu (Ancestor Unit) = Ancestor tree2) : (dsuScore (performMerge dsu tree1 tree2 u v) = dsuScore dsu + Z.of_nat (leafCount tree1) + Z.of_nat (leafCount tree2))%Z.
Proof.
  unfold performMerge. rewrite (insert_take_drop dsu); [| ltac:(lia)].
  assert (h : forall a (b : list Slot), <[u:=a]> b =  <[length (take v dsu) + (u - v):=a]> b).
  { intros a b. rewrite take_length, (ltac:(lia) : v `min` length dsu + (u - v) = u). reflexivity. } rewrite h.
  rewrite insert_app_r, ((ltac:(intros; easy) : forall a b, a :: b = [a] ++ b) (Ancestor _)), (ltac:(simpl; lia) : u - v = length [Ancestor (Unite tree2 tree1)] + (u - v - 1)), insert_app_r. rewrite insert_take_drop, drop_drop; [| rewrite drop_length; lia]. rewrite (ltac:(lia) : S v + S (u - v - 1) = u + 1), (ltac:(easy) : ReferTo v :: drop (u + 1) dsu = [ReferTo v] ++ drop (u + 1) dsu). unfold dsuScore.
  pose proof ListDecomposition.listDecomposition dsu v u hUV hL (Ancestor Unit) as a. rewrite a at 4. rewrite take_drop_commute, (ltac:(lia) : S v + (u - v - 1) = u), !map_app, !list_sum_app, hU, hV. simpl. lia.
Qed.

Lemma performMergeScore (dsu : list Slot) (tree1 tree2 : Tree) (u v : nat) (hUV : u <> v) (hLt1 : u < length dsu) (hLt2 : v < length dsu) (hL : v < length dsu) (hU : nth u dsu (Ancestor Unit) = Ancestor tree1) (hV : nth v dsu (Ancestor Unit) = Ancestor tree2) : (dsuScore (performMerge dsu tree1 tree2 u v) = dsuScore dsu + Z.of_nat (leafCount tree1) + Z.of_nat (leafCount tree2))%Z.
Proof.
  destruct (ltac:(lia) : u < v \/ v < u) as [hs | hs].
  - apply performMergeScore'; assumption.
  - apply performMergeScore''; assumption.
Qed.

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
      if decide (leafCount tree2 < leafCount tree1) then performMerge dsu2 tree2 tree1 v u else performMerge dsu2 tree1 tree2 u v
    end
  end.

Fixpoint dsuFromInteractions (dsu : list Slot) (interactions : list (nat * nat)) :=
  match interactions with
  | [] => dsu
  | (a, b)::tail => if decide (a < length dsu /\ b < length dsu) then dsuFromInteractions (unite dsu a b) tail else dsuFromInteractions dsu tail
  end.

Lemma pathCompressPreservesLength (dsu : list Slot) (n a b : nat) : length (pathCompress dsu n a b) = length dsu.
Proof.
  induction n as [| n IH] in dsu, a |- *; [easy |].
  simpl. destruct (nth a dsu (Ancestor Unit)) as [x | x]; [| easy]. rewrite IH. apply insert_length.
Qed.

Lemma pathCompressPreservesScore (dsu : list Slot) (n a b : nat) : dsuScore (pathCompress dsu n a b) = dsuScore dsu.
Proof.
  induction n as [| n IH] in dsu, a |- *; [easy |].
  simpl.
  remember (nth a dsu (Ancestor Unit)) as x eqn:hx. symmetry in hx. destruct x as [x | x]; [| reflexivity].
  rewrite IH.
  destruct (decide (a < length dsu)) as [ha | ha]; [| rewrite list_insert_ge; lia].
  rewrite insert_take_drop; [| exact ha]. unfold dsuScore. rewrite (ltac:(intros; listsEqual) : forall a b, a :: b = [a] ++ b), !map_app, !list_sum_app.
  assert (s : list_sum
      (map
         (λ _0 : Slot,
            match _0 with
            | ReferTo _ => 0
            | Ancestor _1 => score _1
            end) [ReferTo b]) = list_sum
      (map
         (λ _0 : Slot,
            match _0 with
            | ReferTo _ => 0
            | Ancestor _1 => score _1
            end) [nth a dsu (Ancestor Unit)])).
  { rewrite hx. easy. }
  rewrite s, <- !list_sum_app, <- !map_app, <- ListDecomposition.listDecompositionSingle. { reflexivity. } exact ha.
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

Lemma pathCompressPreservesNoIllegalIndices (dsu : list Slot) (h1 : noIllegalIndices dsu) (n u v : nat) (hU : u < length dsu) (hV : v < length dsu) : noIllegalIndices (pathCompress dsu n u v).
Proof.
  revert u hU. revert h1. revert hV. revert dsu. induction n as [| n IH]; intros dsu hV h1 u hU.
  - simpl. intros. exact h1.
  - simpl. intros i j hi. remember (nth u dsu (Ancestor Unit)) as e eqn:he. symmetry in he. destruct e as [e | e].
    + assert (h : noIllegalIndices (<[u:=ReferTo v]> dsu)).
      { intros a b c. destruct (decide (a = u)) as [ha | ha].
        - rewrite ha, nth_lookup, list_lookup_insert, (ltac:(intros; easy) : forall a, default _ (Some a) = a) in c; [| exact hU]. injection c. intro d. subst v. rewrite insert_length. exact hV.
        - rewrite insert_length. rewrite nth_lookup, list_lookup_insert_ne in c; [| lia]. rewrite <- (nth_lookup _ _ (Ancestor Unit)) in c. exact (h1 _ _ c). }
      exact (IH (<[u:=ReferTo v]> dsu) ltac:(rewrite insert_length; exact hV) h e ltac:(rewrite insert_length; exact (h1 _ _ he)) i _ hi).
    + pose proof h1 i j hi. assumption.
Qed.

Lemma pathCompressPreservesWithoutCycles (dsu : list Slot) (h : withoutCyclesN dsu (length dsu)) (h1 : noIllegalIndices dsu) (n u : nat) (hU : u < length dsu) : withoutCyclesN (pathCompress dsu n u (ancestor dsu (length dsu) u)) (length dsu).
Proof.
  induction n as [| n IH] in u, dsu, h, hU, h1 |- *. { simpl. assumption. }
  simpl. remember (nth u dsu (Ancestor Unit)) as x eqn:hX. destruct x as [x | x]; [| easy]. pose proof (fun t => IH (<[u:=ReferTo (ancestor dsu (length dsu) u)]> dsu) t ltac:(intros v1 v2; destruct (decide (v1 = u)) as [h2 | h2]; [destruct (decide (length dsu <= u)); [rewrite list_insert_ge; [| lia]; intro h3; rewrite h2 in h3; rewrite <- hX in h3; injection h3; intro h4; subst x; subst u; exact (h1 v1 v2 ltac:(symmetry in hX; exact hX)) | pose proof list_lookup_insert dsu u (ReferTo (ancestor dsu (length dsu) u)) ltac:(lia) as step; pose proof nth_lookup_Some _ _ (Ancestor Unit) _ step as step2; subst u; rewrite step2; pose proof ancestorLtLength dsu h1 (length dsu) v1 ltac:(lia) as step3]; intro h3; injection h3; intro h4; rewrite insert_length | pose proof list_lookup_insert_ne dsu u v1 (ReferTo (ancestor dsu (length dsu) u)) ltac:(lia) as step; pose proof nth_lookup dsu v1 (Ancestor Unit) as step1; pose proof (nth_lookup (<[u:=ReferTo (ancestor dsu (length dsu) u)]> dsu) v1 (Ancestor Unit)) as step2; rewrite step in step2; rewrite <- step1 in step2; rewrite step2; intro step3; rewrite insert_length; exact (h1 v1 v2 step3)]; lia) x ltac:(rewrite insert_length; exact (h1 u x ltac:(symmetry; assumption)))) as step. rewrite !insert_length in step.
  assert (step1 : u < length dsu -> x < length dsu -> ancestor (<[u:=ReferTo (ancestor dsu (length dsu) u)]> dsu) (length dsu) x = ancestor dsu (length dsu) x).
  { revert h h1 hX. clear. intros h1 h2 h3 h4 h5. rewrite <- ancestorInsert; try (assumption || reflexivity). rewrite <- h3. easy. } rewrite step1 in step; try assumption; pose proof h1 u x ltac:(symmetry in hX; exact hX) as hX1; [| exact hX1].
  remember (nth x dsu (Ancestor Unit)) as s eqn:hS.
  symmetry in hS. destruct s as [s | s].
  - pose proof ancestorOfVertexInAncestorChain dsu (ancestorChain dsu (length dsu) u) u x h1 h hU hX1 ltac:(now rewrite hS) ltac:(split; [apply validChainAncestorChain; assumption | rewrite ancestorEqLastAncestorChain; pose proof h u hU; destruct (nth (ancestor dsu (length dsu) u)) as [| tree]; [easy | now exists tree]]) ltac:(destruct (length dsu); simpl; destruct (nth u dsu (Ancestor Unit)); simpl; try lia) 1 as step2. rewrite <- step2 in step.
    + apply step. intros i hi. rewrite insert_length, <- ancestorInsert; try assumption; [| now rewrite <- hX].
      destruct (decide (ancestor dsu (length dsu) i = u)) as [hA | hA].
      * pose proof h i hi as hj. rewrite hA, <- hX in hj. exfalso. exact hj.
      * rewrite nth_lookup, list_lookup_insert_ne; [| lia]. rewrite <- nth_lookup. apply h. assumption.
    + assert (ht : 2 <= length dsu).
      { destruct dsu as [| head tail]. { simpl in hU. lia. }
        destruct tail. { simpl in hU. pose proof (ltac:(lia) : u = 0). subst u. simpl in hX, hX1. pose proof (ltac:(lia) : x = 0). subst x. pose proof h 0 ltac:(simpl; lia) as step3. simpl in step3, hS. subst head. exfalso. exact step3. } simpl. lia. }
      destruct (ltac:(exists (length dsu - 2); lia) : exists n, length dsu = S (S n)) as [nn hn]. rewrite hn. simpl. rewrite <- hX, hS. easy.
    + assert (ht : 2 <= length dsu).
      { destruct dsu as [| head tail]. { simpl in hU. lia. }
        destruct tail. { simpl in hU. pose proof (ltac:(lia) : u = 0). subst u. simpl in hX, hX1. pose proof (ltac:(lia) : x = 0). subst x. pose proof h 0 ltac:(simpl; lia) as step3. simpl in step3, hS. subst head. exfalso. exact step3. } simpl. lia. }
      destruct (ltac:(exists (length dsu - 2); lia) : exists n, length dsu = S (S n)) as [nn hn]. rewrite hn. simpl. rewrite <- hX, hS. simpl. lia.
  - assert (ht : 2 <= length dsu).
    { destruct dsu as [| head tail]. { simpl in hU. lia. }
      destruct tail. { simpl in hU. pose proof (ltac:(lia) : u = 0). subst u. simpl in hX, hX1. pose proof (ltac:(lia) : x = 0). subst x. pose proof h 0 ltac:(simpl; lia) as step3. simpl in step3, hS. subst head. exfalso. exact step3. } simpl. lia. }
    destruct (ltac:(exists (length dsu - 2); lia) : exists n, length dsu = S (S n)) as [nn hn].
    assert (hg : ancestor dsu (length dsu) u = x).
    { rewrite hn. simpl. rewrite <- hX, hS. reflexivity. }
    rewrite hg.
    assert (hh : pathCompress (<[u:=ReferTo x]> dsu) n x x = <[u:=ReferTo x]> dsu).
    { destruct n. { easy. } simpl. destruct (decide (u = x)) as [hd | hd].
      - subst u. rewrite hS in hX. easy.
      - rewrite nth_lookup, list_lookup_insert_ne, <- nth_lookup, hS. { reflexivity. } assumption. }
    rewrite hh. clear hh. intros i hh. rewrite <- hg, insert_length, <- ancestorInsert; try assumption; [| now rewrite <- hX].
    destruct (decide (ancestor dsu (length dsu) i = u)) as [hs | hs].
    + pose proof h i hh as step2. rewrite hs, <- hX in step2. exfalso. exact step2.
    + rewrite nth_lookup, list_lookup_insert_ne, <- nth_lookup; [| lia]. pose proof h i hh as step2. exact step2.
Qed.

Lemma pathCompressPreservesAncestorLength (dsu : list Slot) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (n a b c : nat) (hA : a < length dsu) (hB : b < length dsu) (hC : c < length dsu) (hSameRoot : ancestor dsu (length dsu) c = ancestor dsu (length dsu) a) : ancestor (pathCompress dsu n c (ancestor dsu (length dsu) a)) (length dsu) b = ancestor dsu (length dsu) b.
Proof.
  revert dsu h1 h2 hA hB c hC hSameRoot.
  induction n as [| n IH]. { easy. }
  intros dsu h1 h2 hA hB c hC hSameRoot.
  rewrite (ltac:(simpl; reflexivity) : pathCompress dsu (S n) _ = _).
  remember (nth c dsu (Ancestor Unit)) as x eqn:hx. destruct x as [x | x]; symmetry in hx; [| reflexivity].
  assert (stepC : match nth c dsu (Ancestor Unit) with | ReferTo _ => true | Ancestor _ => false end). { rewrite hx. easy. }
  pose proof h1 c _ hx as stepX.
  pose proof (fun g1 g2 g3 g4 g5 => IH (<[c:=ReferTo (ancestor dsu (length dsu) a)]> dsu) g1 g2 g3 g4 x g5) as step. rewrite insert_length, <- hSameRoot, <- !ancestorInsert, !hSameRoot in step; try (assumption || lia).
  pose proof pathCompressPreservesNoIllegalIndices _ h1 1 c (ancestor dsu (length dsu) a) hC ltac:(apply ancestorLtLength; assumption) as stepN. simpl in stepN. rewrite hx in stepN.
  pose proof pathCompressPreservesWithoutCycles _ h2 h1 1 c hC as stepW. simpl in stepW. rewrite hx, hSameRoot in stepW.
  pose proof ancestorReferTo dsu c x hC h1 h2 hx as stepD. rewrite hSameRoot in stepD. symmetry in stepD.
  apply step; assumption.
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

Lemma runAncestor1 (dsu : list Slot) state1 state2 (hL : length dsu = 100) (hM : Z.to_nat (dsuLeafCount dsu) = length dsu) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (whatever2 a : Z) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) (communication : list Z) continuation continuation2 whatever n (hN : n <= 100) : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state1 state2
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
  (eliminateLocalVariables
  (λ _ : varsfuncdef_0__ancestor, false) (λ _0 : varsfuncdef_0__ancestor,
  match _0
with
| vardef_0__ancestor_vertex =>
    whatever2
| vardef_0__ancestor_work =>
    a
end)
  (λ _ : varsfuncdef_0__ancestor, repeat 0%Z 20)
  (loop n
  (λ _ : nat,
  dropWithinLoop
  (liftToWithinLoop
  (numberLocalGet arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__ancestor
  vardef_0__ancestor_work >>=
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
  varsfuncdef_0__ancestor arraydef_0__dsu
  _1 >>=
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
  (arrayType arrayIndex0
  environment0)
  varsfuncdef_0__ancestor)
  withLocalVariablesReturnValue bool
  (bool_decide
  (toSigned _2 8 < toSigned _3 8)%Z)) >>=
λ _0 : bool,
  (if _0
then
 break arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__ancestor >>=
λ _ : (),
  Done
  (WithinLoop arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__ancestor)
  withinLoopReturnValue ()
  ()
else
 Done
  (WithinLoop arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__ancestor)
  withinLoopReturnValue ()
  ()) >>=
λ _ : (),
  liftToWithinLoop
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
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__ancestor)
  withLocalVariablesReturnValue Z
  (coerceInt _1 64) >>=
λ _2 : Z,
  retrieve arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__ancestor
  arraydef_0__dsu _2 >>=
λ _3 : arrayType arrayIndex0
  environment0 arraydef_0__dsu,
  numberLocalSet arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__ancestor
  vardef_0__ancestor_work
  _3) >>=
λ _ : (),
  Done
  (WithinLoop arrayIndex0
  (arrayType arrayIndex0 environment0)
  varsfuncdef_0__ancestor)
  withinLoopReturnValue ()
  ())) >>= continuation) >>= continuation2) = invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state1 state2
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
  (eliminateLocalVariables
  (λ _ : varsfuncdef_0__ancestor, false) (λ _0 : varsfuncdef_0__ancestor,
  match _0
with
| vardef_0__ancestor_vertex =>
    whatever2
| vardef_0__ancestor_work =>
    Z.of_nat (ancestor dsu n (Z.to_nat a))
end)
  (λ _ : varsfuncdef_0__ancestor, repeat 0%Z 20) (continuation tt) >>= continuation2).
Proof.
  revert a hLt1 hLe1. induction n as [| n IH]; intros a hLt1 hLe1.
  - rewrite (ltac:(simpl; reflexivity) : loop 0 _ = _), (ltac:(simpl; reflexivity) : ancestor dsu 0 _ = _), Z2Nat.id, leftIdentity; [reflexivity | lia].
  - rewrite (ltac:(simpl; reflexivity) : loop (S _) _ = _). unfold numberLocalGet at 1. rewrite <- !bindAssoc, liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop, <- !bindAssoc. pose proof @pushNumberGet2 arrayIndex0 (arrayType arrayIndex0 environment0) varsfuncdef_0__ancestor _ (λ _ : varsfuncdef_0__ancestor, false) (λ _1 : varsfuncdef_0__ancestor,
  match
  _1
with
| vardef_0__ancestor_vertex =>
    whatever2
| vardef_0__ancestor_work =>
    a
end) (λ _ : varsfuncdef_0__ancestor,
  repeat
  0%Z 20) as step. rewrite step. clear step.
  assert (step : coerceInt a 64 = a).
  { revert hLe1 hLt1. clear. intros h1 h2. unfold coerceInt. rewrite Z.mod_small. { reflexivity. } lia. }
  rewrite step, !leftIdentity, liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop. unfold retrieve at 1.
  pose proof pushDispatch2 (λ _ : varsfuncdef_0__ancestor, false)
  (λ _0 : varsfuncdef_0__ancestor,
     match _0 with
     | vardef_0__ancestor_vertex => whatever2
     | vardef_0__ancestor_work => a
     end) (λ _ : varsfuncdef_0__ancestor, repeat 0%Z 20) (Retrieve arrayIndex0 (arrayType arrayIndex0 environment0)
     arraydef_0__dsu a) as step2. rewrite <- !bindAssoc, step2. clear step2.
  rewrite (ltac:(simpl; reflexivity) : forall effect continuation f, bind (Dispatch _ _ _ effect continuation) f = _). autorewrite with advance_program.
  case_decide as hs; [| rewrite lengthConvert in hs; lia].
  rewrite !leftIdentity, (ltac:(easy) : toSigned (coerceInt 0%Z 8) 8 = 0%Z).
  rewrite (ltac:(easy) : @nth_lt (arrayType arrayIndex0 environment0 arraydef_0__dsu) (convertToArray dsu) (Z.to_nat a) hs = @nth_lt Z (convertToArray dsu) (Z.to_nat a) hs), (nth_lt_default (convertToArray dsu) (Z.to_nat a) hs 0%Z), nthConvert; [| lia].
  remember (nth (Z.to_nat a) dsu (Ancestor Unit)) as g eqn:hg. symmetry in hg.
  destruct g as [g | g]; clear hs.
  + case_bool_decide as hs. { unfold toSigned in hs. pose proof h1 (Z.to_nat a) g hg. case_decide; [| lia]. lia. } rewrite (ltac:(easy) : liftToWithinLoop
  (Done
     (WithLocalVariables arrayIndex0 (arrayType arrayIndex0 environment0)
        varsfuncdef_0__ancestor) withLocalVariablesReturnValue bool false) = Done _ _ bool false), !leftIdentity.
    rewrite liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite <- !bindAssoc, pushNumberGet2, !step, !leftIdentity, liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop. unfold retrieve at 1. rewrite <- !bindAssoc, pushDispatch2. rewrite (ltac:(simpl; reflexivity) : forall effect continuation f, bind (Dispatch _ _ _ effect continuation) f = _). autorewrite with advance_program. clear hs. case_decide as hs; [| rewrite lengthConvert in hs; lia]. rewrite liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop, <- !bindAssoc. unfold numberLocalSet at 1. pose proof (@pushNumberSet2 arrayIndex0 (arrayType arrayIndex0 environment0) varsfuncdef_0__ancestor _ (λ _ : varsfuncdef_0__ancestor, false)
    (λ _0 : varsfuncdef_0__ancestor,
       match _0 with
       | vardef_0__ancestor_vertex => whatever2
       | vardef_0__ancestor_work => a
       end) (λ _ : varsfuncdef_0__ancestor, repeat 0%Z 20) vardef_0__ancestor_work) (nth_lt (convertToArray dsu) (Z.to_nat a) hs) as step3. rewrite step3. clear step3.
    rewrite (ltac:(cbv; reflexivity) : dropWithinLoop
    (Done
       (WithinLoop arrayIndex0 (arrayType arrayIndex0 environment0)
          varsfuncdef_0__ancestor) withinLoopReturnValue () ())  = _), !leftIdentity.
    assert (step3 : nth_lt (convertToArray dsu) (Z.to_nat a) hs = Z.of_nat g).
    { rewrite (nth_lt_default _ _ _ 0%Z), nthConvert; [| lia]. rewrite hg. reflexivity. } rewrite step3. clear step3.
    assert (step3 : (update
    (λ _0 : varsfuncdef_0__ancestor,
       match _0 with
       | vardef_0__ancestor_vertex => whatever2
       | vardef_0__ancestor_work => a
       end) vardef_0__ancestor_work (Z.of_nat g)) = fun x => match x with | vardef_0__ancestor_vertex => whatever2 | vardef_0__ancestor_work => Z.of_nat g end). { unfold update. apply functional_extensionality_dep. intro aa. destruct aa; easy. } rewrite step3. clear step3.
    pose proof IH ltac:(lia) (Z.of_nat g) ltac:(pose proof h1 (Z.to_nat a) _ hg as ls; lia) ltac:(lia) as step3. rewrite !liftToWithinLoopBind, <- !bindAssoc in step3. rewrite step3, Nat2Z.id.
    clear step3. assert (step3 : ancestor dsu (S n) (Z.to_nat a) = ancestor dsu n g). { simpl. rewrite hg. reflexivity. } rewrite step3. reflexivity.
  + case_bool_decide as hs.
    * rewrite liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop. rewrite <- !bindAssoc, leftIdentity, <- !bindAssoc, dropWithinLoop_break, !leftIdentity.
      assert (step3 : ancestor dsu (S n) (Z.to_nat a) = Z.to_nat a).
      { simpl. rewrite hg. reflexivity. } rewrite step3, Z2Nat.id; [| lia]. reflexivity.
    * unfold toSigned in hs. case_decide as hss. { simpl in hss. rewrite (ltac:(easy) : (2 ^ (8 - 1) = 128)%Z) in hss. pose proof nthLowerBoundConvertAuxStep dsu ltac:(lia) ltac:(lia) (Z.to_nat a) ltac:(lia) g hg. lia. } rewrite (ltac:(easy) : (2 ^ 8 = 256)%Z) in hs. pose proof oneLeqLeafCount g. lia.
Qed.

Fixpoint roll (dsu : list Slot) : option Tree :=
  match dsu with
  | [] => None
  | Ancestor x :: rest =>
    match roll rest with
    | None => Some x
    | Some y => Some (Unite x y)
    end
  | ReferTo x :: rest => roll rest
  end.

Lemma maxScore (dsu : list Slot) : Z.to_nat (dsuScore dsu) <= score (default Unit (roll dsu)).
Proof.
  induction dsu as [| head tail IH]. { easy. }
  unfold dsuScore. rewrite Nat2Z.id. rewrite -> (ltac:(listsEqual) : head :: tail = [head] ++ tail) at 1. rewrite map_app, list_sum_app.
  destruct head as [x | x].
  - simpl. unfold dsuScore in IH. rewrite Nat2Z.id in IH. exact IH.
  - simpl. remember (roll tail) as g eqn:hg. destruct g as [g |].
    { simpl in *. unfold dsuScore in IH. rewrite Nat2Z.id in IH. lia. }
    { simpl in *. unfold dsuScore in IH. rewrite Nat2Z.id in IH. lia. }
Qed.

Lemma rollPreservesLeafCount (dsu : list Slot) : Z.to_nat (dsuLeafCount dsu) = match roll dsu with | None => 0 | Some x => leafCount x end.
Proof.
  induction dsu as [| head tail IH]. { easy. }
  unfold dsuLeafCount. rewrite Nat2Z.id. rewrite -> (ltac:(listsEqual) : head :: tail = [head] ++ tail) at 1. rewrite map_app, list_sum_app.
  destruct head as [x | x]; simpl in *.
  - unfold dsuLeafCount in IH. rewrite Nat2Z.id in IH. exact IH.
  - remember (roll tail) as g eqn:hg. destruct g as [g |].
    { simpl in *. unfold dsuLeafCount in IH. rewrite Nat2Z.id in IH. lia. }
    { simpl in *. unfold dsuLeafCount in IH. rewrite Nat2Z.id in IH. lia. }
Qed.

Lemma rollNoneScore (dsu : list Slot) (h : roll dsu = None) : dsuScore dsu = 0%Z.
Proof.
  induction dsu as [| head tail IH]. { easy. }
  destruct head as [g |].
  - simpl in h. unfold dsuScore. rewrite (ltac:(easy) : ReferTo g :: tail = [ReferTo g] ++ tail). rewrite map_app, list_sum_app. simpl. exact (IH h).
  - simpl in h. destruct (roll tail); easy.
Qed.

Lemma rollNoneLeafCount (dsu : list Slot) (h : roll dsu = None) : dsuLeafCount dsu = 0%Z.
Proof.
  induction dsu as [| head tail IH]. { easy. }
  destruct head as [g |].
  - simpl in h. unfold dsuLeafCount. rewrite (ltac:(easy) : ReferTo g :: tail = [ReferTo g] ++ tail). rewrite map_app, list_sum_app. simpl. exact (IH h).
  - simpl in h. destruct (roll tail); easy.
Qed.

Lemma maxScore2 (dsu : list Slot) : Z.to_nat (dsuScore dsu) <= score (constructTree (Z.to_nat (dsuLeafCount dsu) - 1)).
Proof.
  remember (roll dsu) as g eqn:hg. destruct g as [g |]; symmetry in hg; [| rewrite rollNoneScore, rollNoneLeafCount; (assumption || lia)].
  pose proof maxScore dsu as a1.
  pose proof constructTreeIsOptimal (Z.to_nat (dsuLeafCount dsu) - 1) (default Unit (roll dsu)) as a2.
  rewrite rollPreservesLeafCount in *. rewrite hg in *. simpl in *.
  pose proof oneLeqLeafCount g.
  pose proof a2 ltac:(rewrite constructTreeSize; lia). lia.
Qed.

Lemma scoreZeroIfLeafCountZero (dsu : list Slot) (h : dsuLeafCount dsu = 0%Z) : dsuScore dsu = 0%Z.
Proof.
  induction dsu as [| head tail IH]. { easy. }
  unfold dsuScore. unfold dsuLeafCount in h. rewrite (ltac:(easy) : head :: tail = [head] ++ tail), map_app, list_sum_app in *.
  destruct head as [x | x].
  - simpl in *. exact (IH h).
  - simpl in *. pose proof oneLeqLeafCount x. lia.
Qed.

Lemma maxScore3 (dsu : list Slot) : Z.to_nat (dsuScore dsu) <= (Z.to_nat (dsuLeafCount dsu)) * (Z.to_nat (dsuLeafCount dsu) + 1) / 2 - 1.
Proof.
  pose proof maxScore2 dsu as h1.
  pose proof constructTreeScore (Z.to_nat (dsuLeafCount dsu) - 1) as h2.
  assert (hS : (dsuLeafCount dsu = 0%Z \/ 0%Z < dsuLeafCount dsu)%Z).
  { unfold dsuLeafCount. lia. }
  destruct hS as [hS | hS].
  - pose proof scoreZeroIfLeafCountZero _ hS as hI. lia.
  - rewrite (ltac:(lia) : Z.to_nat (dsuLeafCount dsu) - 1 + 1 = Z.to_nat (dsuLeafCount dsu)), (ltac:(lia) : Z.to_nat (dsuLeafCount dsu) - 1 + 2 = Z.to_nat (dsuLeafCount dsu) + 1) in h2. lia.
Qed.

Lemma unitePreservesLength (dsu : list Slot) (a b : nat) : length (unite dsu a b) = length dsu.
Proof.
  unfold unite. case_decide as h1. { reflexivity. } case_decide as h2. { reflexivity. } case_decide as h3. { rewrite !pathCompressPreservesLength. reflexivity. }
  destruct (nth _ _ _) as [m | m]. { rewrite !pathCompressPreservesLength. reflexivity. } destruct (nth _ _ _) as [n | n]. { rewrite !pathCompressPreservesLength. reflexivity. } case_decide as h4.
  - unfold performMerge. rewrite !insert_length, !pathCompressPreservesLength. reflexivity.
  - unfold performMerge. rewrite !insert_length, !pathCompressPreservesLength. reflexivity.
Qed.

Lemma unitePreservesLeafCount (dsu : list Slot) (hN : noIllegalIndices dsu) (a b : nat) : dsuLeafCount (unite dsu a b) = dsuLeafCount dsu.
Proof.
  unfold unite. case_decide as h1. { reflexivity. } case_decide as h2. { reflexivity. } case_decide as h3. { rewrite !pathCompressPreservesLength, !pathCompressPreservesLeafCount. reflexivity. }
  remember (nth (ancestor dsu (length dsu) a) _ _) as ya eqn:yb.
  destruct ya as [m | m]. { rewrite !pathCompressPreservesLength, !pathCompressPreservesLeafCount. reflexivity. } remember (nth (ancestor (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
    (length (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)))
    b) _ _) as za eqn:zb. destruct za as [n | n]. { rewrite !pathCompressPreservesLength, !pathCompressPreservesLeafCount. reflexivity. } case_decide as h4.
  - unfold performMerge.
    remember (ancestor dsu (length dsu) a) as x eqn:hx.
    assert (xL : x < length dsu).
    { rewrite hx. apply ancestorLtLength. { exact hN. } lia. }
    remember (ancestor (pathCompress dsu (length dsu) a x) (length (pathCompress dsu (length dsu) a x)) b) as y eqn:hy.
    assert (yL : y < length dsu).
    { rewrite hy. rewrite (ltac:(rewrite pathCompressPreservesLength; reflexivity): length dsu = (length (pathCompress dsu (length dsu) a x))) at 3. apply ancestorLtLength.
      - apply pathCompressPreservesNoIllegalIndices. { assumption. } { lia. } { exact xL. }
      - rewrite pathCompressPreservesLength. lia. }
    assert (lp : dsuLeafCount dsu = dsuLeafCount (pathCompress (pathCompress dsu (length dsu) a x) (length dsu) b y)).
    { rewrite !pathCompressPreservesLeafCount. reflexivity. }
    rewrite lp, !pathCompressPreservesLength.
    remember (pathCompress (pathCompress dsu (length dsu) a x) (length dsu) b y) as f eqn:hf.
    assert (cr : length dsu = length f).
    { rewrite hf, !pathCompressPreservesLength. reflexivity. }
    destruct (ltac:(lia) : x < y \/ y < x) as [jj | jj].
    + rewrite insert_take_drop, drop_insert_gt; try rewrite ?insert_length; try lia.
      rewrite insert_take_drop, take_app, take_take, take_length, (ltac:(lia) : y `min` x = x), (ltac:(lia) : x `min` length f = x), (ltac:(easy) : Ancestor (Unite m n) :: drop (S x) f = [Ancestor (Unite m n)] ++ drop (S x) f), take_app; try lia. simpl.
      assert (stp : take (y - x) [Ancestor (Unite m n)] = [Ancestor (Unite m n)]).
      { rewrite (ltac:(lia) : y - x = S (y - x - 1)). simpl. rewrite take_nil. reflexivity. }
      rewrite stp, (ltac:(easy) : ReferTo x :: drop (S y) f = [ReferTo x] ++ drop (S y) f).
      rewrite (ListDecomposition.listDecomposition f x y jj ltac:(lia) (Ancestor Unit)) at 4. unfold dsuLeafCount.
      rewrite !map_app, !list_sum_app, take_drop_commute, (ltac:(lia) : S x + (y - x - 1) = y). rewrite !pathCompressPreservesLength in yb, zb.
      rewrite <- hf in yb, zb. rewrite <- yb, <- zb. simpl. rewrite (ltac:(lia) : y + 1 = S y). lia.
    + rewrite insert_take_drop, drop_insert_le; try rewrite ?insert_length; try lia.
      rewrite insert_take_drop, take_app, take_take, take_length, (ltac:(lia) : y `min` x = y), (ltac:(lia) : x `min` length f = x), (ltac:(easy) : Ancestor (Unite m n) :: drop (S x) f = [Ancestor (Unite m n)] ++ drop (S x) f), take_app; try lia. simpl.
      assert (stp : take (y - x) [Ancestor (Unite m n)] = []).
      { rewrite (ltac:(lia) : y - x = 0). simpl. reflexivity. }
      rewrite stp, !app_nil_l, insert_take_drop, drop_drop, !take_drop_commute, (ltac:(lia) : S y + S (x - S y) = S x), (ltac:(lia) : S x + (y - x - 1) = S x), (ltac:(lia) : S y + (x - S y) = x); [| rewrite drop_length; lia].
      rewrite (ltac:(intros; simpl; easy) : forall a b, a :: b = [a] ++ b), ((ltac:(intros; simpl; easy) : forall a b, a :: b = [a] ++ b) (Ancestor (Unite m n)) (drop (S x) f)).
      rewrite (ListDecomposition.listDecomposition f y x jj ltac:(lia) (Ancestor Unit)) at 5. unfold dsuLeafCount.
      rewrite !map_app, !list_sum_app. rewrite !pathCompressPreservesLength in yb, zb.
      rewrite <- hf in yb, zb. rewrite <- yb, <- zb.
      simpl. rewrite (ltac:(lia) : x + 1 = S x).
      assert (ms : drop (S x) (take (S x) f) = []).
      { assert (mt : length (drop (S x) (take (S x) f)) = 0).
        { rewrite drop_length, take_length. lia. }
        exact (nil_length_inv _ mt). }
      rewrite ms. simpl.
      lia.
  - unfold performMerge.
    remember (ancestor dsu (length dsu) a) as x eqn:hx.
    assert (xL : x < length dsu).
    { rewrite hx. apply ancestorLtLength. { exact hN. } lia. }
    remember (ancestor (pathCompress dsu (length dsu) a x) (length (pathCompress dsu (length dsu) a x)) b) as y eqn:hy.
    assert (yL : y < length dsu).
    { rewrite hy. rewrite (ltac:(rewrite pathCompressPreservesLength; reflexivity): length dsu = (length (pathCompress dsu (length dsu) a x))) at 3. apply ancestorLtLength.
      - apply pathCompressPreservesNoIllegalIndices. { assumption. } { lia. } { exact xL. }
      - rewrite pathCompressPreservesLength. lia. }
    assert (lp : dsuLeafCount dsu = dsuLeafCount (pathCompress (pathCompress dsu (length dsu) a x) (length dsu) b y)).
    { rewrite !pathCompressPreservesLeafCount. reflexivity. }
    rewrite lp, !pathCompressPreservesLength.
    remember (pathCompress (pathCompress dsu (length dsu) a x) (length dsu) b y) as f eqn:hf.
    assert (cr : length dsu = length f).
    { rewrite hf, !pathCompressPreservesLength. reflexivity. }
    destruct (ltac:(lia) : x < y \/ y < x) as [jj | jj].
    + rewrite insert_take_drop, drop_insert_le; try rewrite ?insert_length; try lia.
      rewrite insert_take_drop, take_app, take_take, take_length, (ltac:(lia) : x `min` y = x), (ltac:(lia) : y `min` length f = y), (ltac:(easy) : Ancestor (Unite n m) :: drop (S y) f = [Ancestor (Unite n m)] ++ drop (S y) f), take_app; try lia. simpl.
      assert (stp : take (x - y) [Ancestor (Unite n m)] = []).
      { rewrite (ltac:(lia) : x - y = 0). easy. }
      rewrite stp, !app_nil_l, insert_take_drop, drop_drop, !take_drop_commute, (ltac:(lia) : S x + S (y - S x) = S y), (ltac:(lia) : S x + (y - S x) = y), (ltac:(lia) : S y + (x - y - 1) = S y); [| rewrite drop_length; lia].
      rewrite (ltac:(intros; simpl; easy) : forall a b, a :: b = [a] ++ b), ((ltac:(intros; simpl; easy) : forall a b, a :: b = [a] ++ b) (Ancestor (Unite n m))).
      rewrite (ListDecomposition.listDecomposition f x y jj ltac:(lia) (Ancestor Unit)) at 5. unfold dsuLeafCount.
      rewrite !map_app, !list_sum_app. rewrite !pathCompressPreservesLength in yb, zb.
      rewrite <- hf in yb, zb. rewrite <- yb, <- zb. simpl. rewrite (ltac:(lia) : y + 1 = S y).
      assert (ms : drop (S y) (take (S y) f) = []).
      { assert (mt : length (drop (S y) (take (S y) f)) = 0).
        { rewrite drop_length, take_length. lia. }
        exact (nil_length_inv _ mt). }
      rewrite ms. simpl.
      lia.
    + rewrite insert_take_drop, drop_insert_gt; try rewrite ?insert_length; try lia.
      rewrite insert_take_drop, take_app, take_take, take_length, (ltac:(lia) : x `min` y = y), (ltac:(lia) : y `min` length f = y), (ltac:(easy) : Ancestor (Unite n m) :: drop (S y) f = [Ancestor (Unite n m)] ++ drop (S y) f), take_app; try lia. simpl.
      assert (stp : take (x - y) [Ancestor (Unite n m)] = [Ancestor (Unite n m)]).
      { rewrite (ltac:(lia) : x - y = S (x - y - 1)). simpl. rewrite take_nil. reflexivity. }
      rewrite stp, !take_drop_commute, (ltac:(lia) : S y + (x - y - 1) = x).
      rewrite ((ltac:(intros; simpl; easy) : forall a b, a :: b = [a] ++ b) (ReferTo _)).
      rewrite (ListDecomposition.listDecomposition f y x jj ltac:(lia) (Ancestor Unit)) at 4. unfold dsuLeafCount.
      rewrite !map_app, !list_sum_app. rewrite !pathCompressPreservesLength in yb, zb.
      rewrite <- hf in yb, zb. rewrite <- yb, <- zb.
      simpl. rewrite (ltac:(lia) : x + 1 = S x).
      assert (ms : drop (S x) (take (S x) f) = []).
      { assert (mt : length (drop (S x) (take (S x) f)) = 0).
        { rewrite drop_length, take_length. lia. }
        exact (nil_length_inv _ mt). }
      lia.
Qed.

Lemma unitePreservesNoIllegalIndices (dsu : list Slot) (a b : nat) (h : noIllegalIndices dsu) : noIllegalIndices (unite dsu a b).
Proof.
  unfold unite. case_decide as h1. { exact h. } case_decide as h2. { exact h. }
  assert (gameover : noIllegalIndices
  (pathCompress
     (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
     (length (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)))
     b
     (ancestor
        (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
        (length
           (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))) b))).
  { rewrite pathCompressPreservesLength at 1.
    assert (step : noIllegalIndices (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))).
    { apply pathCompressPreservesNoIllegalIndices. { exact h. } { lia. } { apply ancestorLtLength; (assumption || lia). } }
    apply pathCompressPreservesNoIllegalIndices. { exact step. } { rewrite pathCompressPreservesLength. lia. } { apply ancestorLtLength; [| rewrite pathCompressPreservesLength; lia]. exact step. } }
  case_decide as heq. { exact gameover. }
  remember (nth (ancestor dsu (length dsu) a)
      (pathCompress
         (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
         (length
            (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)))
         b
         (ancestor
            (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
            (length
               (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)))
            b)) (Ancestor Unit)) as A eqn:hA.
  symmetry in hA. destruct A as [A | A]. { exact gameover. }
  remember (nth
      (ancestor
         (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
         (length
            (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)))
         b)
      (pathCompress
         (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
         (length
            (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)))
         b
         (ancestor
            (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
            (length
               (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)))
            b)) (Ancestor Unit)) as B eqn:hB.
  symmetry in hB. destruct B as [B | B]. { exact gameover. }
  case_decide as h3; unfold performMerge.
  - intros g j i. destruct (decide (g = ancestor (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
       (length
          (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))) b)) as [hs | hs].
    { rewrite <- hs, nth_lookup, list_lookup_insert in i.
      - simpl in i. rewrite !insert_length, !pathCompressPreservesLength. injection i. intro ht. rewrite <- ht. apply ancestorLtLength; (assumption || lia).
      - rewrite insert_length, hs, pathCompressPreservesLength, pathCompressPreservesLength. apply ancestorLtLength. { apply pathCompressPreservesNoIllegalIndices; try (assumption || lia). apply ancestorLtLength; try (assumption || lia). }
        rewrite pathCompressPreservesLength. lia. }
    rewrite nth_lookup, list_lookup_insert_ne in i; [| lia].
    destruct (decide (g = ancestor dsu (length dsu) a)) as [ht | ht].
    { rewrite ht, list_lookup_insert in i. { easy. } rewrite !pathCompressPreservesLength. apply ancestorLtLength; (assumption || lia). }
    rewrite list_lookup_insert_ne, <- nth_lookup in i; [| lia].
    rewrite !insert_length. exact (gameover _ _ i).
  - intros g j i. destruct (decide (g = ancestor dsu (length dsu) a)) as [hs | hs].
    { rewrite <- hs, nth_lookup, list_lookup_insert in i.
      - simpl in i. rewrite !insert_length, pathCompressPreservesLength. injection i. intro ht. rewrite <- ht, <- hs. apply ancestorLtLength; try rewrite pathCompressPreservesLength; try (assumption || lia). apply pathCompressPreservesNoIllegalIndices; try (assumption || lia). rewrite hs. apply ancestorLtLength; (assumption || lia).
      - rewrite !insert_length, !pathCompressPreservesLength, hs. apply ancestorLtLength; (assumption || lia). }
    rewrite nth_lookup, list_lookup_insert_ne in i; [| lia].
    destruct (decide (g = ancestor (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
       (length
          (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))) b)) as [ht | ht].
    { rewrite ht, list_lookup_insert in i. { easy. } rewrite !pathCompressPreservesLength. pose proof ancestorLtLength (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)) as t. rewrite !pathCompressPreservesLength in t. apply t; [| lia]. apply pathCompressPreservesNoIllegalIndices; try (assumption || lia). apply ancestorLtLength; (assumption || lia). }
    rewrite list_lookup_insert_ne, <- nth_lookup in i; [| lia].
    rewrite !insert_length. exact (gameover _ _ i).
Qed.

Lemma performMergePreservesWithoutCycles (dsu : list Slot) (a b : nat) (ha : a < length dsu) (hb : b < length dsu) (hD : a <> b) t1 t2 (h : noIllegalIndices dsu) (h1 : withoutCyclesN dsu (length dsu)) t3 (h3 : nth a dsu (Ancestor Unit) = Ancestor t3) t4 (h4 : nth b dsu (Ancestor Unit) = Ancestor t4) : withoutCyclesN (performMerge dsu t1 t2 a b) (length dsu).
Proof.
  unfold performMerge.
  intros i j.
  assert (als : noIllegalIndices (<[a:=ReferTo b]> (<[b:=Ancestor (Unite t2 t1)]> dsu))).
  { intros yy rr hh.
    rewrite !insert_length.
    destruct (Nat.eq_dec yy a) as [ww | ww].
    - rewrite ww in hh.
      rewrite nth_lookup, list_lookup_insert in hh.
      + simpl in hh.
        injection hh.
        intro als.
        subst b.
        pose proof ancestorLtLength dsu ltac:(assumption) (length dsu) i ltac:(lia). lia.
      + rewrite insert_length. lia.
    - rewrite nth_lookup in hh.
      destruct (Nat.eq_dec yy b) as [ii | ii].
      + subst yy.
        rewrite (list_lookup_insert_ne _ _ _ _ (ltac:(lia) : a ≠ b)), list_lookup_insert in hh.
        * simpl in hh. easy.
        * rewrite list_lookup_insert in hh.
          { simpl in hh. easy. }
          { lia. }
      + rewrite (list_lookup_insert_ne _ _ _ _ (Nat.neq_sym _ _ ww)), (list_lookup_insert_ne _ _ _ _ (Nat.neq_sym _ _ ii)), <- nth_lookup in hh.
        exact (h _ _ hh). }
  assert (hL : 2 <= length dsu).
  { destruct dsu as [| head [| head' tail]]; simpl in *; lia. }
  destruct (Nat.eq_dec (ancestor dsu (length dsu) i) a) as [hs | hs].
  { assert (ya : validChainToAncestor (<[a:=ReferTo b]> (<[b:=Ancestor (Unite t2 t1)]> dsu)) (ancestorChain dsu (length dsu) i ++ [b])).
    { pose proof validChainAncestorChain dsu (length dsu) i ltac:(assumption) ltac:(assumption) as [g1 [g2 g3]].
      repeat split.
      - intro ga.
        assert (ayw : length (ancestorChain dsu (length dsu) i ++ [b]) = length ([] : list nat)).
        { rewrite ga. reflexivity. }
        rewrite app_length in ayw. simpl in ayw. lia.
      - rewrite !insert_length, nth_lookup, lookup_app_l.
        + rewrite <- nth_lookup. exact g2.
        + pose proof (ltac:(lia) : 0 < length (ancestorChain dsu (length dsu) i) \/ length (ancestorChain dsu (length dsu) i) = 0) as [ds | ds]. { exact ds. }
          pose proof nil_length_inv _ ds. tauto.
      - intros ja k. rewrite app_length in k. simpl in k.
        pose proof (ltac:(lia) : S ja < length (ancestorChain dsu (length dsu) i) \/ S ja = length (ancestorChain dsu (length dsu) i)) as [u | u].
        + rewrite !nth_lookup, lookup_app_l, lookup_app_l, <- !nth_lookup; [| lia | lia].
          pose proof g3 ja ltac:(lia) as g4.
          assert (n1 : nth ja (ancestorChain dsu (length dsu) i) 0 <> a).
          { intro n1. rewrite n1 in g4. rewrite g4 in h3. easy. }
          assert (n2 : nth ja (ancestorChain dsu (length dsu) i) 0 <> b).
          { intro n2. rewrite n2 in g4. rewrite g4 in h4. easy. }
          rewrite !nth_lookup, !list_lookup_insert_ne, <- !nth_lookup. { assumption. }
          * rewrite <- nth_lookup. lia.
          * rewrite <- nth_lookup. lia.
        + assert (stp : nth (S ja) (ancestorChain dsu (length dsu) i ++ [b]) 0 = b).
          { rewrite nth_lookup, lookup_app_r. { rewrite <- u, (ltac:(lia) : S ja - S ja = 0). easy. } lia. }
          rewrite stp.
          pose proof ancestorEqLastAncestorChain dsu (length dsu) i as gh.
          rewrite hs in gh.
          assert (spt : nth ja (ancestorChain dsu (length dsu) i ++ [b]) 0 = a).
          { rewrite nth_lookup, lookup_app_l, (ltac:(lia) : ja = length (ancestorChain dsu (length dsu) i) - 1), <- nth_lookup. { exact gh. } lia. }
          rewrite spt, nth_lookup, list_lookup_insert. { easy. } rewrite insert_length. exact ha.
      - exists (Unite t2 t1).
        assert (ajk : nth (length (ancestorChain dsu (length dsu) i ++ [b]) - 1) (ancestorChain dsu (length dsu) i ++ [b]) 0 = b).
        { rewrite app_length. simpl. rewrite Nat.add_sub, nth_lookup, lookup_app_r, Nat.sub_diag. { easy. } lia. }
        rewrite ajk, nth_lookup, list_lookup_insert_ne, list_lookup_insert; (easy || lia). }
    pose proof validChainAncestorLength (<[a:=ReferTo b]> (<[b:=Ancestor (Unite t2 t1)]> dsu)) (ancestorChain dsu (length dsu) i ++ [b]) als ya i ltac:(rewrite nth_lookup, lookup_app_l; [destruct (length dsu) as [| g]; [simpl; easy |]; simpl; destruct (nth i dsu (Ancestor Unit)) as [jk | jk]; easy | apply zeroLtLengthAncestorChain]) as ua. rewrite !insert_length in ua.
    pose proof ancestorEqLastAncestorChain (<[a:=ReferTo b]> (<[b:=Ancestor (Unite t2 t1)]> dsu)) (length dsu) i as ra.
    rewrite <- !ua, nth_lookup, lookup_app_r, app_length, (ltac:(easy) : length [b] = 1), Nat.add_sub, Nat.sub_diag in ra; [| rewrite app_length; simpl; lia]. symmetry in ra. rewrite (ltac:(easy) : default 0 ([b] !! 0) = b) in ra. rewrite !insert_length, ra, nth_lookup, list_lookup_insert_ne, list_lookup_insert; (easy || lia). }
  destruct (Nat.eq_dec (ancestor dsu (length dsu) i) b) as [ht | ht].
  { assert (ter: validChainToAncestor (<[a:=ReferTo b]> (<[b:=Ancestor (Unite t2 t1)]> dsu)) (ancestorChain dsu (length dsu) i)).
    { pose proof validChainAncestorChain dsu (length dsu) i ltac:(assumption) ltac:(assumption) as [g1 [g2 g3]].
      repeat split.
      - destruct (length dsu) as [| g]. { simpl. easy. } simpl. destruct (nth i dsu (Ancestor Unit)) as [jk | jk]; easy.
      - rewrite !insert_length. assumption.
      - intros y u.
        pose proof g3 y u as su.
        assert (n1 : nth y (ancestorChain dsu (length dsu) i) 0 <> a).
        { intro w. rewrite w, h3 in su. easy. }
        assert (n2 : nth y (ancestorChain dsu (length dsu) i) 0 <> b).
        { intro w. rewrite w, h4 in su. easy. }
        rewrite !nth_lookup, !list_lookup_insert_ne, <- !nth_lookup, su; [easy | |]; rewrite <- nth_lookup; lia.
      - exists (Unite t2 t1).
        rewrite ancestorEqLastAncestorChain, ht, !nth_lookup, list_lookup_insert_ne, list_lookup_insert; [easy | |]; lia. }
    pose proof validChainAncestorLength (<[a:=ReferTo b]> (<[b:=Ancestor (Unite t2 t1)]> dsu)) (ancestorChain dsu (length dsu) i) als ter i ltac:(destruct (length dsu); simpl; destruct (nth i dsu (Ancestor Unit)); simpl; try lia) as nn.
    rewrite <- ancestorEqLastAncestorChain, <- nn, ancestorEqLastAncestorChain, ht, !nth_lookup, list_lookup_insert_ne, list_lookup_insert; (easy || lia). }
  assert (ter : validChainToAncestor (<[a:=ReferTo b]> (<[b:=Ancestor (Unite t2 t1)]> dsu)) (ancestorChain dsu (length dsu) i)).
  { pose proof validChainAncestorChain dsu (length dsu) i ltac:(assumption) ltac:(assumption) as [g1 [g2 g3]].
    repeat split.
    - destruct (length dsu); try easy; simpl; destruct (nth i _ _); easy.
    - rewrite !insert_length. assumption.
    - intros y u.
      pose proof g3 y u as us.
      assert (n1 : nth y (ancestorChain dsu (length dsu) i) 0 <> a).
      { intro g. rewrite g, h3 in us. easy. }
      assert (n2 : nth y (ancestorChain dsu (length dsu) i) 0 <> b).
      { intro g. rewrite g, h4 in us. easy. }
      rewrite nth_lookup, !list_lookup_insert_ne; [rewrite <- nth_lookup; assumption | |]; lia.
    - rewrite ancestorEqLastAncestorChain, nth_lookup, !list_lookup_insert_ne; [| lia | lia]. rewrite <- nth_lookup.
      pose proof h1 i j as ji.
      destruct (nth (ancestor dsu (length dsu) i) dsu (Ancestor Unit)) as [nn | nn]. { easy. } exists nn. reflexivity. }
  pose proof validChainAncestorLength (<[a:=ReferTo b]> (<[b:=Ancestor (Unite t2 t1)]> dsu)) (ancestorChain dsu (length dsu) i) als ter i ltac:(destruct (length dsu); simpl; destruct (nth i dsu (Ancestor Unit)); simpl; try lia) as nn.
  rewrite <- ancestorEqLastAncestorChain, <- nn, ancestorEqLastAncestorChain, nth_lookup, !list_lookup_insert_ne, <- nth_lookup; [| lia | lia]. apply (h1 i j).
Qed.

Lemma unitePreservesWithoutCycles (dsu : list Slot) (a b : nat) (h : noIllegalIndices dsu) (h1 : withoutCyclesN dsu (length dsu)) : withoutCyclesN (unite dsu a b) (length dsu).
Proof.
  unfold unite. case_decide as a1. { exact h1. }
  case_decide as a2. { exact h1. }
  assert (hR : withoutCyclesN
  (pathCompress
     (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
     (length (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)))
     b
     (ancestor
        (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
        (length
           (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))) b))
  (length dsu)).
  { pose proof pathCompressPreservesWithoutCycles _ h1 h (length dsu) a ltac:(lia) as step1. rewrite !pathCompressPreservesLength.
    pose proof pathCompressPreservesWithoutCycles (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)) ltac:(rewrite pathCompressPreservesLength; exact step1) ltac:(apply pathCompressPreservesNoIllegalIndices; try rewrite pathCompressPreservesLength; try (assumption || lia); apply ancestorLtLength; (assumption || lia)) (length dsu) b ltac:(rewrite pathCompressPreservesLength; lia) as step2. rewrite !pathCompressPreservesLength in step2. exact step2. }
  case_decide as a3. { exact hR. }
  remember (nth _ _ _) as g eqn:hg. symmetry in hg. destruct g as [g | g]. { exact hR. }
  remember (nth (ancestor _ _ b) _ _) as g1 eqn:hg1. symmetry in hg1. destruct g1 as [g1 | g1]. { exact hR. }
  case_decide as hs.
  - pose proof performMergePreservesWithoutCycles (pathCompress
        (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
        (length
           (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))) b
        (ancestor
           (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
           (length
              (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)))
           b)) (ancestor
        (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
        (length
           (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))) b)
     (ancestor dsu (length dsu) a) ltac:(rewrite !pathCompressPreservesLength,!pathCompressPreservesAncestorLength; try (assumption || lia); apply ancestorLtLength; (assumption || lia)) ltac:(rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia)) ltac:(rewrite !pathCompressPreservesLength,!pathCompressPreservesAncestorLength in *; try (assumption || lia)) g1 g ltac:(apply pathCompressPreservesNoIllegalIndices; (try apply pathCompressPreservesNoIllegalIndices); (try rewrite !pathCompressPreservesLength); (try lia); (try assumption); [| rewrite pathCompressPreservesAncestorLength; try (assumption || lia)]; apply ancestorLtLength; (assumption || lia)) ltac:(pose proof pathCompressPreservesWithoutCycles (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)) as kw; rewrite !pathCompressPreservesLength in kw; rewrite !pathCompressPreservesLength; apply kw; (try lia); (try apply pathCompressPreservesNoIllegalIndices); (try apply pathCompressPreservesWithoutCycles); (try assumption); (try lia); apply ancestorLtLength; (assumption || lia)) as ii.
     rewrite !pathCompressPreservesLength in *.
     exact (ii g1 hg1 g hg).
  - pose proof performMergePreservesWithoutCycles (pathCompress
        (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
        (length
           (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))) b
        (ancestor
           (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
           (length
              (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)))
           b)) (ancestor dsu (length dsu) a)
     (ancestor
        (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))
        (length
           (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a))) b) ltac:(rewrite !pathCompressPreservesLength; apply ancestorLtLength; (assumption || lia)) ltac:(rewrite !pathCompressPreservesLength,!pathCompressPreservesAncestorLength; try (assumption || lia); apply ancestorLtLength; (assumption || lia)) ltac:(rewrite !pathCompressPreservesLength,!pathCompressPreservesAncestorLength in *; try (assumption || lia)) g g1 ltac:(apply pathCompressPreservesNoIllegalIndices; (try apply pathCompressPreservesNoIllegalIndices); (try rewrite !pathCompressPreservesLength); (try lia); (try assumption); [| rewrite pathCompressPreservesAncestorLength; try (assumption || lia)]; apply ancestorLtLength; (assumption || lia)) ltac:(pose proof pathCompressPreservesWithoutCycles (pathCompress dsu (length dsu) a (ancestor dsu (length dsu) a)) as kw; rewrite !pathCompressPreservesLength in kw; rewrite !pathCompressPreservesLength; apply kw; (try lia); (try apply pathCompressPreservesNoIllegalIndices); (try apply pathCompressPreservesWithoutCycles); (try assumption); (try lia); apply ancestorLtLength; (assumption || lia)) as ii.
     rewrite !pathCompressPreservesLength in *.
     exact (ii g hg g1 hg1).
Qed.
