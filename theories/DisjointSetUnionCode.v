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
  - rewrite (ltac:(destruct head; reflexivity) : nth (S n) (convertToArray (head :: tail)) 0%Z = nth n (convertToArray tail) 0%Z), (ltac:(simpl; reflexivity) : nth (S _) (_ :: _) _ = _). apply IH. simpl in hN. lia.
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

Lemma nthLowerBoundConvertAuxStep (dsu : list Slot) (h : length dsu < 256) (h1 : Z.to_nat (dsuLeafCount dsu) < 128) (n : nat) (hn : n < length dsu) x (h2 : nth n dsu (Ancestor Unit) = Ancestor x) : leafCount x < 128.
Proof.
  revert n hn x h2. induction dsu as [| head tail IH].
  { simpl. intro. lia. }
  intros n h2 h3 h4.
  destruct n as [| n].
  - simpl in h4. unfold dsuLeafCount in h1. rewrite Nat2Z.id, map_cons, (ltac:(simpl; reflexivity) : list_sum (_ :: _) = _ + list_sum _) in h1. rewrite h4 in h1. lia.
  - exact (IH ltac:(simpl in h; lia) ltac:(unfold dsuLeafCount in h1; rewrite Nat2Z.id in h1; rewrite map_cons, (ltac:(simpl; reflexivity) : list_sum (_ :: _) = _ + list_sum _) in h1; unfold dsuLeafCount; rewrite Nat2Z.id; lia) n ltac:(simpl in h2; lia) h3 ltac:(simpl in h4; exact h4)).
Qed.

Lemma nthLowerBoundConvertAux (dsu : list Slot) (h : length dsu < 256) (h1 : Z.to_nat (dsuLeafCount dsu) < 128) (n : nat) : Z.le 0%Z (nth n (convertToArray dsu) (0%Z)).
Proof.
  revert n h1. induction dsu as [| head tail IH].
  { cbv. intros a b. destruct a; easy. }
  intros [| a] b.
  - simpl. destruct head as [x | x]. { simpl. lia. }
    simpl. unfold dsuLeafCount in b. rewrite Nat2Z.id, map_cons, (ltac:(simpl; reflexivity) : list_sum (_ :: _) = _ + list_sum _) in b. lia.
  - rewrite (ltac:(simpl; destruct head; easy) : nth (S a) (convertToArray (head :: tail)) (0%Z) = nth a (convertToArray tail) (0%Z)).
    exact (IH ltac:(simpl in h; lia) a ltac:(unfold dsuLeafCount in b; rewrite Nat2Z.id, map_cons, (ltac:(simpl; reflexivity) : list_sum (_ :: _) = _ + list_sum _) in b; unfold dsuLeafCount; rewrite Nat2Z.id; lia)).
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
  { easy. } rewrite (ltac:(simpl; reflexivity) : length (_ :: _) = _) in *. rewrite (ltac:(lia) : S (length tail') - 1 = length tail') in IH. rewrite <- IH.
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

Lemma runAncestor1 (dsu : list Slot) (hL : length dsu = 100) (hM : Z.to_nat (dsuLeafCount dsu) = length dsu) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (whatever2 a : Z) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) (communication : list Z) continuation whatever n (hN : n < 100) : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state state
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
  ())) >>= continuation)) = invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state state
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
  (λ _ : varsfuncdef_0__ancestor, repeat 0%Z 20) (continuation tt)).
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
  autorewrite with advance_program.
  case_decide as hs; [| rewrite lengthConvert in hs; lia].
  rewrite !leftIdentity, (ltac:(easy) : toSigned (coerceInt 0%Z 8) 8 = 0%Z).
  rewrite (ltac:(easy) : @nth_lt (arrayType arrayIndex0 environment0 arraydef_0__dsu) (convertToArray dsu) (Z.to_nat a) hs = @nth_lt Z (convertToArray dsu) (Z.to_nat a) hs), (nth_lt_default (convertToArray dsu) (Z.to_nat a) hs 0%Z), nthConvert; [| lia].
  remember (nth (Z.to_nat a) dsu (Ancestor Unit)) as g eqn:hg. symmetry in hg.
  destruct g as [g | g]; clear hs.
  + case_bool_decide as hs. { unfold toSigned in hs. pose proof h1 (Z.to_nat a) g hg. case_decide; [| lia]. lia. } rewrite (ltac:(easy) : liftToWithinLoop
  (Done
     (WithLocalVariables arrayIndex0 (arrayType arrayIndex0 environment0)
        varsfuncdef_0__ancestor) withLocalVariablesReturnValue bool false) = Done _ _ bool false), !leftIdentity.
    rewrite liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop. unfold numberLocalGet at 1. rewrite <- !bindAssoc, pushNumberGet2, !step, !leftIdentity, liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop. unfold retrieve at 1. rewrite <- !bindAssoc, pushDispatch2. autorewrite with advance_program. clear hs. case_decide as hs; [| rewrite lengthConvert in hs; lia]. rewrite liftToWithinLoopBind, <- !bindAssoc, dropWithinLoopLiftToWithinLoop, <- !bindAssoc. unfold numberLocalSet at 1. pose proof (@pushNumberSet2 arrayIndex0 (arrayType arrayIndex0 environment0) varsfuncdef_0__ancestor _ (λ _ : varsfuncdef_0__ancestor, false)
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

Lemma runAncestor (dsu : list Slot) (hL : length dsu = 100) (h1 : noIllegalIndices dsu) (h2 : withoutCyclesN dsu (length dsu)) (a b : Z) (hLe1 : Z.le 0 a) (hLt1 : Z.lt a 100) (hLe2 : Z.le 0 b) (hLt2 : Z.lt b 100) continuation whatever : invokeContractAux (repeat 1%Z 20) (repeat 0%Z 20) 0 state state
  [a; b] 1 arrayIndex0 arrayIndexEqualityDecidable0
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
  [a; b] 1 arrayIndex0 arrayIndexEqualityDecidable0
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
  unfold funcdef_0__ancestor. rewrite !leftIdentity, <- !bindAssoc.
  assert (hs : update (λ _ : varsfuncdef_0__ancestor, 0%Z) vardef_0__ancestor_vertex a = fun x => match x with | vardef_0__ancestor_vertex => a | _ => 0%Z end).
  { unfold update. apply functional_extensionality_dep. intro x. destruct x; easy. }
  rewrite hs. unfold numberLocalGet at 1. autorewrite with advance_program.
  unfold numberLocalSet at 1. pose proof @pushNumberSet2 arrayIndex0 (arrayType arrayIndex0 environment0) varsfuncdef_0__ancestor _ (λ _ : varsfuncdef_0__ancestor, false) (λ _1 : varsfuncdef_0__ancestor,
  match _1 with
| vardef_0__ancestor_vertex =>
    a
| vardef_0__ancestor_work =>
    0%Z
end) (λ _ : varsfuncdef_0__ancestor,
  @repeat Z
  0%Z 20) vardef_0__ancestor_work a as step. rewrite step. clear step hs.
  assert (hs : (update (λ _0 : varsfuncdef_0__ancestor,
  match _0
with
| vardef_0__ancestor_vertex =>
    a
| vardef_0__ancestor_work =>
    0%Z
end) vardef_0__ancestor_work
  a) = fun x => match x with | vardef_0__ancestor_vertex => a | vardef_0__ancestor_work => a end). { apply functional_extensionality_dep. intro x. destruct x; easy. }
  rewrite hs. clear hs.
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
