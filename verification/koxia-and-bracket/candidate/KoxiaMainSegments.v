From CoqCP Require Import Options Imperative Execution.
From Submission Require Import KoxiaPreprocess KoxiaIntegers KoxiaArrays.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
Local Open Scope Z_scope.
Definition bracketByte (opening:bool):Z := if opening then 40 else 41.
Definition solveForwardNums finish := update (update (fun _:varsfuncdef_0__solve=>0) vardef_0__solve_begin 0) vardef_0__solve_end finish.
Definition solveReverseNums start finish := update (update (fun _:varsfuncdef_0__solve=>0) vardef_0__solve_begin start) vardef_0__solve_end finish.
Definition reverseBrackets (word:list bool):=rev(map negb word).
Lemma reverseBrackets_length word : length (reverseBrackets word)=length word.
Proof. unfold reverseBrackets. rewrite length_rev,length_map. reflexivity. Qed.
Lemma mappedByte_nth word index : (index<length word)%nat ->
  nth index (map bracketByte word) 0=bracketByte(nth index word false).
Proof.
  intro room. rewrite (nth_indep _ 0 (bracketByte false)) by (rewrite length_map; exact room).
  apply map_nth.
Qed.
Lemma reverseBrackets_nth word index : (index<length word)%nat ->
  negb (nth index (reverseBrackets word) false)=nth (length word-S index) word false.
Proof.
  intro room. unfold reverseBrackets. rewrite rev_nth by (rewrite length_map; exact room).
  rewrite length_map.
  rewrite (nth_indep _ false (negb false)) by (rewrite length_map; lia).
  rewrite map_nth,negb_involutive. reflexivity.
Qed.

Lemma forward_prepInput state a b padding :
  Z.of_nat (length (a++b))<=500000 ->
  memory state arraydef_0__sequence=map bracketByte (a++b)++padding ->
  prepInput state (solveForwardNums (Z.of_nat (length a))) false (Z.of_nat (length a)) a.
Proof.
  intros bound source offset room. unfold prepReadAddress,solveForwardNums.
  rewrite lookupDifferent by congruence. rewrite lookupSame.
  assert (indexEq : Z.of_nat (length a)-Z.of_nat (length a-S offset)-1=Z.of_nat offset) by lia.
  rewrite indexEq. rewrite coerce64_small by (rewrite length_app,Nat2Z.inj_add in bound; cbn; lia).
  rewrite Z.add_0_l,Nat2Z.id. split; [lia|].
  rewrite source. split; [rewrite length_app,length_map,length_app; lia|].
  rewrite app_nth1 by (rewrite length_map,length_app; lia).
  rewrite mappedByte_nth by (rewrite length_app; lia).
  rewrite app_nth1 by exact room. reflexivity.
Qed.

Lemma reverse_prepInput state a b padding :
  Z.of_nat (length (a++b))<=500000 ->
  memory state arraydef_0__sequence=map bracketByte (a++b)++padding ->
  prepInput state (solveReverseNums (Z.of_nat (length a)) (Z.of_nat (length (a++b)))) true
    (Z.of_nat (length (reverseBrackets b))) (reverseBrackets b).
Proof.
  intros bound source offset room. rewrite reverseBrackets_length in room |- *.
  unfold prepReadAddress,solveReverseNums. rewrite lookupSame.
  assert (indexEq : Z.of_nat (length b)-Z.of_nat (length b-S offset)-1=Z.of_nat offset) by lia.
  rewrite indexEq.
  rewrite (coerce64_small (Z.of_nat (length (a++b))-Z.of_nat offset)) by
    (rewrite length_app,Nat2Z.inj_add in *; cbn; lia).
  assert (addressEq : Z.of_nat (length (a++b))-Z.of_nat offset-1=Z.of_nat (length a+(length b-S offset)))
    by (rewrite length_app,Nat2Z.inj_add; lia).
  rewrite addressEq,coerce64_small by (rewrite length_app,Nat2Z.inj_add in bound; cbn; lia).
  rewrite Nat2Z.id. split; [lia|]. rewrite source. split.
  - rewrite !length_app,length_map,length_app. lia.
  - rewrite app_nth1 by (rewrite length_map,length_app; lia).
    rewrite mappedByte_nth by (rewrite length_app; lia).
    rewrite app_nth2 by lia. replace (length a+(length b-S offset)-length a)%nat with (length b-S offset)%nat by lia.
    rewrite reverseBrackets_nth by exact room. reflexivity.
Qed.
