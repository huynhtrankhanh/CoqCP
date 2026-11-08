From CoqCP Require Import Options Imperative Execution.
From UniformMemoFixture Require Import UniformMemoProgram.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith Lia.
Open Scope Z_scope.
Module UniformMemoPutAction.
Definition LocalAction R := Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__uniformMemoPutNew)
  withLocalVariablesReturnValue R.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__uniformMemoPutNew.
Definition after_hash : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__uniformMemoPutNew_body in funcdef_0__uniformMemoPutNew_body in
  lazymatch code with bind _ ?next =>
    let code := eval cbn beta in (next tt) in
    lazymatch code with bind (bind _ ?branch) _ =>
      let code := eval cbn beta iota in (branch true) in
      lazymatch code with bind _ ?next =>
        let code := eval cbn beta in (next tt) in
        lazymatch code with bind (bind _ ?branch) _ =>
          let code := eval cbn beta iota in (branch false) in
          lazymatch code with bind _ ?next =>
            let code := eval cbn beta in (next tt) in exact code
          end
        end
      end
    end
  end).
Definition after_bucket : LocalAction unit := ltac:(
  let code := eval unfold after_hash in after_hash in
  lazymatch code with bind _ ?next => let code := eval cbn beta in (next tt) in exact code end).
Definition inserted (s : @Execution.Machine arrayIndex1 (arrayType _ environment1)) count bucket node depth value size :=
  let prior := List.nth bucket (memory s arraydef_0__uniformMemoBuckets) 0 in
  let grown := withMemory s (growArrays (memory s) arraydef_0__uniformMemoEntries (S count) (0,0,0,0)) in
  let entries := withMemory grown (modifyArray (memory grown) arraydef_0__uniformMemoEntries count (node,depth,value,prior)) in
  let buckets := withMemory entries (modifyArray (memory entries) arraydef_0__uniformMemoBuckets bucket (Z.of_nat (S count))) in
  withMemory buckets (modifyArray (memory buckets) arraydef_0__uniformMemoState 0 (Z.of_nat (S count),size,0,0)).
Lemma local_get (f : Frame) name : execLocal (R := Z) (numberLocalGet _ _ _ name) f = Some (nums f name,f).
Proof. reflexivity. Qed.
Lemma local_done {R} (f : Frame) (value : R) : execLocal (Done _ _ _ value) f = Some (value,f).
Proof. reflexivity. Qed.
Lemma local_grow (f : Frame) count : execLocal (grow _ _ _ arraydef_0__uniformMemoEntries (Z.of_nat (S count)) (0,0,0,0)) f =
  Some (tt, setMachine f (withMemory (machine f) (growArrays (memory (machine f)) arraydef_0__uniformMemoEntries (S count) (0,0,0,0)))).
Proof. destruct f. cbn [grow execLocal localStep step]. now rewrite Nat2Z.id. Qed.
Definition maximum : Z := 18446744073709551615.
Lemma add_count (f : Frame) count : nums f vardef_0__uniformMemoPutNew_count = Z.of_nat count ->
  Z.of_nat count < maximum ->
  execLocal (addInt 64 (numberLocalGet _ _ _ vardef_0__uniformMemoPutNew_count) (Done _ _ _ 1)) f =
  Some (Z.of_nat (S count),f).
Proof.
 intros Hcount Hlimit. unfold addInt. rewrite execLocal_bind, local_get. cbn [optionBind fst snd].
 rewrite execLocal_bind, local_done. cbn [optionBind fst snd]. rewrite Hcount. unfold maximum in Hlimit.
 replace (Z.of_nat count + 1) with (Z.of_nat (S count)) by lia.
 unfold coerceInt. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma read_bucket (f : Frame) bucket :
  (bucket < length (memory (machine f) arraydef_0__uniformMemoBuckets))%nat ->
  execLocal (retrieve _ _ _ arraydef_0__uniformMemoBuckets (Z.of_nat bucket)) f =
  Some (List.nth bucket (memory (machine f) arraydef_0__uniformMemoBuckets) 0,f).
Proof.
 destruct f. intro H. cbn [retrieve execLocal localStep step]. rewrite Nat2Z.id.
 case_decide; [|lia]. rewrite nth_lt_default with (default := 0). reflexivity.
Qed.
Lemma store_entry (f : Frame) count value :
  (count < length (memory (machine f) arraydef_0__uniformMemoEntries))%nat ->
  execLocal (store _ _ _ arraydef_0__uniformMemoEntries (Z.of_nat count) value) f =
  Some (tt,setMachine f (withMemory (machine f) (modifyArray (memory (machine f)) arraydef_0__uniformMemoEntries count value))).
Proof. destruct f. intro H. cbn [store execLocal localStep step]. rewrite Nat2Z.id. case_decide; [reflexivity|lia]. Qed.
Lemma store_bucket (f : Frame) bucket value :
  (bucket < length (memory (machine f) arraydef_0__uniformMemoBuckets))%nat ->
  execLocal (store _ _ _ arraydef_0__uniformMemoBuckets (Z.of_nat bucket) value) f =
  Some (tt,setMachine f (withMemory (machine f) (modifyArray (memory (machine f)) arraydef_0__uniformMemoBuckets bucket value))).
Proof. destruct f. intro H. cbn [store execLocal localStep step]. rewrite Nat2Z.id. case_decide; [reflexivity|lia]. Qed.
Lemma store_state (f : Frame) value :
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  execLocal (store _ _ _ arraydef_0__uniformMemoState 0 value) f =
  Some (tt,setMachine f (withMemory (machine f) (modifyArray (memory (machine f)) arraydef_0__uniformMemoState 0 value))).
Proof. destruct f. intro H. cbn [store execLocal localStep step]. case_decide; [reflexivity|lia]. Qed.
Lemma modify_other (values : forall name, list (arrayType _ environment1 name)) name slot value other :
  other <> name -> modifyArray values name slot value other = values other.
Proof. destruct name, other; intro H; try congruence; reflexivity. Qed.
Theorem generated_writes (f : Frame) count bucket size :
  nums f vardef_0__uniformMemoPutNew_count = Z.of_nat count ->
  nums f vardef_0__uniformMemoPutNew_bucket = Z.of_nat bucket ->
  Z.of_nat count < maximum ->
  (bucket < length (memory (machine f) arraydef_0__uniformMemoBuckets))%nat ->
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) =
    (Z.of_nat count,size,0,0) ->
  execLocal after_bucket f = Some (tt,setMachine f (inserted (machine f) count bucket
    (nums f vardef_0__uniformMemoPutNew_node) (nums f vardef_0__uniformMemoPutNew_depth)
    (nums f vardef_0__uniformMemoPutNew_value) size)).
Proof.
 intros Hcount Hbucket Hlimit Hbuckets Hstate Hstateval.
 destruct f as [s bs ns]. cbn [machine nums] in *.
 unfold after_bucket, after_hash.
 cbv beta iota zeta delta [numberLocalGet retrieve store grow addInt bind
   execLocal localStep step optionBind setNum setMachine machine nums bools fst snd].
rewrite Hcount, Hbucket.
  unfold maximum in Hlimit.
  replace (coerceInt (Z.of_nat count + 1) 64) with (Z.of_nat (S count))
    by (unfold coerceInt; rewrite Z.mod_small by lia; lia).
  repeat rewrite Nat2Z.id. cbn [withMemory memory].
  rewrite growArrays_other by discriminate.
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z).
  cbn [fst snd].
  cbn [withMemory memory]. rewrite growArrays_same, growList_length.
  case_decide; [|lia]. cbn [fst snd machine nums bools].
  rewrite Hbucket, Hcount.
  replace (coerceInt (Z.of_nat count + 1) 64) with (Z.of_nat (S count))
    by (unfold coerceInt; rewrite Z.mod_small by lia; lia).
  rewrite Nat2Z.id. cbn [withMemory memory].
  rewrite modify_other by discriminate. rewrite growArrays_other by discriminate.
  case_decide; [|lia]. cbn [fst snd machine nums bools].
  rewrite Hcount. replace (coerceInt (Z.of_nat count + 1) 64) with (Z.of_nat (S count))
    by (unfold coerceInt; rewrite Z.mod_small by lia; lia).
  cbn [withMemory memory]. repeat rewrite modify_other by discriminate.
  repeat rewrite growArrays_other by discriminate.
  replace (Z.to_nat 0) with 0%nat by reflexivity.
  case_decide; [|lia]. rewrite nth_lt_default with (default := (0,0,0,0)).
  cbn [withMemory memory]. repeat rewrite modify_other by discriminate.
  repeat rewrite growArrays_other by discriminate.
  case_decide; [|lia].
  destruct (memory s arraydef_0__uniformMemoState) as [|[[[a b] c] d] tail] eqn:Hs; [cbn in Hstate; lia|].
  cbn in Hstateval. inversion Hstateval; subst.
  unfold inserted. cbn. reflexivity. Qed.
End UniformMemoPutAction.
