From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts HashScan.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module InternTailExecution.
Import IndexExecution.
Import HashScanExecution.

Definition after_scan : HashScanExecution.LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__intern_body in funcdef_0__intern_body in
  let code := eval cbn zeta in code in
  lazymatch code with bind _ ?next =>
    let code := eval cbn beta in (next tt) in
    lazymatch code with bind _ ?next =>
      let code := eval cbn beta in (next tt) in
      lazymatch code with bind (bind _ ?branch) _ =>
        let code := eval cbn beta iota in (branch true) in
        lazymatch code with bind _ ?next =>
          let code := eval cbn beta in (next tt) in
          lazymatch code with bind _ ?next =>
            let code := eval cbn beta in (next tt) in
            lazymatch code with bind _ ?next =>
              let code := eval cbn beta in (next tt) in
              lazymatch code with bind _ ?next => exact (next tt) end
            end
          end
        end
      end
    end
  end).


Theorem after_scan_found (f : Frame) : nums f vardef_0__intern_found <> 0 ->
  execLocal after_scan f = Some (tt,f).
Proof.
  intros Hfound. unfold after_scan.
  cbv beta iota zeta delta [bind numberLocalGet execLocal localStep nums optionBind fst snd].
  rewrite bool_decide_false by exact Hfound. reflexivity.
Qed.

Theorem after_scan_full (f : Frame) :
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__intern_found = 0 ->
  List.nth 1 (memory (machine f) arraydef_0__meta) 0 = maximum ->
  execLocal after_scan f = Some (tt,setMachine f (store_meta (machine f) 8 1)).
Proof.
  intros Hmeta Hfound Hcount. destruct f as [s bs ns]. cbn [machine nums] in *.
  change (@List.nth Z 1 (memory s arraydef_0__meta) 0 = maximum) in Hcount.
  cbv beta iota zeta delta [memory] in Hmeta, Hcount.
  unfold after_scan.
  repeat first [rewrite Hfound |rewrite Hcount
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 1) with 1%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |rewrite nth_lt_default with (default := 0%Z)
    |rewrite bool_decide_true by reflexivity
    |progress cbv beta iota zeta delta [bind numberLocalGet retrieve store execLocal localStep step
      optionBind setMachine machine nums bools fst snd memory]
    |match goal with |- context [decide (Nat.lt ?slot ?len)] =>
      let Hready := fresh "Hready" in
      assert (Hready : (slot < len)%nat) by lia;
      case_decide; [clear Hready|contradiction] end].
  reflexivity.
Qed.

Definition append_state (s : Machine) n bucket tuple :=
  let saved := store_meta s 0 (Z.of_nat n) in
  let grown := withMemory saved (growArrays (memory saved) arraydef_0__formulas (S n) (0,0,0)) in
  let grown := withMemory grown (growArrays (memory grown) arraydef_0__formulaLinks (S n) 0) in
  let written := withMemory grown (modifyArray (memory grown) arraydef_0__formulas n tuple) in
  let written := withMemory written (modifyArray (memory written) arraydef_0__formulaLinks n
    (List.nth bucket (memory written arraydef_0__formulaBuckets) 0)) in
  let written := withMemory written (modifyArray (memory written) arraydef_0__formulaBuckets bucket (Z.of_nat (S n))) in
  store_meta written 1 (Z.of_nat (S n)).

Lemma modify_other (values : forall name, list (arrayType _ environment1 name)) name slot value other :
  other <> name -> modifyArray values name slot value other = values other.
Proof. destruct name, other; intro H; try congruence; reflexivity. Qed.
Lemma modify_same (values : forall name, list (arrayType _ environment1 name)) name slot value :
  modifyArray values name slot value name = <[slot := value]> (values name).
Proof. destruct name; reflexivity. Qed.

Theorem after_scan_fresh (f : Frame) n bucket :
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  List.nth 1 (memory (machine f) arraydef_0__meta) 0 = Z.of_nat n ->
  Z.of_nat n < maximum ->
  nums f vardef_0__intern_found = 0 ->
  nums f vardef_0__intern_bucket = Z.of_nat bucket ->
  (bucket < length (memory (machine f) arraydef_0__formulaBuckets))%nat ->
  execLocal after_scan f = Some (tt,setMachine f (append_state (machine f) n bucket (sought f))).
Proof.
  intros Hmeta Hcount Hlimit Hfound Hbucket Hbucketbound.
  destruct f as [s bs ns]. cbn [nums machine] in *.
  change (@List.nth Z 1 (memory s arraydef_0__meta) 0 = Z.of_nat n) in Hcount.
  cbv beta iota zeta delta [memory] in Hmeta, Hcount, Hbucketbound.
  unfold after_scan. unfold maximum in Hlimit.
  repeat first [rewrite Hfound |rewrite Hbucket |rewrite Hcount
    |rewrite nth_lt_default with (default := 0%Z)
    |rewrite growArrays_other by discriminate |rewrite growArrays_same
    |rewrite modify_other by discriminate
    |rewrite modify_same
    |rewrite ArrayFacts.nth_insert_other by lia
    |rewrite Nat2Z.id
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 1) with 1%nat by reflexivity
    |progress replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia
    |match goal with |- context [coerceInt ?value 64] =>
        rewrite (coerce_word value) by (unfold word, maximum; lia) end
    |match goal with |- context [bool_decide ?P] => first
        [rewrite (bool_decide_true P) by (first [reflexivity|lia])
        |rewrite (bool_decide_false P) by lia] end
    |progress cbv beta iota zeta delta [bind numberLocalGet numberLocalSet retrieve store grow addInt
      execLocal localStep step optionBind setNum setMachine machine nums bools fst snd withMemory memory]
    |match goal with |- context [decide (Nat.lt ?slot ?len)] =>
        let Hready := fresh "Hready" in
        assert (Hready : (slot < len)%nat) by
          (repeat rewrite length_insert; try rewrite growList_length; lia);
        case_decide; [clear Hready|contradiction] end
  ].
  reflexivity.
Qed.

Ltac arrays := unfold append_state, store_meta; cbn [withMemory memory];
  repeat first [rewrite modify_other by discriminate |rewrite modify_same
    |rewrite growArrays_other by discriminate |rewrite growArrays_same].
Lemma append_formulas s n bucket tuple :
  memory (append_state s n bucket tuple) arraydef_0__formulas =
  <[n := tuple]> (growList (memory s arraydef_0__formulas) (S n) (0,0,0)).
Proof. arrays. reflexivity. Qed.
Lemma append_links s n bucket tuple :
  memory (append_state s n bucket tuple) arraydef_0__formulaLinks =
  <[n := List.nth bucket (memory s arraydef_0__formulaBuckets) 0]>
    (growList (memory s arraydef_0__formulaLinks) (S n) 0).
Proof. arrays. reflexivity. Qed.
Lemma append_buckets s n bucket tuple :
  memory (append_state s n bucket tuple) arraydef_0__formulaBuckets =
  <[bucket := Z.of_nat (S n)]> (memory s arraydef_0__formulaBuckets).
Proof. arrays. reflexivity. Qed.
Lemma append_meta s n bucket tuple :
  memory (append_state s n bucket tuple) arraydef_0__meta =
  <[1%nat := Z.of_nat (S n)]> (<[0%nat := Z.of_nat n]> (memory s arraydef_0__meta)).
Proof. arrays. reflexivity. Qed.
Lemma append_other s n bucket tuple name :
  name <> arraydef_0__meta -> name <> arraydef_0__formulas ->
  name <> arraydef_0__formulaLinks -> name <> arraydef_0__formulaBuckets ->
  memory (append_state s n bucket tuple) name = memory s name.
Proof. intros. arrays. now repeat first
  [rewrite modify_other by assumption |rewrite growArrays_other by assumption]. Qed.
Lemma append_io s n bucket tuple :
  stdin (append_state s n bucket tuple) = stdin s /\
  stdout (append_state s n bucket tuple) = stdout s.
Proof. split; reflexivity. Qed.
Lemma append_formula_new s n bucket tuple :
  List.nth n (memory (append_state s n bucket tuple) arraydef_0__formulas) (0,0,0) = tuple.
Proof. rewrite append_formulas. apply OverflowExecution.nth_insert_same.
  rewrite growList_length. lia. Qed.
Lemma append_link_new s n bucket tuple :
  List.nth n (memory (append_state s n bucket tuple) arraydef_0__formulaLinks) 0 =
  List.nth bucket (memory s arraydef_0__formulaBuckets) 0.
Proof. rewrite append_links. apply OverflowExecution.nth_insert_same.
  rewrite growList_length. lia. Qed.
Lemma append_formula_previous s n bucket tuple i :
  (n <= length (memory s arraydef_0__formulas))%nat -> (i < n)%nat ->
  List.nth i (memory (append_state s n bucket tuple) arraydef_0__formulas) (0,0,0) =
  List.nth i (memory s arraydef_0__formulas) (0,0,0).
Proof. intros Hlength Hi. rewrite append_formulas, ArrayFacts.nth_insert_other by lia.
  unfold growList. apply app_nth1. lia. Qed.
Lemma append_link_previous s n bucket tuple i :
  (n <= length (memory s arraydef_0__formulaLinks))%nat -> (i < n)%nat ->
  List.nth i (memory (append_state s n bucket tuple) arraydef_0__formulaLinks) 0 =
  List.nth i (memory s arraydef_0__formulaLinks) 0.
Proof. intros Hlength Hi. rewrite append_links, ArrayFacts.nth_insert_other by lia.
  unfold growList. apply app_nth1. lia. Qed.
Lemma append_table_valid s n bucket tuple :
  table_valid s n -> 0 <= List.nth bucket (memory s arraydef_0__formulaBuckets) 0 <= Z.of_nat n ->
  table_valid (append_state s n bucket tuple) (S n).
Proof.
  intros [Hformulas [Hlinks Hdescending]] Hhead.
  split; [rewrite append_formulas, length_insert, growList_length; lia|].
  split; [rewrite append_links, length_insert, growList_length; lia|].
  intros i Hi. destruct (Nat.eq_dec i n) as [->|Hne].
  - now rewrite append_link_new.
  - rewrite append_link_previous by lia. apply Hdescending. lia.
Qed.
Lemma append_chain_previous s n bucket tuple pointer index :
  table_valid s n -> (pointer <= n)%nat -> in_chain s pointer index ->
  in_chain (append_state s n bucket tuple) pointer index.
Proof.
  intros [_ [Hlinks Hdescending]] Hbound Hchain.
  induction Hchain as [i | i j Hchain IH] in Hbound |- *.
  - constructor.
  - apply chain_tail. rewrite append_link_previous by lia. apply IH.
    pose proof (Hdescending i ltac:(lia)) as Hlink.
    pose proof (Z2Nat.id (List.nth i (memory s arraydef_0__formulaLinks) 0) ltac:(lia)). lia.
Qed.
End InternTailExecution.
