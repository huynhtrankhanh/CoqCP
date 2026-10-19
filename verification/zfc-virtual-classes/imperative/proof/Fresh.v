From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Intern Overflow.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith Lia.
Open Scope Z_scope.

Module FreshExecution.
Import IndexExecution InternExecution.
Lemma modify_meta_formulas (values : forall name, list (arrayType _ environment1 name)) slot value :
  modifyArray values arraydef_0__meta slot value arraydef_0__formulas = values arraydef_0__formulas.
Proof. reflexivity. Qed.
Lemma modify_formulas_meta (values : forall name, list (arrayType _ environment1 name)) slot value :
  modifyArray values arraydef_0__formulas slot value arraydef_0__meta = values arraydef_0__meta.
Proof. reflexivity. Qed.
Lemma nth_count_insert_result (xs : list Z) value :
  List.nth 1 (<[0%nat := value]> xs) 0 = List.nth 1 xs 0.
Proof. destruct xs; reflexivity. Qed.

Definition fresh_state (s : Machine) n entry :=
  let first := store_meta s 0 (Z.of_nat n) in
  let grown := withMemory first (growArrays (memory first) arraydef_0__formulas (S n) (0,0,0)) in
  let written := withMemory grown (modifyArray (memory grown) arraydef_0__formulas n entry) in
  store_meta written 1 (Z.of_nat (S n)).

Lemma insert_grown_end {A} (values : list A) zero entry :
  <[length values := entry]> (growList values (S (length values)) zero) =
  values ++ [entry].
Proof.
  unfold growList. replace (S (length values) - length values)%nat with 1%nat by lia.
  rewrite insert_app_r_alt, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma fresh_formulas s n entry : length (memory s arraydef_0__formulas) = n ->
  memory (fresh_state s n entry) arraydef_0__formulas =
  memory s arraydef_0__formulas ++ [entry].
Proof.
  intro Hlength. unfold fresh_state, store_meta. cbn [withMemory memory].
  rewrite modify_meta_formulas.
  change (<[n := entry]>
    (growArrays (modifyArray (memory s) arraydef_0__meta 0 (Z.of_nat n))
      arraydef_0__formulas (S n) (0,0,0) arraydef_0__formulas) =
    memory s arraydef_0__formulas ++ [entry]).
  rewrite growArrays_same, modify_meta_formulas, <- Hlength. apply insert_grown_end.
Qed.

Lemma fresh_metadata s n entry :
  memory (fresh_state s n entry) arraydef_0__meta =
  <[1%nat := Z.of_nat (S n)]> (<[0%nat := Z.of_nat n]> (memory s arraydef_0__meta)).
Proof.
  unfold fresh_state, store_meta. cbn [withMemory memory].
  rewrite modify_meta, modify_formulas_meta, growArrays_other by discriminate.
  rewrite modify_meta. reflexivity.
Qed.

Lemma fresh_other s n entry name :
  name <> arraydef_0__meta -> name <> arraydef_0__formulas ->
  memory (fresh_state s n entry) name = memory s name.
Proof. destruct name; intros; try congruence; reflexivity. Qed.

Lemma fresh_io s n entry :
  stdin (fresh_state s n entry) = stdin s /\
  stdout (fresh_state s n entry) = stdout s.
Proof. split; reflexivity. Qed.

Theorem after_scan_fresh s bs ns n :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 1 (memory s arraydef_0__meta) 0 = Z.of_nat n ->
  List.nth 8 (memory s arraydef_0__meta) 0 = 0 ->
  length (memory s arraydef_0__formulas) = n -> Z.of_nat n < maximum ->
  ns vardef_0__intern_found = 0 ->
  execLocal after_scan {| machine := s; bools := bs; nums := ns |} =
    Some (tt, {| machine := fresh_state s n
      (ns vardef_0__intern_tag, ns vardef_0__intern_a, ns vardef_0__intern_b);
      bools := bs; nums := ns |}).
Proof.
  intros Hmeta Hcount Hflag Hlength Hlimit Hfound.
  change (@List.nth Z (Z.to_nat 1) (memory s arraydef_0__meta) 0 = Z.of_nat n) in Hcount.
  change (@List.nth Z (Z.to_nat 8) (memory s arraydef_0__meta) 0 = 0) in Hflag.
  unfold maximum in Hlimit. unfold after_scan.
  cbv beta iota zeta delta [shortCircuitAnd numberLocalGet retrieve store grow addInt bind
    execLocal localStep step optionBind setNum setMachine machine nums fst snd].
  rewrite bool_decide_true by (rewrite Hfound; reflexivity).
  cbv beta iota zeta delta [bind execLocal localStep step optionBind fst snd nums bools machine setMachine].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z), Hflag.
  change (@List.nth Z 1 (memory s arraydef_0__meta) 0 = Z.of_nat n) in Hcount.
  change (@List.length (Z * Z * Z)%type (memory s arraydef_0__formulas) = n) in Hlength.
  change (8 < @List.length Z (memory s arraydef_0__meta))%nat in Hmeta.
  cbv beta iota zeta delta [memory] in Hcount, Hlength, Hmeta.
  repeat first [
    match goal with |- context [bool_decide ?P] =>
      first [rewrite (bool_decide_true P) by lia | rewrite (bool_decide_false P) by lia]
    end
    | rewrite nth_lt_default with (default := 0%Z)
    | rewrite Hcount
    | rewrite Nat2Z.id
    | progress replace (Z.to_nat 1) with 1%nat by reflexivity
    | progress replace (Z.to_nat 8) with 8%nat by reflexivity
    | progress replace (Z.to_nat 0) with 0%nat by reflexivity
    | progress replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia
    | match goal with |- context [coerceInt ?value 64] =>
        rewrite (coerce_word value) by (unfold word, maximum; lia)
      end
    | progress cbv beta iota zeta delta [shortCircuitAnd numberLocalGet retrieve store grow addInt bind
        execLocal localStep step optionBind setNum setMachine machine nums bools fst snd withMemory memory]
    | rewrite modify_meta | rewrite modify_meta_formulas | rewrite modify_formulas_meta
    | rewrite growArrays_other by discriminate | rewrite growArrays_same
    | rewrite nth_count_insert_result
    | rewrite length_insert | rewrite growList_length | rewrite Hlength
    | match goal with |- context [decide (Nat.lt ?slot ?len)] =>
        let Hready := fresh "Hready" in
        assert (Hready : (slot < len)%nat) by
          (repeat rewrite length_insert; try rewrite growList_length;
           try rewrite Hlength;
           first [change (slot < length (memory s arraydef_0__meta))%nat; lia | lia]);
        case_decide; [clear Hready | contradiction]
      end
    | case_decide; [|lia]
  ].
  reflexivity.
Qed.

Theorem after_scan_full s bs ns :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 1 (memory s arraydef_0__meta) 0 = maximum ->
  List.nth 8 (memory s arraydef_0__meta) 0 = 0 ->
  ns vardef_0__intern_found = 0 ->
  execLocal after_scan {| machine := s; bools := bs; nums := ns |} =
    Some (tt, {| machine := store_meta s 8 1; bools := bs; nums := ns |}).
Proof.
  intros Hmeta Hcount Hflag Hfound.
  change (@List.nth Z (Z.to_nat 1) (memory s arraydef_0__meta) 0 = maximum) in Hcount.
  change (@List.nth Z (Z.to_nat 8) (memory s arraydef_0__meta) 0 = 0) in Hflag.
  unfold after_scan.
  cbv beta iota zeta delta [shortCircuitAnd numberLocalGet retrieve store bind
    execLocal localStep step optionBind setNum setMachine machine nums fst snd].
  rewrite bool_decide_true by (rewrite Hfound; reflexivity).
  cbv beta iota zeta delta [bind execLocal localStep step optionBind fst snd nums bools machine setMachine].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z), Hflag.
  cbv beta iota zeta delta [bind execLocal localStep step optionBind fst snd nums bools machine setMachine].
  rewrite bool_decide_true by reflexivity.
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z), Hcount.
  rewrite bool_decide_true by reflexivity.
  cbv beta iota zeta delta [store bind execLocal localStep step optionBind fst snd nums bools machine setMachine].
  case_decide; [reflexivity |lia].
Qed.

Theorem intern_fresh s bs ns count :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 1 (memory s arraydef_0__meta) 0 = Z.of_nat count ->
  List.nth 8 (memory s arraydef_0__meta) 0 = 0 ->
  length (memory s arraydef_0__formulas) = count ->
  Z.of_nat count < maximum ->
  find_from (start_frame s bs ns) 0 count = None ->
  exec (funcdef_0__intern bs ns) s =
    Some (tt, fresh_state s count (sought (start_frame s bs ns))).
Proof.
  intros Hmeta Hcount Hflag Hlength Hlimit Hfind.
  rewrite (intern_after_count s bs ns (Z.of_nat count) Hmeta Hcount).
  rewrite split_scan, execLocal_bind, Nat2Z.id.
  rewrite (scan_loop (start_frame s bs ns) count 0 count).
  2: reflexivity.
  2: cbn [start_frame setNum machine]; lia.
  2: exact (Nat.lt_trans 0 8 _ ltac:(lia) Hmeta).
  rewrite Hfind. cbn [optionBind fst snd].
  unfold start_frame, setNum.
  rewrite after_scan_fresh with (n := count); try assumption.
  - reflexivity.
  - reflexivity.
Qed.

Theorem intern_full s bs ns count :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 1 (memory s arraydef_0__meta) 0 = Z.of_nat count ->
  List.nth 8 (memory s arraydef_0__meta) 0 = 0 ->
  length (memory s arraydef_0__formulas) = count ->
  Z.of_nat count = maximum ->
  find_from (start_frame s bs ns) 0 count = None ->
  exec (funcdef_0__intern bs ns) s = Some (tt, store_meta s 8 1).
Proof.
  intros Hmeta Hcount Hflag Hlength Hlimit Hfind.
  rewrite (intern_after_count s bs ns (Z.of_nat count) Hmeta Hcount).
  rewrite split_scan, execLocal_bind, Nat2Z.id.
  rewrite (scan_loop (start_frame s bs ns) count 0 count).
  2: reflexivity.
  2: cbn [start_frame setNum machine]; lia.
  2: exact (Nat.lt_trans 0 8 _ ltac:(lia) Hmeta).
  rewrite Hfind. cbn [optionBind fst snd].
  unfold start_frame, setNum.
  rewrite after_scan_full; try assumption.
  - reflexivity.
  - exact (eq_trans Hcount Hlimit).
  - reflexivity.
Qed.

(* The result of interning a tuple in the finite arena. A full arena can
   still return an existing node; only a genuinely fresh allocation fails. *)
Definition intern_output s bs ns count :=
  match find_from (start_frame s bs ns) 0 count with
  | Some index => store_meta s 0 (Z.of_nat index)
  | None => if Z.eq_dec (Z.of_nat count) maximum then store_meta s 8 1
      else fresh_state s count (sought (start_frame s bs ns))
  end.

Theorem generated_intern_correct s bs ns count :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 1 (memory s arraydef_0__meta) 0 = Z.of_nat count ->
  List.nth 8 (memory s arraydef_0__meta) 0 = 0 ->
  length (memory s arraydef_0__formulas) = count ->
  Z.of_nat count <= maximum ->
  exec (funcdef_0__intern bs ns) s = Some (tt, intern_output s bs ns count).
Proof.
  intros Hmeta Hcount Hflag Hlength Hlimit. unfold intern_output.
  destruct (find_from (start_frame s bs ns) 0 count) as [index |] eqn:Hfind.
  - apply intern_existing with (count := count); try assumption. lia.
  - destruct (Z.eq_dec (Z.of_nat count) maximum).
    + now apply intern_full with (count := count).
    + apply intern_fresh; try assumption. lia.
Qed.
End FreshExecution.
