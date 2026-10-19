From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith Lia.
Open Scope Z_scope.

Module IndexExecution.
Definition Machine := @Execution.Machine arrayIndex1 (arrayType _ environment1).
Definition arguments i depth mode shift arg : varsfuncdef_0__renameIndex -> Z :=
  fun name => match name with
  | vardef_0__renameIndex_index => i
  | vardef_0__renameIndex_depth => depth
  | vardef_0__renameIndex_mode => mode
  | vardef_0__renameIndex_shift => shift
  | vardef_0__renameIndex_arg => arg
  | _ => 0
  end.
Definition store_meta (s : Machine) slot value :=
  withMemory s (modifyArray (memory s) arraydef_0__meta slot value).
Lemma modify_meta (values : forall name, list (arrayType _ environment1 name)) slot value :
  modifyArray values arraydef_0__meta slot value arraydef_0__meta =
  <[slot := value]> (values arraydef_0__meta).
Proof. reflexivity. Qed.
Lemma store_meta_length s slot value :
  length (memory (store_meta s slot value) arraydef_0__meta) =
  length (memory s arraydef_0__meta).
Proof. unfold store_meta. cbn [withMemory memory]. rewrite modify_meta. apply length_insert. Qed.
Lemma store_result_read s value : (0 < length (memory s arraydef_0__meta))%nat ->
  List.nth 0 (memory (store_meta s 0 value) arraydef_0__meta) 0 = value.
Proof.
  intro H. unfold store_meta. cbn [withMemory memory]. rewrite modify_meta.
  destruct (memory s arraydef_0__meta); [cbn in H; lia | reflexivity].
Qed.
Lemma store_result_flag s value :
  List.nth 8 (memory (store_meta s 0 value) arraydef_0__meta) 0 =
  List.nth 8 (memory s arraydef_0__meta) 0.
Proof.
  unfold store_meta. cbn [withMemory memory]. rewrite modify_meta.
  destruct (memory s arraydef_0__meta); reflexivity.
Qed.
Lemma store_meta_other s slot value name : name <> arraydef_0__meta ->
  memory (store_meta s slot value) name = memory s name.
Proof. destruct name; intro H; [congruence | ..]; reflexivity. Qed.
Definition result (s final : Machine) value :=
  List.nth 0 (memory final arraydef_0__meta) 0 = value /\
  List.nth 8 (memory final arraydef_0__meta) 0 = List.nth 8 (memory s arraydef_0__meta) 0 /\
  (forall name, name <> arraydef_0__meta -> memory final name = memory s name) /\
  stdin final = stdin s /\ stdout final = stdout s.
Lemma store_result_correct s value : (0 < length (memory s arraydef_0__meta))%nat ->
  result s (store_meta s 0 value) value.
Proof.
  intro H. split; [now apply store_result_read |].
  split; [apply store_result_flag |]. split; [intros; now apply store_meta_other |].
  split; reflexivity.
Qed.
Lemma result_trans s middle final first last :
  result s middle first -> result middle final last -> result s final last.
Proof.
  intros [_ [Hflag [Hother [Hinput Houtput]]]] [Hlast [Hflag' [Hother' [Hinput' Houtput']]]].
  split; [exact Hlast |]. split; [congruence |].
  split; [intros name Hname; rewrite Hother', Hother by exact Hname; reflexivity |].
  split; congruence.
Qed.

Definition maximum : Z := 18446744073709551615.
Definition word x := 0 <= x <= maximum.
Lemma coerce_word x : word x -> coerceInt x 64 = x.
Proof.
  intros H. unfold coerceInt. apply Z.mod_small. unfold word, maximum in H. lia.
Qed.

Inductive mode := shift_mode | instantiate_mode | separation_mode
  | replacement_left_mode | replacement_right_mode | replacement_image_mode | predicate_mode.
Definition mode_number m : Z := match m with
  | shift_mode => 0 | instantiate_mode => 1 | separation_mode => 2
  | replacement_left_mode => 3 | replacement_right_mode => 4
  | replacement_image_mode => 5 | predicate_mode => 6
  end.
Definition free_index m root shift arg :=
  match m with
  | shift_mode => root + shift
  | instantiate_mode => if bool_decide (root = 0) then arg else root - 1
  | separation_mode => if bool_decide (root = 0) then 0 else root + 1
  | replacement_left_mode => if bool_decide (root = 0) then 2
      else if bool_decide (root = 1) then 1 else root + 1
  | replacement_right_mode => if bool_decide (root = 0) then 2
      else if bool_decide (root = 1) then 0 else root + 1
  | replacement_image_mode => if bool_decide (root < 2) then root else root + 1
  | predicate_mode => if bool_decide (root = 0) then arg else root - 1 + shift
  end.
Definition renamed_index m i depth shift arg :=
  if bool_decide (i < depth) then i else free_index m (i - depth) shift arg + depth.

Theorem bound_variable s i depth mode shift arg :
  (8 < length (memory s arraydef_0__meta))%nat -> i < depth ->
  exec (funcdef_0__renameIndex (fun _ => false) (arguments i depth mode shift arg)) s =
  Some (tt, store_meta s 0 i).
Proof.
  intros Hlength Hbound. unfold funcdef_0__renameIndex. rewrite exec_eliminate.
  unfold funcdef_0__renameIndex_body.
  cbn [arguments numberLocalGet store bind execLocal localStep step optionBind
       nums machine setMachine setNum withMemory fst snd Z.to_nat].
  case_decide; [|lia].
  cbn [optionBind machine setMachine nums fst snd arguments].
  rewrite bool_decide_true by exact Hbound.
  cbn [negb execLocal bind optionBind fst snd machine setMachine].
  reflexivity.
Qed.

Theorem free_variable_shift s i depth shift arg :
  (8 < length (memory s arraydef_0__meta))%nat ->
  word i -> word depth -> word shift -> depth <= i -> word (i + shift) ->
  exec (funcdef_0__renameIndex (fun _ => false)
    (arguments i depth 0 shift arg)) s =
  Some (tt, store_meta (store_meta s 0 i) 0 (i + shift)).
Proof.
  intros Hlength Hi Hd Hs Hfree Hresult.
  unfold funcdef_0__renameIndex. rewrite exec_eliminate.
  unfold funcdef_0__renameIndex_body.
  cbn [arguments numberLocalGet numberLocalSet store bind execLocal localStep step optionBind
       nums machine setMachine setNum withMemory fst snd Z.to_nat].
  case_decide; [|lia].
  cbn [optionBind machine setMachine nums fst snd arguments].
  rewrite bool_decide_false by lia.
  cbv beta iota zeta delta [negb subInt addInt numberLocalGet numberLocalSet store bind
    execLocal localStep step optionBind fst snd nums setNum setMachine machine arguments
    Imperative.update decide decide_rel variableIndexEqualityDecidablevarsfuncdef_0__renameIndex
    varsfuncdef_0__renameIndex_rec shortCircuitAnd shortCircuitOr].
  unfold word, maximum in *.
  repeat first [rewrite coerce_word by (unfold word, maximum; lia)
    | rewrite bool_decide_true by lia | rewrite bool_decide_false by lia
    | progress cbn [bind execLocal localStep step optionBind fst snd nums bools machine
        setNum setMachine arguments Imperative.update decide decide_rel
        variableIndexEqualityDecidablevarsfuncdef_0__renameIndex
        varsfuncdef_0__renameIndex_rec shortCircuitAnd shortCircuitOr]].
  cbn [withMemory memory Z.to_nat].
  rewrite modify_meta, length_insert.
  destruct (Nat.lt_dec (Z.to_nat 0) (length (memory s arraydef_0__meta))) as [Hok | Hbad]; [|lia].
  cbn [fst snd machine optionBind].
  replace (i - depth + shift + depth) with (i + shift) by lia.
  reflexivity.
Qed.

Theorem free_variable s m i depth shift arg :
  (8 < length (memory s arraydef_0__meta))%nat ->
  word i -> word depth -> word shift -> word arg -> depth <= i ->
  word (free_index m (i - depth) shift arg + depth) ->
  exec (funcdef_0__renameIndex (fun _ => false)
    (arguments i depth (mode_number m) shift arg)) s =
  Some (tt, store_meta (store_meta s 0 i) 0 (free_index m (i - depth) shift arg + depth)).
Proof.
  intros Hlength Hi Hd Hshift Harg Hfree Hresult.
  destruct m; cbn [mode_number free_index] in *.
  all: repeat case_bool_decide.
  all: try (lazymatch goal with
    | |- context [arguments _ _ 5 _ _] => destruct (Z.eq_dec (i - depth) 0)
    end).
  all: unfold word, maximum in *.
  all: try lia.
  all: unfold funcdef_0__renameIndex; rewrite exec_eliminate; unfold funcdef_0__renameIndex_body.
  all: cbn [arguments numberLocalGet numberLocalSet store bind execLocal localStep step optionBind
       nums machine setMachine setNum withMemory fst snd Z.to_nat].
  all: case_decide; [|lia].
  all: cbn [optionBind machine setMachine nums fst snd arguments].
  all: rewrite bool_decide_false by lia.
  all: cbv beta iota zeta delta [negb subInt addInt numberLocalGet numberLocalSet store bind
    execLocal localStep step optionBind fst snd nums setNum setMachine machine arguments
    Imperative.update decide decide_rel variableIndexEqualityDecidablevarsfuncdef_0__renameIndex
    varsfuncdef_0__renameIndex_rec shortCircuitAnd shortCircuitOr].
  all: repeat first [match goal with |- context [coerceInt ?value 64] =>
      let Hword := fresh "Hword" in
      assert (Hword : word value) by (unfold word, maximum; lia);
      rewrite (coerce_word value Hword); clear Hword
    end
    | rewrite bool_decide_true by lia | rewrite bool_decide_false by lia
    | progress cbn [bind execLocal localStep step optionBind fst snd nums bools machine
        setNum setMachine arguments Imperative.update decide decide_rel
        variableIndexEqualityDecidablevarsfuncdef_0__renameIndex
        varsfuncdef_0__renameIndex_rec shortCircuitAnd shortCircuitOr]].
  all: cbn [withMemory memory Z.to_nat].
  all: rewrite modify_meta, length_insert.
  all: destruct (Nat.lt_dec (Z.to_nat 0) (length (memory s arraydef_0__meta))) as [Hok | Hbad]; [|lia].
  all: cbn [fst snd machine optionBind].
  all: lazymatch goal with
    | |- Some (_, withMemory _ (modifyArray _ arraydef_0__meta _ ?value)) =
          Some (_, store_meta _ _ ?expected) =>
      replace value with expected by lia; reflexivity
    end.
Qed.

Theorem index_execution s m i depth shift arg :
  (8 < length (memory s arraydef_0__meta))%nat ->
  word i -> word depth -> word shift -> word arg ->
  word (renamed_index m i depth shift arg) ->
  exists final,
    exec (funcdef_0__renameIndex (fun _ => false)
      (arguments i depth (mode_number m) shift arg)) s = Some (tt, final) /\
    result s final (renamed_index m i depth shift arg).
Proof.
  intros Hlength Hi Hd Hshift Harg Hresult.
  unfold renamed_index in *. case_bool_decide as Hbound.
  - exists (store_meta s 0 i). split.
    + now apply bound_variable.
    + apply store_result_correct. lia.
  - exists (store_meta (store_meta s 0 i) 0 (free_index m (i - depth) shift arg + depth)). split.
    + apply free_variable; try assumption. lia.
    + eapply result_trans.
      * apply store_result_correct. lia.
      * apply store_result_correct. rewrite store_meta_length. lia.
Qed.
End IndexExecution.
