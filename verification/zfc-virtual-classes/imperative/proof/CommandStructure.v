From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import CommandQuit.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module CommandStructure.
Import CommandQuitExecution.
Ltac select_handler code wanted use :=
  match code with
  | context [bind (shortCircuitAnd (bind (numberLocalGet _ _ _ vardef_0__command_op) ?compare) ?guard) ?branch] =>
      let comparison := eval cbn beta in (compare 0%Z) in
      lazymatch comparison with bind (Done _ _ _ ?opcode) _ =>
        constr_eq opcode wanted;
        let selected := eval cbn beta iota in (branch true) in use selected
      end
  end.
Definition handler_1 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 1%Z ltac:(fun selected => exact selected)).
Definition handler_2 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 2%Z ltac:(fun selected => exact selected)).
Definition handler_3 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 3%Z ltac:(fun selected => exact selected)).
Definition handler_4 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 4%Z ltac:(fun selected => exact selected)).
Definition handler_5 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 5%Z ltac:(fun selected => exact selected)).
Definition handler_6 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 6%Z ltac:(fun selected => exact selected)).
Definition handler_7 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 7%Z ltac:(fun selected => exact selected)).
Definition handler_8 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 8%Z ltac:(fun selected => exact selected)).
Definition handler_9 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 9%Z ltac:(fun selected => exact selected)).
Definition handler_10 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 10%Z ltac:(fun selected => exact selected)).
Definition handler_11 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 11%Z ltac:(fun selected => exact selected)).
Definition handler_12 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 12%Z ltac:(fun selected => exact selected)).
Definition handler_13 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 13%Z ltac:(fun selected => exact selected)).
Definition handler_14 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 14%Z ltac:(fun selected => exact selected)).
Definition handler_15 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 15%Z ltac:(fun selected => exact selected)).
Definition handler_16 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 16%Z ltac:(fun selected => exact selected)).
Definition handler_17 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 17%Z ltac:(fun selected => exact selected)).
Definition handler_18 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 18%Z ltac:(fun selected => exact selected)).
Definition handler_19 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 19%Z ltac:(fun selected => exact selected)).
Definition handler_20 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 20%Z ltac:(fun selected => exact selected)).
Definition handler_21 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 21%Z ltac:(fun selected => exact selected)).
Definition handler_22 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 22%Z ltac:(fun selected => exact selected)).
Definition handler_23 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 23%Z ltac:(fun selected => exact selected)).
Definition handler_24 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 24%Z ltac:(fun selected => exact selected)).
Definition handler_25 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 25%Z ltac:(fun selected => exact selected)).
Definition handler_26 (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  select_handler code 26%Z ltac:(fun selected => exact selected)).
Ltac fold_handler code raw call :=
  let abstracted := eval pattern raw in code in
  lazymatch abstracted with ?family _ =>
    let folded := constr:(family call) in
    let reduced := eval cbv beta in folded in reduced
  end.
Definition compact_body (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold body_with in (body_with reader) in
  let raw := eval unfold handler_1 in (handler_1 reader) in
  let code := fold_handler code raw (handler_1 reader) in
  let raw := eval unfold handler_2 in (handler_2 reader) in
  let code := fold_handler code raw (handler_2 reader) in
  let raw := eval unfold handler_3 in (handler_3 reader) in
  let code := fold_handler code raw (handler_3 reader) in
  let raw := eval unfold handler_4 in (handler_4 reader) in
  let code := fold_handler code raw (handler_4 reader) in
  let raw := eval unfold handler_5 in (handler_5 reader) in
  let code := fold_handler code raw (handler_5 reader) in
  let raw := eval unfold handler_6 in (handler_6 reader) in
  let code := fold_handler code raw (handler_6 reader) in
  let raw := eval unfold handler_7 in (handler_7 reader) in
  let code := fold_handler code raw (handler_7 reader) in
  let raw := eval unfold handler_8 in (handler_8 reader) in
  let code := fold_handler code raw (handler_8 reader) in
  let raw := eval unfold handler_9 in (handler_9 reader) in
  let code := fold_handler code raw (handler_9 reader) in
  let raw := eval unfold handler_10 in (handler_10 reader) in
  let code := fold_handler code raw (handler_10 reader) in
  let raw := eval unfold handler_11 in (handler_11 reader) in
  let code := fold_handler code raw (handler_11 reader) in
  let raw := eval unfold handler_12 in (handler_12 reader) in
  let code := fold_handler code raw (handler_12 reader) in
  let raw := eval unfold handler_13 in (handler_13 reader) in
  let code := fold_handler code raw (handler_13 reader) in
  let raw := eval unfold handler_14 in (handler_14 reader) in
  let code := fold_handler code raw (handler_14 reader) in
  let raw := eval unfold handler_15 in (handler_15 reader) in
  let code := fold_handler code raw (handler_15 reader) in
  let raw := eval unfold handler_16 in (handler_16 reader) in
  let code := fold_handler code raw (handler_16 reader) in
  let raw := eval unfold handler_17 in (handler_17 reader) in
  let code := fold_handler code raw (handler_17 reader) in
  let raw := eval unfold handler_18 in (handler_18 reader) in
  let code := fold_handler code raw (handler_18 reader) in
  let raw := eval unfold handler_19 in (handler_19 reader) in
  let code := fold_handler code raw (handler_19 reader) in
  let raw := eval unfold handler_20 in (handler_20 reader) in
  let code := fold_handler code raw (handler_20 reader) in
  let raw := eval unfold handler_21 in (handler_21 reader) in
  let code := fold_handler code raw (handler_21 reader) in
  let raw := eval unfold handler_22 in (handler_22 reader) in
  let code := fold_handler code raw (handler_22 reader) in
  let raw := eval unfold handler_23 in (handler_23 reader) in
  let code := fold_handler code raw (handler_23 reader) in
  let raw := eval unfold handler_24 in (handler_24 reader) in
  let code := fold_handler code raw (handler_24 reader) in
  let raw := eval unfold handler_25 in (handler_25 reader) in
  let code := fold_handler code raw (handler_25 reader) in
  let raw := eval unfold handler_26 in (handler_26 reader) in
  let code := fold_handler code raw (handler_26 reader) in
  exact code).
Lemma actual_body reader : body_with reader = compact_body reader.
Proof. reflexivity. Qed.
End CommandStructure.
