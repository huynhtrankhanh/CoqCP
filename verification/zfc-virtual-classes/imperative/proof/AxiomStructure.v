From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomStructure.
Definition LocalAction (A:Type) := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom) withLocalVariablesReturnValue A.
Ltac select_handler code wanted use :=
  multimatch code with
  | context [bind ?condition ?branch] =>
    lazymatch condition with context [bind (numberLocalGet _ _ _ vardef_0__axiom_tag) ?compare] =>
      let comparison := eval cbn beta in (compare 0%Z) in
      lazymatch comparison with bind (Done _ _ _ ?opcode) _ =>
        constr_eq opcode wanted;
        let selected := eval cbn beta iota in (branch true) in
        let selected := constr:(selected : LocalAction unit) in use selected
      end
    end
  end.
Definition handler_0 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 0%Z ltac:(fun selected => exact selected)).
Definition handler_1 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 1%Z ltac:(fun selected => exact selected)).
Definition handler_2 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 2%Z ltac:(fun selected => exact selected)).
Definition handler_3 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 3%Z ltac:(fun selected => exact selected)).
Definition handler_4 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 4%Z ltac:(fun selected => exact selected)).
Definition handler_5 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 5%Z ltac:(fun selected => exact selected)).
Definition handler_6 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 6%Z ltac:(fun selected => exact selected)).
Definition handler_7 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 7%Z ltac:(fun selected => exact selected)).
Definition handler_8 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 8%Z ltac:(fun selected => exact selected)).
Definition handler_9 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 9%Z ltac:(fun selected => exact selected)).
Definition handler_10 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 10%Z ltac:(fun selected => exact selected)).
Definition handler_11 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 11%Z ltac:(fun selected => exact selected)).
Definition handler_12 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 12%Z ltac:(fun selected => exact selected)).
Definition handler_13 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 13%Z ltac:(fun selected => exact selected)).
Definition handler_14 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 14%Z ltac:(fun selected => exact selected)).
Definition handler_15 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 15%Z ltac:(fun selected => exact selected)).
Definition handler_16 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 16%Z ltac:(fun selected => exact selected)).
Definition handler_17 : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  select_handler code 17%Z ltac:(fun selected => exact selected)).
Ltac fold_handler code raw call :=
  let abstracted := eval pattern raw in code in
  lazymatch abstracted with ?family _ =>
    let folded := constr:(family call) in
    let reduced := eval cbv beta in folded in reduced
  end.
Definition compact_body : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  let raw := eval unfold handler_0 in handler_0 in
  let code := fold_handler code raw handler_0 in
  let raw := eval unfold handler_1 in handler_1 in
  let code := fold_handler code raw handler_1 in
  let raw := eval unfold handler_2 in handler_2 in
  let code := fold_handler code raw handler_2 in
  let raw := eval unfold handler_3 in handler_3 in
  let code := fold_handler code raw handler_3 in
  let raw := eval unfold handler_4 in handler_4 in
  let code := fold_handler code raw handler_4 in
  let raw := eval unfold handler_5 in handler_5 in
  let code := fold_handler code raw handler_5 in
  let raw := eval unfold handler_6 in handler_6 in
  let code := fold_handler code raw handler_6 in
  let raw := eval unfold handler_7 in handler_7 in
  let code := fold_handler code raw handler_7 in
  let raw := eval unfold handler_8 in handler_8 in
  let code := fold_handler code raw handler_8 in
  let raw := eval unfold handler_9 in handler_9 in
  let code := fold_handler code raw handler_9 in
  let raw := eval unfold handler_10 in handler_10 in
  let code := fold_handler code raw handler_10 in
  let raw := eval unfold handler_11 in handler_11 in
  let code := fold_handler code raw handler_11 in
  let raw := eval unfold handler_12 in handler_12 in
  let code := fold_handler code raw handler_12 in
  let raw := eval unfold handler_13 in handler_13 in
  let code := fold_handler code raw handler_13 in
  let raw := eval unfold handler_14 in handler_14 in
  let code := fold_handler code raw handler_14 in
  let raw := eval unfold handler_15 in handler_15 in
  let code := fold_handler code raw handler_15 in
  let raw := eval unfold handler_16 in handler_16 in
  let code := fold_handler code raw handler_16 in
  let raw := eval unfold handler_17 in handler_17 in
  let code := fold_handler code raw handler_17 in
  exact code).
Theorem actual_body : funcdef_0__axiom_body=compact_body.
Proof. reflexivity. Qed.
End AxiomStructure.
