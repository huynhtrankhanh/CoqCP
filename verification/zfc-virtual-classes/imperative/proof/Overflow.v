From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith Lia.
Open Scope Z_scope.

Module OverflowExecution.
Import IndexExecution.
Lemma wrap_range value : 0 <= coerceInt value 64 <= maximum.
Proof.
  unfold coerceInt, maximum.
  pose proof (Z.mod_pos_bound value (2^64) ltac:(lia)). lia.
Qed.
Lemma nth_insert_same {A} (xs : list A) n value default :
  (n < length xs)%nat -> List.nth n (<[n := value]> xs) default = value.
Proof.
  induction xs as [|x xs IH] in n |- *; [cbn; lia |].
  destruct n as [|n]; cbn; [reflexivity |]. intro H. apply IH. lia.
Qed.
Lemma nth_flag_insert_result (xs : list Z) value :
  List.nth 8 (<[0%nat := value]> xs) 0 = List.nth 8 xs 0.
Proof. destruct xs; reflexivity. Qed.

Ltac normalize :=
  repeat first [
    match goal with |- context [coerceInt ?value 64] =>
      let Hword := fresh "Hword" in
      assert (Hword : word value) by (unfold word, maximum in *; lia);
      rewrite (coerce_word value Hword); clear Hword
    end
    | rewrite bool_decide_true by lia | rewrite bool_decide_false by lia
    | progress cbv beta iota zeta delta [negb subInt addInt numberLocalGet numberLocalSet store bind
        execLocal localStep step optionBind fst snd nums bools setNum setMachine machine
        withMemory memory arguments Imperative.update decide decide_rel
        variableIndexEqualityDecidablevarsfuncdef_0__renameIndex
        varsfuncdef_0__renameIndex_rec shortCircuitAnd shortCircuitOr]
    | progress rewrite modify_meta
    | progress rewrite length_insert
    | match goal with |- context [Nat.lt_dec ?slot ?len] =>
        let Hbound := fresh "Hbound" in
        assert (Hbound : (slot < len)%nat) by
          (lazymatch goal with H : (8 < length ?xs)%nat |- _ =>
            change (slot < length xs)%nat; lia end);
        destruct (Nat.lt_dec slot len); [clear Hbound | lia]
      end
    | match goal with |- context [coerceInt ?value 64] =>
        let wrapped := constr:(coerceInt value 64) in
        lazymatch goal with
        | _ : 0 <= wrapped <= 18446744073709551615 |- _ => fail
        | _ => let Hrange := fresh "Hrange" in
          pose proof (wrap_range value) as Hrange; unfold maximum in Hrange
        end
      end
    ].

Theorem overflow_rejected s m i depth shift arg :
  (8 < length (memory s arraydef_0__meta))%nat ->
  word i -> word depth -> word shift -> word arg ->
  ~ word (renamed_index m i depth shift arg) ->
  exists final,
    exec (funcdef_0__renameIndex (fun _ => false)
      (arguments i depth (mode_number m) shift arg)) s = Some (tt, final) /\
    List.nth 8 (memory final arraydef_0__meta) 0 = 1.
Proof.
  intros Hlength Hi Hd Hshift Harg Hbad.
  unfold renamed_index in Hbad. case_bool_decide as Hbound.
  - contradiction.
  - destruct m; cbn [mode_number free_index] in *.
    all: repeat case_bool_decide.
    all: unfold word, maximum in *.
    all: try lia.
    all: unfold funcdef_0__renameIndex; rewrite exec_eliminate; unfold funcdef_0__renameIndex_body.
    all: cbn [arguments numberLocalGet numberLocalSet store bind execLocal localStep step optionBind
         nums machine setMachine setNum withMemory fst snd Z.to_nat].
    all: case_decide; [|lia].
    all: cbn [optionBind machine setMachine nums fst snd arguments].
    all: rewrite bool_decide_false by lia.
    all: normalize.
    all: repeat (case_bool_decide; normalize).
    all: try lia.
    all: lazymatch goal with
      | |- exists final, Some (tt, ?actual) = Some (tt, final) /\ _ =>
        exists actual; split; [reflexivity |]
      end.
    all: cbn [memory withMemory].
    all: repeat rewrite modify_meta.
    all: repeat rewrite nth_flag_insert_result.
    all: rewrite nth_insert_same; [reflexivity |].
    all: repeat rewrite length_insert.
    all: change (8 < length (memory s arraydef_0__meta))%nat; exact Hlength.
Qed.

Definition word_dec value : {word value} + {~ word value}.
Proof. unfold word. apply and_dec; apply Z_le_dec. Defined.

(* Total execution and the acceptance condition needed by the caller: a clear
   error flag guarantees an exact mathematical result, without assuming that
   the result fits beforehand. Overflow must set the flag. *)
Theorem checked_index s m i depth shift arg :
  (8 < length (memory s arraydef_0__meta))%nat ->
  word i -> word depth -> word shift -> word arg ->
  exists final,
    exec (funcdef_0__renameIndex (fun _ => false)
      (arguments i depth (mode_number m) shift arg)) s = Some (tt, final) /\
    (List.nth 8 (memory final arraydef_0__meta) 0 = 0 ->
      word (renamed_index m i depth shift arg) /\
      result s final (renamed_index m i depth shift arg)) /\
    (~ word (renamed_index m i depth shift arg) ->
      List.nth 8 (memory final arraydef_0__meta) 0 = 1).
Proof.
  intros Hlength Hi Hd Hshift Harg.
  destruct (word_dec (renamed_index m i depth shift arg)) as [Hfit | Hbad].
  - destruct (index_execution s m i depth shift arg Hlength Hi Hd Hshift Harg Hfit)
      as [final [Hrun Hresult]]. exists final. split; [exact Hrun |].
    split; [intro; auto | contradiction].
  - destruct (overflow_rejected s m i depth shift arg Hlength Hi Hd Hshift Harg Hbad)
      as [final [Hrun Hflag]]. exists final. split; [exact Hrun |].
    split; [intro Hzero; congruence | intro; exact Hflag].
Qed.
End OverflowExecution.
