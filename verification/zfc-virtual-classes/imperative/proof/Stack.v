From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow Fresh Representation.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith Lia.
Open Scope Z_scope.

Module StackExecution.
Import IndexExecution.
Definition push_state (s : Machine) top node depth :=
  let grown := withMemory s
    (growArrays (memory s) arraydef_0__frames (S top) (0,0,0,0)) in
  let written := withMemory grown
    (modifyArray (memory grown) arraydef_0__frames top (node,depth,0,0)) in
  store_meta written 10 (Z.of_nat (S top)).

Lemma modify_frames_meta (values : forall name, list (arrayType _ environment1 name)) slot value :
  modifyArray values arraydef_0__frames slot value arraydef_0__meta = values arraydef_0__meta.
Proof. reflexivity. Qed.

Theorem generated_push s bs ns top :
  (10 < length (memory s arraydef_0__meta))%nat ->
  List.nth 10 (memory s arraydef_0__meta) 0 = Z.of_nat top ->
  Z.of_nat top < maximum ->
  exec (funcdef_0__push bs ns) s =
    Some (tt, push_state s top (ns vardef_0__push_node) (ns vardef_0__push_depth)).
Proof.
  intros Hmeta Htop Hlimit.
  change (@List.nth Z 10 (memory s arraydef_0__meta) 0 = Z.of_nat top) in Htop.
  change (10 < @List.length Z (memory s arraydef_0__meta))%nat in Hmeta.
  cbv beta iota zeta delta [memory] in Hmeta, Htop.
  unfold funcdef_0__push. rewrite exec_eliminate. unfold funcdef_0__push_body.
  unfold maximum in Hlimit.
  cbv beta iota zeta delta [numberLocalGet retrieve store grow addInt bind
    execLocal localStep step optionBind setNum setMachine machine nums bools fst snd withMemory memory].
  replace (Z.to_nat 10) with 10%nat by reflexivity.
  let guard := constr:(Nat.lt 10 (length (memory s arraydef_0__meta))) in
  let guard := eval cbv beta iota zeta delta [memory] in guard in
  lazymatch goal with |- context [@decide guard ?decision] =>
    destruct (@decide guard decision) as [Hbound |Hbound];
      [|exfalso; apply Hbound; exact Hmeta]
  end.
  rewrite nth_lt_default with (default := 0%Z), Htop.
  rewrite bool_decide_false by lia.
  repeat first [
    match goal with |- context [bool_decide ?P] =>
      first [rewrite (bool_decide_true P) by lia |rewrite (bool_decide_false P) by lia]
    end
    | rewrite nth_lt_default with (default := 0%Z)
    | rewrite Htop | rewrite Nat2Z.id
    | progress replace (Z.to_nat 10) with 10%nat by reflexivity
    | progress replace (Z.of_nat top + 1) with (Z.of_nat (S top)) by lia
    | match goal with |- context [coerceInt ?value 64] =>
        rewrite (coerce_word value) by (unfold word, maximum; lia)
      end
    | progress cbv beta iota zeta delta [shortCircuitAnd numberLocalGet retrieve store grow addInt bind
        execLocal localStep step optionBind setNum setMachine machine nums bools fst snd withMemory memory]
    | rewrite modify_frames_meta
    | rewrite growArrays_other by discriminate | rewrite growArrays_same
    | match goal with |- context [decide (Nat.lt ?slot ?len)] =>
        let Hready := fresh "Hready" in
        assert (Hready : (slot < len)%nat) by
          (repeat rewrite length_insert; try rewrite growList_length;
           first [change (slot < length (memory s arraydef_0__meta))%nat; lia |lia]);
        case_decide; [clear Hready |contradiction]
      end
    | case_decide; [|lia]
  ].
  reflexivity.
Qed.

Theorem generated_push_full s bs ns :
  (10 < length (memory s arraydef_0__meta))%nat ->
  List.nth 10 (memory s arraydef_0__meta) 0 = maximum ->
  exec (funcdef_0__push bs ns) s = Some (tt, store_meta s 8 1).
Proof.
  intros Hmeta Htop.
  change (@List.nth Z (Z.to_nat 10) (memory s arraydef_0__meta) 0 = maximum) in Htop.
  unfold funcdef_0__push. rewrite exec_eliminate. unfold funcdef_0__push_body.
  cbv beta iota zeta delta [numberLocalGet retrieve store bind execLocal localStep step
    optionBind setNum setMachine machine nums bools fst snd].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z), Htop.
  rewrite bool_decide_true by reflexivity.
  cbv beta iota zeta delta [store bind execLocal localStep step optionBind
    setMachine machine nums bools fst snd].
  case_decide; [reflexivity |lia].
Qed.

Theorem generated_checked_push s bs ns top :
  (10 < length (memory s arraydef_0__meta))%nat ->
  List.nth 10 (memory s arraydef_0__meta) 0 = Z.of_nat top ->
  Z.of_nat top <= maximum ->
  exists final,
    exec (funcdef_0__push bs ns) s = Some (tt, final) /\
    (List.nth 8 (memory final arraydef_0__meta) 0 = 0 ->
      Z.of_nat top < maximum /\
      final = push_state s top (ns vardef_0__push_node) (ns vardef_0__push_depth)) /\
    (Z.of_nat top = maximum -> List.nth 8 (memory final arraydef_0__meta) 0 = 1).
Proof.
  intros Hmeta Htop Hlimit. destruct (Z.eq_dec (Z.of_nat top) maximum) as [Heq |Hneq].
  - exists (store_meta s 8 1). split.
    + apply generated_push_full; [exact Hmeta |exact (eq_trans Htop Heq)].
    + split.
      * rewrite NativeRepresentation.full_flag by lia. discriminate.
      * intros _. apply NativeRepresentation.full_flag. lia.
  - exists (push_state s top (ns vardef_0__push_node) (ns vardef_0__push_depth)).
    split; [apply generated_push; try assumption; lia |].
    split; [intros; split; [lia |reflexivity] |contradiction].
Qed.

Lemma push_frames s top node depth :
  memory (push_state s top node depth) arraydef_0__frames =
  <[top := (node,depth,0,0)]>
    (growList (memory s arraydef_0__frames) (S top) (0,0,0,0)).
Proof.
  unfold push_state. rewrite store_meta_other by discriminate.
  change (<[top := (node,depth,0,0)]>
    (growArrays (memory s) arraydef_0__frames (S top) (0,0,0,0) arraydef_0__frames) =
    <[top := (node,depth,0,0)]>
      (growList (memory s arraydef_0__frames) (S top) (0,0,0,0))).
  now rewrite growArrays_same.
Qed.

Lemma push_metadata s top node depth :
  memory (push_state s top node depth) arraydef_0__meta =
  <[10%nat := Z.of_nat (S top)]> (memory s arraydef_0__meta).
Proof.
  unfold push_state, store_meta. cbn [withMemory memory].
  rewrite modify_meta, modify_frames_meta, growArrays_other by discriminate. reflexivity.
Qed.

Lemma push_top_read s top node depth :
  List.nth top (memory (push_state s top node depth) arraydef_0__frames) (0,0,0,0) =
    (node,depth,0,0).
Proof.
  rewrite push_frames. apply OverflowExecution.nth_insert_same.
  rewrite growList_length. lia.
Qed.

Lemma push_preserves_previous s top node depth index :
  (top <= length (memory s arraydef_0__frames))%nat -> (index < top)%nat ->
  List.nth index (memory (push_state s top node depth) arraydef_0__frames) (0,0,0,0) =
    List.nth index (memory s arraydef_0__frames) (0,0,0,0).
Proof.
  intros Hlength Hindex. rewrite push_frames.
  rewrite NativeRepresentation.nth_insert_other by lia.
  unfold growList. apply app_nth1. lia.
Qed.

Lemma push_count s top node depth :
  (10 < length (memory s arraydef_0__meta))%nat ->
  List.nth 10 (memory (push_state s top node depth) arraydef_0__meta) 0 =
    Z.of_nat (S top).
Proof. intro H. rewrite push_metadata. now apply OverflowExecution.nth_insert_same. Qed.

Lemma push_flag s top node depth :
  List.nth 8 (memory (push_state s top node depth) arraydef_0__meta) 0 =
    List.nth 8 (memory s arraydef_0__meta) 0.
Proof. rewrite push_metadata. now apply NativeRepresentation.nth_insert_other. Qed.

Lemma push_other s top node depth name :
  name <> arraydef_0__meta -> name <> arraydef_0__frames ->
  memory (push_state s top node depth) name = memory s name.
Proof. destruct name; intros; try congruence; reflexivity. Qed.

Lemma push_io s top node depth :
  stdin (push_state s top node depth) = stdin s /\
  stdout (push_state s top node depth) = stdout s.
Proof. split; reflexivity. Qed.
End StackExecution.
