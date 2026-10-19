From CoqCP Require Import Options Imperative Execution SetTheory.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow Fresh Representation PrintingFrame.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module AppendExecution.
Import IndexExecution NativeRepresentation.

Definition before_print (s : Machine) count node :=
  let grown := withMemory s
    (growArrays (memory s) arraydef_0__theorems (S count) 0) in
  withMemory grown (modifyArray (memory grown) arraydef_0__theorems count node).

Lemma modify_history_meta values slot value :
  @modifyArray arrayIndex1 arrayIndexEqualityDecidable1 (arrayType _ environment1)
    values arraydef_0__theorems slot value arraydef_0__meta = values arraydef_0__meta.
Proof. reflexivity. Qed.

Lemma before_print_metadata s count node :
  memory (before_print s count node) arraydef_0__meta = memory s arraydef_0__meta.
Proof.
  unfold before_print. cbn [withMemory memory].
  rewrite modify_history_meta, growArrays_other by discriminate. reflexivity.
Qed.

Theorem generated_append_fits s bs ns count :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 3 (memory s arraydef_0__meta) 0 = Z.of_nat count ->
  List.nth 8 (memory s arraydef_0__meta) 0 = 0 ->
  Z.of_nat count < maximum ->
  exec (funcdef_0__appendTheorem bs ns) s =
    optionBind (exec (funcdef_0__ok (fun _ => false)
      (update (fun _ => 0) vardef_0__ok_value (Z.of_nat count)))
      (before_print s count (ns vardef_0__appendTheorem_node)))
      (fun response => Some (tt, store_meta (snd response) 3 (Z.of_nat (S count)))).
Proof.
  intros Hmeta Hcount Hflag Hlimit.
  change (@List.nth Z (Z.to_nat 3) (memory s arraydef_0__meta) 0 = Z.of_nat count) in Hcount.
  change (@List.nth Z (Z.to_nat 8) (memory s arraydef_0__meta) 0 = 0) in Hflag.
  unfold funcdef_0__appendTheorem. rewrite exec_eliminate.
  unfold funcdef_0__appendTheorem_body.
  rewrite execLocal_bind.
  cbn [bind retrieve execLocal localStep step optionBind nums machine setMachine fst snd].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z), Hflag.
  cbn [bind execLocal optionBind fst snd nums machine setMachine].
  rewrite bool_decide_true by reflexivity.
  repeat rewrite execLocal_bind.
  cbn [bind retrieve execLocal localStep step optionBind nums machine setMachine fst snd].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z), Hcount.
  cbn [bind execLocal optionBind fst snd nums machine setMachine].
  rewrite bool_decide_false by (unfold maximum in Hlimit; lia).
  repeat rewrite execLocal_bind.
  change (@List.nth Z 3 (memory s arraydef_0__meta) 0 = Z.of_nat count) in Hcount.
  assert (Hcount_native : @List.nth (arrayType _ environment1 arraydef_0__meta)
    3 (memory s arraydef_0__meta) 0 = Z.of_nat count) by exact Hcount.
  repeat first [
    rewrite execLocal_bind | rewrite execLocal_lift
    | rewrite nth_lt_default with (default := 0%Z)
    | rewrite Hcount | rewrite Hcount_native | rewrite Nat2Z.id
    | progress replace (Z.to_nat 3) with 3%nat by reflexivity
    | progress replace (Z.of_nat count + 1) with (Z.of_nat (S count)) by lia
    | match goal with |- context [coerceInt ?value 64] =>
        rewrite (coerce_word value) by (unfold word, maximum in *; lia)
      end
    | progress cbn [addInt bind retrieve grow store numberLocalGet execLocal localStep step
        optionBind nums bools machine setMachine withMemory memory fst snd]
    | rewrite modify_history_meta
    | rewrite growArrays_other by discriminate | rewrite growArrays_same
    | match goal with |- context [decide (Nat.lt ?slot ?len)] =>
        let Hready := fresh "Hready" in
        assert (Hready : (slot < len)%nat) by
          (repeat rewrite length_insert; try rewrite growList_length;
           first [change (slot < length (memory s arraydef_0__meta))%nat; lia |lia]);
        case_decide; [clear Hready |contradiction]
      end
  ].
  lazymatch goal with
  | |- context [exec (funcdef_0__ok _ _) (withMemory ?base ?values)] =>
    change (withMemory base values) with
      (before_print s count (ns vardef_0__appendTheorem_node))
  end.
  destruct (exec (funcdef_0__ok (fun _ => false)
    (update (fun _ => 0) vardef_0__ok_value (Z.of_nat count)))
    (before_print s count (ns vardef_0__appendTheorem_node)))
    as [[[] printed] |] eqn:Hprint.
  2: reflexivity.
  cbn [optionBind fst snd machine setMachine nums bools].
  pose proof (PrintingFrame.generated_ok_preserves _ _ _ _ arraydef_0__meta
    ltac:(discriminate) Hprint) as Hprinted.
  rewrite before_print_metadata in Hprinted.
  repeat first [
    rewrite execLocal_bind
    | rewrite nth_lt_default with (default := 0%Z)
    | rewrite Hprinted | rewrite Hcount | rewrite Hcount_native
    | progress replace (Z.to_nat 3) with 3%nat by reflexivity
    | progress replace (Z.of_nat count + 1) with (Z.of_nat (S count)) by lia
    | match goal with |- context [coerceInt ?value 64] =>
        rewrite (coerce_word value) by (unfold word, maximum in *; lia)
      end
    | progress cbn [addInt bind retrieve store execLocal localStep step optionBind
        nums bools machine setMachine fst snd]
    | case_decide; [|lia]
  ].
  reflexivity.
Qed.

Lemma before_print_history s count node :
  memory (before_print s count node) arraydef_0__theorems =
    <[count := node]> (growList (memory s arraydef_0__theorems) (S count) 0).
Proof.
  unfold before_print. cbn [withMemory memory].
  change (<[count := node]>
    (growArrays (memory s) arraydef_0__theorems (S count) 0 arraydef_0__theorems) =
    <[count := node]> (growList (memory s arraydef_0__theorems) (S count) 0)).
  now rewrite growArrays_same.
Qed.

Lemma before_print_other s count node name : name <> arraydef_0__theorems ->
  memory (before_print s count node) name = memory s name.
Proof. destruct name; intros; try congruence; reflexivity. Qed.

Definition valid_id meaning id :=
  exists p, nth_error meaning (Z.to_nat id) = Some p /\ SetTheory.derives p.

Lemma history_as_Forall s meaning :
  history_safe s meaning <-> Forall (valid_id meaning) (memory s arraydef_0__theorems).
Proof. unfold history_safe, valid_id. rewrite Forall_forall. reflexivity. Qed.

Lemma update_grown_history {A} (P : A -> Prop) values count zero value :
  (count <= length values)%nat -> Forall P values -> P value ->
  Forall P (<[count := value]> (growList values (S count) zero)).
Proof.
  intros Hcount Hold Hvalue. destruct (Nat.eq_dec count (length values)) as [-> |Hneq].
  - rewrite FreshExecution.insert_grown_end. apply Forall_app. split; [exact Hold |].
    constructor; [exact Hvalue |constructor].
  - rewrite growList_no_shrink by lia. now apply Forall_insert.
Qed.

Lemma before_print_safe s count node meaning :
  (count <= length (memory s arraydef_0__theorems))%nat ->
  history_safe s meaning -> valid_id meaning node ->
  history_safe (before_print s count node) meaning.
Proof.
  intros Hcount Hsafe Hnode. apply history_as_Forall.
  rewrite before_print_history. apply update_grown_history; try assumption.
  now apply history_as_Forall.
Qed.

Lemma history_safe_frame s final meaning :
  memory final arraydef_0__theorems = memory s arraydef_0__theorems ->
  history_safe s meaning -> history_safe final meaning.
Proof. unfold history_safe. intros Hmemory Hsafe. now rewrite Hmemory. Qed.

Lemma store_meta_safe s meaning slot value :
  history_safe s meaning -> history_safe (store_meta s slot value) meaning.
Proof.
  apply history_safe_frame. now apply store_meta_other.
Qed.

Theorem generated_append_fits_safe s bs ns count final meaning :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 3 (memory s arraydef_0__meta) 0 = Z.of_nat count ->
  List.nth 8 (memory s arraydef_0__meta) 0 = 0 -> Z.of_nat count < maximum ->
  (count <= length (memory s arraydef_0__theorems))%nat ->
  history_safe s meaning -> valid_id meaning (ns vardef_0__appendTheorem_node) ->
  exec (funcdef_0__appendTheorem bs ns) s = Some (tt,final) -> history_safe final meaning.
Proof.
  intros Hmeta Hcount Hflag Hlimit Hallocated Hsafe Hnode Hrun.
  rewrite (generated_append_fits s bs ns count Hmeta Hcount Hflag Hlimit) in Hrun.
  destruct (exec (funcdef_0__ok (fun _ => false)
    (update (fun _ => 0) vardef_0__ok_value (Z.of_nat count)))
    (before_print s count (ns vardef_0__appendTheorem_node)))
    as [[[] printed] |] eqn:Hprint; [|discriminate].
  cbn [optionBind fst snd] in Hrun. injection Hrun as <-. apply store_meta_safe.
  apply history_safe_frame with
    (s := before_print s count (ns vardef_0__appendTheorem_node)).
  - eapply PrintingFrame.generated_ok_preserves; [discriminate |exact Hprint].
  - now apply before_print_safe.
Qed.

Theorem generated_append_full s bs ns :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 3 (memory s arraydef_0__meta) 0 = maximum ->
  List.nth 8 (memory s arraydef_0__meta) 0 = 0 ->
  exec (funcdef_0__appendTheorem bs ns) s = Some (tt, store_meta s 8 1).
Proof.
  intros Hmeta Hcount Hflag.
  change (@List.nth Z (Z.to_nat 3) (memory s arraydef_0__meta) 0 = maximum) in Hcount.
  change (@List.nth Z (Z.to_nat 8) (memory s arraydef_0__meta) 0 = 0) in Hflag.
  unfold funcdef_0__appendTheorem. rewrite exec_eliminate.
  unfold funcdef_0__appendTheorem_body. rewrite execLocal_bind.
  cbn [bind retrieve execLocal localStep step optionBind nums machine setMachine fst snd].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z), Hflag.
  cbn [bind execLocal optionBind fst snd nums machine setMachine].
  rewrite bool_decide_true by reflexivity. repeat rewrite execLocal_bind.
  cbn [bind retrieve execLocal localStep step optionBind nums machine setMachine fst snd].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z), Hcount.
  cbn [bind execLocal optionBind fst snd nums machine setMachine].
  rewrite bool_decide_true by reflexivity.
  cbn [store bind execLocal localStep step optionBind nums machine setMachine fst snd].
  case_decide; [reflexivity |lia].
Qed.

Theorem generated_append_error s bs ns :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 8 (memory s arraydef_0__meta) 0 <> 0 ->
  exec (funcdef_0__appendTheorem bs ns) s = Some (tt, s).
Proof.
  intros Hmeta Hflag.
  change (@List.nth Z (Z.to_nat 8) (memory s arraydef_0__meta) 0 <> 0) in Hflag.
  unfold funcdef_0__appendTheorem. rewrite exec_eliminate.
  unfold funcdef_0__appendTheorem_body. rewrite execLocal_bind.
  cbn [bind retrieve execLocal localStep step optionBind nums machine setMachine fst snd].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z).
  cbn [bind execLocal optionBind fst snd nums machine setMachine].
  rewrite bool_decide_false by exact Hflag. reflexivity.
Qed.

Theorem generated_append_safe s bs ns count final meaning :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 3 (memory s arraydef_0__meta) 0 = Z.of_nat count ->
  Z.of_nat count <= maximum -> (count <= length (memory s arraydef_0__theorems))%nat ->
  history_safe s meaning -> valid_id meaning (ns vardef_0__appendTheorem_node) ->
  exec (funcdef_0__appendTheorem bs ns) s = Some (tt, final) -> history_safe final meaning.
Proof.
  intros Hmeta Hcount Hlimit Hallocated Hsafe Hnode Hrun.
  destruct (Z.eq_dec (List.nth 8 (memory s arraydef_0__meta) 0) 0) as [Hclear |Herror].
  - destruct (Z.eq_dec (Z.of_nat count) maximum) as [Hfull |Hspace].
    + rewrite (generated_append_full s bs ns Hmeta (eq_trans Hcount Hfull) Hclear) in Hrun.
      injection Hrun as <-. now apply store_meta_safe.
    + eapply generated_append_fits_safe; try eassumption. lia.
  - rewrite (generated_append_error s bs ns Hmeta Herror) in Hrun.
    injection Hrun as <-. exact Hsafe.
Qed.

Definition append_post (s final : Machine) count node :=
  memory final arraydef_0__theorems =
    <[count := node]> (growList (memory s arraydef_0__theorems) (S count) 0) /\
  List.nth 3 (memory final arraydef_0__meta) 0 = Z.of_nat (S count) /\
  (forall slot, slot <> 3%nat -> List.nth slot (memory final arraydef_0__meta) 0 =
    List.nth slot (memory s arraydef_0__meta) 0) /\
  length (memory final arraydef_0__meta) = length (memory s arraydef_0__meta) /\
  (forall name, name <> arraydef_0__meta -> name <> arraydef_0__theorems ->
    name <> arraydef_0__printBuffer -> memory final name = memory s name).

Theorem generated_append_fits_post s bs ns count final :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 3 (memory s arraydef_0__meta) 0 = Z.of_nat count ->
  List.nth 8 (memory s arraydef_0__meta) 0 = 0 -> Z.of_nat count < maximum ->
  exec (funcdef_0__appendTheorem bs ns) s = Some (tt,final) ->
  append_post s final count (ns vardef_0__appendTheorem_node).
Proof.
  intros Hmeta Hcount Hflag Hlimit Hrun.
  rewrite (generated_append_fits s bs ns count Hmeta Hcount Hflag Hlimit) in Hrun.
  destruct (exec (funcdef_0__ok (fun _ => false)
    (update (fun _ => 0) vardef_0__ok_value (Z.of_nat count)))
    (before_print s count (ns vardef_0__appendTheorem_node)))
    as [[[] printed] |] eqn:Hprint; [|discriminate].
  cbn [optionBind fst snd] in Hrun. injection Hrun as <-.
  assert (Hframe : forall name, name <> arraydef_0__printBuffer ->
    memory printed name = memory (before_print s count (ns vardef_0__appendTheorem_node)) name).
  { intros name Hname. eapply PrintingFrame.generated_ok_preserves; eassumption. }
  assert (Hprinted : memory printed arraydef_0__meta = memory s arraydef_0__meta).
  { rewrite Hframe by discriminate. apply before_print_metadata. }
  unfold append_post. split.
  - rewrite store_meta_other by discriminate. rewrite Hframe by discriminate.
    apply before_print_history.
  - split.
    + unfold store_meta. cbn [withMemory memory]. rewrite modify_meta.
      apply OverflowExecution.nth_insert_same. rewrite Hprinted. lia.
    + split.
      * intros slot Hslot. unfold store_meta. cbn [withMemory memory].
        rewrite modify_meta, nth_insert_other by exact Hslot. now rewrite Hprinted.
      * split.
        -- rewrite store_meta_length, Hprinted. reflexivity.
        -- intros name Hmeta' Hhistory Hbuffer.
           rewrite store_meta_other by exact Hmeta'. rewrite Hframe by exact Hbuffer.
           now apply before_print_other.
Qed.
End AppendExecution.
