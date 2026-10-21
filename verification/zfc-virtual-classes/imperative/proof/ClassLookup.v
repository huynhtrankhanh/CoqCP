From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash ClassStorage NameRepresentation RenameStorage.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ClassLookup.
Import IndexExecution SipHashExecution.
(* Allocation writes unsigned values. Keep that fact explicit in addition to
   the semantic decode relation, which alone forgets signed representations. *)
Definition wellformed (s : Machine) := Forall (fun (raw : Z * Z) => word (snd raw)) (memory s arraydef_0__classes).
Lemma empty s : memory s arraydef_0__classes = [] -> wellformed s.
Proof. intros Hempty. unfold wellformed. rewrite Hempty. constructor. Qed.
Lemma transport s t : memory t arraydef_0__classes = memory s arraydef_0__classes -> wellformed s -> wellformed t.
Proof. intros Harray. unfold wellformed. now rewrite Harray. Qed.
Lemma append_wellformed s fs classes tag value : ClassStorage.represents s fs classes -> wellformed s -> word value ->
  wellformed (ClassStorage.result s (length classes) (tag,value)).
Proof.
  intros Hclasses Hgood Hword. unfold wellformed. rewrite ClassStorage.result_classes, ClassStorage.written_app by (now apply ClassStorage.represents_length in Hclasses).
  apply Forall_app. split; [exact Hgood|]. constructor; [exact Hword|constructor].
Qed.
Lemma frame_wellformed s t : RenameStorage.logical_frame s t -> wellformed s -> wellformed t.
Proof. intros [Ha Hrest]. apply transport. apply Ha. repeat split; discriminate. Qed.
Lemma lookup s fs classes index cls : ClassStorage.represents s fs classes -> wellformed s -> nth_error classes index = Some cls ->
  (index < length (memory s arraydef_0__classes))%nat /\
  ((exists variable, cls = VirtualClasses.set variable /\ word (Z.of_nat variable) /\
      nth_error (memory s arraydef_0__classes) index = Some (0,Z.of_nat variable)) \/
   (exists root p, cls = VirtualClasses.abstract (VirtualClasses.core p) /\
      nth_error fs root = Some p /\ nth_error (memory s arraydef_0__classes) index = Some (1,Z.of_nat root))).
Proof.
  intros [_ Hclasses] Hgood Hlookup.
  destruct (NameRepresentation.related_lookup _ _ _ index cls Hclasses Hlookup) as [[tag value] [Hraw Hdecode]].
  assert (Hbound : (index < length (memory s arraydef_0__classes))%nat).
  { apply nth_error_Some. match goal with |- ?expression <> None =>
      assert (Hsame : expression = Some (tag,value)) by exact Hraw; rewrite Hsame; discriminate end. }
  assert (Hword : word value).
  { unfold wellformed in Hgood. apply List.Forall_forall with (x:=(tag,value)) in Hgood; [exact Hgood|]. eapply List.nth_error_In. exact Hraw. }
  assert (Hnatural : value = Z.of_nat (Z.to_nat value)) by (rewrite Z2Nat.id by exact (proj1 Hword); reflexivity).
  split; [exact Hbound|]. unfold ClassStorage.decode in Hdecode.
  destruct (Z.eq_dec tag 0) as [->|Hnotzero].
  - injection Hdecode as <-. left. exists (Z.to_nat value). split; [reflexivity|]. split.
    + now rewrite <-Hnatural.
    + now rewrite <-Hnatural.
  - destruct (Z.eq_dec tag 1) as [->|Hnotone]; [|discriminate].
    destruct (nth_error fs (Z.to_nat value)) as [p|] eqn:Hp; [|discriminate]. injection Hdecode as <-.
    right. exists (Z.to_nat value),p. split; [reflexivity|]. split; [exact Hp|]. now rewrite <-Hnatural.
Qed.
End ClassLookup.
