From CoqCP Require Import Options.

From Stdlib Require Import Lists.List Bool.Bool ZArith.ZArith Lia
  Logic.FunctionalExtensionality.
Import ListNotations.
Local Open Scope Z_scope.

(* Coefficients are indexed by all integers; negative states are zeroed by
   the boundary condition. This file proves the algebraic decomposition used
   by the fast solver. It does not assume an NTT is correct. *)
Definition Coefficients := Z -> Z.
Definition plus (p q : Coefficients) : Coefficients := fun j => p j + q j.
Definition supported (lo : Z) (p : Coefficients) := forall j, j < lo -> p j = 0.
Definition flag (special : bool) : Z := if special then 1 else 0.
(* Special transitions are p[j]+p[j+1], whereas ordinary transitions
   are p[j]+p[j-1]. The special case includes the deletion option at j. *)
Definition unrestrictedStep (special : bool) (p : Coefficients) : Coefficients :=
  fun j => if special then p j + p (j + 1) else p j + p (j - 1).
Definition boundaryStep (special : bool) (p : Coefficients) : Coefficients :=
  fun j => if j <? 0 then 0 else unrestrictedStep special p j.

Fixpoint run (events : list bool) (p : Coefficients) : Coefficients :=
  match events with
  | [] => p
  | special :: events => run events (boundaryStep special p)
  end.
Fixpoint unrestricted (events : list bool) (p : Coefficients) : Coefficients :=
  match events with
  | [] => p
  | special :: events => unrestricted events (unrestrictedStep special p)
  end.
Fixpoint specials (events : list bool) : Z :=
  match events with [] => 0 | b :: events => flag b + specials events end.

Lemma specials_nonnegative events : 0 <= specials events.
Proof. induction events as [| b events IH]; cbn; [lia |]. destruct b; cbn [flag]; lia. Qed.

Lemma unrestrictedStep_supported b p lo : supported lo p ->
  supported (lo - flag b) (unrestrictedStep b p).
Proof.
  intros hp j hj. unfold unrestrictedStep. destruct b; cbn [flag] in hj.
  - rewrite (hp j), (hp (j+1)); lia.
  - rewrite (hp j), (hp (j-1)); lia.
Qed.

Lemma boundaryStep_unrestricted b p : supported (flag b) p ->
  boundaryStep b p = unrestrictedStep b p.
Proof.
  intro hp. apply functional_extensionality. intro j.
  unfold boundaryStep. destruct (j <? 0) eqn:hj; [| reflexivity].
  apply Z.ltb_lt in hj. symmetry.
  pose proof (unrestrictedStep_supported b p (flag b) hp) as supported'.
  apply supported'. lia.
Qed.

Lemma unrestricted_high events p : supported (specials events) p ->
  run events p = unrestricted events p.
Proof.
  induction events as [| b events IH] in p |- *; [reflexivity |].
  cbn [specials]. intro hp. cbn [run unrestricted].
  rewrite boundaryStep_unrestricted.
  - apply IH. pose proof (unrestrictedStep_supported b p (flag b + specials events) hp) as hs.
    unfold supported in *. intros j hj. apply hs. lia.
  - intros j hj. apply hp. pose proof (specials_nonnegative events). lia.
Qed.

Lemma boundaryStep_plus b p q :
  boundaryStep b (plus p q) = plus (boundaryStep b p) (boundaryStep b q).
Proof.
  apply functional_extensionality. intro j.
  unfold boundaryStep, unrestrictedStep, plus.
  destruct (j <? 0); [ring |]. destruct b; ring.
Qed.

Lemma run_plus events p q : run events (plus p q) = plus (run events p) (run events q).
Proof.
  induction events as [| b events IH] in p, q |- *; [reflexivity |].
  cbn [run]. rewrite boundaryStep_plus. apply IH.
Qed.

Definition low (cut : Z) (p : Coefficients) : Coefficients :=
  fun j => if j <? cut then p j else 0.
Definition high (cut : Z) (p : Coefficients) : Coefficients :=
  fun j => if j <? cut then 0 else p j.

Lemma split_coefficients cut p : p = plus (low cut p) (high cut p).
Proof.
  apply functional_extensionality. intro j. unfold plus, low, high.
  destruct (j <? cut); ring.
Qed.

Lemma high_supported cut p : supported cut (high cut p).
Proof.
  intros j hj. unfold high. apply Z.ltb_lt in hj. rewrite hj. reflexivity.
Qed.

Lemma run_split_high events p :
  run events p = plus (run events (low (specials events) p))
    (unrestricted events (high (specials events) p)).
Proof.
  rewrite (split_coefficients (specials events) p) at 1.
  rewrite run_plus.
  rewrite (unrestricted_high events (high (specials events) p) (high_supported _ _)).
  reflexivity.
Qed.

Lemma run_app left right p : run (left ++ right) p = run right (run left p).
Proof. induction left as [| b left IH] in p |- *; cbn; [reflexivity | apply IH]. Qed.

(* Removing the boundary leaves multiplication by (1+x) at every event,
   followed by a shift for every special event. *)
Definition shift (amount : Z) (p : Coefficients) : Coefficients :=
  fun j => p (j + amount).
Definition multiplyOnePlusX (p : Coefficients) : Coefficients :=
  fun j => p j + p (j - 1).
Fixpoint binomialTransform (n : nat) (p : Coefficients) : Coefficients :=
  match n with O => p | S n => multiplyOnePlusX (binomialTransform n p) end.

Lemma shift_add a b p : shift a (shift b p) = shift (a+b) p.
Proof. apply functional_extensionality. intro j. unfold shift. f_equal. lia. Qed.
Lemma shift_zero p : shift 0 p = p.
Proof. apply functional_extensionality. intro j. unfold shift. f_equal. lia. Qed.
Lemma shift_multiply amount p :
  shift amount (multiplyOnePlusX p) = multiplyOnePlusX (shift amount p).
Proof.
  apply functional_extensionality. intro j. unfold shift, multiplyOnePlusX.
  replace (j - 1 + amount) with (j + amount - 1) by lia. reflexivity.
Qed.
Lemma binomialTransform_shift n amount p :
  binomialTransform n (shift amount p) = shift amount (binomialTransform n p).
Proof.
  induction n as [| n IH]; [reflexivity |].
  cbn [binomialTransform]. rewrite IH, shift_multiply. reflexivity.
Qed.
Lemma binomialTransform_multiply n p :
  binomialTransform n (multiplyOnePlusX p) = multiplyOnePlusX (binomialTransform n p).
Proof.
  induction n as [| n IH]; [reflexivity |]. cbn [binomialTransform]. rewrite IH. reflexivity.
Qed.
Lemma unrestrictedStep_shift b p :
  unrestrictedStep b p = shift (flag b) (multiplyOnePlusX p).
Proof.
  apply functional_extensionality. intro j.
  unfold unrestrictedStep, shift, multiplyOnePlusX. destruct b; cbn [flag].
  - replace (j+1-1) with j by lia. ring.
  - rewrite Z.add_0_r. reflexivity.
Qed.

Theorem unrestricted_binomial events p :
  unrestricted events p = shift (specials events) (binomialTransform (length events) p).
Proof.
  induction events as [| b events IH] in p |- *.
  - cbn [unrestricted specials length binomialTransform]. symmetry. apply shift_zero.
  - cbn [unrestricted specials length]. rewrite IH, unrestrictedStep_shift.
    rewrite binomialTransform_shift, binomialTransform_multiply, shift_add.
    cbn [binomialTransform]. replace (specials events + flag b) with
      (flag b + specials events) by lia. reflexivity.
Qed.

Theorem divide_and_conquer_decomposition left right p :
  let cut := specials (left ++ right) in
  run (left ++ right) p =
    plus (run right (run left (low cut p)))
      (shift cut (binomialTransform (length (left ++ right)) (high cut p))).
Proof.
  cbn zeta. rewrite run_split_high, run_app, unrestricted_binomial. reflexivity.
Qed.

(* An explicit binary tree makes the recursive argument structural, with no
   unchecked termination or assumed recursion equations. *)
Inductive EventTree :=
| Leaf (events : list bool)
| Branch (ltree rtree : EventTree).
Fixpoint treeEvents (tree : EventTree) : list bool :=
  match tree with
  | Leaf events => events
  | Branch ltree rtree => treeEvents ltree ++ treeEvents rtree
  end.
Fixpoint accelerated (tree : EventTree) (p : Coefficients) : Coefficients :=
  match tree with
  | Leaf events => run events p
  | Branch ltree rtree =>
      let events := treeEvents ltree ++ treeEvents rtree in
      let cut := specials events in
      plus (accelerated rtree (accelerated ltree (low cut p)))
        (shift cut (binomialTransform (length events) (high cut p)))
  end.

Theorem accelerated_correct tree p : accelerated tree p = run (treeEvents tree) p.
Proof.
  induction tree as [events | left IHleft right IHright] in p |- *.
  - reflexivity.
  - cbn [accelerated treeEvents]. rewrite IHright, IHleft.
    symmetry. apply divide_and_conquer_decomposition.
Qed.

Fixpoint addPolynomial (a b : list Z) : list Z :=
  match a, b with
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => (x+y) :: addPolynomial a b
  end.
Fixpoint binomialRow (n : nat) : list Z :=
  match n with
  | O => [1]
  | S n => let row := binomialRow n in addPolynomial row (0 :: row)
  end.
Fixpoint convolution (kernel : list Z) (p : Coefficients) : Coefficients :=
  match kernel with
  | [] => fun _ => 0
  | a :: kernel => fun j => a * p j + convolution kernel p (j-1)
  end.

Lemma convolution_plus a b p :
  convolution (addPolynomial a b) p = plus (convolution a p) (convolution b p).
Proof.
  induction a as [| x a IH] in b |- *; destruct b as [| y b];
    cbn [convolution addPolynomial plus].
  - reflexivity.
  - apply functional_extensionality. intro j. unfold plus. ring.
  - apply functional_extensionality. intro j. unfold plus. ring.
  - rewrite IH. apply functional_extensionality. intro j. unfold plus. ring.
Qed.

Theorem binomialTransform_convolution n p :
  binomialTransform n p = convolution (binomialRow n) p.
Proof.
  induction n as [| n IH].
  - cbn [binomialTransform binomialRow convolution].
    apply functional_extensionality. intro j. ring.
  - cbn [binomialTransform binomialRow]. rewrite convolution_plus, IH.
    apply functional_extensionality. intro j. cbn [convolution].
    unfold multiplyOnePlusX, plus. ring.
Qed.

Lemma convolution_shift kernel amount p :
  shift amount (convolution kernel p) = convolution kernel (shift amount p).
Proof.
  induction kernel as [| a kernel IH]; [reflexivity |].
  apply functional_extensionality. intro j. unfold shift at 1. cbn [convolution].
  replace (j-1+amount) with (j+amount-1) by lia.
  pose proof (f_equal (fun f => f (j-1)) IH) as same.
  unfold shift in same |- *. rewrite <- same.
  f_equal. f_equal. lia.
Qed.

(* This is exactly the bulk operation: discard states below cut, extract
   the high tail, then convolve it with the binomial row. *)
Theorem bulk_convolution events p :
  unrestricted events (high (specials events) p) =
  convolution (binomialRow (length events)) (shift (specials events) (high (specials events) p)).
Proof. rewrite unrestricted_binomial, binomialTransform_convolution, convolution_shift. reflexivity. Qed.

Definition reduce (modulus : Z) (p : Coefficients) : Coefficients :=
  fun j => p j mod modulus.

Lemma boundaryStep_mod modulus b p : modulus <> 0 ->
  reduce modulus (boundaryStep b (reduce modulus p)) = reduce modulus (boundaryStep b p).
Proof.
  intro hm. apply functional_extensionality. intro j.
  unfold reduce, boundaryStep, unrestrictedStep. destruct (j <? 0); [reflexivity |].
  destruct b; symmetry; apply Z.add_mod; exact hm.
Qed.

Lemma run_mod_inputs events modulus p : modulus <> 0 ->
  reduce modulus (run events (reduce modulus p)) = reduce modulus (run events p).
Proof.
  intro hm. induction events as [| b events IH] in p |- *.
  - apply functional_extensionality. intro j. unfold reduce. apply Z.mod_mod. exact hm.
  - cbn [run]. rewrite <- (IH (boundaryStep b (reduce modulus p))).
    rewrite boundaryStep_mod by exact hm. apply IH.
Qed.

Fixpoint modularRun (modulus : Z) (events : list bool) (p : Coefficients) : Coefficients :=
  match events with
  | [] => reduce modulus p
  | b :: events => modularRun modulus events (reduce modulus (boundaryStep b p))
  end.

Theorem modularRun_correct modulus events p : modulus <> 0 ->
  modularRun modulus events p = reduce modulus (run events p).
Proof.
  intro hm. induction events as [| b events IH] in p |- *; [reflexivity |].
  cbn [modularRun run]. rewrite IH, run_mod_inputs by exact hm. reflexivity.
Qed.
