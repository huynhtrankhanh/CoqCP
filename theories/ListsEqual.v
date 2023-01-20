From stdpp Require Import numbers list.

Inductive ListExpression (A : Type) :=
| NilExpression
| VarExpression (x : list A)
| ConsExpression (head : A) (tail : ListExpression A)
| AppExpression (l1 l2 : ListExpression A). 

Fixpoint interpret {A : Type} (expression : ListExpression A) : list A :=
  match expression with
  | NilExpression _ => []
  | VarExpression _ x => x
  | ConsExpression _ a b => a :: interpret b
  | AppExpression _ l1 l2 => interpret l1 ++ interpret l2
  end.

Inductive ListExpressionFlattenedTerm (A : Type) :=
| Singleton (x : A)
| AnyList (x : list A).

Fixpoint flatten {A : Type} (expression : ListExpression A) : list (ListExpressionFlattenedTerm A) :=
  match expression with
  | (NilExpression _) => []
  | (VarExpression _ x) => [AnyList _ x]
  | (ConsExpression _ head tail) => [Singleton _ head] ++ flatten tail
  | (AppExpression _ l1 l2) => flatten l1 ++ flatten l2
  end.

Fixpoint interpretFlattened {A : Type} (flattenedExpression : list (ListExpressionFlattenedTerm A)) :=
  match flattenedExpression with
  | [] => []
  | (Singleton _ x :: tail) => x :: interpretFlattened tail
  | (AnyList _ x :: tail) => x ++ interpretFlattened tail
  end.

Lemma flattenCorrect {A : Type} (expression : ListExpression A) : interpret expression = interpretFlattened (flatten expression).
Proof.
  assert (h1 : forall head expression, interpret (ConsExpression A head expression) = head :: interpret expression). { unfold interpret. easy. }
  assert (h2 : forall head expression, flatten (ConsExpression A head expression) = [Singleton _ head] ++ flatten expression). { unfold interpret. easy. }
  assert (h3 : forall expression1 expression2, interpret (AppExpression A expression1 expression2) = interpret expression1 ++ interpret expression2). { unfold interpret. easy. }
  assert (h4 : forall expression1 expression2, flatten (AppExpression A expression1 expression2) = flatten expression1 ++ flatten expression2). { unfold flatten. easy. }
  assert (h5 : forall expression1 expression2 : ListExpression A, interpretFlattened (flatten expression1 ++ flatten expression2) = interpretFlattened (flatten expression1) ++ interpretFlattened (flatten expression2)).
  { intro expression1. induction expression1.
    - simpl. easy.
    - simpl. rewrite app_nil_r. easy.
    - intros. simpl. rewrite IHexpression1. easy.
    - intros. simpl. rewrite <- app_assoc. rewrite <- h4. repeat rewrite IHexpression1_1. rewrite h4. rewrite IHexpression1_2. rewrite app_assoc. easy. }
  induction expression.
  - easy.
  - simpl. rewrite app_nil_r. reflexivity.
  - rewrite h1, h2. simpl. rewrite IHexpression. reflexivity.
  - rewrite h3, h4, h5, <- IHexpression1, <- IHexpression2. reflexivity.
Qed.

Lemma listsEqualReflect {A : Type} (expression1 expression2 : ListExpression A) : interpretFlattened (flatten expression1) = interpretFlattened (flatten expression2) -> interpret expression1 = interpret expression2.
Proof.
  intro h. repeat rewrite flattenCorrect. easy.
Qed.

Ltac listExpressionReify me :=
  match me with
  | nil => NilExpression
  | ?head :: ?tail =>
    let r1 := listExpressionReify head in
    let r2 := listExpressionReify tail in
      constr:(ConsExpression _ r1 r2)
  | ?l1 ++ ?l2 =>
    let r1 := listExpressionReify l1 in
    let r2 := listExpressionReify l2 in
      constr:(AppExpression _ r1 r2)
  | _ => constr:(VarExpression _ me)
  end.

Ltac listsEqual :=
  match goal with
  | [|- ?me1 = ?me2] =>
    let r1 := listExpressionReify me1 in
    let r2 := listExpressionReify me2 in
      change (interpret r1 = interpret r2);
        apply listsEqualReflect; simpl; repeat rewrite app_nil_r; easy
  end.

Lemma test0 (l1 : list nat) (x : nat) : [x] ++ l1 = x :: l1.
Proof. listsEqual. Qed.

Lemma test1 (l1 l2 l3 : list nat) (x : nat) : l1 ++ [x] ++ l2 ++ l3 = l1 ++ (x :: l2) ++ l3.
Proof. listsEqual. Qed.

Lemma test2 (a b c d e : nat) : [a; b; c] ++ [] ++ [d; e] = [a; b; c; d; e] ++ [] ++ [].
Proof. listsEqual. Qed.

Lemma test3 (l1 l2 l3 : list nat) (x : nat) : l1 ++ [x] ++ l2 ++ l3 = l1 ++ (x :: l2 ++ l3).
Proof. listsEqual. Qed.