From CoqCP Require Import Options.
From Trusted Require Import SetTheory.
From NativeProof Require Import RenameStack RenameMemoIndexBounds.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.
Module RenameMemoTransition.
(* A cache hit may replace any complete visit. All other native branches take
   exactly one step of the ordinary capture-avoiding traversal. *)
Inductive step rho : list RenameStack.frame -> SetTheory.formula ->
  list RenameStack.frame -> SetTheory.formula -> Prop :=
| expanded stack value : step rho stack value
    (fst (RenameStack.tick rho (stack,value))) (snd (RenameStack.tick rho (stack,value)))
| cached source depth tail value : step rho (RenameStack.visit source depth::tail) value
    tail (RenameStack.renamed rho depth source).
Theorem source_bounds rho stack value next result bound :
  step rho stack value next result -> RenameMemoIndexBounds.stack_bound bound stack ->
  RenameMemoIndexBounds.stack_bound bound next.
Proof.
  intros Hstep Hbound. destruct Hstep as [stack value|source depth tail value].
  - destruct stack as [|task stack]; [exact Hbound|].
    inversion Hbound as [|front tail Hfront Htail]; subst.
    destruct task as [p depth|p q depth|p q depth left_value|p depth];
      cbn [RenameMemoIndexBounds.source RenameMemoIndexBounds.formula_bound] in Hfront;
      cbn [RenameStack.tick fst]; try exact Htail.
    + destruct p; cbn [RenameStack.tick fst]; try exact Htail.
      * destruct Hfront as [Hp Hq]. repeat constructor; assumption.
      * repeat constructor; assumption.
    + destruct Hfront as [Hp Hq]. repeat constructor; assumption.
  - inversion Hbound; assumption.
Qed.
Fixpoint height p : nat := match p with
  | SetTheory.falsity | SetTheory.equal _ _ | SetTheory.member _ _=>0
  | SetTheory.implies p q=>Nat.max (height p) (height q)
  | SetTheory.all p=>S (height p) end.
Definition depth task := match task with
  | RenameStack.visit _ d | RenameStack.left_done _ _ d
  | RenameStack.right_done _ _ d _ | RenameStack.body_done _ d=>d end.
Definition depth_bounds ceiling stack := Forall
  (fun task=>depth task+height (RenameMemoIndexBounds.source task)<=ceiling) stack.
Theorem binder_depths rho stack value next result ceiling :
  step rho stack value next result -> depth_bounds ceiling stack -> depth_bounds ceiling next.
Proof.
  intros Hstep Hbound. destruct Hstep as [stack value|source d tail value].
  - destruct stack as [|task stack]; [exact Hbound|].
    inversion Hbound as [|front tail Hfront Htail]; subst.
    destruct task as [p d|p q d|p q d left_value|p d];
      cbn [depth RenameMemoIndexBounds.source height] in Hfront;
      cbn [RenameStack.tick fst]; try exact Htail.
    + destruct p as [|i j|i j|p q|p]; cbn [RenameStack.tick fst]; try exact Htail.
      * cbn [height] in Hfront. constructor; [cbn [depth RenameMemoIndexBounds.source]; lia|].
        constructor; [exact Hfront|exact Htail].
      * cbn [height] in Hfront. constructor; [cbn [depth RenameMemoIndexBounds.source]; lia|].
        constructor; [exact Hfront|exact Htail].
    + constructor; [cbn [depth RenameMemoIndexBounds.source]; lia|].
      constructor; [exact Hfront|exact Htail].
  - inversion Hbound; assumption.
Qed.
End RenameMemoTransition.
