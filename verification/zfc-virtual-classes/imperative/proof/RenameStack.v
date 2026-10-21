From CoqCP Require Import Options.
From Trusted Require Import SetTheory.
From NativeProof Require Import Lift.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

(* The four phases are those of the imperative traversal's frame records.
   The execution refinement must additionally relate those records and formula
   IDs to these frames; this module proves the traversal's termination measure
   and its simultaneous, capture-avoiding substitution invariant. *)
Module RenameStack.
Import SetTheory IndexSemantics.
Inductive frame :=
| visit (p : formula) (depth : nat)
| left_done (p q : formula) (depth : nat)
| right_done (p q : formula) (depth : nat) (left_value : formula)
| body_done (p : formula) (depth : nat).
Definition state := (list frame * formula)%type.
Definition renamed rho depth p := rename (under_binders depth rho) p.
Definition frame_meaning rho task result :=
  match task with
  | visit p depth => renamed rho depth p
  | left_done _ q depth => implies result (renamed rho depth q)
  | right_done _ _ _ left_value => implies left_value result
  | body_done _ _ => all result
  end.
Fixpoint meaning rho stack result :=
  match stack with [] => result | task :: tail => meaning rho tail (frame_meaning rho task result) end.
Fixpoint work p : nat := match p with
  | falsity | equal _ _ | member _ _ => 1
  | implies p q => work p + work q + 3
  | all p => work p + 2
  end.
Definition frame_work task : nat := match task with
  | visit p _ => work p
  | left_done _ q _ => work q + 2
  | right_done _ _ _ _ | body_done _ _ => 1
  end.
Fixpoint pending stack : nat := match stack with [] => 0 | task :: tail => frame_work task + pending tail end.
Definition tick rho (s : state) : state :=
  match s with
  | ([],result) => ([],result)
  | (visit p depth :: tail,result) => match p with
    | falsity => (tail,falsity)
    | equal i j => (tail,equal (under_binders depth rho i) (under_binders depth rho j))
    | member i j => (tail,member (under_binders depth rho i) (under_binders depth rho j))
    | implies p q => (visit p depth :: left_done p q depth :: tail,result)
    | all p => (visit p (S depth) :: body_done p depth :: tail,result)
    end
  | (left_done p q depth :: tail,result) => (visit q depth :: right_done p q depth result :: tail,result)
  | (right_done _ _ _ left_value :: tail,result) => (tail,implies left_value result)
  | (body_done _ _ :: tail,result) => (tail,all result)
  end.
Lemma work_positive p : 0 < work p.
Proof. destruct p; cbn; lia. Qed.
Lemma pending_positive task stack : 0 < pending (task :: stack).
Proof.
  destruct task; cbn; try lia.
  match goal with |- context [work ?body] => pose proof (work_positive body); lia end.
Qed.
Lemma tick_decreases rho task stack result :
  pending (task :: stack) = S (pending (fst (tick rho (task :: stack,result)))).
Proof. destruct task as [p depth|p q depth|p q depth left_value|p depth]; [destruct p| | | ]; cbn [tick pending frame_work work fst]; lia. Qed.
Lemma tick_preserves rho stack result :
  meaning rho (fst (tick rho (stack,result))) (snd (tick rho (stack,result))) = meaning rho stack result.
Proof.
  destruct stack as [|task stack]; [reflexivity|].
  destruct task as [p depth|p q depth|p q depth left_value|p depth]; try reflexivity.
  destruct p; reflexivity.
Qed.
Fixpoint run fuel rho (s : state) : state :=
  match fuel with 0 => s | S fuel => match fst s with [] => s | _ :: _ => run fuel rho (tick rho s) end end.
Theorem run_complete fuel rho stack result : pending stack <= fuel ->
  run fuel rho (stack,result) = ([],meaning rho stack result).
Proof.
  induction fuel as [|fuel IH] in stack,result |- *.
  - intros Hbound. destruct stack as [|task stack]; [reflexivity|]. pose proof (pending_positive task stack). lia.
  - intros Hbound. destruct stack as [|task stack]; [reflexivity|].
    change (run fuel rho (tick rho (task :: stack,result)) = ([],meaning rho (task :: stack) result)).
    pose proof (tick_decreases rho task stack result) as Hdecrease.
    pose proof (tick_preserves rho (task :: stack) result) as Hmeaning.
    destruct (tick rho (task :: stack,result)) as [next value]. cbn [fst snd] in Hdecrease,Hmeaning.
    rewrite IH by lia. now rewrite Hmeaning.
Qed.
Theorem root_correct fuel rho p depth result : work p <= fuel ->
  run fuel rho ([visit p depth],result) = ([],rename (under_binders depth rho) p).
Proof. intros Hwork. apply run_complete. cbn [pending frame_work]. lia. Qed.
Theorem unbound_root_correct fuel rho p result : work p <= fuel ->
  run fuel rho ([visit p 0],result) = ([],rename rho p).
Proof. apply root_correct. Qed.
Fixpoint size p : nat := match p with
  | falsity | equal _ _ | member _ _ => 1
  | implies p q => 1 + size p + size q
  | all p => 1 + size p end.
Lemma work_bound p : work p <= 3 * size p.
Proof. induction p; cbn; lia. Qed.
Theorem size_budget_correct fuel rho p depth result : 3 * size p <= fuel ->
  run fuel rho ([visit p depth],result) = ([],rename (under_binders depth rho) p).
Proof. intros Hbound. apply root_correct. pose proof (work_bound p). lia. Qed.
End RenameStack.
