From CoqCP Require Import Options KoxiaPolynomial KoxiaLeafRun KoxiaPolynomialBuffers KoxiaBufferSplit KoxiaArena
  KoxiaTreeBuffers KoxiaTraversal.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.
(* These frames are proof data. They describe one visit of the same three
   phases used by the generated stack; they are not a replacement program. *)
Inductive ProofFrame :=
| BeginTree (tree : EventTree)
| RightTree (tree : EventTree) (saved : list Z) (savedLen : nat)
| MergeTree (saved : list Z) (savedLen : nat).
Fixpoint visitStack fuel stack values len : list ProofFrame*(list Z*nat) :=
  match fuel,stack with
  | O,_ | _,[] => (stack,(values,len))
  | S fuel,BeginTree (Leaf events)::stack =>
    let result := runBuffers events values len in visitStack fuel stack (fst result) (snd result)
  | S fuel,BeginTree (Branch leftTree rightTree)::stack =>
    let events := treeEvents leftTree++treeEvents rightTree in
    let cut := specialCount events in
    visitStack fuel (BeginTree leftTree::RightTree rightTree
      (savedBuffer values len cut (length events)) (savedLength len cut (length events))::stack)
      values (Nat.min len cut)
  | S fuel,RightTree tree saved savedLen::stack =>
    visitStack fuel (BeginTree tree::MergeTree saved savedLen::stack) values len
  | S fuel,MergeTree saved savedLen::stack =>
    visitStack fuel stack (mergeBuffer values len saved savedLen) (Nat.max len savedLen)
  end.
Theorem visitStack_tree tree fuel stack values len :
  visitStack (treeVisits tree+fuel) (BeginTree tree::stack) values len=
  visitStack fuel stack (fst (treeBuffers tree values len)) (snd (treeBuffers tree values len)).
Proof.
  induction tree as [events|leftTree IHleft rightTree IHright] in fuel,stack,values,len |- *.
  - reflexivity.
  - cbn [treeVisits treeBuffers].
    replace (3+treeVisits leftTree+treeVisits rightTree+fuel)%nat with
      (S (treeVisits leftTree+(S (treeVisits rightTree+S fuel))))%nat by lia.
    cbn [visitStack]. rewrite IHleft. cbn [visitStack]. rewrite IHright. reflexivity.
Qed.
Lemma visitStack_empty fuel values len : visitStack fuel [] values len=([],(values,len)).
Proof. destruct fuel; reflexivity. Qed.
Theorem visitStack_complete tree fuel values len : (treeVisits tree<=fuel)%nat ->
  visitStack fuel [BeginTree tree] values len=([],treeBuffers tree values len).
Proof.
  intro enough. replace fuel with (treeVisits tree+(fuel-treeVisits tree))%nat by lia.
  rewrite visitStack_tree,visitStack_empty. destruct (treeBuffers tree values len). reflexivity.
Qed.
Theorem bounded_visits_complete events values len :
  visitStack (4*length events+1) [BeginTree (balancedTree 20 events)] values len=
    ([],treeBuffers (balancedTree 20 events) values len).
Proof. apply visitStack_complete,balancedTree_visits. Qed.
