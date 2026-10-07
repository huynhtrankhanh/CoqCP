From CoqCP Require Import Options KoxiaPolynomial KoxiaLeafRun KoxiaBufferSplit KoxiaTraversal KoxiaArena KoxiaTreeBuffers KoxiaStack.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Lia.

(* The abstract visit stack augmented with precisely the coordinates and
   arena metadata represented in each generated five-field frame. *)
Inductive AnnotatedFrame :=
| VisitTree (start : nat) (tree : EventTree)
| VisitRight (start middle span : nat) (tree : EventTree)
    (saved : list Z) (savedLen base : nat)
| VisitMerge (start span : nat) (saved : list Z) (savedLen base : nat).

Definition eraseAnnotatedFrame frame : ProofFrame :=
  match frame with
  | VisitTree _ tree => BeginTree tree
  | VisitRight _ _ _ tree saved savedLen _ => RightTree tree saved savedLen
  | VisitMerge _ _ saved savedLen _ => MergeTree saved savedLen
  end.
Definition eraseAnnotatedStack (stack : list AnnotatedFrame) : list ProofFrame :=
  map eraseAnnotatedFrame stack.

Definition encodeAnnotatedFrame (frame : AnnotatedFrame) : Z*Z*Z*Z*Z :=
  match frame with
  | VisitTree start tree =>
      (Z.of_nat start,Z.of_nat (start+length (treeEvents tree)),0%Z,0%Z,0%Z)
  | VisitRight start middle span _ _ savedLen base =>
      (Z.of_nat start,Z.of_nat (start+span),1%Z,Z.of_nat base,Z.of_nat savedLen)
  | VisitMerge start span _ savedLen base =>
      (Z.of_nat start,Z.of_nat (start+span),2%Z,Z.of_nat base,Z.of_nat savedLen)
  end.
Definition encodeAnnotatedStack (stack : list AnnotatedFrame) : list (Z*Z*Z*Z*Z) :=
  map encodeAnnotatedFrame (rev stack).

Lemma rev_one_cons {A} (first : A) (stack : list A) :
  rev (first::stack)=rev stack++[first].
Proof. cbn [rev]. reflexivity. Qed.

Lemma encodeAnnotatedStack_cons frame stack :
  encodeAnnotatedStack (frame::stack)=encodeAnnotatedStack stack++[encodeAnnotatedFrame frame].
Proof. unfold encodeAnnotatedStack. rewrite rev_one_cons,map_app. cbn [map]. reflexivity. Qed.

Lemma rev_two_cons {A} (first second : A) (stack : list A) :
  rev (first::second::stack)=rev stack++[second;first].
Proof. rewrite rev_one_cons,rev_one_cons. rewrite <-app_assoc. reflexivity. Qed.
Lemma encode_two_cons (first second : AnnotatedFrame) (stack : list AnnotatedFrame) :
  encodeAnnotatedStack (first::second::stack)=
    encodeAnnotatedStack stack++[encodeAnnotatedFrame second;encodeAnnotatedFrame first].
Proof. unfold encodeAnnotatedStack. rewrite rev_two_cons,map_app. cbn [map]. reflexivity. Qed.

Lemma encode_branch_stack start leftTree rightTree saved savedLen base stack :
  encodeAnnotatedStack
    (VisitTree start leftTree :: VisitRight start (start+length (treeEvents leftTree))
      (length (treeEvents leftTree++treeEvents rightTree)) rightTree saved savedLen base :: stack)=
  encodeAnnotatedStack stack ++
    [encodeAnnotatedFrame (VisitRight start (start+length (treeEvents leftTree))
      (length (treeEvents leftTree++treeEvents rightTree)) rightTree saved savedLen base);
     encodeAnnotatedFrame (VisitTree start leftTree)].
Proof. apply encode_two_cons. Qed.

Lemma encode_right_stack start middle span tree saved savedLen base stack :
  encodeAnnotatedStack
    (VisitTree middle tree :: VisitMerge start span saved savedLen base :: stack)=
  encodeAnnotatedStack stack ++
    [encodeAnnotatedFrame (VisitMerge start span saved savedLen base);
     encodeAnnotatedFrame (VisitTree middle tree)].
Proof. apply encode_two_cons. Qed.

Lemma insert_two_at_end {A} (prefix : list A) current next rest newCurrent newNext :
  <[S (length prefix):=newNext]>(<[length prefix:=newCurrent]>(prefix++current::next::rest))=
    prefix++newCurrent::newNext::rest.
Proof.
  assert (first : <[length prefix:=newCurrent]>(prefix++current::next::rest)=
      prefix++newCurrent::next::rest).
  { rewrite insert_app_r_alt by lia. replace (length prefix-length prefix)%nat with 0%nat by lia.
    cbn [insert list_insert]. reflexivity. }
  rewrite first,insert_app_r_alt by lia.
  replace (S (length prefix)-length prefix)%nat with 1%nat by lia.
  cbn [insert list_insert]. reflexivity.
Qed.

Fixpoint annotatedVisit fuel (stack : list AnnotatedFrame) values len top :
    list AnnotatedFrame * (list Z * nat * nat) :=
  match fuel,stack with
  | O,_ | _,[] => (stack,(values,len,top))
  | S fuel,VisitTree start (Leaf events)::stack =>
    let result := runBuffers events values len in
    annotatedVisit fuel stack (fst result) (snd result) top
  | S fuel,VisitTree start (Branch leftTree rightTree)::stack =>
    let events := treeEvents leftTree++treeEvents rightTree in
    let cut := specialCount events in
    let saved := savedBuffer values len cut (length events) in
    let savedLen := savedLength len cut (length events) in
    let middle := start+length (treeEvents leftTree) in
    annotatedVisit fuel
      (VisitTree start leftTree::VisitRight start middle (length events) rightTree saved savedLen top::stack)
      values (Nat.min len cut) (top+savedLen)
  | S fuel,VisitRight start middle span tree saved savedLen base::stack =>
    annotatedVisit fuel
      (VisitTree middle tree::VisitMerge start span saved savedLen base::stack) values len top
  | S fuel,VisitMerge _ _ saved savedLen base::stack =>
    annotatedVisit fuel stack (mergeBuffer values len saved savedLen) (Nat.max len savedLen) base
  end.

Lemma eraseAnnotatedStack_length stack : length (eraseAnnotatedStack stack)=length stack.
Proof. unfold eraseAnnotatedStack. rewrite length_map. reflexivity. Qed.

Theorem annotatedVisit_erases fuel stack values len top :
  eraseAnnotatedStack (fst (annotatedVisit fuel stack values len top))=
    fst (visitStack fuel (eraseAnnotatedStack stack) values len) /\
  fst (fst (snd (annotatedVisit fuel stack values len top)))=
    fst (snd (visitStack fuel (eraseAnnotatedStack stack) values len)) /\
  snd (fst (snd (annotatedVisit fuel stack values len top)))=
    snd (snd (visitStack fuel (eraseAnnotatedStack stack) values len)).
Proof.
  induction fuel as [|fuel IH] in stack,values,len,top |- *.
  - destruct stack; cbn [annotatedVisit visitStack eraseAnnotatedStack]; tauto.
  - destruct stack as [|frame stack]; [cbn [annotatedVisit visitStack eraseAnnotatedStack]; tauto|].
    destruct frame as [start tree|start middle span tree saved savedLen base|start span saved savedLen base].
    + destruct tree as [events|leftTree rightTree].
      * cbn [annotatedVisit visitStack eraseAnnotatedStack eraseAnnotatedFrame].
        specialize (IH stack (fst (runBuffers events values len)) (snd (runBuffers events values len)) top).
        exact IH.
      * cbn [annotatedVisit visitStack eraseAnnotatedStack eraseAnnotatedFrame].
        specialize (IH
          (VisitTree start leftTree::VisitRight start (start+length (treeEvents leftTree))
            (length (treeEvents leftTree++treeEvents rightTree)) rightTree
            (savedBuffer values len (specialCount (treeEvents leftTree++treeEvents rightTree))
              (length (treeEvents leftTree++treeEvents rightTree)))
            (savedLength len (specialCount (treeEvents leftTree++treeEvents rightTree))
              (length (treeEvents leftTree++treeEvents rightTree))) top::stack)
          values (Nat.min len (specialCount (treeEvents leftTree++treeEvents rightTree)))
          (top+savedLength len (specialCount (treeEvents leftTree++treeEvents rightTree))
            (length (treeEvents leftTree++treeEvents rightTree)))).
        exact IH.
    + cbn [annotatedVisit visitStack eraseAnnotatedStack eraseAnnotatedFrame].
      specialize (IH (VisitTree middle tree::VisitMerge start span saved savedLen base::stack)
        values len top). exact IH.
    + cbn [annotatedVisit visitStack eraseAnnotatedStack eraseAnnotatedFrame].
      specialize (IH stack (mergeBuffer values len saved savedLen) (Nat.max len savedLen) base).
      exact IH.
Qed.

Lemma annotatedVisit_empty fuel values len top :
  annotatedVisit fuel [] values len top=([],(values,len,top)).
Proof. destruct fuel; reflexivity. Qed.

Theorem annotatedVisit_tree tree fuel stack start values len top :
  annotatedVisit (treeVisits tree+fuel) (VisitTree start tree::stack) values len top=
  annotatedVisit fuel stack (fst (treeBuffers tree values len)) (snd (treeBuffers tree values len)) top.
Proof.
  induction tree as [events|leftTree IHleft rightTree IHright] in fuel,stack,start,values,len,top |- *.
  - reflexivity.
  - cbn [treeVisits treeBuffers].
    replace (3+treeVisits leftTree+treeVisits rightTree+fuel)%nat with
      (S (treeVisits leftTree+S (treeVisits rightTree+S fuel)))%nat by lia.
    cbn [annotatedVisit]. rewrite IHleft. cbn [annotatedVisit]. rewrite IHright. reflexivity.
Qed.

Theorem annotatedVisit_complete tree fuel values len top :
  (treeVisits tree<=fuel)%nat ->
  annotatedVisit fuel [VisitTree 0 tree] values len top =
    ([],(fst (treeBuffers tree values len),snd (treeBuffers tree values len),top)).
Proof.
  intro enough. replace fuel with (treeVisits tree+(fuel-treeVisits tree))%nat by lia.
  rewrite annotatedVisit_tree. apply annotatedVisit_empty.
Qed.

Theorem annotatedVisit_balanced_complete events values len top :
  annotatedVisit (4*length events+1) [VisitTree 0 (balancedTree 20 events)] values len top =
    ([],(fst (treeBuffers (balancedTree 20 events) values len),
      snd (treeBuffers (balancedTree 20 events) values len),top)).
Proof.
  apply annotatedVisit_complete. apply balancedTree_visits.
Qed.
