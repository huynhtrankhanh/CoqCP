From CoqCP Require Import Options KoxiaFourier KoxiaPolynomial KoxiaModular KoxiaLeafRun KoxiaPolynomialBuffers
  KoxiaArrayLoops KoxiaTables KoxiaBufferSplit KoxiaArena.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lists.List Lia.
Local Open Scope Z_scope.
Local Existing Instance congruent_equivalence.
Local Existing Instance congruent_add.
Definition savedBuffer values len cut span :=
  map (fun index => binomialTransform span
    (KoxiaPolynomial.shift (Z.of_nat cut) (high (Z.of_nat cut) (activeCoefficient values len)))
    (Z.of_nat index) mod koxiaModulus) (seq 0 (savedLength len cut span)).
Fixpoint treeBuffers tree values len : list Z*nat := match tree with
  | Leaf events => runBuffers events values len
  | Branch leftTree rightTree =>
    let events := treeEvents leftTree++treeEvents rightTree in
    let cut := specialCount events in
    let small := Nat.min len cut in
    let saved := savedBuffer values len cut (length events) in
    let leftResult := treeBuffers leftTree values small in
    let lowResult := treeBuffers rightTree (fst leftResult) (snd leftResult) in
    (mergeBuffer (fst lowResult) (snd lowResult) saved (savedLength len cut (length events)),
     Nat.max (snd lowResult) (savedLength len cut (length events)))
  end.
Lemma savedBuffer_length values len cut span : length (savedBuffer values len cut span)=savedLength len cut span.
Proof. unfold savedBuffer. rewrite length_map,length_seq. reflexivity. Qed.
Lemma savedBuffer_canonical values len cut span : tableCanonical (savedBuffer values len cut span).
Proof. unfold savedBuffer,tableCanonical. apply Forall_map,Forall_forall. intros index present. apply residue_bounds. Qed.
Lemma savedBuffer_lookup values len cut span index : (index<savedLength len cut span)%nat ->
  nth index (savedBuffer values len cut span) 0=
  binomialTransform span (KoxiaPolynomial.shift (Z.of_nat cut) (high (Z.of_nat cut) (activeCoefficient values len)))
    (Z.of_nat index) mod koxiaModulus.
Proof.
  intro bound. unfold savedBuffer.
  set (coefficient := fun index => binomialTransform span (KoxiaPolynomial.shift (Z.of_nat cut) (high (Z.of_nat cut) (activeCoefficient values len))) (Z.of_nat index) mod koxiaModulus).
  rewrite (@nth_indep Z (map coefficient (seq 0 (savedLength len cut span))) index 0 (coefficient 0%nat)) by (rewrite length_map,length_seq; exact bound).
  rewrite (map_nth coefficient _ 0%nat).
  rewrite seq_nth by exact bound. cbn. reflexivity.
Qed.
Lemma shifted_high_bounded values len cut : (cut<=len)%nat ->
  forall j, j<0 \/ Z.of_nat (len-cut)<=j ->
    KoxiaPolynomial.shift (Z.of_nat cut) (high (Z.of_nat cut) (activeCoefficient values len)) j=0.
Proof.
  intros cutBound j outside. unfold KoxiaPolynomial.shift,high.
  destruct outside as [negative|beyond].
  - rewrite (proj2 (Z.ltb_lt (j+Z.of_nat cut) (Z.of_nat cut))) by lia. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (j+Z.of_nat cut) (Z.of_nat cut))) by lia.
    apply activeCoefficient_outside. lia.
Qed.
Lemma high_empty values len cut : (len<=cut)%nat -> high (Z.of_nat cut) (activeCoefficient values len)=(fun _=>0).
Proof.
  intro cutBound. apply functional_extensionality. intro j. unfold high.
  destruct (j <? Z.of_nat cut) eqn:below; [reflexivity|].
  apply Z.ltb_ge in below. apply activeCoefficient_outside. lia.
Qed.
Lemma binomialTransform_zero span : binomialTransform span (fun _=>0)=(fun _=>0).
Proof. induction span as [|span IH]; [reflexivity|]. cbn [binomialTransform]. rewrite IH. reflexivity. Qed.
Theorem savedBuffer_correct values len events j :
  congruent (activeCoefficient (savedBuffer values len (specialCount events) (length events))
    (savedLength len (specialCount events) (length events)) j)
    (unrestricted events (high (specials events) (activeCoefficient values len)) j).
Proof.
  rewrite unrestricted_binomial,specialCount_agrees,<-binomialTransform_shift.
  unfold savedLength. destruct (Nat.ltb (specialCount events) len) eqn:present.
  - apply Nat.ltb_lt in present.
    destruct (Z_lt_ge_dec j 0) as [negative|nonnegative].
    + rewrite activeCoefficient_outside by lia.
      rewrite (binomialTransform_bounded (len-specialCount events) (length events))
        by (try apply shifted_high_bounded; lia). reflexivity.
    + destruct (Z_lt_ge_dec j (Z.of_nat (len-specialCount events+length events))) as [inside|outside].
      * rewrite activeCoefficient_inside by lia.
        rewrite savedBuffer_lookup by (unfold savedLength; rewrite (proj2 (Nat.ltb_lt _ _) present); lia).
        rewrite Z2Nat.id by lia. apply congruent_modulo.
      * rewrite activeCoefficient_outside by lia.
        rewrite (binomialTransform_bounded (len-specialCount events) (length events))
          by (try apply shifted_high_bounded; lia). reflexivity.
  - apply Nat.ltb_ge in present.
    rewrite activeCoefficient_outside by lia. rewrite high_empty by exact present.
    change (congruent 0 (binomialTransform (length events) (fun _=>0) j)).
    rewrite binomialTransform_zero. reflexivity.
Qed.
Lemma output_length_merge len events :
  Nat.max (Nat.min len (specialCount events)+ordinaryCount events) (savedLength len (specialCount events) (length events))=
  (len+ordinaryCount events)%nat.
Proof.
  unfold savedLength. pose proof (event_counts events) as counts.
  destruct (Nat.ltb (specialCount events) len) eqn:present.
  - apply Nat.ltb_lt in present. rewrite Nat.min_r by lia. lia.
  - apply Nat.ltb_ge in present. rewrite Nat.min_l by lia. lia.
Qed.
Lemma treeBuffers_length tree values len : length (fst (treeBuffers tree values len))=length values.
Proof.
  induction tree as [events|leftTree IHleft rightTree IHright] in values,len |- *.
  - apply runBuffers_length.
  - cbn [treeBuffers fst]. rewrite mergeBuffer_length,IHright,IHleft. reflexivity.
Qed.
Lemma treeBuffers_active tree values len : snd (treeBuffers tree values len)=(len+ordinaryCount (treeEvents tree))%nat.
Proof.
  induction tree as [events|leftTree IHleft rightTree IHright] in values,len |- *.
  - apply runBuffers_active.
  - cbn [treeBuffers snd treeEvents]. rewrite IHright,IHleft.
    rewrite <-Nat.add_assoc,<-ordinaryCount_app. apply output_length_merge.
Qed.
Theorem treeBuffers_canonical tree values len : (len+length (treeEvents tree)<=length values)%nat ->
  tableCanonical values -> tableCanonical (fst (treeBuffers tree values len)).
Proof.
  induction tree as [events|leftTree IHleft rightTree IHright] in values,len |- *.
  - apply runBuffers_canonical.
  - intros room canonical. cbn [treeBuffers fst]. apply mergeBuffer_canonical,IHright.
    + rewrite treeBuffers_active,treeBuffers_length. cbn [treeEvents] in room. rewrite length_app in room.
      pose proof (ordinaryCount_bound (treeEvents leftTree)) as ordinaryBound. lia.
    + apply IHleft; [cbn [treeEvents] in room; rewrite length_app in room; lia|exact canonical].
Qed.
Theorem treeBuffers_correct tree values len : (len+length (treeEvents tree)<=length values)%nat -> forall j,
  congruent (activeCoefficient (fst (treeBuffers tree values len)) (snd (treeBuffers tree values len)) j)
    (run (treeEvents tree) (activeCoefficient values len) j).
Proof.
  induction tree as [events|leftTree IHleft rightTree IHright] in values,len |- *.
  - apply runBuffers_correct.
  - intros room j. cbn [treeEvents] in room |- *. rewrite length_app in room.
    cbn [treeBuffers fst snd].
    etransitivity.
    + apply mergeBuffer_correct. rewrite treeBuffers_active,treeBuffers_active,treeBuffers_length,treeBuffers_length.
      rewrite <-Nat.add_assoc,<-ordinaryCount_app,output_length_merge.
      pose proof (ordinaryCount_bound (treeEvents leftTree++treeEvents rightTree)) as ordinaryBound.
      rewrite length_app in ordinaryBound. lia.
    + rewrite run_split_high. unfold KoxiaPolynomial.plus. apply congruent_add.
      * rewrite run_app. transitivity (run (treeEvents rightTree)
          (activeCoefficient (fst (treeBuffers leftTree values (Nat.min len (specialCount (treeEvents leftTree++treeEvents rightTree)))))
          (snd (treeBuffers leftTree values (Nat.min len (specialCount (treeEvents leftTree++treeEvents rightTree)))))) j).
        -- apply IHright. rewrite treeBuffers_active,treeBuffers_length.
           pose proof (ordinaryCount_bound (treeEvents leftTree)) as ordinaryBound. lia.
        -- apply run_congruent. intro index. rewrite specialCount_agrees,<-activeCoefficient_low.
           apply IHleft. lia.
      * apply savedBuffer_correct.
Qed.
