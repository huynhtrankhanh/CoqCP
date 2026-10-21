From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash NameSearch NameRepresentation BindingStorage BindName FormulaProjection ClassStorage HistoryRefinement ReplyNO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module BindNameRefinement.
Import IndexExecution SipHashExecution NameSearchExecution.
Lemma token_transport s t name : storage_frame s t -> NameRepresentation.token_rep s name -> NameRepresentation.token_rep t name.
Proof.
  intros [Harrays [Hcells _]] [Hsize [Hlength Hbytes]]. split; [rewrite Hcells by lia; exact Hsize|].
  rewrite (Harrays arraydef_0__token ltac:(discriminate)). split; assumption.
Qed.
Lemma lookup_projection s t : storage_frame s t ->
  length (memory t arraydef_0__meta) = length (memory s arraydef_0__meta) -> FormulaProjection.storage s t.
Proof.
  intros [Harrays [Hcells _]] Hlength. split; [exact Hlength|]. split.
  - intros name Hname. apply Harrays. unfold FormulaProjection.needed in Hname.
    destruct Hname as [Heq|[Heq|[Heq|Heq]]]; subst name; discriminate.
  - repeat split; apply Hcells; lia.
Qed.
Lemma lookup_classes s t fs classes : storage_frame s t -> ClassStorage.represents s fs classes -> ClassStorage.represents t fs classes.
Proof.
  intros [Harrays [Hcells _]] [Hcount Hclasses]. split; [rewrite Hcells by lia; exact Hcount|].
  now rewrite (Harrays arraydef_0__classes ltac:(discriminate)).
Qed.
Lemma lookup_history s t logical : storage_frame s t -> HistoryRefinement.represents s logical -> HistoryRefinement.represents t logical.
Proof.
  intros [Harrays [Hcells _]] [Hcount Hhistory]. split; [rewrite Hcells by lia; exact Hcount|].
  now rewrite (Harrays arraydef_0__theorems ltac:(discriminate)).
Qed.
Theorem generated_fresh s bs ns bindings name value kind meaning observations :
  (8 < length (memory s arraydef_0__meta))%nat -> (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  NameRepresentation.represents s bindings -> NameRepresentation.token_rep s name -> Protocol.valid_name name ->
  Protocol.lookup name bindings = None -> Z.of_nat (length bindings) < maximum ->
  Z.of_nat (length (memory s arraydef_0__names) + length name) <= maximum -> Z.of_nat value <= maximum ->
  NameRepresentation.decode (Z.of_nat value) 0 kind = Some meaning ->
  ns vardef_0__bindName_value = Z.of_nat value -> ns vardef_0__bindName_kind = kind ->
  exists final, execObserved (funcdef_0__bindName bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK value); unreadInput := stdin s|}])) /\
    NameRepresentation.represents final (bindings ++ [(name,meaning)]) /\ FormulaProjection.storage s final /\
    (forall fs classes, ClassStorage.represents s fs classes -> ClassStorage.represents final fs classes) /\
    (forall logical, HistoryRefinement.represents s logical -> HistoryRefinement.represents final logical) /\
    meta_value final 8 = meta_value s 8.
Proof.
  intros Hmeta Hbuffer Hrep Htoken Hvalid Hfresh Hcountword Hbytesword Hvalueword Hdecode Hvalue Hkind.
  assert (Hfind : find_native s (length bindings) (length name) (length bindings) = None).
  { pose proof (NameRepresentation.lookup_correspondence s bindings name Hrep Htoken) as Hmeaning.
    destruct (find_native s (length bindings) (length name) (length bindings)); [|reflexivity].
    destruct Hmeaning as [meaning' [Hentry Hlookup]]. congruence. }
  destruct (generated_lookup_with_capacity s (fun _ => false) (fun _ => 0) (length bindings) (length name) observations
    ltac:(lia) (proj1 Hrep) (proj1 Htoken) (proj1 (proj2 Htoken)) (NameRepresentation.valid_storage s bindings Hrep))
    as [looked [Hlookup [Hcorrect Hlength]]].
  rewrite Hfind in Hcorrect. destruct Hcorrect as [Hmissing Hframe].
  pose proof (NameRepresentation.storage_transport s looked bindings Hframe Hrep) as Hrep'.
  pose proof (token_transport s looked name Hframe Htoken) as Htoken'.
  pose proof Hframe as [Harrays [Hcells [Hinput Houtput]]].
  assert (Hmeta' : (8 < length (memory looked arraydef_0__meta))%nat) by (now rewrite Hlength).
  assert (Hbuffer' : (20 <= length (memory looked arraydef_0__printBuffer))%nat)
    by (now rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate))).
  assert (Hbytesword' : Z.of_nat (length (memory looked arraydef_0__names) + length name) <= maximum)
    by (now rewrite (Harrays arraydef_0__names ltac:(discriminate))).
  set (final := BindingStorage.result looked (length bindings) (length (memory looked arraydef_0__names)) (length name) value kind).
  exists final. split.
  - pose proof (BindNameExecution.generated_bind s bs ns looked (length bindings) (length (memory looked arraydef_0__names))
      (length name) value kind observations Hlookup Hmeta' Hbuffer' Hmissing (proj1 Hrep') (proj1 (proj2 Hrep'))
      (proj1 Htoken') Hcountword Hbytesword' Hvalueword Hvalue Hkind (proj1 (proj2 Htoken'))) as Hrun.
    rewrite Hinput,Houtput in Hrun. exact Hrun.
  - split.
    + exact (BindingStorage.append_represents looked bindings name value kind meaning ltac:(lia)
        Hrep' Htoken' Hcountword Hbytesword' Hvalueword Hdecode Hvalid).
    + split.
      * eapply FormulaProjection.storage_trans; [exact (lookup_projection s looked Hframe Hlength)|apply BindingStorage.result_projection].
      * split.
        -- intros fs classes Hclasses. apply BindingStorage.result_classes. exact (lookup_classes s looked fs classes Hframe Hclasses).
        -- split.
           ++ intros logical Hhistory. apply BindingStorage.result_history. exact (lookup_history s looked logical Hframe Hhistory).
           ++ unfold final. rewrite BindingStorage.result_meta_other by lia. apply Hcells. lia.
Qed.
Theorem generated_duplicate s bs ns bindings name meaning observations :
  (6 < length (memory s arraydef_0__meta))%nat ->
  NameRepresentation.represents s bindings -> NameRepresentation.token_rep s name ->
  Protocol.lookup name bindings = Some meaning ->
  exists final, execObserved (funcdef_0__bindName bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin s|}])) /\
    NameRepresentation.represents final bindings /\ FormulaProjection.storage s final /\
    (forall fs classes, ClassStorage.represents s fs classes -> ClassStorage.represents final fs classes) /\
    (forall logical, HistoryRefinement.represents s logical -> HistoryRefinement.represents final logical) /\
    meta_value final 8 = meta_value s 8.
Proof.
  intros Hmeta Hrep Htoken Hpresent.
  assert (Hfind : exists index, find_native s (length bindings) (length name) (length bindings) = Some index).
  { pose proof (NameRepresentation.lookup_correspondence s bindings name Hrep Htoken) as Hmeaning.
    destruct (find_native s (length bindings) (length name) (length bindings)) as [index|]; [now exists index|congruence]. }
  destruct Hfind as [index Hfind].
  destruct (generated_lookup_with_capacity s (fun _ => false) (fun _ => 0) (length bindings) (length name) observations
    Hmeta (proj1 Hrep) (proj1 Htoken) (proj1 (proj2 Htoken)) (NameRepresentation.valid_storage s bindings Hrep))
    as [looked [Hlookup [Hcorrect Hlength]]].
  rewrite Hfind in Hcorrect. destruct Hcorrect as [Hfound Hframe].
  pose proof (found_below_sentinel s (length bindings) (length name) index (proj1 (proj2 (proj2 Hrep))) Hfind) as Hindex.
  pose proof (NameRepresentation.storage_transport s looked bindings Hframe Hrep) as Hrep'.
  pose proof Hframe as [Harrays [Hcells [Hinput Houtput]]].
  exists (ReplyNOExecution.reply_state looked). split.
  - pose proof (BindNameExecution.generated_duplicate s bs ns looked observations Hlookup ltac:(rewrite Hlength; lia) ltac:(lia)) as Hrun.
    rewrite Hinput,Houtput in Hrun. exact Hrun.
  - split.
    + change (NameRepresentation.represents looked bindings). exact Hrep'.
    + split.
      * change (FormulaProjection.storage s looked). exact (lookup_projection s looked Hframe Hlength).
      * split.
        -- intros fs classes Hclasses. change (ClassStorage.represents looked fs classes). exact (lookup_classes s looked fs classes Hframe Hclasses).
        -- split.
           ++ intros logical Hhistory. change (HistoryRefinement.represents looked logical). exact (lookup_history s looked logical Hframe Hhistory).
           ++ change (meta_value looked 8 = meta_value s 8). apply Hcells. lia.
Qed.
End BindNameRefinement.
