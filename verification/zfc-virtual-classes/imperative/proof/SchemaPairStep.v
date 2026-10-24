From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  FormulaProjection Representation ClassStorage FormulaTopology HashTable SchemaPair SchemaEvaluation SchemaEvaluationControl SchemaMarking ArrayFacts InternTail Overflow.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaPairStep.
Import IndexExecution SipHashExecution ObservedLocal SchemaPair SchemaEvaluationControl.
Definition written (s:Machine) key id := withMemory s (modifyArray (memory s) arraydef_0__schemaValues key id).
Lemma written_other s key id name : name<>arraydef_0__schemaValues -> memory (written s key id) name=memory s name.
Proof. intro Hname. unfold written. cbn [memory withMemory]. now apply InternTailExecution.modify_other. Qed.
Lemma written_length s key id : length (memory (written s key id) arraydef_0__schemaValues)=length (memory s arraydef_0__schemaValues).
Proof. unfold written. cbn [memory withMemory]. rewrite InternTailExecution.modify_same. apply length_insert. Qed.
Lemma written_same s key id : (key<length (memory s arraydef_0__schemaValues))%nat ->
 SchemaEvaluation.value (written s key id) key=id.
Proof. intro Hkey. unfold SchemaEvaluation.value,written. cbn [memory withMemory]. rewrite InternTailExecution.modify_same. now apply OverflowExecution.nth_insert_same. Qed.
Lemma written_preserves s key id index : index<>key -> SchemaEvaluation.value (written s key id) index=SchemaEvaluation.value s index.
Proof. intro Hindex. unfold SchemaEvaluation.value,written. cbn [memory withMemory]. rewrite InternTailExecution.modify_same. now apply ArrayFacts.nth_insert_other. Qed.
Theorem generated_output (f:Frame) width remaining outer_remaining key observations :
 (0<length (memory (machine f) arraydef_0__meta))%nat ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key ->
 (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 execLocalObserved (dropWithinLoop (raw_output width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(setMachine f (written (machine f) key (meta_value (machine f) 0)),observations)).
Proof.
 intros Hmeta Hkey Hbound. unfold raw_output.
 repeat first [progress cbn [optionBind fst snd bind]
 |progress rewrite drop_assoc|progress rewrite drop_lift|progress rewrite drop_lift_final
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine];rewrite ?Nat2Z.id;first [exact Hbound|exact Hmeta|lia])
 |progress rewrite Hkey|progress rewrite Nat2Z.id
 |progress cbn [dropWithinLoop Action_rect]]. reflexivity.
Qed.
Theorem generated_compute which (f middle:Frame) width remaining outer_remaining kind key observations :
 nums f vardef_0__schemaInstance_kind=kind -> nums middle vardef_0__schemaInstance_kind=kind -> applies which kind ->
 execLocalObserved (dropWithinLoop (selected which width remaining outer_remaining)) (f,observations)=Some (KeepGoing,(middle,observations)) ->
 (0<length (memory (machine middle) arraydef_0__meta))%nat ->
 nums middle vardef_0__schemaInstance_key=Z.of_nat key ->
 (key<length (memory (machine middle) arraydef_0__schemaValues))%nat ->
 execLocalObserved (dropWithinLoop (SchemaEvaluation.compute_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(setMachine middle (written (machine middle) key (meta_value (machine middle) 0)),observations)).
Proof.
 intros Hkind Hmiddle Happly Hrun Hmeta Hkey Hbound.
 rewrite (generated_dispatch which f middle width remaining outer_remaining kind observations Hkind Hmiddle Happly Hrun).
 now apply generated_output.
Qed.
Definition descriptor_frame (f:Frame) (raw:Z*Z*Z*Z*Z*Z*Z) :=
 let '(kind,a,b,c,d,_,_):=raw in
 setNum (setNum (setNum (setNum (setNum f vardef_0__schemaInstance_kind kind)
   vardef_0__schemaInstance_a a) vardef_0__schemaInstance_b b) vardef_0__schemaInstance_c c) vardef_0__schemaInstance_d d.
Definition marked_with width remaining outer_remaining (work:LoopAction unit) : LoopAction unit := ltac:(
 let code:=eval cbv beta iota zeta delta [SchemaEvaluation.marked_body] in (SchemaEvaluation.marked_body width remaining outer_remaining) in
 let rest:=eval cbv beta iota zeta delta [SchemaEvaluation.compute_body] in (SchemaEvaluation.compute_body width remaining outer_remaining) in
 let family:=eval pattern rest in code in lazymatch family with ?family _=>exact (family work) end).
Lemma actual_marked width remaining outer_remaining : SchemaEvaluation.marked_body width remaining outer_remaining=
 marked_with width remaining outer_remaining (SchemaEvaluation.compute_body width remaining outer_remaining).
Proof. reflexivity. Qed.
Theorem generated_descriptor (f:Frame) width remaining outer_remaining node raw (work:LoopAction unit) observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some raw ->
 execLocalObserved (dropWithinLoop (marked_with width remaining outer_remaining work)) (f,observations)=
 execLocalObserved (dropWithinLoop work) (descriptor_frame f raw,observations).
Proof.
 intros Hnode Hraw.
 assert (Hbound:(node<length (memory (machine f) arraydef_0__schemaNodes))%nat) by (apply nth_error_Some;congruence).
 pose proof (List.nth_error_nth _ _ (0,0,0,0,0,0,0) Hraw) as Hnth.
 unfold SchemaEvaluation.depth in Hnode. destruct raw as [[[[[[kind a] b] c] d] typ] arity].
 unfold marked_with,descriptor_frame.
 repeat first [progress cbn [optionBind fst snd bind]
 |progress rewrite drop_assoc|progress rewrite drop_lift|progress rewrite drop_lift_final
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];rewrite ?Hnode,?Nat2Z.id;exact Hbound)
 |progress rewrite Hnode|progress rewrite Nat2Z.id
 |match goal with |- context [List.nth ?i ?xs ?zero]=>
   let expression:=constr:(List.nth i xs zero) in
   let Hsame:=fresh in assert (Hsame:expression=(kind,a,b,c,d,typ,arity)) by exact Hnth;rewrite Hsame;clear Hsame end
 |progress cbn [machine setMachine setNum]]. reflexivity.
Qed.
Lemma written_meta s key id cell : meta_value (written s key id) cell=meta_value s cell.
Proof. unfold meta_value. now rewrite written_other by discriminate. Qed.
Lemma written_all_lengths s key id name : length (memory (written s key id) name)=length (memory s name).
Proof. destruct (decide (name=arraydef_0__schemaValues)) as [->|Hname];[apply written_length|now rewrite written_other]. Qed.
Lemma written_arena s key id fs : NativeRepresentation.canonical_arena s fs ->
 NativeRepresentation.canonical_arena (written s key id) fs.
Proof.
 apply FormulaProjection.storage_arena. split;[now rewrite written_other by discriminate|]. split.
 - intros name Hneeded. apply written_other. unfold FormulaProjection.needed in Hneeded.
   destruct Hneeded as [Heq|[Heq|[Heq|Heq]]];subst name;discriminate.
 - repeat split;apply written_meta.
Qed.
Lemma written_classes s key id fs classes : ClassStorage.represents s fs classes -> ClassStorage.represents (written s key id) fs classes.
Proof. unfold ClassStorage.represents. rewrite written_meta,written_other by discriminate. tauto. Qed.
Lemma written_topology s key id count : FormulaTopology.ordered s count -> FormulaTopology.ordered (written s key id) count.
Proof. intro H. apply (FormulaTopology.same s);[exact H|]. intros parent Hparent. unfold HashTableInvariant.tuple_at. now rewrite written_other by discriminate. Qed.
Lemma descriptor_machine f raw : machine (descriptor_frame f raw)=machine f.
Proof. destruct raw as [[[[[[k a] b] c] d] ty] ar]. reflexivity. Qed.
Lemma descriptor_kind f kind a b c d ty ar : nums (descriptor_frame f (kind,a,b,c,d,ty,ar)) vardef_0__schemaInstance_kind=kind.
Proof. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. Qed.
Lemma descriptor_key f raw : nums (descriptor_frame f raw) vardef_0__schemaInstance_key=nums f vardef_0__schemaInstance_key.
Proof. destruct raw as [[[[[[k a] b] c] d] ty] ar]. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. reflexivity. Qed.
Theorem generated_marked which (f middle:Frame) width remaining outer_remaining node kind a b c d ty ar key observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (kind,a,b,c,d,ty,ar) ->
 nums middle vardef_0__schemaInstance_kind=kind -> applies which kind ->
 execLocalObserved (dropWithinLoop (selected which width remaining outer_remaining))
   (descriptor_frame f (kind,a,b,c,d,ty,ar),observations)=Some (KeepGoing,(middle,observations)) ->
 (0<length (memory (machine middle) arraydef_0__meta))%nat ->
 nums middle vardef_0__schemaInstance_key=Z.of_nat key ->
 (key<length (memory (machine middle) arraydef_0__schemaValues))%nat ->
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(setMachine middle (written (machine middle) key (meta_value (machine middle) 0)),observations)).
Proof.
 intros Hnode Hraw Hkind Happly Hrun Hmeta Hkey Hbound. rewrite actual_marked.
 rewrite (generated_descriptor f width remaining outer_remaining node (kind,a,b,c,d,ty,ar)
   (SchemaEvaluation.compute_body width remaining outer_remaining) observations Hnode Hraw).
 eapply generated_compute;[apply descriptor_kind|exact Hkind|exact Happly|exact Hrun|exact Hmeta|exact Hkey|exact Hbound].
Qed.
Theorem generated_marked_literal (f:Frame) width remaining outer_remaining node kind a b c d ty ar key fs classes rho depth expression observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (kind,a,b,c,d,ty,ar) ->
 (kind=1 \/ kind=2 \/ kind=11) ->
 (0<length (memory (machine f) arraydef_0__meta))%nat ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key ->
 (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 SchemaEvaluation.meaning fs classes rho depth expression a ->
 exists final,execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\
 SchemaEvaluation.meaning fs classes rho depth expression (SchemaEvaluation.value (machine final) key) /\
 (forall index,index<>key -> SchemaEvaluation.value (machine final) index=SchemaEvaluation.value (machine f) index) /\
 (forall name,length (memory (machine final) name)=length (memory (machine f) name)).
Proof.
 intros Hnode Hraw Hkind Hmeta Hkey Hbound Hmeaning.
 set (parsed:=descriptor_frame f (kind,a,b,c,d,ty,ar)).
 set (middle:=setMachine parsed (store_meta (machine f) 0 a)).
 set (final:=setMachine middle (written (machine middle) key (meta_value (machine middle) 0))).
 assert (Hparsed:machine parsed=machine f) by apply descriptor_machine.
 assert (Ha:nums parsed vardef_0__schemaInstance_a=a).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 assert (Hrun:execLocalObserved (dropWithinLoop (selected literal width remaining outer_remaining)) (parsed,observations)=Some (KeepGoing,(middle,observations))).
 { change (execLocalObserved (SchemaEvaluation.literal_handler width remaining outer_remaining) (parsed,observations)=Some (KeepGoing,(middle,observations))).
   unfold middle. rewrite <-Hparsed. rewrite <-Ha. apply SchemaEvaluation.generated_literal. now rewrite Hparsed. }
 assert (Hmiddlemeta:meta_value (machine middle) 0=a).
 { unfold middle. cbn [machine setMachine]. now apply meta_store_same. }
 exists final. split.
 - unfold final. eapply (generated_marked literal);try eassumption.
   + unfold middle. cbn [nums setMachine]. apply descriptor_kind.
   + unfold middle. cbn [machine setMachine]. rewrite store_meta_length. exact Hmeta.
 - split.
   + unfold final. cbn [machine setMachine]. rewrite written_same.
     * now rewrite Hmiddlemeta.
     * unfold middle. cbn [machine setMachine]. rewrite store_meta_other by discriminate. exact Hbound.
   + split.
     * intros index Hindex. unfold final. cbn [machine setMachine]. rewrite written_preserves by exact Hindex.
       unfold middle,SchemaEvaluation.value. cbn [machine setMachine]. now rewrite store_meta_other by discriminate.
     * intro name. unfold final. cbn [machine setMachine]. rewrite written_all_lengths.
       unfold middle. cbn [machine setMachine]. destruct (decide (name=arraydef_0__meta)) as [->|Hname].
       -- apply store_meta_length.
       -- now rewrite store_meta_other.
Qed.
End SchemaPairStep.
