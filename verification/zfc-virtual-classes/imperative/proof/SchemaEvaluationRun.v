From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal SchemaEvaluation SchemaEvaluationInvariant
 SchemaEvaluationLoop SchemaEvaluationResources SchemaEvaluationFrames SchemaRepresentation SchemaMetadata SchemaMarking
 SchemaEvaluationDependencies SchemaEvaluationFailure SchemaEvaluationFinish SchemaPairSemantic InternInvariant SchemaEvaluationCell
 SchemaGraph Representation ClassStorage ClassLookup FormulaTopology InternReserve RenameMemoControl RenameMemoLengths RenameStorage SchemaEvaluationPreservation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationRun.
Import IndexExecution SipHashExecution ObservedLocal.
Definition logical_with logical fs classes :=
 Protocol.State fs classes (Protocol.history logical) (Protocol.bindings logical) (Protocol.expressions logical).

Record domain source logical root (rho:nat->VirtualClasses.class) fs classes (f:SchemaEvaluation.Frame) : Prop := Domain {
 arena : NativeRepresentation.canonical_arena (machine f) fs;
 class_meaning : ClassStorage.represents (machine f) fs classes;
 class_words : ClassLookup.wellformed (machine f);
 topology : FormulaTopology.ordered (machine f) (length fs);
 falsity_zero : nth_error fs 0=Some SetTheory.falsity;
 schemas : SchemaRepresentation.represents (machine f) (logical_with logical fs classes);
 source_nodes : memory (machine f) arraydef_0__schemaNodes=memory source arraydef_0__schemaNodes;
 marks : forall node depth,(node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
   (SchemaMarking.cell (machine f) (SchemaGraph.key root node depth)<>0 <-> SchemaGraph.reachable source root node depth);
 meta_allocated : (31<length (memory (machine f) arraydef_0__meta))%nat;
 sip_allocated : (0<length (memory (machine f) arraydef_0__sipState))%nat;
 values_allocated : (SchemaMarking.size root<=length (memory (machine f) arraydef_0__schemaValues))%nat;
 marks_allocated : (SchemaMarking.size root<=length (memory (machine f) arraydef_0__schemaMarks))%nat;
 root_number : nums f vardef_0__schemaInstance_root=Z.of_nat root;
 width_number : nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root);
 error_clear : meta_value (machine f) 8=0
}.

Record frame (before after:SchemaEvaluation.Frame) : Prop := Frame {
 nodes_same : memory (machine after) arraydef_0__schemaNodes=memory (machine before) arraydef_0__schemaNodes;
 marks_same : memory (machine after) arraydef_0__schemaMarks=memory (machine before) arraydef_0__schemaMarks;
 arguments_same : memory (machine after) arraydef_0__schemaArguments=memory (machine before) arraydef_0__schemaArguments;
 allocations_same : forall watched,SchemaEvaluationFrames.protected watched ->
   length (memory (machine after) watched)=length (memory (machine before) watched);
 schema_count_same : meta_value (machine after) 16=meta_value (machine before) 16;
 root_same : nums after vardef_0__schemaInstance_root=nums before vardef_0__schemaInstance_root;
 width_same : nums after vardef_0__schemaInstance_width=nums before vardef_0__schemaInstance_width
}.
Lemma frame_refl f : frame f f.
Proof. constructor;reflexivity. Qed.
Lemma frame_trans before middle after : frame before middle -> frame middle after -> frame before after.
Proof.
 intros Hfirst Hsecond. constructor.
 - rewrite (nodes_same _ _ Hsecond). exact (nodes_same _ _ Hfirst).
 - rewrite (marks_same _ _ Hsecond). exact (marks_same _ _ Hfirst).
 - rewrite (arguments_same _ _ Hsecond). exact (arguments_same _ _ Hfirst).
 - intros watched Hprotected. rewrite (allocations_same _ _ Hsecond watched Hprotected).
   exact (allocations_same _ _ Hfirst watched Hprotected).
 - rewrite (schema_count_same _ _ Hsecond). exact (schema_count_same _ _ Hfirst).
 - rewrite (root_same _ _ Hsecond). exact (root_same _ _ Hfirst).
 - rewrite (width_same _ _ Hsecond). exact (width_same _ _ Hfirst).
Qed.
Lemma frame_key f key : frame f (setNum f vardef_0__schemaInstance_key (Z.of_nat key)).
Proof.
 constructor;reflexivity.
Qed.
Lemma protected_meta : SchemaEvaluationFrames.protected arraydef_0__meta.
Proof. unfold SchemaEvaluationFrames.protected,RenameMemoLengths.protected. repeat split;discriminate. Qed.
Lemma protected_sip : SchemaEvaluationFrames.protected arraydef_0__sipState.
Proof. unfold SchemaEvaluationFrames.protected,RenameMemoLengths.protected. repeat split;discriminate. Qed.
Lemma protected_values : SchemaEvaluationFrames.protected arraydef_0__schemaValues.
Proof. unfold SchemaEvaluationFrames.protected,RenameMemoLengths.protected. repeat split;discriminate. Qed.
Lemma protected_marks : SchemaEvaluationFrames.protected arraydef_0__schemaMarks.
Proof. unfold SchemaEvaluationFrames.protected,RenameMemoLengths.protected. repeat split;discriminate. Qed.

Lemma domain_extend source logical root rho fs classes before after extra_fs extra_classes :
 domain source logical root rho fs classes before -> frame before after ->
 NativeRepresentation.canonical_arena (machine after) (fs++extra_fs) ->
 ClassStorage.represents (machine after) (fs++extra_fs) (classes++extra_classes) ->
 ClassLookup.wellformed (machine after) -> FormulaTopology.ordered (machine after) (length (fs++extra_fs)) ->
 meta_value (machine after) 8=0 ->
 domain source logical root rho (fs++extra_fs) (classes++extra_classes) after.
Proof.
 intros Hbefore Hframe Harena Hclasses Hwords Htop Herror. constructor;try assumption.
 - eapply InternReserve.lookup_preserved;[exists extra_fs;reflexivity|exact (falsity_zero _ _ _ _ _ _ _ Hbefore)].
 - eapply SchemaRepresentation.extend;[exact (schemas _ _ _ _ _ _ _ Hbefore)| | | | |reflexivity].
   + exact (schema_count_same _ _ Hframe).
   + exact (nodes_same _ _ Hframe).
   + intros i p Hi. eapply InternReserve.lookup_preserved;[exists extra_fs;reflexivity|exact Hi].
   + intros i cls Hi. eapply InternReserve.lookup_preserved;[exists extra_classes;reflexivity|exact Hi].
 - rewrite (nodes_same _ _ Hframe). exact (source_nodes _ _ _ _ _ _ _ Hbefore).
 - intros node depth Hnode Hdepth. unfold SchemaMarking.cell. rewrite (marks_same _ _ Hframe).
   exact (marks _ _ _ _ _ _ _ Hbefore node depth Hnode Hdepth).
 - rewrite (allocations_same _ _ Hframe _ protected_meta). exact (meta_allocated _ _ _ _ _ _ _ Hbefore).
 - rewrite (allocations_same _ _ Hframe _ protected_sip). exact (sip_allocated _ _ _ _ _ _ _ Hbefore).
 - rewrite (allocations_same _ _ Hframe _ protected_values). exact (values_allocated _ _ _ _ _ _ _ Hbefore).
 - rewrite (allocations_same _ _ Hframe _ protected_marks). exact (marks_allocated _ _ _ _ _ _ _ Hbefore).
 - rewrite (root_same _ _ Hframe). exact (root_number _ _ _ _ _ _ _ Hbefore).
 - rewrite (width_same _ _ Hframe). exact (width_number _ _ _ _ _ _ _ Hbefore).
Qed.

Lemma domain_key source logical root rho fs classes f key :
 domain source logical root rho fs classes f ->
 domain source logical root rho fs classes (setNum f vardef_0__schemaInstance_key (Z.of_nat key)).
Proof.
 intro Hdomain.
 assert (H:domain source logical root rho (fs++[]) (classes++[]) (setNum f vardef_0__schemaInstance_key (Z.of_nat key))).
 { apply (domain_extend source logical root rho fs classes f _ [] [] Hdomain (frame_key f key));
   rewrite ?app_nil_r;first [exact (arena _ _ _ _ _ _ _ Hdomain)|exact (class_meaning _ _ _ _ _ _ _ Hdomain)|
     exact (class_words _ _ _ _ _ _ _ Hdomain)|exact (topology _ _ _ _ _ _ _ Hdomain)|exact (error_clear _ _ _ _ _ _ _ Hdomain)]. }
 now rewrite !app_nil_r in H.
Qed.

Theorem generated_unmarked source logical root rho fs classes (f:SchemaEvaluation.Frame) node depth remaining outer_remaining observations :
 domain source logical root rho fs classes f -> SchemaGraph.ordered source ->
 (root<length (memory source arraydef_0__schemaNodes))%nat ->
 (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) remaining=Z.of_nat depth ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) outer_remaining=Z.of_nat node ->
 Z.of_nat (SchemaMarking.size root)<=maximum -> meta_value (machine f) 18<>0 ->
 SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho fs classes (machine f) (SchemaGraph.key root node depth) ->
 SchemaMarking.cell (machine f) (SchemaGraph.key root node depth)=0 ->
 let after:=setNum f vardef_0__schemaInstance_key (Z.of_nat (SchemaGraph.key root node depth)) in
 execLocalObserved (SchemaEvaluation.inner_body (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining)
   (f,observations)=Some (KeepGoing,(after,observations)) /\
 domain source logical root rho fs classes after /\ meta_value (machine after) 18<>0 /\
 SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho fs classes (machine after) (S (SchemaGraph.key root node depth)).
Proof.
 intros Hdomain Hordered Hroot Hnode Hdepth Hd Hn Hword Hvalid Hcompleted Hzero after.
 pose proof (SchemaGraph.grid_bound root node depth Hnode Hdepth) as Hgrid.
 split.
 - rewrite SchemaEvaluationLoop.actual_inner.
   rewrite (SchemaEvaluationLoop.generated_cell f (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining
     (SchemaGraph.width root) node depth (SchemaGraph.key root node depth) _ observations
     ltac:(pose proof (meta_allocated _ _ _ _ _ _ _ Hdomain);lia) Hvalid (error_clear _ _ _ _ _ _ _ Hdomain)
     (width_number _ _ _ _ _ _ _ Hdomain) Hn Hd eq_refl ltac:(unfold SchemaMarking.size in Hword;lia)
     ltac:(pose proof (marks_allocated _ _ _ _ _ _ _ Hdomain);unfold SchemaMarking.size in *;lia)).
   rewrite bool_decide_false by congruence. reflexivity.
 - split;[now apply domain_key|]. split;[exact Hvalid|].
   eapply SchemaEvaluationInvariant.completed_skip;[exact Hcompleted|reflexivity|].
   intros other otherDepth Hreachable Hequal.
   destruct (SchemaGraph.reachable_grid source root other otherDepth Hordered Hroot Hreachable) as [_ [HotherDepth _]].
   destruct (SchemaGraph.key_injective root other otherDepth node depth HotherDepth Hdepth Hequal) as [-> ->].
   apply (proj2 (marks _ _ _ _ _ _ _ Hdomain node depth Hnode Hdepth)) in Hreachable. congruence.
Qed.

Theorem completed_success source logical root rho fs classes (before after:SchemaEvaluation.Frame) extra_fs extra_classes node depth expression :
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 (depth<SchemaGraph.width root)%nat -> nth_error (Protocol.expressions logical) node=Some expression ->
 SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho fs classes (machine before) (SchemaGraph.key root node depth) ->
 (forall index,index<>SchemaGraph.key root node depth ->
   SchemaEvaluation.value (machine after) index=SchemaEvaluation.value (machine before) index) ->
 SchemaEvaluation.meaning (fs++extra_fs) (classes++extra_classes) rho depth expression
   (SchemaEvaluation.value (machine after) (SchemaGraph.key root node depth)) ->
 SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho (fs++extra_fs) (classes++extra_classes)
   (machine after) (S (SchemaGraph.key root node depth)).
Proof.
 intros Hordered Hroot Hdepth Hlookup Hcompleted Hvalues Hmeaning.
 assert (Htransport:SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho
   (fs++extra_fs) (classes++extra_classes) (machine after) (SchemaGraph.key root node depth)).
 { eapply SchemaEvaluationInvariant.completed_transport;[exact Hcompleted|]. intros index Hindex. apply Hvalues;lia. }
 eapply SchemaEvaluationInvariant.completed_step;[exact Hordered|exact Hroot|exact Htransport|reflexivity|
   exact Hdepth|reflexivity|exact Hlookup|exact Hmeaning].
Qed.

Lemma marked_frame f after width remaining outer_remaining observations :
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining))
   (f,observations)=Some (KeepGoing,(after,observations)) -> frame f after.
Proof.
 intro Hrun. constructor.
 - eapply SchemaEvaluationFrames.marked_arrays;[unfold SchemaEvaluationFrames.persistent,RenameStorage.Arrays.persistent_array;repeat split;discriminate|discriminate|exact Hrun].
 - eapply SchemaEvaluationFrames.marked_arrays;[unfold SchemaEvaluationFrames.persistent,RenameStorage.Arrays.persistent_array;repeat split;discriminate|discriminate|exact Hrun].
 - eapply SchemaEvaluationFrames.marked_arrays;[unfold SchemaEvaluationFrames.persistent,RenameStorage.Arrays.persistent_array;repeat split;discriminate|discriminate|exact Hrun].
 - intros watched Hprotected. eapply SchemaEvaluationFrames.marked_lengths;[exact Hprotected|exact Hrun].
 - eapply SchemaEvaluationPreservation.marked_cell;[unfold RenameStorage.Cells.protected;repeat split;discriminate|lia|lia|lia|exact Hrun].
 - eapply SchemaEvaluationPreservation.marked_numbers;[unfold SchemaEvaluationPreservation.protected_number;repeat split;discriminate|exact Hrun].
 - eapply SchemaEvaluationPreservation.marked_numbers;[unfold SchemaEvaluationPreservation.protected_number;repeat split;discriminate|exact Hrun].
Qed.

(** A bounded mathematical successor records the properties of a successful
    cell. It refers to arrays, typed meanings, and cardinalities, never to an
    execution of the program. *)
Definition successor source logical root rho key fs classes before next_fs next_classes after :=
 domain source logical root rho fs classes before /\ domain source logical root rho next_fs next_classes after /\
 frame before after /\ (exists extra,next_fs=fs++extra) /\ (exists extra,next_classes=classes++extra) /\
 (length next_classes<=S (length classes))%nat /\ Z.of_nat (length next_fs)<=maximum /\
 SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho fs classes (machine before) key /\
 SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho next_fs next_classes (machine after) (S key).
Definition ready_at source logical root rho key fs classes (f:SchemaEvaluation.Frame) :=
 forall node depth expression k a b c d,
 key=SchemaGraph.key root node depth -> SchemaGraph.reachable source root node depth ->
 nth_error (Protocol.expressions logical) node=Some expression ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode k a b c d expression) ->
 SchemaEvaluationResources.ready (machine f) fs classes rho depth k a b c d.

(** [fits] is a finite sufficient-resource condition. Its successor relation is
    an overapproximation by bounded semantic states; it assumes no successful
    native execution. Numeric protocol budgets can imply this condition. *)
Fixpoint fits source logical root rho count key fs classes (f:SchemaEvaluation.Frame) : Prop :=
 match count with
 | O=>True
 | S count=>ready_at source logical root rho key fs classes f /\
     forall next_fs next_classes after,
       successor source logical root rho key fs classes f next_fs next_classes after ->
       fits source logical root rho count (S key) next_fs next_classes after
 end.
Lemma fits_zero source logical root rho key fs classes f : fits source logical root rho 0 key fs classes f.
Proof. exact I. Qed.
Lemma fits_ready source logical root rho count key fs classes f :
 fits source logical root rho (S count) key fs classes f -> ready_at source logical root rho key fs classes f.
Proof. exact (@proj1 _ _). Qed.
Lemma fits_next source logical root rho count key fs classes f next_fs next_classes after :
 fits source logical root rho (S count) key fs classes f ->
 successor source logical root rho key fs classes f next_fs next_classes after ->
 fits source logical root rho count (S key) next_fs next_classes after.
Proof. intros [_ Hnext]. apply Hnext. Qed.
Lemma ready_literal native fs classes rho depth kind a b c d :
 (kind=1%nat \/ kind=2%nat \/ kind=11%nat) ->
 SchemaEvaluationResources.ready native fs classes rho depth kind a b c d.
Proof. intros [Hkind|[Hkind|Hkind]];subst kind;exact I. Qed.
Lemma fits_one_literal source logical rho fs classes (f:SchemaEvaluation.Frame) kind a b c d expression :
 (kind=1%nat \/ kind=2%nat \/ kind=11%nat) ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) 0=Some (SchemaRepresentation.encode kind a b c d expression) ->
 fits source logical 0 rho 1 0 fs classes f.
Proof.
 intros Hkind Hraw. split;[|intros;exact I].
 intros node depth other k aa bb cc dd Hkey Hreach Hlookup Hother.
 unfold SchemaGraph.key,SchemaGraph.width in Hkey.
 assert (node=0%nat /\ depth=0%nat) as [-> ->] by nia.
 rewrite Hraw in Hother. injection Hother as Hequal.
 assert (Htag:Z.of_nat kind=Z.of_nat k).
 { exact Hequal. }
 assert (kind=k) by lia. subst k. now apply ready_literal.
Qed.
Lemma arena_count s fs : NativeRepresentation.canonical_arena s fs -> Z.of_nat (length fs)<=maximum.
Proof.
 intros [Htable Hmeaning]. unfold InternInvariant.table in Htable. destruct Htable as [_ [_ [Hlimit [_ [Hbound _]]]]]. lia.
Qed.
Lemma domain_prefix source logical root rho fs classes before after next_fs next_classes :
 domain source logical root rho fs classes before -> frame before after ->
 (exists extra,next_fs=fs++extra) -> (exists extra,next_classes=classes++extra) ->
 NativeRepresentation.canonical_arena (machine after) next_fs ->
 ClassStorage.represents (machine after) next_fs next_classes ->
 ClassLookup.wellformed (machine after) -> FormulaTopology.ordered (machine after) (length next_fs) ->
 meta_value (machine after) 8=0 -> domain source logical root rho next_fs next_classes after.
Proof.
 intros Hdomain Hframe [extra_fs ->] [extra_classes ->].
 exact (domain_extend source logical root rho fs classes before after extra_fs extra_classes Hdomain Hframe).
Qed.
Lemma completed_prefix source logical root rho fs classes before after next_fs next_classes node depth expression :
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 (depth<SchemaGraph.width root)%nat -> nth_error (Protocol.expressions logical) node=Some expression ->
 (exists extra,next_fs=fs++extra) -> (exists extra,next_classes=classes++extra) ->
 SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho fs classes (machine before) (SchemaGraph.key root node depth) ->
 SchemaPairSemantic.post before after next_fs next_classes rho depth expression (SchemaGraph.key root node depth) ->
 SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho next_fs next_classes (machine after) (S (SchemaGraph.key root node depth)).
Proof.
 intros Hordered Hroot Hdepth Hlookup [extra_fs ->] [extra_classes ->] Hcompleted [Hmeaning [Hvalues Hlengths]].
 eapply completed_success;eassumption.
Qed.
Lemma prefix_transitive {A} (xs ys zs:list A) :
 (exists extra,ys=xs++extra) -> (exists extra,zs=ys++extra) -> exists extra,zs=xs++extra.
Proof. intros [first ->] [second ->]. exists (first++second). now rewrite app_assoc. Qed.
Definition progress source logical root rho initial_fs initial_classes (initial:SchemaEvaluation.Frame) key (f:SchemaEvaluation.Frame) :=
 exists fs classes,domain source logical root rho fs classes f /\ meta_value (machine f) 18<>0 /\
 SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho fs classes (machine f) key /\
 fits source logical root rho (SchemaMarking.size root-key)%nat key fs classes f /\
 frame initial f /\ (exists extra,fs=initial_fs++extra) /\ (exists extra,classes=initial_classes++extra).
Definition rejected source logical root rho rootCert initial_fs initial_classes (initial:SchemaEvaluation.Frame) (f:SchemaEvaluation.Frame) :=
 exists fs classes,domain source logical root rho fs classes f /\ meta_value (machine f) 18=0 /\
 Schemata.infer rho 0 rootCert=None /\ frame initial f /\
 (exists extra,fs=initial_fs++extra) /\ (exists extra,classes=initial_classes++extra).
Lemma progress_initial source logical root rho fs classes f :
 domain source logical root rho fs classes f -> meta_value (machine f) 18<>0 ->
 fits source logical root rho (SchemaMarking.size root) 0 fs classes f ->
 progress source logical root rho fs classes f 0 f.
Proof.
 intros Hdomain Hvalid Hfits. exists fs,classes.
 repeat first [assumption|apply SchemaEvaluationInvariant.completed_zero|apply frame_refl|
   exists [];now rewrite app_nil_r|split].
Qed.
Theorem progress_unmarked source logical root rho initial_fs initial_classes initial (f:SchemaEvaluation.Frame) node depth remaining outer_remaining observations :
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) remaining=Z.of_nat depth ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) outer_remaining=Z.of_nat node ->
 Z.of_nat (SchemaMarking.size root)<=maximum ->
 progress source logical root rho initial_fs initial_classes initial (SchemaGraph.key root node depth) f ->
 SchemaMarking.cell (machine f) (SchemaGraph.key root node depth)=0 ->
 exists after,execLocalObserved (SchemaEvaluation.inner_body (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining)
   (f,observations)=Some (KeepGoing,(after,observations)) /\
 progress source logical root rho initial_fs initial_classes initial (S (SchemaGraph.key root node depth)) after.
Proof.
 intros Hordered Hroot Hnode Hdepth Hd Hn Hword
   (fs & classes & Hdomain & Hvalid & Hcompleted & Hfits & Hframe & Hfs & Hclasses) Hzero.
 set (key:=SchemaGraph.key root node depth).
 set (after:=setNum f vardef_0__schemaInstance_key (Z.of_nat key)).
 destruct (generated_unmarked source logical root rho fs classes f node depth remaining outer_remaining observations
   Hdomain Hordered Hroot Hnode Hdepth Hd Hn Hword Hvalid Hcompleted Hzero) as [Hrun [Hafter [Haftervalid Hcomplete]]].
 assert (Hgrid:(key<SchemaMarking.size root)%nat) by (apply SchemaGraph.grid_bound;assumption).
 assert (Hremaining:(SchemaMarking.size root-key=S (SchemaMarking.size root-S key))%nat) by lia.
 change (fits source logical root rho (SchemaMarking.size root-key)%nat key fs classes f) in Hfits.
 rewrite Hremaining in Hfits.
 assert (Hsuccessor:successor source logical root rho key fs classes f fs classes after).
 { unfold successor. repeat first [assumption|apply frame_key|exact (arena_count (machine f) fs (arena _ _ _ _ _ _ _ Hdomain))|
     exists [];now rewrite app_nil_r|split|lia]. }
 exists after. split;[exact Hrun|]. exists fs,classes.
 repeat first [assumption|exact (frame_trans initial f after Hframe (frame_key f key))|split].
 exact (fits_next source logical root rho (SchemaMarking.size root-S key) key fs classes f fs classes after Hfits Hsuccessor).
Qed.
Theorem progress_marked source logical root rootCert rho initial_fs initial_classes initial (f:SchemaEvaluation.Frame) node depth remaining outer_remaining observations :
 SchemaRepresentation.represents source logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE rootCert) ->
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) remaining=Z.of_nat depth ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) outer_remaining=Z.of_nat node ->
 Z.of_nat (SchemaMarking.size root)<=maximum ->
 progress source logical root rho initial_fs initial_classes initial (SchemaGraph.key root node depth) f ->
 SchemaMarking.cell (machine f) (SchemaGraph.key root node depth)<>0 ->
 exists after,execLocalObserved (SchemaEvaluation.inner_body (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining)
   (f,observations)=Some (KeepGoing,(after,observations)) /\
 (progress source logical root rho initial_fs initial_classes initial (S (SchemaGraph.key root node depth)) after \/
  rejected source logical root rho rootCert initial_fs initial_classes initial after).
Proof.
 intros HsourceRep Hrootlookup Hordered Hroot Hnode Hdepth Hd Hn Hword
   (fs & classes & Hdomain & Hvalid & Hcompleted & Hfits & Hframe & Hfs & Hclasses) Hmarked.
 set (key:=SchemaGraph.key root node depth).
 set (keyed:=setNum f vardef_0__schemaInstance_key (Z.of_nat key)).
 assert (Hreachable:SchemaGraph.reachable source root node depth) by
   (apply (proj1 (marks _ _ _ _ _ _ _ Hdomain node depth Hnode Hdepth));exact Hmarked).
 assert (Hnodebound:(node<length (Protocol.expressions logical))%nat).
 { destruct (SchemaGraph.reachable_bound source root node depth Hordered Hroot Hreachable) as [Hbound _].
   rewrite <-(SchemaMetadata.represents_length source _ (SchemaRepresentation.metadata source logical HsourceRep)). exact Hbound. }
 destruct (nth_error (Protocol.expressions logical) node) as [expression|] eqn:Hlookup;
   [|apply nth_error_None in Hlookup;lia].
 destruct (SchemaEvaluationDependencies.represented_view (machine f) (logical_with logical fs classes) node expression
   (schemas _ _ _ _ _ _ _ Hdomain) Hlookup) as (kind & a & b & c & d & Hraw & Hfit & Hview).
 assert (HrawSource:nth_error (memory source arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode kind a b c d expression)).
 { rewrite <-(source_nodes _ _ _ _ _ _ _ Hdomain). exact Hraw. }
 assert (Hgrid:(key<SchemaMarking.size root)%nat) by (apply SchemaGraph.grid_bound;assumption).
 assert (Hremaining:(SchemaMarking.size root-key=S (SchemaMarking.size root-S key))%nat) by lia.
 change (fits source logical root rho (SchemaMarking.size root-key)%nat key fs classes f) in Hfits.
 rewrite Hremaining in Hfits.
 pose proof (fits_ready source logical root rho (SchemaMarking.size root-S key) key fs classes f Hfits) as Hready.
 specialize (Hready node depth expression kind a b c d eq_refl Hreachable Hlookup Hraw).
 destruct (SchemaEvaluationCell.generated_view source keyed root fs classes (Protocol.expressions logical) rho node depth kind a b c d expression
   (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining observations
   Hordered Hroot Hreachable Hview Hfit Hraw HrawSource Hcompleted Hword
   (values_allocated _ _ _ _ _ _ _ Hdomain) Hn Hd (width_number _ _ _ _ _ _ _ Hdomain)
   ltac:(unfold keyed;cbn [nums setNum];apply RenameMemoControl.updated_same)
   (meta_allocated _ _ _ _ _ _ _ Hdomain) (sip_allocated _ _ _ _ _ _ _ Hdomain)
   (arena _ _ _ _ _ _ _ Hdomain) (topology _ _ _ _ _ _ _ Hdomain)
   (class_meaning _ _ _ _ _ _ _ Hdomain) (class_words _ _ _ _ _ _ _ Hdomain)
   (falsity_zero _ _ _ _ _ _ _ Hdomain) (error_clear _ _ _ _ _ _ _ Hdomain) Hready)
   as (after & next_fs & next_classes & Hrun & Harena & Herror & HnextFs & HnextClasses & Hclassrep & Htop & Hgood & Hgrowth & Hcount & Hsemantic).
 assert (Hcellframe:frame f after).
 { eapply frame_trans;[apply frame_key|eapply marked_frame;exact Hrun]. }
 assert (Hafter:domain source logical root rho next_fs next_classes after).
 { eapply domain_prefix;[exact Hdomain|exact Hcellframe|exact HnextFs|exact HnextClasses|
     exact Harena|exact Hclassrep|exact Hgood|exact Htop|exact Herror]. }
 assert (Hexec:execLocalObserved (SchemaEvaluation.inner_body (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining)
   (f,observations)=Some (KeepGoing,(after,observations))).
 { rewrite SchemaEvaluationLoop.actual_inner.
   rewrite (SchemaEvaluationLoop.generated_cell f (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining
     (SchemaGraph.width root) node depth key _ observations
     ltac:(pose proof (meta_allocated _ _ _ _ _ _ _ Hdomain);lia) Hvalid (error_clear _ _ _ _ _ _ _ Hdomain)
     (width_number _ _ _ _ _ _ _ Hdomain) Hn Hd eq_refl ltac:(lia)
     ltac:(pose proof (marks_allocated _ _ _ _ _ _ _ Hdomain);lia)).
   rewrite bool_decide_true by exact Hmarked. exact Hrun. }
 assert (Htotalframe:frame initial after) by exact (frame_trans initial f after Hframe Hcellframe).
 assert (HtotalFs:exists extra,next_fs=initial_fs++extra) by exact (prefix_transitive _ _ _ Hfs HnextFs).
 assert (HtotalClasses:exists extra,next_classes=initial_classes++extra) by exact (prefix_transitive _ _ _ Hclasses HnextClasses).
 exists after. split;[exact Hexec|].
 destruct Hsemantic as [[Hpost Hvalidnext]|[cert [Hexpression [Hinfer Hzero]]]].
 - left. change (SchemaPairSemantic.post f after next_fs next_classes rho depth expression key) in Hpost.
   assert (Hcomplete:SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho next_fs next_classes (machine after) (S key)).
   { eapply completed_prefix;[exact Hordered|exact Hroot|exact Hdepth|exact Hlookup|
       exact HnextFs|exact HnextClasses|exact Hcompleted|exact Hpost]. }
   assert (Hsuccessor:successor source logical root rho key fs classes f next_fs next_classes after).
   { unfold successor. repeat first [assumption|exact (proj2 Hcount)|split]. }
   exists next_fs,next_classes. repeat first [assumption|split].
   + rewrite Hvalidnext. exact Hvalid.
   + exact (fits_next source logical root rho (SchemaMarking.size root-S key) key fs classes f next_fs next_classes after Hfits Hsuccessor).

 - right. exists next_fs,next_classes. repeat first [assumption|split].
   + subst expression. exact (SchemaEvaluationFailure.reachable_failure source logical root rootCert rho node depth cert
       HsourceRep Hrootlookup Hreachable Hlookup Hinfer).

Qed.
Theorem progress_cell source logical root rootCert rho initial_fs initial_classes initial (f:SchemaEvaluation.Frame) node depth remaining outer_remaining observations :
 SchemaRepresentation.represents source logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE rootCert) ->
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) remaining=Z.of_nat depth ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) outer_remaining=Z.of_nat node ->
 Z.of_nat (SchemaMarking.size root)<=maximum ->
 progress source logical root rho initial_fs initial_classes initial (SchemaGraph.key root node depth) f ->
 exists after,execLocalObserved (SchemaEvaluation.inner_body (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining)
   (f,observations)=Some (KeepGoing,(after,observations)) /\
 (progress source logical root rho initial_fs initial_classes initial (S (SchemaGraph.key root node depth)) after \/
  rejected source logical root rho rootCert initial_fs initial_classes initial after).
Proof.
 intros HsourceRep Hrootlookup Hordered Hroot Hnode Hdepth Hd Hn Hword Hprogress.
 destruct (Z.eq_dec (SchemaMarking.cell (machine f) (SchemaGraph.key root node depth)) 0) as [Hzero|Hnonzero].
 - destruct (progress_unmarked source logical root rho initial_fs initial_classes initial f node depth remaining outer_remaining observations
     Hordered Hroot Hnode Hdepth Hd Hn Hword Hprogress Hzero) as [after [Hrun Hafter]].
   exists after. split;[exact Hrun|now left].
 - exact (progress_marked source logical root rootCert rho initial_fs initial_classes initial f node depth remaining outer_remaining observations
     HsourceRep Hrootlookup Hordered Hroot Hnode Hdepth Hd Hn Hword Hprogress Hnonzero).
Qed.

Theorem generated_pass source logical root rootCert rho fs classes (f:SchemaEvaluation.Frame) observations :
 SchemaRepresentation.represents source logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE rootCert) ->
 domain source logical root rho fs classes f -> meta_value (machine f) 18<>0 ->
 Z.of_nat (SchemaMarking.size root)<=maximum -> fits source logical root rho (SchemaMarking.size root) 0 fs classes f ->
 exists after,execLocalObserved SchemaEvaluationFinish.pass (f,observations)=Some (tt,(after,observations)) /\
 (progress source logical root rho fs classes f (SchemaMarking.size root) after \/
  rejected source logical root rho rootCert fs classes f after).
Proof.
 intros HsourceRep Hrootlookup Hdomain Hvalid Hword Hfits.
 pose proof (SchemaGraph.represented_ordered source logical HsourceRep) as Hordered.
 assert (Hroot:(root<length (memory source arraydef_0__schemaNodes))%nat).
 { rewrite (SchemaMetadata.represents_length source _ (SchemaRepresentation.metadata source logical HsourceRep)). apply nth_error_Some;congruence. }
 assert (Hgrid:exists after,execLocalObserved (loop (SchemaGraph.width root) (SchemaEvaluation.outer_body (Z.of_nat (SchemaGraph.width root))))
   (f,observations)=Some (tt,(after,observations)) /\
   (progress source logical root rho fs classes f (SchemaMarking.size root) after \/
    rejected source logical root rho rootCert fs classes f after)).
 { eapply (SchemaEvaluationLoop.generated_grid (SchemaGraph.width root)
     (progress source logical root rho fs classes f) (rejected source logical root rho rootCert fs classes f)).
   - intros key before (current_fs & current_classes & Hbefore & Hbeforevalid & Hrest).
     repeat split;try assumption.
     + pose proof (meta_allocated _ _ _ _ _ _ _ Hbefore);lia.
     + exact (error_clear _ _ _ _ _ _ _ Hbefore).
     + exact (width_number _ _ _ _ _ _ _ Hbefore).
   - intros before (current_fs & current_classes & Hbefore & Hzero & Hrest).
     split;[pose proof (meta_allocated _ _ _ _ _ _ _ Hbefore);lia|now left].
   - intros node depth remaining outer_remaining before trace Hnode Hdepth Hd Hn Hprogress.
     exact (progress_cell source logical root rootCert rho fs classes f before node depth remaining outer_remaining trace
       HsourceRep Hrootlookup Hordered Hroot Hnode Hdepth Hd Hn Hword Hprogress).
   - exact (progress_initial source logical root rho fs classes f Hdomain Hvalid Hfits). }
 destruct Hgrid as [after [Hrun Hpost]]. exists after. split;[|exact Hpost].
 rewrite (SchemaEvaluationFinish.generated_pass f (SchemaGraph.width root) observations (width_number _ _ _ _ _ _ _ Hdomain)).
 exact Hrun.
Qed.
Lemma zero_frame (f:SchemaEvaluation.Frame) id : frame f (setMachine f (store_meta (machine f) 0 id)).
Proof.
 constructor;cbn [machine setMachine nums].
 - apply store_meta_other;discriminate.
 - apply store_meta_other;discriminate.
 - apply store_meta_other;discriminate.
 - intros watched Hprotected. destruct (decide (watched=arraydef_0__meta)) as [->|Hother].
   + apply store_meta_length.
   + now rewrite store_meta_other by exact Hother.
 - apply meta_store_other;discriminate.
 - reflexivity.
 - reflexivity.
Qed.
Lemma domain_zero source logical root rho fs classes (f:SchemaEvaluation.Frame) id :
 domain source logical root rho fs classes f -> domain source logical root rho fs classes (setMachine f (store_meta (machine f) 0 id)).
Proof.
 intro Hdomain. eapply domain_prefix;[exact Hdomain|apply zero_frame| | | | | | |].
 - exists [];now rewrite app_nil_r.
 - exists [];now rewrite app_nil_r.
 - apply SchemaEvaluationCell.zero_store_arena. exact (arena _ _ _ _ _ _ _ Hdomain).
 - apply SchemaEvaluationCell.zero_store_classes. exact (class_meaning _ _ _ _ _ _ _ Hdomain).
 - apply SchemaEvaluationCell.zero_store_wellformed. exact (class_words _ _ _ _ _ _ _ Hdomain).
 - apply SchemaEvaluationCell.zero_store_topology. exact (topology _ _ _ _ _ _ _ Hdomain).
 - cbn [machine setMachine]. rewrite meta_store_other by discriminate. exact (error_clear _ _ _ _ _ _ _ Hdomain).
Qed.

Theorem generated_evaluation source logical root rootCert rho fs classes (f:SchemaEvaluation.Frame) observations :
 SchemaRepresentation.represents source logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE rootCert) ->
 domain source logical root rho fs classes f -> meta_value (machine f) 18<>0 ->
 Z.of_nat (SchemaMarking.size root)<=maximum -> fits source logical root rho (SchemaMarking.size root) 0 fs classes f ->
 exists final next_fs next_classes,
 execLocalObserved SchemaMarking.evaluation (f,observations)=Some (tt,(final,observations)) /\
 domain source logical root rho next_fs next_classes final /\ frame f final /\
 (exists extra,next_fs=fs++extra) /\ (exists extra,next_classes=classes++extra) /\
 ((exists p,Schemata.infer rho 0 rootCert=Some p /\ SetTheory.derives p /\
    SchemaEvaluation.formula_value next_fs (meta_value (machine final) 0) p /\ meta_value (machine final) 18<>0) \/
   (Schemata.infer rho 0 rootCert=None /\ meta_value (machine final) 18=0)).
Proof.
 intros HsourceRep Hrootlookup Hdomain Hvalid Hword Hfits.
 pose proof (SchemaGraph.represented_ordered source logical HsourceRep) as Hordered.
 assert (Hroot:(root<length (memory source arraydef_0__schemaNodes))%nat).
 { rewrite (SchemaMetadata.represents_length source _ (SchemaRepresentation.metadata source logical HsourceRep)). apply nth_error_Some;congruence. }
 destruct (generated_pass source logical root rootCert rho fs classes f observations HsourceRep Hrootlookup Hdomain Hvalid Hword Hfits)
   as [middle [Hpass [Hsuccess|Hrejected]]].
 - destruct Hsuccess as (next_fs & next_classes & Hmiddle & Hmiddlevalid & Hcompleted & Hfits' & Hframe & Hfs & Hclasses).
   destruct (SchemaEvaluationInvariant.completed_proof source root (Protocol.expressions logical) rho next_fs next_classes (machine middle) rootCert
     Hordered Hroot Hcompleted Hrootlookup) as [p [Hinfer [Hmeaning Hderive]]].
   set (key:=SchemaGraph.key root root 0).
   set (id:=SchemaEvaluation.value (machine middle) key).
   set (final:=setMachine middle (store_meta (machine middle) 0 id)).
   assert (Hgrid:(key<SchemaMarking.size root)%nat).
   { exact (proj2 (proj2 (SchemaGraph.reachable_grid source root root 0 Hordered Hroot (SchemaGraph.root_reachable source root)))). }
   assert (Hfinish:execLocalObserved SchemaEvaluationFinish.finish (middle,observations)=Some (tt,(final,observations))).
   { apply (SchemaEvaluationFinish.generated_accepted middle root (SchemaGraph.width root) key id observations
       ltac:(pose proof (meta_allocated _ _ _ _ _ _ _ Hmiddle);lia) (error_clear _ _ _ _ _ _ _ Hmiddle) Hmiddlevalid
       (root_number _ _ _ _ _ _ _ Hmiddle) (width_number _ _ _ _ _ _ _ Hmiddle)).
     - unfold key,SchemaGraph.key;lia.
     - lia.
     - unfold id,SchemaEvaluation.value. apply List.nth_error_nth'. pose proof (values_allocated _ _ _ _ _ _ _ Hmiddle);lia. }
   assert (Hfinaldomain:domain source logical root rho next_fs next_classes final) by (apply domain_zero;exact Hmiddle).
   assert (Hfinalframe:frame f final) by exact (frame_trans f middle final Hframe (zero_frame middle id)).
   exists final,next_fs,next_classes. split.
   + rewrite SchemaEvaluationFinish.evaluation_execution.
     match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state]=>
       let expression:=constr:(@execLocalObserved I T EI V EV R code state) in
       let Hsame:=fresh in assert (Hsame:expression=Some (tt,(middle,observations))) by exact Hpass;rewrite Hsame;clear Hsame end.
     exact Hfinish.
   + repeat first [assumption|split]. left. exists p. split;[exact Hinfer|]. split;[exact Hderive|]. split.
     * unfold final. cbn [machine setMachine]. rewrite meta_store_same by (pose proof (meta_allocated _ _ _ _ _ _ _ Hmiddle);lia). exact Hmeaning.
     * unfold final. cbn [machine setMachine]. rewrite meta_store_other by discriminate. exact Hmiddlevalid.
 - destruct Hrejected as (next_fs & next_classes & Hmiddle & Hzero & Hinfer & Hframe & Hfs & Hclasses).
   exists middle,next_fs,next_classes. split.
   + rewrite SchemaEvaluationFinish.evaluation_execution.
     match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state]=>
       let expression:=constr:(@execLocalObserved I T EI V EV R code state) in
       let Hsame:=fresh in assert (Hsame:expression=Some (tt,(middle,observations))) by exact Hpass;rewrite Hsame;clear Hsame end.
     apply SchemaEvaluationFinish.generated_rejected;[pose proof (meta_allocated _ _ _ _ _ _ _ Hmiddle);lia|now right].
   + repeat first [assumption|split]. right. split;assumption.
Qed.
End SchemaEvaluationRun.
