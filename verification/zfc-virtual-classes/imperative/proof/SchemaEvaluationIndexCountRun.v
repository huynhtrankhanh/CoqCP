From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal SchemaEvaluation SchemaEvaluationInvariant
 SchemaEvaluationLoop SchemaEvaluationResources SchemaEvaluationFrames SchemaRepresentation SchemaMetadata SchemaMarking
 SchemaEvaluationDependencies SchemaEvaluationFailure SchemaEvaluationFinish SchemaPairSemantic InternInvariant SchemaEvaluationCell
 SchemaGraph Representation ClassStorage ClassLookup FormulaTopology InternReserve RenameMemoControl RenameMemoLengths RenameStorage SchemaEvaluationPreservation SchemaEvaluationRun SchemaEvaluationBoundedCell SchemaEvaluationIndexRun SchemaEvaluationIndexCell SchemaEvaluationIndexBounds SchemaEvaluationIndexShiftClass.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationIndexCountRun.
Import IndexExecution SipHashExecution ObservedLocal SchemaEvaluationRun.
Section Ceiling.
Variable ceiling:nat->nat.
Hypothesis ceiling_word:forall key,Z.of_nat (ceiling key)<=SchemaEvaluationBoundedCell.bound.
Hypothesis ceiling_step:forall key,(ceiling key<=ceiling (S key))%nat.
Variable index_ceiling:nat->nat.
Hypothesis index_ceiling_word:forall key,Z.of_nat (index_ceiling key)<=maximum.
Hypothesis index_ceiling_step:forall key,(index_ceiling key<=index_ceiling (S key))%nat.
Lemma index_ceiling_mono first last : (first<=last)%nat -> (index_ceiling first<=index_ceiling last)%nat.
Proof. intro Hle. induction Hle as [|last Hle IH];[reflexivity|eapply Nat.le_trans;[exact IH|apply index_ceiling_step]]. Qed.
Lemma bounded_mono native fs classes lower upper : (lower<=upper)%nat ->
 SchemaEvaluationIndexCell.bounded native fs classes lower -> SchemaEvaluationIndexCell.bounded native fs classes upper.
Proof. intros Hle [Hraw Hclasses]. split.
 - exact (SchemaEvaluationIndexBounds.raw_arena_mono native (length fs) lower upper Hle Hraw).
 - exact (SchemaEvaluationIndexShiftClass.classes_mono lower upper classes Hle Hclasses).
Qed.
Lemma bounded_zero native fs classes bound id : SchemaEvaluationIndexCell.bounded native fs classes bound ->
 SchemaEvaluationIndexCell.bounded (store_meta native 0 id) fs classes bound.
Proof. intros [Hraw Hclasses]. split;[|exact Hclasses]. eapply SchemaEvaluationIndexBounds.raw_array_frame;[apply store_meta_other;discriminate|exact Hraw]. Qed.
Lemma ceiling_mono first last : (first<=last)%nat -> (ceiling first<=ceiling last)%nat.
Proof. intro Hle. induction Hle as [|last Hle IH];[reflexivity|eapply Nat.le_trans;[exact IH|apply ceiling_step]]. Qed.
Definition reserve key := (Z.to_nat SchemaEvaluationBoundedCell.bound-ceiling (S key))%nat.
Lemma reserve_spec key : Z.of_nat (reserve key)+Z.of_nat (ceiling (S key))=SchemaEvaluationBoundedCell.bound.
Proof.
 assert (Hbound:(ceiling (S key)<=Z.to_nat SchemaEvaluationBoundedCell.bound)%nat).
 { apply Nat2Z.inj_le. rewrite Z2Nat.id by (unfold SchemaEvaluationBoundedCell.bound;lia). apply ceiling_word. }
 unfold reserve. rewrite Nat2Z.inj_sub by exact Hbound.
 rewrite Z2Nat.id by (unfold SchemaEvaluationBoundedCell.bound;lia). lia.
Qed.
(** Successors obey a chosen numeric arena envelope, rather than allowing
    arbitrary jumps to any word-sized formula cardinality. *)
Definition successor source logical root rho key fs classes before next_fs next_classes after :=
 SchemaEvaluationRun.successor source logical root rho key fs classes before next_fs next_classes after /\
 (length next_fs<=ceiling (S key))%nat /\
 SchemaEvaluationIndexCell.bounded (machine after) next_fs next_classes (index_ceiling (S key)).
Definition ready_at source logical root rho key fs classes (f:SchemaEvaluation.Frame) :=
 (length fs<=ceiling key)%nat /\
 SchemaEvaluationIndexCell.bounded (machine f) fs classes (index_ceiling key) /\
 forall node depth expression k a b c d,
 key=SchemaGraph.key root node depth -> SchemaGraph.reachable source root node depth ->
 nth_error (Protocol.expressions logical) node=Some expression ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode k a b c d expression) ->
 SchemaEvaluationBoundedCell.ready (machine f) fs classes rho depth k a b c d (reserve key) /\
 (SchemaEvaluationIndexCell.successor k (index_ceiling key) depth b c d<=index_ceiling (S key))%nat.
Fixpoint fits source logical root rho count key fs classes (f:SchemaEvaluation.Frame) : Prop :=
 match count with
 | O=>True
 | S count=>ready_at source logical root rho key fs classes f /\
     forall next_fs next_classes after,
       successor source logical root rho key fs classes f next_fs next_classes after ->
       fits source logical root rho count (S key) next_fs next_classes after
 end.
Lemma fits_ready source logical root rho count key fs classes f :
 fits source logical root rho (S count) key fs classes f -> ready_at source logical root rho key fs classes f.
Proof. exact (@proj1 _ _). Qed.
Lemma fits_next source logical root rho count key fs classes f next_fs next_classes after :
 fits source logical root rho (S count) key fs classes f ->
 successor source logical root rho key fs classes f next_fs next_classes after ->
 fits source logical root rho count (S key) next_fs next_classes after.
Proof. intros [_ Hnext]. apply Hnext. Qed.
Lemma reserve_same key : reserve key=SchemaEvaluationIndexRun.reserve ceiling key.
Proof. unfold reserve,SchemaEvaluationIndexRun.reserve. reflexivity. Qed.
Lemma ready_from_index source logical root rho key fs classes f :
 SchemaEvaluationIndexRun.ready_at ceiling index_ceiling source logical root rho key fs classes f ->
 ready_at source logical root rho key fs classes f.
Proof.
 intros [HF [HB Hready]]. split;[exact HF|]. split;[exact HB|].
 intros node depth expression kind a b c d Hkey Hreachable Hlookup Hraw.
 rewrite reserve_same. exact (Hready node depth expression kind a b c d Hkey Hreachable Hlookup Hraw).
Qed.
Lemma fits_from_index source logical root rho count key fs classes f :
 SchemaEvaluationIndexRun.fits ceiling index_ceiling source logical root rho count key fs classes f ->
 fits source logical root rho count key fs classes f.
Proof.
 induction count as [|count IH] in key,fs,classes,f|-*;[intro H;exact I|].
 intros [Hready Htail]. split;[exact (ready_from_index source logical root rho key fs classes f Hready)|].
 intros next_fs next_classes after Hsuccessor.
 apply IH. apply Htail. exact Hsuccessor.
Qed.
Definition progress source logical root rho initial_fs initial_classes (initial:SchemaEvaluation.Frame) key (f:SchemaEvaluation.Frame) :=
 exists fs classes,domain source logical root rho fs classes f /\ meta_value (machine f) 18<>0 /\
 SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho fs classes (machine f) key /\
 fits source logical root rho (SchemaMarking.size root-key)%nat key fs classes f /\
 (length fs<=ceiling key)%nat /\ SchemaEvaluationIndexCell.bounded (machine f) fs classes (index_ceiling key) /\
 (length classes<=length initial_classes+key)%nat /\ frame initial f /\ (exists extra,fs=initial_fs++extra) /\ (exists extra,classes=initial_classes++extra).
Definition rejected source logical root rho rootCert initial_fs initial_classes (initial:SchemaEvaluation.Frame) (f:SchemaEvaluation.Frame) :=
 exists fs classes,domain source logical root rho fs classes f /\ meta_value (machine f) 18=0 /\
 Schemata.infer rho 0 rootCert=None /\ (length fs<=ceiling (SchemaMarking.size root))%nat /\ SchemaEvaluationIndexCell.bounded (machine f) fs classes (index_ceiling (SchemaMarking.size root)) /\
 (length classes<=length initial_classes+SchemaMarking.size root)%nat /\ frame initial f /\
 (exists extra,fs=initial_fs++extra) /\ (exists extra,classes=initial_classes++extra).
Lemma progress_initial source logical root rho fs classes f :
 domain source logical root rho fs classes f -> meta_value (machine f) 18<>0 ->
 fits source logical root rho (SchemaMarking.size root) 0 fs classes f ->
 progress source logical root rho fs classes f 0 f.
Proof.
 intros Hdomain Hvalid Hfits.
 assert (Hpositive:(0<SchemaMarking.size root)%nat) by (unfold SchemaMarking.size,SchemaGraph.width;nia).
 assert (Hceiling:(length fs<=ceiling 0)%nat).
 { destruct (SchemaMarking.size root) as [|count] eqn:Hsize;[lia|]. exact (proj1 (fits_ready _ _ _ _ _ _ _ _ _ Hfits)). }
 assert (Hindices:SchemaEvaluationIndexCell.bounded (machine f) fs classes (index_ceiling 0)).
 { destruct (SchemaMarking.size root) as [|count] eqn:Hsize;[lia|]. exact (proj1 (proj2 (fits_ready _ _ _ _ _ _ _ _ _ Hfits))). }
 exists fs,classes.
 repeat first [assumption|apply SchemaEvaluationInvariant.completed_zero|apply frame_refl|
   exists [];now rewrite app_nil_r|split|lia].
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
   (fs & classes & Hdomain & Hvalid & Hcompleted & Hfits & HcurrentCeiling & HcurrentIndices & HclassCount & Hframe & Hfs & Hclasses) Hzero.
 set (key:=SchemaGraph.key root node depth).
 set (after:=setNum f vardef_0__schemaInstance_key (Z.of_nat key)).
 destruct (generated_unmarked source logical root rho fs classes f node depth remaining outer_remaining observations
   Hdomain Hordered Hroot Hnode Hdepth Hd Hn Hword Hvalid Hcompleted Hzero) as [Hrun [Hafter [Haftervalid Hcomplete]]].
 assert (Hgrid:(key<SchemaMarking.size root)%nat) by (apply SchemaGraph.grid_bound;assumption).
 assert (Hremaining:(SchemaMarking.size root-key=S (SchemaMarking.size root-S key))%nat) by lia.
 change (fits source logical root rho (SchemaMarking.size root-key)%nat key fs classes f) in Hfits.
 rewrite Hremaining in Hfits.
 assert (Hceiling:(length fs<=ceiling (S key))%nat).
 { destruct (fits_ready source logical root rho (SchemaMarking.size root-S key) key fs classes f Hfits) as [Hcurrent _].
   eapply Nat.le_trans;[exact Hcurrent|apply ceiling_step]. }
 assert (Hsuccessor:successor source logical root rho key fs classes f fs classes after).
 { split;[unfold SchemaEvaluationRun.successor|split;[exact Hceiling|exact (bounded_mono (machine f) fs classes (index_ceiling key) (index_ceiling (S key)) (index_ceiling_step key) HcurrentIndices)]].
   repeat first [assumption|apply frame_key|exact (arena_count (machine f) fs (arena _ _ _ _ _ _ _ Hdomain))|
     exists [];now rewrite app_nil_r|split|lia]. }
 assert (HafterIndices:SchemaEvaluationIndexCell.bounded (machine after) fs classes (index_ceiling (S key)))
   by exact (bounded_mono (machine f) fs classes (index_ceiling key) (index_ceiling (S key)) (index_ceiling_step key) HcurrentIndices).
 assert (HafterClassCount:(length classes<=length initial_classes+S key)%nat) by lia.
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
   (fs & classes & Hdomain & Hvalid & Hcompleted & Hfits & HcurrentCeiling & HcurrentIndices & HclassCount & Hframe & Hfs & Hclasses) Hmarked.
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
 destruct (fits_ready source logical root rho (SchemaMarking.size root-S key) key fs classes f Hfits) as [Hcurrent [HindexBound Hready]].
 specialize (Hready node depth expression kind a b c d eq_refl Hreachable Hlookup Hraw). destruct Hready as [Hready HindexNext].
 destruct (SchemaEvaluationIndexCell.generated_view source keyed root fs classes (Protocol.expressions logical) rho node depth kind a b c d expression
   (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining (reserve key) (index_ceiling key) observations
   Hordered Hroot Hreachable Hview Hfit Hraw HrawSource Hcompleted Hword
   (values_allocated _ _ _ _ _ _ _ Hdomain) Hn Hd (width_number _ _ _ _ _ _ _ Hdomain)
   ltac:(unfold keyed;cbn [nums setNum];apply RenameMemoControl.updated_same)
   (meta_allocated _ _ _ _ _ _ _ Hdomain) (sip_allocated _ _ _ _ _ _ _ Hdomain)
   (arena _ _ _ _ _ _ _ Hdomain) (topology _ _ _ _ _ _ _ Hdomain)
   (class_meaning _ _ _ _ _ _ _ Hdomain) (class_words _ _ _ _ _ _ _ Hdomain)
   (falsity_zero _ _ _ _ _ _ _ Hdomain) (error_clear _ _ _ _ _ _ _ Hdomain) Hready HindexBound
   ltac:(pose proof (index_ceiling_word (S key));lia))
   as (after & next_fs & next_classes & HnextIndices & Hrun & Harena & Herror & HnextFs & HnextClasses & Hclassrep & Htop & Hgood & Hgrowth & Hcount & Hroom & Hsemantic).
 assert (Hceiling:(length next_fs<=ceiling (S key))%nat).
 { pose proof (reserve_spec key). unfold SchemaEvaluationBoundedCell.bound in *. rewrite Nat2Z.inj_add in Hroom. lia. }
 assert (HafterIndices:SchemaEvaluationIndexCell.bounded (machine after) next_fs next_classes (index_ceiling (S key))).
 { exact (bounded_mono (machine after) next_fs next_classes _ _ HindexNext HnextIndices). }
 assert (HafterClassCount:(length next_classes<=length initial_classes+S key)%nat) by lia.
 assert (HtotalClassCount:(length next_classes<=length initial_classes+SchemaMarking.size root)%nat) by lia.
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
 assert (HtotalCeiling:(length next_fs<=ceiling (SchemaMarking.size root))%nat).
 { eapply Nat.le_trans;[exact Hceiling|apply ceiling_mono;lia]. }
 assert (HtotalIndices:SchemaEvaluationIndexCell.bounded (machine after) next_fs next_classes (index_ceiling (SchemaMarking.size root))).
 { exact (bounded_mono (machine after) next_fs next_classes _ _ (index_ceiling_mono (S key) (SchemaMarking.size root) ltac:(lia)) HafterIndices). }
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
   { split;[unfold SchemaEvaluationRun.successor;repeat first [assumption|exact (proj2 Hcount)|split]|exact (conj Hceiling HafterIndices)]. }
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
Theorem generated_evaluation source logical root rootCert rho fs classes (f:SchemaEvaluation.Frame) observations :
 SchemaRepresentation.represents source logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE rootCert) ->
 domain source logical root rho fs classes f -> meta_value (machine f) 18<>0 ->
 Z.of_nat (SchemaMarking.size root)<=maximum -> fits source logical root rho (SchemaMarking.size root) 0 fs classes f ->
 exists final next_fs next_classes,
 execLocalObserved SchemaMarking.evaluation (f,observations)=Some (tt,(final,observations)) /\
 domain source logical root rho next_fs next_classes final /\ frame f final /\
 (exists extra,next_fs=fs++extra) /\ (exists extra,next_classes=classes++extra) /\
 (length next_classes<=length classes+SchemaMarking.size root)%nat /\
 (length next_fs<=ceiling (SchemaMarking.size root))%nat /\
 SchemaEvaluationIndexCell.bounded (machine final) next_fs next_classes (index_ceiling (SchemaMarking.size root)) /\
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
 - destruct Hsuccess as (next_fs & next_classes & Hmiddle & Hmiddlevalid & Hcompleted & Hfits' & Hceiling & Hindices & HclassCount & Hframe & Hfs & Hclasses).
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
   assert (HfinalIndices:SchemaEvaluationIndexCell.bounded (machine final) next_fs next_classes (index_ceiling (SchemaMarking.size root)))
     by exact (bounded_zero (machine middle) next_fs next_classes _ id Hindices).
   exists final,next_fs,next_classes. split.
   + rewrite SchemaEvaluationFinish.evaluation_execution.
     match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state]=>
       let expression:=constr:(@execLocalObserved I T EI V EV R code state) in
       let Hsame:=fresh in assert (Hsame:expression=Some (tt,(middle,observations))) by exact Hpass;rewrite Hsame;clear Hsame end.
     exact Hfinish.
   + repeat first [assumption|split]. left. exists p. split;[exact Hinfer|]. split;[exact Hderive|]. split.
     * unfold final. cbn [machine setMachine]. rewrite meta_store_same by (pose proof (meta_allocated _ _ _ _ _ _ _ Hmiddle);lia). exact Hmeaning.
     * unfold final. cbn [machine setMachine]. rewrite meta_store_other by discriminate. exact Hmiddlevalid.
 - destruct Hrejected as (next_fs & next_classes & Hmiddle & Hzero & Hinfer & Hceiling & Hindices & HclassCount & Hframe & Hfs & Hclasses).
   exists middle,next_fs,next_classes. split.
   + rewrite SchemaEvaluationFinish.evaluation_execution.
     match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state]=>
       let expression:=constr:(@execLocalObserved I T EI V EV R code state) in
       let Hsame:=fresh in assert (Hsame:expression=Some (tt,(middle,observations))) by exact Hpass;rewrite Hsame;clear Hsame end.
     apply SchemaEvaluationFinish.generated_rejected;[pose proof (meta_allocated _ _ _ _ _ _ _ Hmiddle);lia|now right].
   + repeat first [assumption|split]. right. split;assumption.
Qed.
End Ceiling.
End SchemaEvaluationIndexCountRun.
