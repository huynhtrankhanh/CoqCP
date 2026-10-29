From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal SchemaEvaluation SchemaEvaluationInvariant
 SchemaEvaluationLoop SchemaEvaluationResources SchemaEvaluationFrames SchemaRepresentation SchemaMetadata SchemaMarking
 SchemaEvaluationDependencies SchemaEvaluationFailure SchemaEvaluationFinish SchemaPairSemantic InternInvariant SchemaEvaluationCell
 SchemaGraph Representation ClassStorage ClassLookup FormulaTopology InternReserve RenameMemoControl RenameMemoLengths RenameStorage SchemaEvaluationPreservation SchemaEvaluationRun SchemaEvaluationSetCell SchemaEvaluationGeneralBudget SchemaEvaluationSetRun SchemaEvaluationBoundedCell.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationSetBoundedRun.
Import IndexExecution SipHashExecution ObservedLocal SchemaEvaluationRun.
Section Envelope.
Variable root:nat.
Variable ceiling:nat->nat.
Hypothesis ceiling_word:forall key,Z.of_nat(ceiling key)<=SchemaEvaluationSetCell.bound.
Hypothesis ceiling_step:forall key,(ceiling key<=ceiling(S key))%nat.
Hypothesis ceiling_growth:forall key,(key<SchemaMarking.size root)%nat -> (ceiling key+42<=ceiling(S key))%nat.
Definition reserve key := (Z.to_nat SchemaEvaluationSetCell.bound-ceiling(S key))%nat.
Lemma reserve_spec key : Z.of_nat(reserve key)+Z.of_nat(ceiling(S key))=SchemaEvaluationSetCell.bound.
Proof.
 assert(Hbound:(ceiling(S key)<=Z.to_nat SchemaEvaluationSetCell.bound)%nat).
 { apply Nat2Z.inj_le. rewrite Z2Nat.id by (unfold SchemaEvaluationSetCell.bound;lia). apply ceiling_word. }
 unfold reserve. rewrite Nat2Z.inj_sub by exact Hbound. rewrite Z2Nat.id by (unfold SchemaEvaluationSetCell.bound;lia). lia.
Qed.
Lemma ceiling_mono first last : (first<=last)%nat -> (ceiling first<=ceiling last)%nat.
Proof. intro H. induction H as [|last H IH];[reflexivity|eapply Nat.le_trans;[exact IH|apply ceiling_step]]. Qed.
Definition progress source logical rho initial_fs initial_classes (initial:SchemaEvaluation.Frame) key (f:SchemaEvaluation.Frame) :=
 exists fs classes,domain source logical root rho fs classes f /\ meta_value(machine f)18<>0 /\
 SchemaEvaluationInvariant.completed source root(Protocol.expressions logical)rho fs classes(machine f)key /\
 (length fs<=ceiling key)%nat /\
 frame initial f /\ (exists extra,fs=initial_fs++extra) /\ (exists extra,classes=initial_classes++extra) /\
 SchemaEvaluationSetCell.sets classes /\ SchemaEvaluationGeneralBudget.parameters source root(machine f)classes rho /\
 classes=initial_classes.
Definition rejected source logical rho rootCert initial_fs initial_classes (initial:SchemaEvaluation.Frame) (f:SchemaEvaluation.Frame) :=
 exists fs classes,domain source logical root rho fs classes f /\ meta_value(machine f)18=0 /\ Schemata.infer rho 0 rootCert=None /\
 frame initial f /\ (exists extra,fs=initial_fs++extra) /\ (exists extra,classes=initial_classes++extra) /\
 (length fs<=ceiling(SchemaMarking.size root))%nat /\ classes=initial_classes /\ SchemaEvaluationSetCell.sets classes.
Lemma progress_initial source logical rho fs classes f :
 SchemaEvaluationSetCell.sets classes -> SchemaEvaluationGeneralBudget.parameters source root (machine f) classes rho ->
 domain source logical root rho fs classes f -> meta_value (machine f) 18<>0 ->
 (length fs<=ceiling 0)%nat ->
 progress source logical rho fs classes f 0 f.
Proof.
 intros Hsets Hparameters Hdomain Hvalid Hbudget. exists fs,classes.
 repeat first [assumption|apply SchemaEvaluationInvariant.completed_zero|apply frame_refl|
   exists [];now rewrite app_nil_r|reflexivity|split].
Qed.
Theorem progress_unmarked source logical rho initial_fs initial_classes initial (f:SchemaEvaluation.Frame) node depth remaining outer_remaining observations :
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) remaining=Z.of_nat depth ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) outer_remaining=Z.of_nat node ->
 Z.of_nat (SchemaMarking.size root)<=maximum ->
 progress source logical rho initial_fs initial_classes initial (SchemaGraph.key root node depth) f ->
 SchemaMarking.cell (machine f) (SchemaGraph.key root node depth)=0 ->
 exists after,execLocalObserved (SchemaEvaluation.inner_body (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining)
   (f,observations)=Some (KeepGoing,(after,observations)) /\
 progress source logical rho initial_fs initial_classes initial (S (SchemaGraph.key root node depth)) after.
Proof.
 intros Hordered Hroot Hnode Hdepth Hd Hn Hword
   (fs & classes & Hdomain & Hvalid & Hcompleted & Hbudget & Hframe & Hfs & Hclasses & Hsets & Hparameters & HclassesSame) Hzero.
 set (key:=SchemaGraph.key root node depth).
 set (after:=setNum f vardef_0__schemaInstance_key (Z.of_nat key)).
 destruct (generated_unmarked source logical root rho fs classes f node depth remaining outer_remaining observations
   Hdomain Hordered Hroot Hnode Hdepth Hd Hn Hword Hvalid Hcompleted Hzero) as [Hrun [Hafter [Haftervalid Hcomplete]]].
 assert (Hgrid:(key<SchemaMarking.size root)%nat) by (apply SchemaGraph.grid_bound;assumption).
 assert (Hremaining:(SchemaMarking.size root-key=S (SchemaMarking.size root-S key))%nat) by lia.
 exists after. split;[exact Hrun|]. exists fs,classes.
 repeat first [assumption|exact (frame_trans initial f after Hframe (frame_key f key))|split].
 change(length fs<=ceiling key)%nat in Hbudget. pose proof(ceiling_step key). lia.
Qed.
Theorem progress_marked source logical rootCert rho initial_fs initial_classes initial (f:SchemaEvaluation.Frame) node depth remaining outer_remaining observations :
 SchemaRepresentation.represents source logical -> SchemaEvaluationSetRun.fragment source root -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE rootCert) ->
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) remaining=Z.of_nat depth ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) outer_remaining=Z.of_nat node ->
 Z.of_nat (SchemaMarking.size root)<=maximum ->
 progress source logical rho initial_fs initial_classes initial (SchemaGraph.key root node depth) f ->
 SchemaMarking.cell (machine f) (SchemaGraph.key root node depth)<>0 ->
 exists after,execLocalObserved (SchemaEvaluation.inner_body (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining)
   (f,observations)=Some (KeepGoing,(after,observations)) /\
 (progress source logical rho initial_fs initial_classes initial (S (SchemaGraph.key root node depth)) after \/
  rejected source logical rho rootCert initial_fs initial_classes initial after).
Proof.
 intros HsourceRep Hfragment Hrootlookup Hordered Hroot Hnode Hdepth Hd Hn Hword
   (fs & classes & Hdomain & Hvalid & Hcompleted & Hbudget & Hframe & Hfs & Hclasses & Hsets & Hparameters & HclassesSame) Hmarked.
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
 assert (Hsupported:SchemaEvaluationSetCell.supported kind depth a) by (eapply Hfragment;eassumption).
 assert (Hcellbudget:Z.of_nat(length fs+42+reserve key)<=SchemaEvaluationSetCell.bound).
 { change(length fs<=ceiling key)%nat in Hbudget. pose proof(ceiling_growth key Hgrid). pose proof(reserve_spec key).
   repeat rewrite Nat2Z.inj_add in *. lia. }
 destruct (SchemaEvaluationSetCell.generated_view source keyed root fs classes (Protocol.expressions logical) rho node depth kind a b c d expression
   (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining (reserve key) observations
   Hordered Hroot Hreachable Hview Hfit Hraw HrawSource Hcompleted Hword
   (values_allocated _ _ _ _ _ _ _ Hdomain) Hn Hd (width_number _ _ _ _ _ _ _ Hdomain)
   ltac:(unfold keyed;cbn [nums setNum];apply RenameMemoControl.updated_same)
   (meta_allocated _ _ _ _ _ _ _ Hdomain) (sip_allocated _ _ _ _ _ _ _ Hdomain)
   (arena _ _ _ _ _ _ _ Hdomain) (topology _ _ _ _ _ _ _ Hdomain)
   (class_meaning _ _ _ _ _ _ _ Hdomain) (class_words _ _ _ _ _ _ _ Hdomain)
   (falsity_zero _ _ _ _ _ _ _ Hdomain) (error_clear _ _ _ _ _ _ _ Hdomain) Hsupported Hsets ltac:(intro Hkind;subst kind;eapply Hparameters;[exact Hreachable|exact HrawSource]) Hcellbudget)
   as (after & next_fs & next_classes & Hrun & Harena & Herror & HnextFs & HnextClasses & Hclassrep & Htop & Hgood & Hgrowth & Hcount & Hroom & HclassEqual & Hsemantic).
 subst next_classes.
 assert(HnextCeiling:(length next_fs<=ceiling(S key))%nat).
 { pose proof(reserve_spec key). rewrite Nat2Z.inj_add in Hroom. lia. }
 assert(HterminalCeiling:(length next_fs<=ceiling(SchemaMarking.size root))%nat).
 { pose proof(ceiling_mono (S key)(SchemaMarking.size root)ltac:(lia)). lia. }
 assert (Hcellframe:frame f after).
 { eapply frame_trans;[apply frame_key|eapply marked_frame;exact Hrun]. }
 assert (Hafter:domain source logical root rho next_fs classes after).
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
 assert (HtotalClasses:exists extra,classes=initial_classes++extra) by exact (prefix_transitive _ _ _ Hclasses HnextClasses).
 assert (HnextParameters:SchemaEvaluationGeneralBudget.parameters source root (machine after) classes rho).
 { eapply SchemaEvaluationGeneralBudget.parameters_transport;
   [exact (arguments_same f after Hcellframe)|exists [];now rewrite app_nil_r|exact Hparameters]. }
 exists after. split;[exact Hexec|].
 destruct Hsemantic as [[Hpost Hvalidnext]|[cert [Hexpression [Hinfer Hzero]]]].
 - left. change (SchemaPairSemantic.post f after next_fs classes rho depth expression key) in Hpost.
   assert (Hcomplete:SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho next_fs classes (machine after) (S key)).
   { eapply completed_prefix;[exact Hordered|exact Hroot|exact Hdepth|exact Hlookup|
       exact HnextFs|exact HnextClasses|exact Hcompleted|exact Hpost]. }
   exists next_fs,classes. repeat first [assumption|split].
   rewrite Hvalidnext. exact Hvalid.

 - right. exists next_fs,classes. repeat first [assumption|split].
   + subst expression. exact (SchemaEvaluationFailure.reachable_failure source logical root rootCert rho node depth cert
       HsourceRep Hrootlookup Hreachable Hlookup Hinfer).

Qed.
Theorem progress_cell source logical rootCert rho initial_fs initial_classes initial (f:SchemaEvaluation.Frame) node depth remaining outer_remaining observations :
 SchemaRepresentation.represents source logical -> SchemaEvaluationSetRun.fragment source root -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE rootCert) ->
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) remaining=Z.of_nat depth ->
 SchemaEvaluation.depth (Z.of_nat (SchemaGraph.width root)) outer_remaining=Z.of_nat node ->
 Z.of_nat (SchemaMarking.size root)<=maximum ->
 progress source logical rho initial_fs initial_classes initial (SchemaGraph.key root node depth) f ->
 exists after,execLocalObserved (SchemaEvaluation.inner_body (Z.of_nat (SchemaGraph.width root)) remaining outer_remaining)
   (f,observations)=Some (KeepGoing,(after,observations)) /\
 (progress source logical rho initial_fs initial_classes initial (S (SchemaGraph.key root node depth)) after \/
  rejected source logical rho rootCert initial_fs initial_classes initial after).
Proof.
 intros HsourceRep Hfragment Hrootlookup Hordered Hroot Hnode Hdepth Hd Hn Hword Hprogress.
 destruct (Z.eq_dec (SchemaMarking.cell (machine f) (SchemaGraph.key root node depth)) 0) as [Hzero|Hnonzero].
 - destruct (progress_unmarked source logical rho initial_fs initial_classes initial f node depth remaining outer_remaining observations
     Hordered Hroot Hnode Hdepth Hd Hn Hword Hprogress Hzero) as [after [Hrun Hafter]].
   exists after. split;[exact Hrun|now left].
 - exact (progress_marked source logical rootCert rho initial_fs initial_classes initial f node depth remaining outer_remaining observations
     HsourceRep Hfragment Hrootlookup Hordered Hroot Hnode Hdepth Hd Hn Hword Hprogress Hnonzero).
Qed.

Theorem generated_pass source logical rootCert rho fs classes (f:SchemaEvaluation.Frame) observations :
 SchemaRepresentation.represents source logical -> SchemaEvaluationSetRun.fragment source root -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE rootCert) ->
 SchemaEvaluationSetCell.sets classes -> SchemaEvaluationGeneralBudget.parameters source root (machine f) classes rho ->
 domain source logical root rho fs classes f -> meta_value (machine f) 18<>0 ->
 Z.of_nat (SchemaMarking.size root)<=maximum -> (length fs<=ceiling 0)%nat ->
 exists after,execLocalObserved SchemaEvaluationFinish.pass (f,observations)=Some (tt,(after,observations)) /\
 (progress source logical rho fs classes f (SchemaMarking.size root) after \/
  rejected source logical rho rootCert fs classes f after).
Proof.
 intros HsourceRep Hfragment Hrootlookup Hsets Hparameters Hdomain Hvalid Hword Hbudget.
 pose proof (SchemaGraph.represented_ordered source logical HsourceRep) as Hordered.
 assert (Hroot:(root<length (memory source arraydef_0__schemaNodes))%nat).
 { rewrite (SchemaMetadata.represents_length source _ (SchemaRepresentation.metadata source logical HsourceRep)). apply nth_error_Some;congruence. }
 assert (Hgrid:exists after,execLocalObserved (loop (SchemaGraph.width root) (SchemaEvaluation.outer_body (Z.of_nat (SchemaGraph.width root))))
   (f,observations)=Some (tt,(after,observations)) /\
   (progress source logical rho fs classes f (SchemaMarking.size root) after \/
    rejected source logical rho rootCert fs classes f after)).
 { eapply (SchemaEvaluationLoop.generated_grid (SchemaGraph.width root)
     (progress source logical rho fs classes f) (rejected source logical rho rootCert fs classes f)).
   - intros key before (current_fs & current_classes & Hbefore & Hbeforevalid & Hrest).
     repeat split;try assumption.
     + pose proof (meta_allocated _ _ _ _ _ _ _ Hbefore);lia.
     + exact (error_clear _ _ _ _ _ _ _ Hbefore).
     + exact (width_number _ _ _ _ _ _ _ Hbefore).
   - intros before (current_fs & current_classes & Hbefore & Hzero & Hrest).
     split;[pose proof (meta_allocated _ _ _ _ _ _ _ Hbefore);lia|now left].
   - intros node depth remaining outer_remaining before trace Hnode Hdepth Hd Hn Hprogress.
     exact (progress_cell source logical rootCert rho fs classes f before node depth remaining outer_remaining trace
       HsourceRep Hfragment Hrootlookup Hordered Hroot Hnode Hdepth Hd Hn Hword Hprogress).
   - exact (progress_initial source logical rho fs classes f Hsets Hparameters Hdomain Hvalid Hbudget). }
 destruct Hgrid as [after [Hrun Hpost]]. exists after. split;[|exact Hpost].
 rewrite (SchemaEvaluationFinish.generated_pass f (SchemaGraph.width root) observations (width_number _ _ _ _ _ _ _ Hdomain)).
 exact Hrun.
Qed.
Theorem generated_evaluation source logical rootCert rho fs classes (f:SchemaEvaluation.Frame) observations :
 SchemaRepresentation.represents source logical -> SchemaEvaluationSetRun.fragment source root -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE rootCert) ->
 SchemaEvaluationSetCell.sets classes -> SchemaEvaluationGeneralBudget.parameters source root (machine f) classes rho ->
 domain source logical root rho fs classes f -> meta_value (machine f) 18<>0 ->
 Z.of_nat (SchemaMarking.size root)<=maximum -> (length fs<=ceiling 0)%nat ->
 exists final next_fs next_classes,
 execLocalObserved SchemaMarking.evaluation (f,observations)=Some (tt,(final,observations)) /\
 domain source logical root rho next_fs next_classes final /\ frame f final /\
 (exists extra,next_fs=fs++extra) /\ (exists extra,next_classes=classes++extra) /\
 ((exists p,Schemata.infer rho 0 rootCert=Some p /\ SetTheory.derives p /\
    SchemaEvaluation.formula_value next_fs (meta_value (machine final) 0) p /\ meta_value (machine final) 18<>0) \/
   (Schemata.infer rho 0 rootCert=None /\ meta_value (machine final) 18=0)) /\ (length next_fs<=ceiling(SchemaMarking.size root))%nat /\ next_classes=classes /\ SchemaEvaluationSetCell.sets next_classes.
Proof.
 intros HsourceRep Hfragment Hrootlookup Hsets Hparameters Hdomain Hvalid Hword Hbudget.
 pose proof (SchemaGraph.represented_ordered source logical HsourceRep) as Hordered.
 assert (Hroot:(root<length (memory source arraydef_0__schemaNodes))%nat).
 { rewrite (SchemaMetadata.represents_length source _ (SchemaRepresentation.metadata source logical HsourceRep)). apply nth_error_Some;congruence. }
 destruct (generated_pass source logical rootCert rho fs classes f observations HsourceRep Hfragment Hrootlookup Hsets Hparameters Hdomain Hvalid Hword Hbudget)
   as [middle [Hpass [Hsuccess|Hrejected]]].
 - destruct Hsuccess as (next_fs & next_classes & Hmiddle & Hmiddlevalid & Hcompleted & Hroom & Hframe & Hfs & Hclasses & HsetsNext & HparametersNext & HclassesSame).
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
   + split;[exact Hfinaldomain|]. split;[exact Hfinalframe|]. split;[exact Hfs|]. split;[exact Hclasses|]. split.
     * left. exists p. split;[exact Hinfer|]. split;[exact Hderive|]. split.
       -- unfold final. cbn [machine setMachine]. rewrite meta_store_same by (pose proof (meta_allocated _ _ _ _ _ _ _ Hmiddle);lia). exact Hmeaning.
       -- unfold final. cbn [machine setMachine]. rewrite meta_store_other by discriminate. exact Hmiddlevalid.
     * split;[exact Hroom|]. split;[exact HclassesSame|exact HsetsNext].
 - destruct Hrejected as (next_fs & next_classes & Hmiddle & Hzero & Hinfer & Hframe & Hfs & Hclasses & HterminalCeiling & HclassesSame & HsetsNext).
   exists middle,next_fs,next_classes. split.
   + rewrite SchemaEvaluationFinish.evaluation_execution.
     match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state]=>
       let expression:=constr:(@execLocalObserved I T EI V EV R code state) in
       let Hsame:=fresh in assert (Hsame:expression=Some (tt,(middle,observations))) by exact Hpass;rewrite Hsame;clear Hsame end.
     apply SchemaEvaluationFinish.generated_rejected;[pose proof (meta_allocated _ _ _ _ _ _ _ Hmiddle);lia|now right].
   + split;[exact Hmiddle|]. split;[exact Hframe|]. split;[exact Hfs|]. split;[exact Hclasses|].
     split;[right;split;assumption|]. split;[exact HterminalCeiling|]. split;assumption.
Qed.
End Envelope.
End SchemaEvaluationSetBoundedRun.
