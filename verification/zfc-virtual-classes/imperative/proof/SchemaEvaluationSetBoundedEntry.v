From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal SchemaRepresentation SchemaMarking SchemaEvaluation
 SchemaEvaluationRun SchemaEvaluationInitial SchemaEvaluationSetCell SchemaEvaluationSetRun SchemaMetadata SchemaInstanceStorage SchemaInstanceCompletion Representation ClassStorage ClassLookup
 FormulaTopology HistoryRefinement NameRepresentation SemanticFrames InternalIO SchemaEvaluationGeneralBudget SchemaEvaluationSetBoundedRun.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationSetBoundedEntry.
Import IndexExecution SipHashExecution ObservedLocal.
Definition ceiling initial root key := (initial+42*Nat.min key(SchemaMarking.size root))%nat.
Lemma ceiling_word initial root : Z.of_nat(initial+42*SchemaMarking.size root)<=SchemaEvaluationSetCell.bound ->
 forall key,Z.of_nat(ceiling initial root key)<=SchemaEvaluationSetCell.bound.
Proof. intros Hword key. unfold ceiling. pose proof(Nat.le_min_r key(SchemaMarking.size root)). lia. Qed.
Lemma ceiling_step initial root key : (ceiling initial root key<=ceiling initial root(S key))%nat.
Proof. unfold ceiling. pose proof(Nat.min_le_compat_r key(S key)(SchemaMarking.size root)ltac:(lia)). lia. Qed.
Lemma ceiling_growth initial root key : (key<SchemaMarking.size root)%nat -> (ceiling initial root key+42<=ceiling initial root(S key))%nat.
Proof. intro Hkey. unfold ceiling. rewrite !Nat.min_l by lia. lia. Qed.
Definition initial s bs ns : SchemaEvaluation.Frame := {|machine:=s;bools:=bs;nums:=ns|}.
Theorem generated s bs ns logical root cert rho observations :
 SchemaRepresentation.represents s logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE cert) ->
 SchemaEvaluationSetRun.fragment s root ->
 SchemaEvaluationSetCell.sets (Protocol.classes logical) ->
 SchemaEvaluationGeneralBudget.parameters s root s (Protocol.classes logical) rho ->
 Z.of_nat (length (Protocol.formulas logical)+42*SchemaMarking.size root)<=SchemaEvaluationSetCell.bound -> ns vardef_0__schemaInstance_root=Z.of_nat root ->
 NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
 ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
 (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
 meta_value s 8=0 -> meta_value s 18<>0 ->
 exists final fs classes,
 execObserved (funcdef_0__schemaInstance bs ns) (s,observations)=Some (tt,(final,observations)) /\
 NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs classes /\
 HistoryRefinement.represents final (SchemaInstanceCompletion.prepared logical fs classes) /\
 NameRepresentation.represents final (Protocol.bindings logical) /\
 SchemaRepresentation.represents final (SchemaInstanceCompletion.prepared logical fs classes) /\
 ClassLookup.wellformed final /\ FormulaTopology.ordered final (length fs) /\ meta_value final 8=0 /\
 InternalIO.preserves s final /\ (exists extra,fs=Protocol.formulas logical++extra) /\ (exists extra,classes=Protocol.classes logical++extra) /\
 (Guarantees.safe logical -> Guarantees.safe (SchemaInstanceCompletion.prepared logical fs classes)) /\
 ((exists p,Schemata.infer rho 0 cert=Some p /\ SetTheory.derives p /\
    SchemaEvaluation.formula_value fs (meta_value final 0) p /\ meta_value final 18<>0) \/
  (Schemata.infer rho 0 cert=None /\ meta_value final 18=0)) /\
 (length fs<=length(Protocol.formulas logical)+42*SchemaMarking.size root)%nat /\
 classes=Protocol.classes logical /\ SchemaEvaluationSetCell.sets classes.
Proof.
 intros Hschema Hlookup Hfragment Hsets Hparameters Hbudget Hroot Harena Hclasses Hgood Htop Hfalse Hhistory Hnames Hmeta Hsip Herror Hvalid.
 assert (Hroom:Z.of_nat (SchemaMarking.size root)<=maximum).
 { unfold SchemaEvaluationSetCell.bound,maximum in *;lia. }
 assert (Hrootbound:(root<length (memory s arraydef_0__schemaNodes))%nat).
 { rewrite (SchemaMetadata.represents_length _ _ (SchemaRepresentation.metadata _ _ Hschema)). apply nth_error_Some;congruence. }
 destruct (SchemaEvaluationInitial.generated_marking (initial s bs ns) logical root rho observations Hschema Hrootbound Hroom Hroot
   Harena Hclasses Hgood Htop Hfalse Hmeta Hsip Herror)
   as (marked & Hinitial & Hbodyeq & Hmarked & HmarkedDomain & HmarkedValid).
 assert (HmarkedParameters:SchemaEvaluationGeneralBudget.parameters s root (machine marked) (Protocol.classes logical) rho).
 { eapply SchemaEvaluationGeneralBudget.parameters_transport;
   [exact (SchemaEvaluationInitial.untouched _ _ _ Hmarked arraydef_0__schemaArguments ltac:(discriminate) ltac:(discriminate))|
    exists [];now rewrite app_nil_r|exact Hparameters]. }
 destruct(SchemaEvaluationSetBoundedRun.generated_evaluation root (ceiling(length(Protocol.formulas logical))root)
   (ceiling_word (length(Protocol.formulas logical))root Hbudget)
   (ceiling_step (length(Protocol.formulas logical))root) (ceiling_growth (length(Protocol.formulas logical))root)
   s logical cert rho (Protocol.formulas logical) (Protocol.classes logical) marked observations
   Hschema Hfragment Hlookup Hsets HmarkedParameters HmarkedDomain ltac:(now rewrite HmarkedValid) Hroom
   ltac:(unfold ceiling;cbn [Nat.min];lia))
   as(after & fs & classes & Hevaluation & Hdomain & Hframe & Hfs & Hcs & Hresult & Hceiling & HclassesSame & HsetsNext).
 assert(HformulaGrowth:(length fs<=length(Protocol.formulas logical)+42*SchemaMarking.size root)%nat).
 { unfold ceiling in Hceiling. now rewrite Nat.min_id in Hceiling. }

 assert (Hbody:execLocalObserved funcdef_0__schemaInstance_body (initial s bs ns,observations)=Some (tt,(after,observations)))
   by (rewrite Hbodyeq;exact Hevaluation).
 assert (Hrun:execObserved (funcdef_0__schemaInstance bs ns) (s,observations)=Some (tt,(machine after,observations))).
 { change (execObserved (eliminateLocalVariables bs ns funcdef_0__schemaInstance_body) (s,observations)=Some (tt,(machine after,observations))).
   rewrite (ObservedLocal.eliminate_correct funcdef_0__schemaInstance_body bs ns s observations).
   change (optionBind (execLocalObserved funcdef_0__schemaInstance_body (initial s bs ns,observations))
    (fun response=>Some (fst response,(machine (fst (snd response)),snd (snd response))))=Some (tt,(machine after,observations))).
   now rewrite Hbody. }
 destruct (SchemaInstanceStorage.registries s bs ns (machine after) observations observations logical Hrun Hhistory Hnames)
   as [HnextHistory [HnextNames Hio]].
 exists (machine after),fs,classes. split;[exact Hrun|].
 split;[exact (SchemaEvaluationRun.arena _ _ _ _ _ _ _ Hdomain)|].
 split;[exact (SchemaEvaluationRun.class_meaning _ _ _ _ _ _ _ Hdomain)|].
 split;[exact HnextHistory|]. split;[exact HnextNames|].
 split;[exact (SchemaEvaluationRun.schemas _ _ _ _ _ _ _ Hdomain)|].
 split;[exact (SchemaEvaluationRun.class_words _ _ _ _ _ _ _ Hdomain)|].
 split;[exact (SchemaEvaluationRun.topology _ _ _ _ _ _ _ Hdomain)|].
 split;[exact (SchemaEvaluationRun.error_clear _ _ _ _ _ _ _ Hdomain)|].
 split;[exact Hio|]. split;[exact Hfs|]. split;[exact Hcs|]. split.
 2:{ split;[exact Hresult|]. split;[exact HformulaGrowth|]. split;assumption. }
 apply Guarantees.retained. unfold Protocol.retained_storage,SchemaInstanceCompletion.prepared.
 cbn [Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
 split;[exact Hfs|]. split;[exact (SemanticFrames.arena_NoDup _ _ (SchemaEvaluationRun.arena _ _ _ _ _ _ _ Hdomain))|].
 split;[exact Hcs|]. repeat split;reflexivity.
Qed.
End SchemaEvaluationSetBoundedEntry.
