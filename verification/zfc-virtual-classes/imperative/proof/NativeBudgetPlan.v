From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash NativeState NativeRequestBounds NativeUniformCommand NativeUniformResources
 NativeBasicDispatcher NativeGeneralDispatcher NativeNameCompact NativeSchemaFieldBounds NativeSchemaUniformBoundary
 SchemaUniformBudget SchemaSemanticBounds SchemaInstanceCheckedResources SchemaEvaluationIndexCell SchemaEvaluationBoundedCell
 FormulaTopology ClassLookup LogicalRegistryBounds.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeBudgetPlan.
Import IndexExecution SipHashExecution.
Record caps := Caps { formulas:nat; indices:nat; classes:nat; history:nat; bindings:nat; expressions:nat; names:nat }.
Definition initial argument_cap := Caps 1 (Nat.max 3 argument_cap) 0 0 0 0 0.
Definition step argument_cap request before :=
 Caps (NativeUniformCommand.formula_end request (formulas before) (expressions before))
   (NativeUniformCommand.index_end request (indices before) argument_cap (expressions before))
   (NativeUniformCommand.class_end request (classes before) (expressions before))
   (S (history before)) (S (bindings before))
   (NativeUniformCommand.expression_end request (expressions before)) (names before+1024).
Definition common argument_cap before request :=
 Z.leb (Z.of_nat (formulas before)) SchemaEvaluationBoundedCell.bound &&
 Z.leb (Z.of_nat (formulas (step argument_cap request before))) SchemaEvaluationBoundedCell.bound &&
 Z.leb (Z.of_nat (indices (step argument_cap request before))) maximum &&
 Z.leb (Z.of_nat (S (classes before))) maximum &&
 Z.leb (Z.of_nat (S (history before))) maximum &&
 Z.leb (Z.of_nat (S (bindings before))) maximum &&
 Z.leb (Z.of_nat (S (expressions before))) maximum &&
 Z.leb (Z.of_nat (names before+1024)) maximum.
Definition head_check argument_cap before request :=
 Nat.leb (Protocol.opcode request) 26 &&
 Nat.leb (NativeRequestBounds.numbers_max (Protocol.arguments request)) argument_cap &&
 common argument_cap before request &&
 NativeUniformResources.check request (formulas before) (indices before) (classes before) (expressions before) argument_cap.
Fixpoint check argument_cap before requests := match requests with
 | []=>true | request::tail=>if Nat.eqb (Protocol.opcode request) 0 then true else
     head_check argument_cap before request && check argument_cap (step argument_cap request before) tail end.
Record bounds logical before : Prop := Bounds {
 formula_bound : (length (Protocol.formulas logical)<=formulas before)%nat;
 index_bound : (SchemaInstanceCheckedResources.initial_bound logical<=indices before)%nat;
 class_bound : (length (Protocol.classes logical)<=classes before)%nat;
 history_bound : (length (Protocol.history logical)<=history before)%nat;
 binding_bound : (length (Protocol.bindings logical)<=bindings before)%nat;
 expression_bound : (length (Protocol.expressions logical)<=expressions before)%nat;
 name_bound : (NativeNameCompact.bytes logical<=names before)%nat
}.
Definition capacity argument_cap logical requests := exists before,bounds logical before /\ check argument_cap before requests=true.
Definition domain requests := let argument_cap:=NativeRequestBounds.maximum requests in check argument_cap (initial argument_cap) requests=true.
Record conditions argument_cap before request : Prop := Conditions {
 opcode_bound : (Protocol.opcode request<=26)%nat;
 arguments_bound : Forall (fun value=>(value<=argument_cap)%nat) (Protocol.arguments request);
 formula_room : Z.of_nat (formulas before)<=SchemaEvaluationBoundedCell.bound;
 result_formula_room : Z.of_nat (formulas (step argument_cap request before))<=SchemaEvaluationBoundedCell.bound;
 result_index_room : Z.of_nat (indices (step argument_cap request before))<=maximum;
 class_room : Z.of_nat (S (classes before))<=maximum;
 history_room : Z.of_nat (S (history before))<=maximum;
 binding_room : Z.of_nat (S (bindings before))<=maximum;
 expression_room : Z.of_nat (S (expressions before))<=maximum;
 name_room : Z.of_nat (names before+1024)<=maximum;
 specific_check : NativeUniformResources.check request (formulas before) (indices before) (classes before) (expressions before) argument_cap=true
}.
Lemma head_conditions argument_cap before request : head_check argument_cap before request=true -> conditions argument_cap before request.
Proof.
 unfold head_check,common. rewrite !Bool.andb_true_iff. intro H.
 repeat match goal with H:_ /\ _ |- _=>destruct H end.
 repeat match goal with H:Z.leb _ _=true |- _=>apply Z.leb_le in H
 | H:Nat.leb _ _=true |- _=>apply Nat.leb_le in H end.
 constructor;try assumption. apply NativeRequestBounds.numbers_bounded;assumption.
Qed.
Lemma check_tail argument_cap before request requests : Protocol.opcode request<>0%nat ->
 check argument_cap before (request::requests)=true ->
 conditions argument_cap before request /\ check argument_cap (step argument_cap request before) requests=true.
Proof.
 intros Hpositive Hcheck. cbn [check] in Hcheck. rewrite (proj2 (Nat.eqb_neq _ _) Hpositive) in Hcheck.
 apply Bool.andb_true_iff in Hcheck as [Hhead Htail]. split;[now apply head_conditions|exact Htail].
Qed.
Lemma initial_bounds argument_cap : bounds Protocol.initial (initial argument_cap).
Proof.
 constructor;try reflexivity.
 change (0<=Nat.max 3 argument_cap)%nat. lia.
Qed.
Lemma initial_capacity requests : domain requests -> capacity (NativeRequestBounds.maximum requests) Protocol.initial requests.
Proof. intro H. exists (initial (NativeRequestBounds.maximum requests)). split;[apply initial_bounds|exact H]. Qed.
Lemma request_name_bound request : Protocol.shape request -> (Protocol.opcode request<=26)%nat ->
 (length (Protocol.object_name request)<=1024)%nat.
Proof.
 destruct request as [opcode values name]. intros [_ Hshape] Hrange. cbn [Protocol.opcode] in Hrange.
 let rec cases count tag := lazymatch count with O=>idtac|S ?rest=>destruct tag as [|tag];[idtac|cases rest tag] end in cases 27%nat opcode.
 all:try lia.
 all:cbn [Protocol.opcode Protocol.arguments Protocol.object_name] in Hshape|-*.
 all:unfold Protocol.valid_name in Hshape.
 all:intuition subst;try lia.
 all:cbn [length];lia.
Qed.
Lemma bounded native logical before : NativeState.represents native logical -> bounds logical before ->
 SchemaEvaluationIndexCell.bounded native (Protocol.formulas logical) (Protocol.classes logical) (indices before).
Proof.
 intros Hstate Hbounds.
 exact (SchemaEvaluationIndexCell.bounded_mono native _ _ _ _ (index_bound _ _ Hbounds)
   (SchemaInstanceCheckedResources.initial_bounded native logical (NativeState.formula_representation _ _ Hstate))).
Qed.
Lemma basic_resources native logical argument_cap before request :
 Protocol.shape request -> NativeNameCompact.compact native logical -> bounds logical before ->
 conditions argument_cap before request -> NativeBasicDispatcher.resources native logical request /\
 Z.of_nat (length (Protocol.expressions logical))<maximum.
Proof.
 intros Hshape Hcompact [HF HB HC HH Hbind HE Hnames] Hconditions.
 pose proof (request_name_bound request Hshape (opcode_bound _ _ _ Hconditions)) as Hname.
 destruct Hconditions as [Hop Hargs Hf Hfnext Hbnext Hc Hh Hbinding He Hbytes Hspecific].
 rewrite !Nat2Z.inj_succ in Hc,Hh,Hbinding,He.
 unfold NativeNameCompact.compact,NativeNameCompact.compact_bindings,NativeNameCompact.bytes in Hcompact.
 unfold SchemaEvaluationBoundedCell.bound in Hf.
 split;[constructor|];try lia.
 rewrite Nat2Z.inj_add,Hcompact. unfold NativeNameCompact.bytes in Hnames. rewrite Nat2Z.inj_add in Hbytes. lia.
Qed.
Theorem current_resources native logical argument_cap before request :
 Protocol.shape request -> NativeState.represents native logical ->
 FormulaTopology.ordered native (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> NativeNameCompact.compact native logical -> NativeSchemaFieldBounds.fields native argument_cap ->
 bounds logical before -> conditions argument_cap before request -> NativeGeneralDispatcher.resources native logical request.
Proof.
 intros Hshape Hstate Htop Hfalse Hgood Hcompact Hfields Hbounds Hconditions.
 destruct (basic_resources native logical argument_cap before request Hshape Hcompact Hbounds Hconditions) as [Hbasic Hschema].
 exact (NativeUniformResources.resources native logical request (formulas before) (indices before) (classes before) (expressions before) argument_cap
   Hshape Hstate Htop Hfalse Hgood (bounded native logical before Hstate Hbounds) (formula_bound _ _ Hbounds)
   (class_bound _ _ Hbounds) (expression_bound _ _ Hbounds) Hfields (arguments_bound _ _ _ Hconditions) Hbasic Hschema
   (specific_check _ _ _ Hconditions)).
Qed.
Theorem arithmetic native logical argument_cap before request :
 NativeState.represents native logical -> NativeSchemaFieldBounds.fields native argument_cap ->
 bounds logical before -> conditions argument_cap before request ->
 NativeUniformCommand.arithmetic native logical request (formulas before) (indices before) (classes before) (expressions before) argument_cap.
Proof.
 intros Hstate Hfields Hbounds Hconditions. constructor.
 - exact (formula_bound _ _ Hbounds).
 - exact (class_bound _ _ Hbounds).
 - exact (expression_bound _ _ Hbounds).
 - exact (bounded native logical before Hstate Hbounds).
 - exact (arguments_bound _ _ _ Hconditions).
 - exact (result_index_room _ _ _ Hconditions).
 - intro H24. pose proof (specific_check _ _ _ Hconditions) as Hcheck.
   unfold NativeUniformResources.check in Hcheck. rewrite H24 in Hcheck.
   apply Bool.andb_true_iff in Hcheck as [Hguard HC].
   destruct (NativeUniformResources.guard_values _ _ _ Hguard) as [HF [Hfuel HB]]. apply Z.leb_le in HC.
   constructor.
   + exact (expression_bound _ _ Hbounds).
   + exact (formula_bound _ _ Hbounds).
   + exact (class_bound _ _ Hbounds).
   + exact (bounded native logical before Hstate Hbounds).
   + exact (NativeSchemaFieldBounds.encoded_fields native argument_cap Hfields).
   + pose proof (history_room _ _ _ Hconditions) as HhistoryRoom. pose proof (history_bound _ _ Hbounds) as HhistoryCap. rewrite Nat2Z.inj_succ in HhistoryRoom. lia.
   + exact HF.
   + exact HB.
   + exact Hfuel.
   + exact HC.
Qed.
Theorem bounds_next native logical request reply next argument_cap before :
 Protocol.shape request -> (Protocol.opcode request<=26)%nat -> Protocol.step logical request reply next ->
 NativeState.represents native next -> FormulaTopology.ordered native (length (Protocol.formulas next)) ->
 bounds logical before ->
 NativeUniformCommand.quantitative native next request (formulas before) (indices before) (classes before) (expressions before) argument_cap ->
 bounds next (step argument_cap request before).
Proof.
 intros Hshape Hop Hstep Hnext Htop Hbounds [HF [HB [HC HE]]].
 destruct Hbounds as [Hf Hb Hc Hh Hbind He Hnames].
 destruct (LogicalRegistryBounds.step_counts _ _ _ _ Hstep) as [HbindingGrowth [HhistoryGrowth HexpressionGrowth]].
 pose proof (NativeNameCompact.step_bytes_bound _ _ _ _ Hstep) as HnameGrowth.
 pose proof (request_name_bound request Hshape Hop) as Hname.
 pose proof (SchemaSemanticBounds.initial_bound_le native next _ Hnext Htop HB) as Hindex.
 constructor;cbn [step formulas indices classes history bindings expressions names];try assumption;lia.
Qed.
Theorem capacity_next native logical request requests reply next argument_cap before :
 Protocol.shape request -> Protocol.opcode request<>0%nat -> Protocol.step logical request reply next ->
 NativeState.represents native next -> FormulaTopology.ordered native (length (Protocol.formulas next)) ->
 bounds logical before -> check argument_cap before (request::requests)=true ->
 NativeUniformCommand.quantitative native next request (formulas before) (indices before) (classes before) (expressions before) argument_cap ->
 capacity argument_cap next requests.
Proof.
 intros Hshape Hpositive Hstep Hnext Htop Hbounds Hcheck Hquant.
 destruct (check_tail argument_cap before request requests Hpositive Hcheck) as [Hconditions Htail].
 exists (step argument_cap request before). split;[|exact Htail].
 exact (bounds_next native logical request reply next argument_cap before Hshape (opcode_bound _ _ _ Hconditions) Hstep Hnext Htop Hbounds Hquant).
Qed.
End NativeBudgetPlan.
