From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash NativeState NativeBasicDispatcher NativeFullDispatcher NativeGeneralDispatcher NativeProofSession
 NativeNameCompact NativeSchemaFlat NativeRequestBounds SchemaEvaluationSetCell SchemaEvaluationSetRun SchemaInstanceSetReady
 SchemaInstanceSetProtocol SchemaInstanceSetCommand SchemaGraph SchemaMarking SchemaMetadata SchemaRepresentation SchemaNodeMeaning
 NativeAxiomTotal AxiomTaggedInvariant FormulaTopology ClassLookup LogicalRegistryBounds.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeSetBudgetPlan.
Import IndexExecution SipHashExecution.
Record caps := Caps { formulas:nat; classes:nat; history:nat; bindings:nat; expressions:nat; names:nat }.
Definition initial := Caps 1 0 0 0 0 0.
Definition formula_target request formula_cap expression_cap := match Protocol.opcode request with
 | 24%nat=>(formula_cap+42*(expression_cap*expression_cap))%nat
 | 11%nat=>(formula_cap+42)%nat | 22%nat=>formula_cap | _=>S formula_cap end.
Definition expression_target request expression_cap :=
 (expression_cap+NativeRequestBounds.expression_increment request)%nat.
Definition step request before := Caps (formula_target request (formulas before) (expressions before))
 (S (classes before)) (S (history before)) (S (bindings before))
 (expression_target request (expressions before)) (names before+1024).
Definition admissible request := if NativeFullDispatcher.supported_dec (Protocol.opcode request) then
 negb (Nat.eqb (Protocol.opcode request) 6) else match Protocol.opcode request,Protocol.arguments request with
 | 0%nat,_=>true | 11%nat,[tag;_;_;_]=>negb (AxiomTaggedInvariant.uses_rename tag)
 | 22%nat,[kind;tag;_;_;_]=>NativeSchemaFlat.check kind tag | 24%nat,_=>true | _,_=>false end.
Definition head_check before request := admissible request && Nat.leb (Protocol.opcode request) 26 &&
 Z.leb (Z.of_nat (formulas before)) SchemaEvaluationSetCell.bound &&
 Z.leb (Z.of_nat (formulas (step request before))) SchemaEvaluationSetCell.bound &&
 Z.leb (Z.of_nat (S (classes before))) maximum && Z.leb (Z.of_nat (S (history before))) maximum &&
 Z.leb (Z.of_nat (S (bindings before))) maximum && Z.leb (Z.of_nat (S (expressions before))) maximum &&
 Z.leb (Z.of_nat (names before+1024)) maximum.
Fixpoint check before requests := match requests with
 | []=>true|request::tail=>if Nat.eqb (Protocol.opcode request) 0 then true else
 head_check before request && check (step request before) tail end.
Record bounds logical before : Prop := Bounds {
 formula_bound : (length (Protocol.formulas logical)<=formulas before)%nat;
 class_bound : (length (Protocol.classes logical)<=classes before)%nat;
 history_bound : (length (Protocol.history logical)<=history before)%nat;
 binding_bound : (length (Protocol.bindings logical)<=bindings before)%nat;
 expression_bound : (length (Protocol.expressions logical)<=expressions before)%nat;
 name_bound : (NativeNameCompact.bytes logical<=names before)%nat
}.
Definition capacity logical requests := exists before,bounds logical before /\ check before requests=true.
Definition domain requests := check initial requests=true.
Record conditions before request : Prop := Conditions {
 allowed_request : admissible request=true;
 opcode_bound : (Protocol.opcode request<=26)%nat;
 formula_room : Z.of_nat (formulas before)<=SchemaEvaluationSetCell.bound;
 result_formula_room : Z.of_nat (formulas (step request before))<=SchemaEvaluationSetCell.bound;
 class_room : Z.of_nat (S (classes before))<=maximum;
 history_room : Z.of_nat (S (history before))<=maximum;
 binding_room : Z.of_nat (S (bindings before))<=maximum;
 expression_room : Z.of_nat (S (expressions before))<=maximum;
 name_room : Z.of_nat (names before+1024)<=maximum
}.
Lemma head_conditions before request : head_check before request=true -> conditions before request.
Proof.
 unfold head_check. rewrite !Bool.andb_true_iff. intro H.
 repeat match goal with H:_ /\ _ |- _=>destruct H end.
 repeat match goal with H:Z.leb _ _=true |- _=>apply Z.leb_le in H|H:Nat.leb _ _=true |- _=>apply Nat.leb_le in H end.
 constructor;assumption.
Qed.
Lemma check_tail before request requests : Protocol.opcode request<>0%nat -> check before (request::requests)=true ->
 conditions before request /\ check (step request before) requests=true.
Proof.
 intros Hpositive Hcheck. cbn [check] in Hcheck. rewrite (proj2 (Nat.eqb_neq _ _) Hpositive) in Hcheck.
 apply Bool.andb_true_iff in Hcheck as [Hhead Htail]. split;[now apply head_conditions|exact Htail].
Qed.
Lemma initial_bounds : bounds Protocol.initial initial.
Proof. constructor;reflexivity. Qed.
Lemma initial_capacity requests : domain requests -> capacity Protocol.initial requests.
Proof. intro H. exists initial. split;[apply initial_bounds|exact H]. Qed.
Lemma nonrename_simple tag : AxiomTaggedInvariant.uses_rename tag=false -> NativeProofSession.simple_tag tag.
Proof.
 intro Hrename. unfold NativeProofSession.simple_tag.
 let rec cases count index := lazymatch count with O=>idtac|S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 18%nat tag.
 all:cbn [AxiomTaggedInvariant.uses_rename existsb Nat.eqb orb] in Hrename;intuition lia.
Qed.
Inductive form : Protocol.request -> Prop :=
 | basic request : NativeBasicDispatcher.supported (Protocol.opcode request) -> Protocol.opcode request<>6%nat -> form request
 | axiom tag a b c : NativeProofSession.simple_tag tag -> form (Protocol.Req 11 [tag;a;b;c] [])
 | node kind a b c d : NativeSchemaFlat.allowed kind a -> form (Protocol.Req 22 [kind;a;b;c;d] [])
 | instance ids name : form (Protocol.Req 24 ids name).
Lemma form_view request : Protocol.shape request -> Protocol.opcode request<>0%nat -> admissible request=true -> form request.
Proof.
 intros Hshape Hpositive Hallowed. unfold admissible in Hallowed.
 destruct (NativeFullDispatcher.supported_dec (Protocol.opcode request)) as [Hbasic|Hnot].
 - apply basic;[exact Hbasic|]. apply Bool.negb_true_iff in Hallowed. now apply Nat.eqb_neq.
 - destruct request as [opcode values name]. cbn [Protocol.opcode Protocol.arguments] in Hallowed,Hpositive.
   let rec cases count index := lazymatch count with O=>idtac|S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 25%nat opcode.
   all:try discriminate;try contradiction.
   + destruct values as [|tag [|a [|b [|c [|bad values]]]]];try discriminate.
     destruct Hshape as [_ Hfields]. cbn [Protocol.opcode Protocol.arguments Protocol.object_name length] in Hfields.
     destruct Hfields as [_ ->]. apply axiom. apply nonrename_simple. now apply Bool.negb_true_iff in Hallowed.
   + destruct values as [|kind [|a [|b [|c [|d [|bad values]]]]]];try discriminate.
     destruct Hshape as [_ Hfields]. cbn [Protocol.opcode Protocol.arguments Protocol.object_name length] in Hfields.
     destruct Hfields as [_ ->]. apply node. now apply NativeSchemaFlat.check_spec.
   + apply instance.
Qed.
Lemma form_not_abstract request : form request -> Protocol.opcode request<>6%nat.
Proof. intro H. destruct H;cbn [Protocol.opcode];lia. Qed.
Lemma form_flat request : form request -> NativeSchemaFlat.request_allowed request.
Proof.
 intro Hform. destruct Hform as [request Hbasic Hnot6|tag a b c Hsimple|kind a b c d Hallowed|ids name];
  unfold NativeSchemaFlat.request_allowed;try exact I;try exact Hallowed.
 assert (Hnot22:Protocol.opcode request<>22%nat).
 { intro Heq. unfold NativeBasicDispatcher.supported,NativeBasicDispatcher.two,NativeBasicDispatcher.one,NativeBasicDispatcher.zero,
   NativeBasicDispatcher.named,NativeBasicDispatcher.query in Hbasic. rewrite Heq in Hbasic. intuition discriminate. }
 destruct request as [opcode values name]. cbn [Protocol.opcode Protocol.arguments] in Hnot22|-*.
 let rec cases count index := lazymatch count with O=>idtac|S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 23%nat opcode.
 all:try exact I;contradiction.
Qed.
Lemma request_name_bound request : Protocol.shape request -> (Protocol.opcode request<=26)%nat ->
 (length (Protocol.object_name request)<=1024)%nat.
Proof.
 destruct request as [opcode values name]. intros [_ Hshape] Hrange. cbn [Protocol.opcode] in Hrange.
 let rec cases count tag := lazymatch count with O=>idtac|S ?rest=>destruct tag as [|tag];[idtac|cases rest tag] end in cases 27%nat opcode.
 all:try lia. all:cbn [Protocol.opcode Protocol.arguments Protocol.object_name] in Hshape|-*.
 all:unfold Protocol.valid_name in Hshape. all:intuition subst;try lia. all:cbn [length];lia.
Qed.
Lemma basic_resources native logical before request : Protocol.shape request -> NativeNameCompact.compact native logical ->
 bounds logical before -> conditions before request -> NativeBasicDispatcher.resources native logical request /\
 Z.of_nat (length (Protocol.expressions logical))<maximum.
Proof.
 intros Hshape Hcompact [HF HC HH HB HE Hnames] Hconditions.
 pose proof (request_name_bound request Hshape (opcode_bound _ _ Hconditions)) as Hname.
 destruct Hconditions as [Hallowed Hop Hf Hfnext Hc Hh Hb He Hbytes].
 rewrite !Nat2Z.inj_succ in Hc,Hh,Hb,He. unfold SchemaEvaluationSetCell.bound in Hf.
 unfold NativeNameCompact.compact,NativeNameCompact.compact_bindings,NativeNameCompact.bytes in Hcompact.
 split;[constructor|];try lia.
 rewrite Nat2Z.inj_add,Hcompact. unfold NativeNameCompact.bytes in Hnames. rewrite Nat2Z.inj_add in Hbytes. lia.
Qed.
Theorem non_instance_resources native logical before request :
 Protocol.shape request -> Protocol.opcode request<>0%nat -> Protocol.opcode request<>24%nat ->
 NativeNameCompact.compact native logical -> bounds logical before -> conditions before request ->
 NativeGeneralDispatcher.resources native logical request.
Proof.
 intros Hshape Hpositive Hnot24 Hcompact Hbounds Hconditions.
 destruct (basic_resources native logical before request Hshape Hcompact Hbounds Hconditions) as [Hbasic Hschema].
 constructor;[exact Hbasic|exact Hschema|].
 destruct (form_view request Hshape Hpositive (allowed_request _ _ Hconditions)) as [request Hsupported Hnot6|tag a b c Hsimple|kind a b c d Hallowed|ids name].
 - exact (NativeProofSession.basic_specific native logical request Hshape Hsupported).
 - change (NativeAxiomTotal.resources logical tag a b c). apply NativeProofSession.resources;[exact Hsimple|].
   pose proof (result_formula_room _ _ Hconditions) as Hroom. pose proof (formula_bound _ _ Hbounds) as HF.
   change (Z.of_nat (formulas before+42)<=SchemaEvaluationSetCell.bound) in Hroom.
   unfold SchemaEvaluationSetCell.bound in Hroom. rewrite Nat2Z.inj_add in Hroom. lia.
 - exact I.
 - contradiction.
Qed.
Theorem instance_resources native logical before ids name :
 NativeState.represents native logical -> NativeSchemaFlat.flat native -> SchemaEvaluationSetCell.sets (Protocol.classes logical) ->
 bounds logical before -> conditions before (Protocol.Req 24 ids name) ->
 SchemaInstanceSetProtocol.resources native logical ids name.
Proof.
 intros Hstate Hflat Hsets Hbounds Hconditions root cert actual Hlookup Hproof Harity Hactual.
 pose proof (SchemaNodeMeaning.proof_lookup logical root cert Hproof) as HrootLookup.
 assert (Hroot:(root<length (Protocol.expressions logical))%nat) by (apply nth_error_Some;congruence).
 pose proof (expression_bound _ _ Hbounds) as HE. pose proof (formula_bound _ _ Hbounds) as HF.
 assert (Hsize:(SchemaMarking.size root<=expressions before*expressions before)%nat).
 { unfold SchemaMarking.size,SchemaGraph.width;nia. }
 pose proof (result_formula_room _ _ Hconditions) as Hroom.
 change (Z.of_nat (formulas before+42*(expressions before*expressions before))<=SchemaEvaluationSetCell.bound) in Hroom.
 split.
 - unfold SchemaEvaluationSetCell.bound,maximum in *. rewrite Nat2Z.inj_add,Nat2Z.inj_mul in Hroom. nia.
 - split.
   + pose proof (history_room _ _ Hconditions) as HHroom. pose proof (history_bound _ _ Hbounds) as HH.
     rewrite Nat2Z.inj_succ in HHroom. lia.
   + split;[exact (NativeSchemaFlat.fragment native root Hflat)|]. split;[exact Hsets|].
     repeat rewrite Nat2Z.inj_add in *. repeat rewrite Nat2Z.inj_mul in *. nia.
Qed.
Definition quantitative (logical:Protocol.state) request before next :=
 (length (Protocol.formulas next)<=formula_target request (formulas before) (expressions before))%nat /\
 (length (Protocol.classes next)<=S (classes before))%nat /\
 (length (Protocol.expressions next)<=expression_target request (expressions before))%nat.
Theorem bounds_next logical request reply next before :
 Protocol.shape request -> (Protocol.opcode request<=26)%nat -> Protocol.step logical request reply next ->
 bounds logical before -> quantitative logical request before next -> bounds next (step request before).
Proof.
 intros Hshape Hop Hstep [HF HC HH HB HE Hnames] [Hform [Hclass Hexpr]].
 destruct (LogicalRegistryBounds.step_counts _ _ _ _ Hstep) as [HbindingGrowth [HhistoryGrowth HexpressionGrowth]].
 pose proof (NativeNameCompact.step_bytes_bound _ _ _ _ Hstep) as HnameGrowth.
 pose proof (request_name_bound request Hshape Hop) as Hname.
 constructor;cbn [step formulas classes history bindings expressions names];try assumption;lia.
Qed.
Theorem capacity_next logical request requests reply next before :
 Protocol.shape request -> Protocol.opcode request<>0%nat -> Protocol.step logical request reply next ->
 bounds logical before -> check before (request::requests)=true -> quantitative logical request before next -> capacity next requests.
Proof.
 intros Hshape Hpositive Hstep Hbounds Hcheck Hquant.
 destruct (check_tail before request requests Hpositive Hcheck) as [Hconditions Htail].
 exists (step request before). split;[|exact Htail]. exact (bounds_next logical request reply next before Hshape (opcode_bound _ _ Hconditions) Hstep Hbounds Hquant).
Qed.
End NativeSetBudgetPlan.
