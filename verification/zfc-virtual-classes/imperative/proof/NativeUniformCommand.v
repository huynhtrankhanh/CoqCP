From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeBasicDispatcher NativeFullDispatcher NativeGeneralDispatcher NativeGeneralCommandInvariant
 NativeBasicCommandInvariant NativeBasicIndexInvariant NativeBasicCountInvariant NativeNameCompact NativeCommandBoundary NativeClassAdvancedIndexInvariant NativeAxiomIndexInvariant NativeCertifyIndexInvariant
 NativeClassBinaryBoundary NativeSchemaInvariant NativeSchemaBoundary SchemaNodeTotal NativeAxiomTotal NativeAxiomInvariant AxiomRejectionProtocol NativeProofSession
 SchemaEvaluationIndexCell SchemaEvaluationIndexBounds SchemaEvaluationIndexShiftClass SchemaEvaluationIndexBudget SchemaEvaluationIndexAxiomTagged SchemaUniformBudget NativeSchemaUniformBoundary SchemaProtocolFrame
 RenameMemoClassEqual RenameMemoClassMember RenameMemoClassSetness RenameMemoCallers AxiomTaggedInvariant
 FormulaTopology ClassLookup ClassStorage Representation LogicalNames LogicalHistory LogicalRegistryBounds.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeUniformCommand.
Import IndexExecution SipHashExecution.
Module Bounds := SchemaEvaluationIndexBounds.
Definition formula_target request capacity := match Protocol.opcode request with
 | 1%nat|2%nat|3%nat|4%nat|13%nat=>S capacity
 | 7%nat|8%nat=>(capacity+2*(capacity*capacity)+13)%nat
 | 11%nat=>match Protocol.arguments request with tag::_=>(capacity+SchemaEvaluationIndexBudget.axiom_cost capacity tag)%nat|_=>capacity end
 | 14%nat=>(capacity+capacity*capacity+10)%nat
 | _=>capacity end.
Definition index_target request bound argument_cap := match Protocol.opcode request with
 | 7%nat|14%nat=>(bound+2)%nat |8%nat=>(2*bound+3)%nat |11%nat=>(bound+3*argument_cap+4)%nat
 |22%nat=>bound|_=>Nat.max bound argument_cap end.
Lemma bounded_transfer native first second bound : NativeState.represents native first -> NativeState.represents native second ->
 FormulaTopology.ordered native(length(Protocol.formulas second)) ->
 SchemaEvaluationIndexCell.bounded native(Protocol.formulas first)(Protocol.classes first)bound ->
 SchemaEvaluationIndexCell.bounded native(Protocol.formulas second)(Protocol.classes second)bound.
Proof.
 intros Hfirst Hsecond Htop [Hraw Hclasses]. apply NativeBasicIndexInvariant.bounded_final;[exact Hsecond|exact Htop| |].
 - rewrite(NativeBasicCommandInvariant.same_formula_count _ _ _ Hsecond (NativeState.formula_representation _ _ Hfirst)). exact Hraw.
 - eapply NativeBasicIndexInvariant.source_set_indices;[exact(NativeState.class_representation _ _ Hfirst)|exact Hclasses].
Qed.
Lemma class_count_transfer native first second : NativeState.represents native first -> NativeState.represents native second ->
 length(Protocol.classes first)=length(Protocol.classes second).
Proof. intros Hfirst Hsecond. rewrite <-(NativeBasicCommandInvariant.class_count _ _ Hfirst),<-(NativeBasicCommandInvariant.class_count _ _ Hsecond). reflexivity. Qed.
Lemma equal_cost native logical a b ca cb capacity : NativeState.represents native logical -> ClassLookup.wellformed native ->
 nth_error(Protocol.formulas logical)0=Some SetTheory.falsity -> (length(Protocol.formulas logical)<=capacity)%nat ->
 Protocol.class_at logical a=Some ca -> Protocol.class_at logical b=Some cb ->
 (RenameMemoClassEqual.work native a b ca cb<=2*(capacity*capacity)+13)%nat.
Proof.
 intros Hstate Hgood Hfalse Hcap Ha Hb.
 assert(Hpositive:(0<length(Protocol.formulas logical))%nat) by (apply nth_error_Some;congruence).
 pose proof(SchemaEvaluationIndexBudget.growth_bound native _ _ a ca capacity (NativeState.class_representation _ _ Hstate) Hgood Ha Hpositive Hcap) as HgrowthA.
 pose proof(SchemaEvaluationIndexBudget.growth_bound native _ _ b cb capacity (NativeState.class_representation _ _ Hstate) Hgood Hb Hpositive Hcap) as HgrowthB.
 destruct ca,cb;cbn [RenameMemoClassEqual.work];nia.
Qed.
Lemma member_cost native logical a b ca cb capacity : NativeState.represents native logical -> ClassLookup.wellformed native ->
 nth_error(Protocol.formulas logical)0=Some SetTheory.falsity -> (length(Protocol.formulas logical)<=capacity)%nat ->
 Protocol.class_at logical a=Some ca -> Protocol.class_at logical b=Some cb ->
 (RenameMemoClassMember.work native a b ca cb<=2*(capacity*capacity)+13)%nat.
Proof.
 intros Hstate Hgood Hfalse Hcap Ha Hb.
 assert(Hpositive:(0<length(Protocol.formulas logical))%nat) by (apply nth_error_Some;congruence).
 pose proof(SchemaEvaluationIndexBudget.growth_bound native _ _ a ca capacity (NativeState.class_representation _ _ Hstate) Hgood Ha Hpositive Hcap) as HgrowthA.
 pose proof(SchemaEvaluationIndexBudget.growth_bound native _ _ b cb capacity (NativeState.class_representation _ _ Hstate) Hgood Hb Hpositive Hcap) as HgrowthB.
 destruct ca;cbn [RenameMemoClassMember.work];nia.
Qed.
Lemma certify_cost native logical name tid capacity : NativeState.represents native logical -> ClassLookup.wellformed native ->
 nth_error(Protocol.formulas logical)0=Some SetTheory.falsity -> (length(Protocol.formulas logical)<=capacity)%nat ->
 (NativeCertifyIndexInvariant.cost native logical name tid<=capacity*capacity+10)%nat.
Proof.
 intros Hstate Hgood Hfalse Hcap.
 assert(Hpositive:(0<length(Protocol.formulas logical))%nat) by (apply nth_error_Some;congruence).
 unfold NativeCertifyIndexInvariant.cost. destruct(Protocol.lookup name(Protocol.bindings logical)) as [[cls flag|fid|root]|];try lia.
 destruct(Protocol.class_at logical cls) as [c|] eqn:Hclass;try lia.
 pose proof(SchemaEvaluationIndexBudget.growth_bound native _ _ cls c capacity (NativeState.class_representation _ _ Hstate) Hgood Hclass Hpositive Hcap) as Hgrowth.
 destruct c;cbn [RenameMemoClassSetness.work];nia.
Qed.
Lemma binary_growth work native logical next a b capacity :
 NativeClassBinaryBoundary.growth work native logical a b next ->
 (length(Protocol.formulas logical)<=capacity)%nat ->
 (forall ca cb,Protocol.class_at logical a=Some ca -> Protocol.class_at logical b=Some cb ->
   (work native a b ca cb<=2*(capacity*capacity)+13)%nat) ->
 (length(Protocol.formulas next)<=capacity+2*(capacity*capacity)+13)%nat.
Proof.
 intros Hgrowth Hcap Hcost. unfold NativeClassBinaryBoundary.growth in Hgrowth.
 destruct(Protocol.class_at logical a) as [ca|] eqn:Ha;destruct(Protocol.class_at logical b) as [cb|] eqn:Hb;try (rewrite Hgrowth;lia).
 pose proof(Hcost ca cb eq_refl eq_refl). lia.
Qed.

Lemma axiom_growth native logical tag a b c bs ns tail observations final trace next capacity :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat -> meta_value native 15=50 -> meta_value native 8=0 ->
 Z.of_nat tag<=maximum -> Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum ->
 NativeState.represents native logical -> NativeState.represents final next ->
 nth_error(Protocol.formulas logical)0=Some SetTheory.falsity -> (length(Protocol.formulas logical)<=capacity)%nat ->
 stdin native=49::32::decimalBytes tag++32::decimalBytes a++32::decimalBytes b++32::decimalBytes c++10::tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 (length(Protocol.formulas next)<=length(Protocol.formulas logical)+AxiomTaggedInvariant.cost tag a)%nat ->
 (length(Protocol.formulas next)<=capacity+SchemaEvaluationIndexBudget.axiom_cost capacity tag)%nat.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Htag Ha Hb Hc Hstate Hnext Hfalse Hcap Hinput Hrun Hgrowth.
 assert(Hpositive:(0<capacity)%nat).
 { assert(0<length(Protocol.formulas logical))%nat by (apply nth_error_Some;congruence). lia. }
 destruct(Protocol.concrete_axiom logical tag a b c) as [wanted|] eqn:Hconcrete.
 - pose proof(NativeProofSession.ready_from_concrete logical tag a b c wanted Hconcrete) as Hready.
   pose proof(SchemaEvaluationIndexBudget.cost_bound capacity tag a Hpositive) as Hcost.
   assert(Hroot:AxiomTaggedInvariant.uses_rename tag=true -> (a<capacity)%nat).
   { intro Hrename. destruct Hready as [Hp _].
     rewrite(SchemaEvaluationIndexBudget.rename_needs_p tag Hrename) in Hp.
     assert(a<length(Protocol.formulas logical))%nat by (apply nth_error_Some;congruence). lia. }
   specialize(Hcost Hroot). lia.
 - destruct(AxiomRejectionProtocol.generated_rejected native logical bs ns 49 [49] tag a b c 32 32 32 32 10 tail observations
    eq_refl Hconcrete Hmeta Htoken Hprint Hpending Herror Htag Ha Hb Hc
    (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
    (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate) (NativeState.schema_representation _ _ Hstate)
    ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
    ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
    ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
   as(model & Hequal & HmodelRun & Hstep & Harena & Hrest).
   assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). clear Hequal. subst model.
   pose proof(NativeBasicCommandInvariant.same_formula_count _ _ _ Hnext Harena). lia.
Qed.

Lemma basic_target_neutral request capacity : NativeBasicDispatcher.supported(Protocol.opcode request) ->
 (4<Protocol.opcode request)%nat -> Protocol.opcode request<>13%nat -> formula_target request capacity=capacity.
Proof.
 destruct request as [opcode args name]. cbn [Protocol.opcode]. intros Hsupported Hlarge H13.
 unfold NativeBasicDispatcher.supported,NativeBasicDispatcher.two,NativeBasicDispatcher.one,NativeBasicDispatcher.zero,
 NativeBasicDispatcher.named,NativeBasicDispatcher.query in Hsupported.
 unfold formula_target;cbn [Protocol.opcode].
 let rec cases count index := lazymatch count with O=>idtac|S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 27%nat opcode.
 all:try reflexivity;exfalso;intuition lia.
Qed.
Lemma basic_formula_growth native logical request bs ns tail observations final trace next capacity :
 Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> NativeState.represents final next -> (length(Protocol.formulas logical)<=capacity)%nat ->
 (length(Protocol.formulas next)<=S(length(Protocol.formulas logical)))%nat ->
 (length(Protocol.formulas next)<=formula_target request capacity)%nat.
Proof.
 intros Hshape Hsupported Hmeta Htoken Hpending Herror Hinput Hrun Hstate Hnext Hcap Hgrowth.
 pose proof(NativeBasicDispatcher.supported_bound _ Hsupported) as Hrange.
 destruct(le_dec (Protocol.opcode request)4) as [Hsmall|Hlarge].
 - assert(Hcases:Protocol.opcode request=1%nat \/ Protocol.opcode request=2%nat \/ Protocol.opcode request=3%nat \/ Protocol.opcode request=4%nat) by lia.
   unfold formula_target. destruct Hcases as [->|[->|[->| ->]]];lia.
 - destruct(Nat.eq_dec(Protocol.opcode request)13%nat) as [H13|H13].
   + unfold formula_target. rewrite H13. lia.
   + rewrite(basic_target_neutral request capacity Hsupported ltac:(lia) H13).
     pose proof(NativeBasicCommandInvariant.request_count native request bs ns tail observations final trace Hshape Hsupported
       ltac:(unfold NativeBasicCountInvariant.unchanged;repeat split;lia) Hmeta Htoken Hpending Herror Hinput Hrun) as Hcount.
     pose proof(NativeBasicCommandInvariant.formula_count _ _ Hstate). pose proof(NativeBasicCommandInvariant.formula_count _ _ Hnext). lia.
Qed.
Definition primitive_post final next request formula_cap index_cap class_cap argument_cap :=
 (length(Protocol.formulas next)<=formula_target request formula_cap)%nat /\
 SchemaEvaluationIndexCell.bounded final(Protocol.formulas next)(Protocol.classes next)(index_target request index_cap argument_cap) /\
 (length(Protocol.classes next)<=S class_cap)%nat.
Theorem primitive_preserves native logical request bs ns tail observations final trace reply next formula_cap index_cap class_cap argument_cap :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat -> Protocol.opcode request<>24%nat ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat -> (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> LogicalRegistryBounds.unique logical -> NativeGeneralDispatcher.resources native logical request ->
 SchemaEvaluationIndexCell.bounded native(Protocol.formulas logical)(Protocol.classes logical)index_cap ->
 (length(Protocol.formulas logical)<=formula_cap)%nat -> (length(Protocol.classes logical)<=class_cap)%nat ->
 Forall(fun value=>(value<=argument_cap)%nat)(Protocol.arguments request) -> Z.of_nat(index_target request index_cap argument_cap)<=maximum ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 Protocol.step logical request reply next -> NativeState.represents final next ->
 FormulaTopology.ordered final(length(Protocol.formulas next)) ->
 primitive_post final next request formula_cap index_cap class_cap argument_cap.
Proof.
 intros Hshape Hrange Hnot24 Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hresource Hbounded
   HformulaCap HclassCap Hargs HindexWord Hinput Hrun Hstep Hnext HnextTop.
 pose proof(NativeGeneralDispatcher.basic_resources _ _ _ Hresource) as HbasicResource.
 pose proof(NativeGeneralDispatcher.command_resources _ _ _ Hresource) as Hspecific.
 pose proof(NativeGeneralDispatcher.schema_room _ _ _ Hresource) as HschemaRoom.
 pose proof(NativeBasicDispatcher.safe_history _ Hsafe) as HhistoryValid.
 pose proof(NativeBasicDispatcher.safe_names _ Hsafe) as HnamesValid.
 destruct(NativeFullDispatcher.supported_dec (Protocol.opcode request)) as [Hbasic|Hextra].
 - pose proof(NativeBasicCommandInvariant.preserves native logical request bs ns tail observations final trace reply next Hshape Hbasic ltac:(lia)
     Htoken Hprint Hpending Herror Hstate Hsafe HbasicResource Htop Hfalse Hgood Hunique Hinput Hrun Hstep Hnext)
   as(Htop' & Hfalse' & Hgood' & HformGrowth & HclassGrowth & Hrest).
   assert(Htarget:index_target request index_cap argument_cap=Nat.max index_cap argument_cap).
   { destruct request as [opcode values name]. cbn [Protocol.opcode] in Hbasic.
     unfold NativeBasicDispatcher.supported,NativeBasicDispatcher.two,NativeBasicDispatcher.one,NativeBasicDispatcher.zero,
       NativeBasicDispatcher.named,NativeBasicDispatcher.query in Hbasic.
     unfold index_target;cbn [Protocol.opcode].
     let rec cases count index := lazymatch count with O=>idtac|S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 27%nat opcode.
     all:try reflexivity;exfalso;intuition lia. }
   unfold primitive_post. split.
   + exact(basic_formula_growth native logical request bs ns tail observations final trace next formula_cap Hshape Hbasic ltac:(lia)
       Htoken Hpending Herror Hinput Hrun Hstate Hnext HformulaCap HformGrowth).
   + split;[rewrite Htarget|lia].
     eapply NativeBasicIndexInvariant.preserves;try eassumption;try lia.
     eapply Forall_impl;[exact Hargs|]. intros value Hvalue. eapply Nat.le_trans;[exact Hvalue|apply Nat.le_max_r].
 - destruct(NativeFullDispatcher.shape_extra request Hshape Hrange Hextra) as [a b|a b|tag a b c|tid name|kind a b c d|ids name].
   all:try contradiction.
   all:cbn [NativeGeneralDispatcher.specific_resources NativeFullDispatcher.specific_resources Protocol.opcode Protocol.arguments Protocol.object_name] in Hspecific.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|a' values Ha Hrest];subst a' values.
     inversion Hrest as [|b' values Hb Hnil];subst b' values.
     change(meta_value native 15=56) in Hpending. rewrite(NativeFullDispatcher.binary_rest 7 a b tail ltac:(tauto)) in Hinput.
     change(Z.of_nat (index_cap+2)<=maximum) in HindexWord.
     destruct(NativeClassAdvancedIndexInvariant.Equal.generated_total_protocol 55 [] native logical bs ns a b 32 32 10 tail index_cap observations
       eq_refl Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hspecific Ha Hb Hstate Hgood ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hbounded
       ltac:(repeat rewrite Nat2Z.inj_add in HindexWord;repeat rewrite Nat2Z.inj_mul in HindexWord;lia))
       as(model & modelReply & target & HmodelBounded & HmodelRun & HmodelStep & HmodelState & Hpost & HmodelSafe).
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
     destruct Hpost as(Hio & HmodelTop & HmodelGood & Hprefix & Hclasses & Hhistory & Hbindings & Hschemas & Hgrowth).
     pose proof(binary_growth _ native logical target a b formula_cap Hgrowth HformulaCap
       (fun ca cb Ha Hb=>equal_cost native logical a b ca cb formula_cap Hstate Hgood Hfalse HformulaCap Ha Hb)) as HformGrowth.
     pose proof(NativeBasicCommandInvariant.same_formula_count _ _ _ Hnext (NativeState.formula_representation _ _ HmodelState)) as HfEqual.
     pose proof(class_count_transfer final target next HmodelState Hnext) as HcEqual.
     unfold primitive_post,formula_target,index_target;cbn [Protocol.opcode]. split;[lia|]. split.
     * eapply bounded_transfer;[exact HmodelState|exact Hnext|exact HnextTop|exact HmodelBounded].
     * rewrite <-HcEqual,Hclasses;lia.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|a' values Ha Hrest];subst a' values.
     inversion Hrest as [|b' values Hb Hnil];subst b' values.
     change(meta_value native 15=57) in Hpending. rewrite(NativeFullDispatcher.binary_rest 8 a b tail ltac:(tauto)) in Hinput.
     change(Z.of_nat (2*index_cap+3)<=maximum) in HindexWord.
     destruct(NativeClassAdvancedIndexInvariant.Member.generated_total_protocol 56 [] native logical bs ns a b 32 32 10 tail index_cap observations
       eq_refl Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hspecific Ha Hb Hstate Hgood ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hbounded
       ltac:(repeat rewrite Nat2Z.inj_add in HindexWord;repeat rewrite Nat2Z.inj_mul in HindexWord;lia))
       as(model & modelReply & target & HmodelBounded & HmodelRun & HmodelStep & HmodelState & Hpost & HmodelSafe).
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
     destruct Hpost as(Hio & HmodelTop & HmodelGood & Hprefix & Hclasses & Hhistory & Hbindings & Hschemas & Hgrowth).
     pose proof(binary_growth _ native logical target a b formula_cap Hgrowth HformulaCap
       (fun ca cb Ha Hb=>member_cost native logical a b ca cb formula_cap Hstate Hgood Hfalse HformulaCap Ha Hb)) as HformGrowth.
     pose proof(NativeBasicCommandInvariant.same_formula_count _ _ _ Hnext (NativeState.formula_representation _ _ HmodelState)) as HfEqual.
     pose proof(class_count_transfer final target next HmodelState Hnext) as HcEqual.
     unfold primitive_post,formula_target,index_target;cbn [Protocol.opcode]. split;[lia|]. split.
     * eapply bounded_transfer;[exact HmodelState|exact Hnext|exact HnextTop|exact HmodelBounded].
     * rewrite <-HcEqual,Hclasses;lia.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords,Hargs.
     inversion Hwords as [|tag' values Htag Hrest];subst tag' values.
     inversion Hrest as [|a' values Ha Hrest2];subst a' values.
     inversion Hrest2 as [|b' values Hb Hrest3];subst b' values.
     inversion Hrest3 as [|c' values Hc Hnil];subst c' values.
     inversion Hargs as [|tag' values HtagCap Hargs1];subst tag' values.
     inversion Hargs1 as [|a' values HaCap Hargs2];subst a' values.
     inversion Hargs2 as [|b' values HbCap Hargs3];subst b' values.
     inversion Hargs3 as [|c' values HcCap HargsNil];subst c' values.
     change(meta_value native 15=50) in Hpending. rewrite NativeFullDispatcher.axiom_rest in Hinput.
     change(Z.of_nat(index_cap+3*argument_cap+4)<=maximum) in HindexWord.
     destruct(NativeAxiomIndexInvariant.generated_total native logical bs ns 49 [49] tag a b c 32 32 32 32 10 tail index_cap observations
       eq_refl Hmeta Hsip Htoken Hprint Hpending Herror (NativeBasicDispatcher.history_room _ _ _ HbasicResource) Htag Ha Hb Hc Hstate Htop Hfalse Hgood Hspecific
       ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hbounded
       ltac:(unfold SchemaEvaluationIndexAxiomTagged.ceiling;repeat rewrite Nat2Z.inj_add in *;repeat rewrite Nat2Z.inj_mul in *;lia))
       as(model & modelReply & target & HmodelBounded & HmodelRun & HmodelStep & HmodelState & Hio & HmodelSafe & HmodelTop & HmodelGood & Hprefix & Hgrowth).
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
     pose proof(NativeBasicCommandInvariant.same_formula_count _ _ _ Hnext (NativeState.formula_representation _ _ HmodelState)) as HfEqual.
     assert(HgrowthActual:(length(Protocol.formulas next)<=length(Protocol.formulas logical)+AxiomTaggedInvariant.cost tag a)%nat) by lia.
     pose proof(axiom_growth native logical tag a b c bs ns tail observations final trace next formula_cap ltac:(lia) Htoken Hprint Hpending Herror
       Htag Ha Hb Hc Hstate Hnext Hfalse HformulaCap Hinput Hrun HgrowthActual) as HformGrowth.
     pose proof(NativeGeneralCommandInvariant.axiom_class_count native logical(Protocol.Req 11[tag;a;b;c][])bs ns tail observations final trace next
       ltac:(split;[exact Hwords|split;reflexivity]) eq_refl ltac:(lia) Htoken Hpending Herror
       ltac:(rewrite NativeFullDispatcher.axiom_rest;exact Hinput) Hrun Hstate Hnext) as HclassEqual.
     unfold primitive_post,formula_target,index_target;cbn [Protocol.opcode Protocol.arguments]. split;[exact HformGrowth|]. split.
     * eapply SchemaEvaluationIndexCell.bounded_mono;[|eapply bounded_transfer;[exact HmodelState|exact Hnext|exact HnextTop|exact HmodelBounded]].
       unfold SchemaEvaluationIndexAxiomTagged.ceiling;lia.
     * lia.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hfields.
     destruct Hfields as [Hlen Hname]. inversion Hwords as [|tid' values Htid Hnil];subst tid' values.
     change(meta_value native 15=50) in Hpending. rewrite NativeFullDispatcher.certify_rest in Hinput.
     change(Z.of_nat(index_cap+2)<=maximum) in HindexWord.
     destruct(NativeCertifyIndexInvariant.generated_total native logical bs ns name tid 32 32 10 tail 0 index_cap observations
       Hmeta Hsip Htoken Hprint Hpending Herror Hname Htid Hstate Htop Hfalse Hgood Hunique HnamesValid HhistoryValid Hspecific
       ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hbounded ltac:(rewrite Nat2Z.inj_add in HindexWord;lia))
       as(model & modelReply & target & HmodelBounded & Hcomplete).
     destruct Hcomplete as(HmodelRun & HmodelStep & HmodelState & Hio & Hmachine & Hnames & Hhistory & Hunique' & Hclasses & HhistorySame & Hschemas & Hprefix & HmodelSafe & Hgrowth).
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
     pose proof(certify_cost native logical name tid formula_cap Hstate Hgood Hfalse HformulaCap) as Hcost.
     pose proof(NativeBasicCommandInvariant.same_formula_count _ _ _ Hnext (NativeState.formula_representation _ _ HmodelState)) as HfEqual.
     pose proof(class_count_transfer final target next HmodelState Hnext) as HcEqual.
     unfold primitive_post,formula_target,index_target;cbn [Protocol.opcode]. split;[lia|]. split.
     * eapply bounded_transfer;[exact HmodelState|exact Hnext|exact HnextTop|exact HmodelBounded].
     * rewrite <-HcEqual,Hclasses;lia.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|kind' values Hkind Hrest];subst kind' values.
     inversion Hrest as [|a' values Ha Hrest2];subst a' values.
     inversion Hrest2 as [|b' values Hb Hrest3];subst b' values.
     inversion Hrest3 as [|c' values Hc Hrest4];subst c' values.
     inversion Hrest4 as [|d' values Hd Hnil];subst d' values.
     change(meta_value native 15=51) in Hpending. rewrite NativeFullDispatcher.node_rest in Hinput.
     destruct(NativeSchemaInvariant.generated_total native logical bs ns 50 [50] kind a b c d 32 32 32 32 32 10 tail observations
       eq_refl Hsafe ltac:(lia) Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd HschemaRoom Hstate Hgood Htop
       ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
       as(model & modelReply & target & Hcomplete & HmodelGood & HmodelTop & HformSame & HclassSame & Hgrowth).
     destruct Hcomplete as(Hchecked & HmodelState & Hio & Hunchanged & Houtcome).
     destruct Hchecked as(HmodelRun & Hrest').
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
     pose proof(NativeBasicCommandInvariant.same_formula_count _ _ _ Hnext (NativeState.formula_representation _ _ HmodelState)) as HfEqual.
     pose proof(class_count_transfer final target next HmodelState Hnext) as HcEqual.
     assert(HmodelBounded:SchemaEvaluationIndexCell.bounded final(Protocol.formulas target)(Protocol.classes target)index_cap).
     { split.
       - apply Bounds.canonical_formulas_raw;[exact(NativeState.formula_representation _ _ HmodelState)|]. rewrite HformSame.
         exact(Bounds.canonical_raw_formulas native _ index_cap (NativeState.formula_representation _ _ Hstate) Htop (proj1 Hbounded)).
       - rewrite HclassSame. exact(proj2 Hbounded). }
     unfold primitive_post,formula_target,index_target;cbn [Protocol.opcode]. split;[lia|]. split.
     * eapply bounded_transfer;[exact HmodelState|exact Hnext|exact HnextTop|exact HmodelBounded].
     * rewrite <-HcEqual,HclassSame;lia.
Qed.

Definition formula_end request capacity expression_cap :=
 if Nat.eqb(Protocol.opcode request)24 then SchemaUniformBudget.formula_after capacity(SchemaUniformBudget.slots expression_cap)
 else formula_target request capacity.
Definition index_end request bound argument_cap expression_cap :=
 if Nat.eqb(Protocol.opcode request)24 then SchemaUniformBudget.index_after expression_cap argument_cap bound(SchemaUniformBudget.slots expression_cap)
 else index_target request bound argument_cap.
Definition class_end request capacity expression_cap :=
 if Nat.eqb(Protocol.opcode request)24 then (capacity+SchemaUniformBudget.slots expression_cap)%nat else S capacity.
Definition expression_end request capacity := if Nat.eqb(Protocol.opcode request)22 then S capacity else capacity.
Record arithmetic (native:Machine) logical request formula_cap index_cap class_cap expression_cap argument_cap : Prop := Arithmetic {
 formulas_fit : (length(Protocol.formulas logical)<=formula_cap)%nat;
 classes_fit : (length(Protocol.classes logical)<=class_cap)%nat;
 expressions_fit : (length(Protocol.expressions logical)<=expression_cap)%nat;
 indices_fit : SchemaEvaluationIndexCell.bounded native(Protocol.formulas logical)(Protocol.classes logical)index_cap;
 arguments_fit : Forall(fun value=>(value<=argument_cap)%nat)(Protocol.arguments request);
 index_word : Z.of_nat(index_end request index_cap argument_cap expression_cap)<=maximum;
 instance_budget : Protocol.opcode request=24%nat -> NativeSchemaUniformBoundary.budget native logical expression_cap argument_cap formula_cap index_cap class_cap
}.
Definition quantitative final next request formula_cap index_cap class_cap expression_cap argument_cap :=
 (length(Protocol.formulas next)<=formula_end request formula_cap expression_cap)%nat /\
 SchemaEvaluationIndexCell.bounded final(Protocol.formulas next)(Protocol.classes next)(index_end request index_cap argument_cap expression_cap) /\
 (length(Protocol.classes next)<=class_end request class_cap expression_cap)%nat /\
 (length(Protocol.expressions next)<=expression_end request expression_cap)%nat.
Lemma expression_bound logical request reply next cap : Protocol.step logical request reply next ->
 (length(Protocol.expressions logical)<=cap)%nat ->
 (length(Protocol.expressions next)<=expression_end request cap)%nat.
Proof.
 intros Hstep Hcap. unfold expression_end. destruct(Nat.eqb(Protocol.opcode request)22) eqn:Hnode.
 - destruct(LogicalRegistryBounds.step_counts _ _ _ _ Hstep) as [Hb [Hh He]]. lia.
 - apply Nat.eqb_neq in Hnode. now rewrite(SchemaProtocolFrame.step_expressions _ _ _ _ Hstep Hnode).
Qed.
Theorem preserves native logical request bs ns tail observations final trace reply next formula_cap index_cap class_cap expression_cap argument_cap :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat -> (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> LogicalRegistryBounds.unique logical -> NativeGeneralDispatcher.resources native logical request ->
 arithmetic native logical request formula_cap index_cap class_cap expression_cap argument_cap ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 Protocol.step logical request reply next -> NativeState.represents final next ->
 FormulaTopology.ordered final(length(Protocol.formulas next)) ->
 quantitative final next request formula_cap index_cap class_cap expression_cap argument_cap.
Proof.
 intros Hshape Hrange Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hresource
   [HF HC HE Hbounded Hargs HindexWord Hinstance] Hinput Hrun Hstep Hnext HnextTop.
 pose proof(expression_bound logical request reply next expression_cap Hstep HE) as HnextExpressions.
 destruct(Nat.eq_dec(Protocol.opcode request)24%nat) as [H24|H24].
 - pose proof(Hinstance H24) as Hbudget.
   destruct request as [opcode ids name]. cbn [Protocol.opcode] in H24. subst opcode.
   destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hfields.
   destruct Hfields as [Hname Hlength]. change(meta_value native 15=51) in Hpending.
   rewrite NativeFullDispatcher.instance_rest in Hinput.
   destruct(NativeSchemaUniformBoundary.generated_canonical expression_cap argument_cap formula_cap index_cap class_cap native bs ns logical ids name tail observations
     Hmeta Htoken Hsip Hprint Hpending Herror Hname Hwords Hlength Hinput Hstate Hgood Htop Hfalse Hsafe Hbudget)
     as(model & modelReply & target & HmodelRun & HmodelStep & HmodelState & Hclear & HmodelSafe & Hio & HmodelGood & HmodelTop & Hprefix & HclassPrefix & Hword & Hpost).
   assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
   destruct Hpost as(HformGrowth & HclassGrowth & HmodelBounded & HnativeClassGrowth).
   pose proof(NativeBasicCommandInvariant.same_formula_count _ _ _ Hnext (NativeState.formula_representation _ _ HmodelState)) as HfEqual.
   pose proof(class_count_transfer final target next HmodelState Hnext) as HcEqual.
   unfold quantitative,formula_end,index_end,class_end;cbn [Protocol.opcode Nat.eqb]. split;[lia|]. split.
   + eapply bounded_transfer;[exact HmodelState|exact Hnext|exact HnextTop|exact HmodelBounded].
   + split;[lia|exact HnextExpressions].
 - destruct(primitive_preserves native logical request bs ns tail observations final trace reply next formula_cap index_cap class_cap argument_cap
     Hshape Hrange H24 Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hresource Hbounded HF HC Hargs
     ltac:(unfold index_end in HindexWord;assert(Htest:Nat.eqb(Protocol.opcode request)24=false) by (apply Nat.eqb_neq;exact H24);rewrite Htest in HindexWord;exact HindexWord)
     Hinput Hrun Hstep Hnext HnextTop) as(Hforms & Hindices & Hclasses).
   unfold quantitative,formula_end,index_end,class_end. assert(Htest:Nat.eqb(Protocol.opcode request)24=false) by (apply Nat.eqb_neq;exact H24). rewrite Htest. split;[exact Hforms|]. split;[exact Hindices|]. split;[exact Hclasses|exact HnextExpressions].
Qed.
Theorem generated_canonical native logical request bs ns tail observations formula_cap index_cap class_cap expression_cap argument_cap :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat -> (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> LogicalRegistryBounds.unique logical -> NativeGeneralDispatcher.resources native logical request ->
 NativeNameCompact.compact native logical -> arithmetic native logical request formula_cap index_cap class_cap expression_cap argument_cap ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 exists final reply next,
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical request reply next /\ NativeState.represents final next /\ NativeCommandBoundary.io native final reply tail /\
 NativeGeneralCommandInvariant.post native logical final next /\ quantitative final next request formula_cap index_cap class_cap expression_cap argument_cap.
Proof.
 intros Hshape Hrange Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hresource Hcompact Hcaps Hinput.
 destruct(NativeGeneralCommandInvariant.generated_canonical native logical request bs ns tail observations Hshape Hrange Hmeta Hsip Htoken Hprint
 Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hcompact Hresource Hinput)
 as(final & reply & next & Hrun & Hstep & Hnext & Hio & Hpost).
 pose proof Hpost as(Hsafe' & Htop' & Hrest).
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hnext|]. split;[exact Hio|].
 split;[exact Hpost|]. eapply preserves;eassumption.
Qed.
End NativeUniformCommand.
