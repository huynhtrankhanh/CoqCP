From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Guarantees.
From NativeProof Require Import Index SipHash DecimalInput TokenByte NativeState NativeBasicDispatcher NativeCommandBoundary
 NativeClassBinaryBoundary RenameMemoClassEqual RenameMemoClassMember RenameMemoResourceBounds FormulaTopology ClassLookup
 NativeAxiomTotal NativeClassCertifyBoundary ClassCertifyTotal NativeSchemaBoundary SchemaNodeTotal
 NativeSchemaInstanceBoundary SchemaInstanceCommand LogicalNames LogicalHistory.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeFullDispatcher.
Import IndexExecution SipHashExecution.
Definition binary_resources (ready:Machine->list SetTheory.formula->nat->nat->VirtualClasses.class->VirtualClasses.class->Prop) (work:Machine->nat->nat->VirtualClasses.class->VirtualClasses.class->nat) native logical a b := forall ca cb,
 Protocol.class_at logical a=Some ca -> Protocol.class_at logical b=Some cb ->
 ready native (Protocol.formulas logical) a b ca cb /\
 Z.of_nat(length (Protocol.formulas logical)+work native a b ca cb)<=RenameMemoResourceBounds.doubling_limit.
(** Every clause is a pure capacity/readiness proposition. In particular the
    schema clause quantifies over parser frames without assuming execution. *)
Definition specific_resources native logical request :=
 match Protocol.opcode request,Protocol.arguments request with
 | 7%nat,[a;b] => binary_resources RenameMemoClassEqual.ready RenameMemoClassEqual.work native logical a b
 | 8%nat,[a;b] => binary_resources RenameMemoClassMember.ready RenameMemoClassMember.work native logical a b
 | 11%nat,[tag;a;b;c] => NativeAxiomTotal.resources logical tag a b c
 | 14%nat,[tid] => ClassCertifyTotal.capacity native logical (Protocol.object_name request) tid 0
 | 24%nat,ids => forall bs ns tail,SchemaInstanceCommand.resources native bs ns logical ids (Protocol.object_name request) tail
 | _,_ => True end.
Record resources native logical request : Prop := Resources {
 basic_resources : NativeBasicDispatcher.resources native logical request;
 schema_room : Z.of_nat(length (Protocol.expressions logical))<maximum;
 command_resources : specific_resources native logical request
}.
Inductive extra_form : Protocol.request -> Prop :=
 | extra_equal a b : extra_form (Protocol.Req 7 [a;b] [])
 | extra_member a b : extra_form (Protocol.Req 8 [a;b] [])
 | extra_axiom tag a b c : extra_form (Protocol.Req 11 [tag;a;b;c] [])
 | extra_certify tid name : extra_form (Protocol.Req 14 [tid] name)
 | extra_node kind a b c d : extra_form (Protocol.Req 22 [kind;a;b;c;d] [])
 | extra_instance ids name : extra_form (Protocol.Req 24 ids name).
Lemma shape_extra request : Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 ~NativeBasicDispatcher.supported (Protocol.opcode request) -> extra_form request.
Proof.
 destruct request as [opcode values name]. intros [Hwords Hshape] Hbound Hnot.
 cbn [Protocol.opcode] in Hnot,Hbound.
 let rec cases count index := lazymatch count with O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 27%nat opcode.
 all:try lia.
 all:try (exfalso;apply Hnot;unfold NativeBasicDispatcher.supported,NativeBasicDispatcher.two,NativeBasicDispatcher.one,NativeBasicDispatcher.zero,NativeBasicDispatcher.named,NativeBasicDispatcher.query;tauto).
 all:cbn [Protocol.arguments Protocol.object_name] in Hshape.
 - destruct Hshape as [Hlen ->]. destruct values as [|a [|b [|bad values]]];cbn [length] in Hlen;try lia. constructor.
 - destruct Hshape as [Hlen ->]. destruct values as [|a [|b [|bad values]]];cbn [length] in Hlen;try lia. constructor.
 - destruct Hshape as [Hlen ->]. destruct values as [|tag [|a [|b [|c [|bad values]]]]];cbn [length] in Hlen;try lia. constructor.
 - destruct Hshape as [Hlen Hname]. destruct values as [|tid [|bad values]];cbn [length] in Hlen;try lia. constructor.
 - destruct Hshape as [Hlen ->]. destruct values as [|kind [|a [|b [|c [|d [|bad values]]]]]];cbn [length] in Hlen;try lia. constructor.
 - constructor.
Qed.
Lemma supported_dec opcode : {NativeBasicDispatcher.supported opcode}+{~NativeBasicDispatcher.supported opcode}.
Proof. unfold NativeBasicDispatcher.supported,NativeBasicDispatcher.two,NativeBasicDispatcher.one,NativeBasicDispatcher.zero,NativeBasicDispatcher.named,NativeBasicDispatcher.query. solve_decision. Defined.
Lemma binary_rest opcode a b tail : (opcode=7%nat \/ opcode=8%nat) ->
 NativeBasicDispatcher.rest (Protocol.Req opcode [a;b] [])++tail=32::decimalBytes a++32::decimalBytes b++10::tail.
Proof.
 intros [->| ->];unfold NativeBasicDispatcher.rest,Protocol.request_bytes,Protocol.number_tokens;
 cbn [Protocol.opcode Protocol.arguments Protocol.object_name map Protocol.join_tokens];NativeBasicDispatcher.opcode_digits;
 cbn [List.tl List.app Protocol.join_tokens];repeat first [progress rewrite <-app_assoc|progress cbn [List.app]];reflexivity.
Qed.
Lemma axiom_rest tag a b c tail : NativeBasicDispatcher.rest (Protocol.Req 11 [tag;a;b;c] [])++tail=
 49::32::decimalBytes tag++32::decimalBytes a++32::decimalBytes b++32::decimalBytes c++10::tail.
Proof. unfold NativeBasicDispatcher.rest,Protocol.request_bytes,Protocol.number_tokens;
 cbn [Protocol.opcode Protocol.arguments Protocol.object_name map Protocol.join_tokens];NativeBasicDispatcher.opcode_digits;
 cbn [List.tl List.app Protocol.join_tokens];repeat first [progress rewrite <-app_assoc|progress cbn [List.app]];reflexivity. Qed.
Lemma certify_rest tid name tail : NativeBasicDispatcher.rest (Protocol.Req 14 [tid] name)++tail=
 52::32::name++32::decimalBytes tid++10::tail.
Proof. unfold NativeBasicDispatcher.rest,Protocol.request_bytes,Protocol.number_tokens;
 cbn [Protocol.opcode Protocol.arguments Protocol.object_name map Protocol.join_tokens];NativeBasicDispatcher.opcode_digits;
 cbn [List.tl List.app Protocol.join_tokens];repeat first [progress rewrite <-app_assoc|progress cbn [List.app]];reflexivity. Qed.
Lemma node_rest kind a b c d tail : NativeBasicDispatcher.rest (Protocol.Req 22 [kind;a;b;c;d] [])++tail=
 50::32::decimalBytes kind++32::decimalBytes a++32::decimalBytes b++32::decimalBytes c++32::decimalBytes d++10::tail.
Proof. unfold NativeBasicDispatcher.rest,Protocol.request_bytes,Protocol.number_tokens;
 cbn [Protocol.opcode Protocol.arguments Protocol.object_name map Protocol.join_tokens];NativeBasicDispatcher.opcode_digits;
 cbn [List.tl List.app Protocol.join_tokens];repeat first [progress rewrite <-app_assoc|progress cbn [List.app]];reflexivity. Qed.
Lemma instance_rest ids name tail : NativeBasicDispatcher.rest (Protocol.Req 24 ids name)++tail=
 52::32::SchemaInstanceCommand.payload ids name tail.
Proof.
 pose proof (f_equal (@List.tl Z) (SchemaInstanceCommand.canonical_wire ids name tail)) as Hwire.
 cbn [List.tl] in Hwire. rewrite Hwire. unfold NativeBasicDispatcher.rest.
 destruct (NativeBasicDispatcher.request_prefix (Protocol.Req 24 ids name)) as [suffix Hprefix].
 change (Protocol.request_bytes (Protocol.Req 24 ids name)=[50;52]++suffix) in Hprefix.
 rewrite Hprefix. reflexivity.
Qed.
Lemma request_encoding request : (1<=Protocol.opcode request<=26)%nat ->
 Protocol.request_bytes request=NativeBasicDispatcher.first (Protocol.opcode request)::NativeBasicDispatcher.rest request /\
 0<=NativeBasicDispatcher.first (Protocol.opcode request)<256.
Proof.
 intro Hbound.
 destruct (DecimalInput.decimal_word (Protocol.opcode request) ltac:(unfold maximum;lia)) as [_ [Hdigits Hlength]].
 destruct (NativeBasicDispatcher.request_prefix request) as [suffix Hprefix].
 destruct (decimalBytes (Protocol.opcode request)) as [|ch chars] eqn:Hdecimal;[cbn [length] in Hlength;lia|].
 inversion Hdigits as [|ch' chars' Hbyte Hrest];subst ch' chars'.
 unfold NativeBasicDispatcher.first,NativeBasicDispatcher.rest. rewrite Hdecimal,Hprefix.
 cbn [List.app List.hd List.tl]. split;[reflexivity|lia].
Qed.
Theorem generated_canonical native logical request bs ns tail observations :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 (31<length (memory native arraydef_0__meta))%nat -> (0<length (memory native arraydef_0__sipState))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat -> (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first (Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical ->
 FormulaTopology.ordered native (length (Protocol.formulas logical)) ->
 nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity -> ClassLookup.wellformed native ->
 NoDup (map fst (Protocol.bindings logical)) -> resources native logical request ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 NativeBasicDispatcher.checked native logical request bs ns tail observations.
Proof.
 intros Hshape Hbound Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hresources Hinput.
 destruct Hresources as [Hbasic Hschema Hspecific].
 destruct (supported_dec (Protocol.opcode request)) as [Hsupported|Hnot].
 - exact (NativeBasicDispatcher.generated_canonical native logical request bs ns tail observations Hshape Hsupported
     ltac:(lia) Htoken Hprint Hpending Herror Hstate Hsafe Hbasic Hinput).
 - pose proof (NativeBasicDispatcher.safe_history logical Hsafe) as HhistoryValid.
   pose proof (NativeBasicDispatcher.safe_names logical Hsafe) as HnamesValid.
   destruct Hbasic as [HformulaRoom HclassRoom HhistoryRoom HbindingRoom HnameRoom].
   destruct (shape_extra request Hshape Hbound Hnot) as [a b|a b|tag a b c|tid name|kind a b c d|ids name].
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|a' values Ha Hvalues];subst a' values.
     inversion Hvalues as [|b' values Hb Hnil];subst b' values.
     change (meta_value native 15=56) in Hpending. rewrite (binary_rest 7 a b tail ltac:(tauto)) in Hinput.
     destruct (NativeClassBinaryBoundary.Equal.generated_total_protocol 55 [] native logical bs ns a b 32 32 10 tail observations
       eq_refl Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hspecific Ha Hb Hstate Hgood ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hpost & Hsafe').
     eapply NativeBasicDispatcher.finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact (proj1 Hpost)].
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|a' values Ha Hvalues];subst a' values.
     inversion Hvalues as [|b' values Hb Hnil];subst b' values.
     change (meta_value native 15=57) in Hpending. rewrite (binary_rest 8 a b tail ltac:(tauto)) in Hinput.
     destruct (NativeClassBinaryBoundary.Member.generated_total_protocol 56 [] native logical bs ns a b 32 32 10 tail observations
       eq_refl Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hspecific Ha Hb Hstate Hgood ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hpost & Hsafe').
     eapply NativeBasicDispatcher.finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact (proj1 Hpost)].
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|tag' values Htag Hrest];subst tag' values.
     inversion Hrest as [|a' values Ha Hrest2];subst a' values.
     inversion Hrest2 as [|b' values Hb Hrest3];subst b' values.
     inversion Hrest3 as [|c' values Hc Hnil];subst c' values.
     change (meta_value native 15=50) in Hpending. rewrite axiom_rest in Hinput.
     destruct (NativeAxiomTotal.generated_total native logical bs ns 49 [49] tag a b c 32 32 32 32 10 tail observations
       eq_refl Hmeta Hsip Htoken Hprint Hpending Herror HhistoryRoom Htag Ha Hb Hc Hstate Htop Hfalse Hspecific
       ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hio & Hsafe').
     eapply NativeBasicDispatcher.finish;eassumption.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hfields.
     destruct Hfields as [Hlen Hname]. inversion Hwords as [|tid' values Htid Hnil];subst tid' values.
     change (meta_value native 15=50) in Hpending. rewrite certify_rest in Hinput.
     destruct (NativeClassCertifyBoundary.generated_total native logical bs ns name tid 32 32 10 tail 0 observations
       Hmeta Hsip Htoken Hprint Hpending Herror Hname Htid Hstate Htop Hfalse Hgood Hunique HnamesValid HhistoryValid Hspecific
       ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hcomplete).
     destruct Hcomplete as (Hrun & Hstep & Hnext & Hio & Hrest).
     eapply NativeBasicDispatcher.finish;eassumption.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
     inversion Hwords as [|kind' values Hkind Hrest];subst kind' values.
     inversion Hrest as [|a' values Ha Hrest2];subst a' values.
     inversion Hrest2 as [|b' values Hb Hrest3];subst b' values.
     inversion Hrest3 as [|c' values Hc Hrest4];subst c' values.
     inversion Hrest4 as [|d' values Hd Hnil];subst d' values.
     change (meta_value native 15=51) in Hpending. rewrite node_rest in Hinput.
     destruct (NativeSchemaBoundary.generated_total native logical bs ns 50 [50] kind a b c d 32 32 32 32 32 10 tail observations
       eq_refl Hsafe ltac:(lia) Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hschema Hstate
       ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hchecked & Hnext & Hio & Hremaining).
     destruct Hchecked as (Hrun & Hstep & Hrest').
     eapply NativeBasicDispatcher.finish;eassumption.
   + destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hfields.
     destruct Hfields as [Hname Hlength].
     change (meta_value native 15=51) in Hpending. rewrite instance_rest in Hinput.
     destruct (NativeSchemaInstanceBoundary.generated_canonical native bs ns logical ids name tail observations
       Hmeta Htoken Hsip Hprint Hpending Herror Hname Hwords Hlength Hinput Hstate Hgood Htop Hfalse Hsafe (Hspecific bs ns tail))
     as (final & reply & next & Hrun & Hstep & Hnext & Hclear & Hsafe' & Hio).
     eapply NativeBasicDispatcher.finish;eassumption.
Qed.
End NativeFullDispatcher.
