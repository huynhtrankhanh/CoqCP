From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import VirtualClasses Protocol.
From NativeProof Require Import Index SipHash NativeState NativeBasicDispatcher NativeBasicInvariant NativeBasicCommandInvariant
 NativeGeneralCommandInvariant NativeSchemaInvariant NativeFullDispatcher NativeClassCommands ClassSetInput ClassStorage
 SchemaEvaluationSetCell LogicalStorageMonotone CommandInput ReadOne TokenByte Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSetClassInvariant.
Import IndexExecution SipHashExecution.
Definition raw_sets (native:Machine) := Forall(fun raw:Z*Z=>fst raw=0)(memory native arraydef_0__classes).
Lemma represented_raw native fs classes : ClassStorage.represents native fs classes -> SchemaEvaluationSetCell.sets classes -> raw_sets native.
Proof.
 intros [_ Hrep] Hsets. unfold raw_sets. induction Hrep as [|[tag value] cls raws classes Hdecode Hrep IH] in Hsets|-*;[constructor|].
 inversion Hsets as [|head tail Hhead Htail];subst head tail. constructor;[|now apply IH].
 destruct Hhead as [variable ->]. unfold ClassStorage.decode in Hdecode.
 destruct(Z.eq_dec tag 0) as [->|Hnot];[reflexivity|].
 destruct(Z.eq_dec tag 1);[destruct(nth_error fs(Z.to_nat value))|];discriminate.
Qed.
Lemma raw_represented native fs classes : ClassStorage.represents native fs classes -> raw_sets native -> SchemaEvaluationSetCell.sets classes.
Proof.
 intros [_ Hrep] Hraw. unfold raw_sets in Hraw. induction Hrep as [|[tag value] cls raws classes Hdecode Hrep IH] in Hraw|-*;[constructor|].
 inversion Hraw as [|head tail Htag Htail];subst head tail. constructor;[|now apply IH].
 cbn [fst] in Htag. subst tag. change(Some(VirtualClasses.set(Z.to_nat value))=Some cls) in Hdecode.
 injection Hdecode as <-. now exists(Z.to_nat value).
Qed.
Lemma array_transport before after fs next classes next_classes :
 ClassStorage.represents before fs classes -> ClassStorage.represents after next next_classes ->
 memory after arraydef_0__classes=memory before arraydef_0__classes ->
 SchemaEvaluationSetCell.sets classes -> SchemaEvaluationSetCell.sets next_classes.
Proof.
 intros Hbefore Hafter Harray Hsets. apply(raw_represented after next next_classes Hafter).
 unfold raw_sets. rewrite Harray. exact(represented_raw before fs classes Hbefore Hsets).
Qed.
Lemma prefix_same {A} (before after:list A) : (exists extra,after=before++extra) -> length after=length before -> after=before.
Proof.
 intros [extra Hextra] Hlength. rewrite Hextra,length_app in Hlength. assert(Hnil:length extra=0%nat) by lia.
 apply length_zero_iff_nil in Hnil. subst extra. now rewrite app_nil_r in Hextra.
Qed.
Lemma set_result native fs classes value sep tail : ClassStorage.represents native fs classes -> SchemaEvaluationSetCell.sets classes ->
 raw_sets(ClassSetInput.result native(length classes)value sep tail).
Proof.
 intros Hclasses Hsets. unfold raw_sets,ClassSetInput.result.
 rewrite ClassStorage.result_classes,ClassStorage.written_app.
 - rewrite ClassSetInput.argument_other by discriminate. apply Forall_app. split;[exact(represented_raw _ _ _ Hclasses Hsets)|].
   constructor;[reflexivity|constructor].
 - rewrite ClassSetInput.argument_other by discriminate. exact(ClassStorage.represents_length _ _ _ Hclasses).
Qed.
Theorem basic native logical request bs ns tail observations final trace next :
 Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) -> Protocol.opcode request<>6%nat ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 Z.of_nat(length(Protocol.classes logical))<maximum ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> NativeState.represents final next ->
 SchemaEvaluationSetCell.sets(Protocol.classes logical) -> SchemaEvaluationSetCell.sets(Protocol.classes next).
Proof.
 intros Hshape Hsupported Hnot6 Hmeta Htoken Hprint Hpending Herror Hroom Hinput Hrun Hstate Hnext Hsets.
 destruct(Nat.eq_dec(Protocol.opcode request)5%nat) as [Hop|Hnot5].
 - destruct request as [opcode args name]. cbn [Protocol.opcode] in Hop. subst opcode.
   destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments Protocol.object_name] in Hfields.
   destruct Hfields as [Hlength ->]. destruct args as [|value [|bad args]];cbn [length] in Hlength;try lia.
   inversion Hwords as [|value' values Hvalue Hnil];subst value' values.
   change(meta_value native 15=54) in Hpending.
   rewrite(NativeBasicDispatcher.one_rest 5%nat value tail ltac:(unfold NativeBasicDispatcher.one;tauto)) in Hinput.
   change(stdin native=32::decimalBytes value++10::tail) in Hinput.
   pose proof(ClassSetInput.generated_pending native bs ns(length(Protocol.classes logical))value 32 10 tail observations
    Hmeta Htoken Hprint Hpending Herror (proj1(NativeState.class_representation _ _ Hstate)) Hroom Hvalue
    ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput) as Hexpected.
   rewrite Hexpected in Hrun. injection Hrun as Hfinal Htrace. subst final.
   apply(raw_represented _ _ _ (NativeState.class_representation _ _ Hnext)).
   exact(set_result native(Protocol.formulas logical)(Protocol.classes logical)value 10 tail (NativeState.class_representation _ _ Hstate) Hsets).
 - apply(array_transport native final(Protocol.formulas logical)(Protocol.formulas next)(Protocol.classes logical)(Protocol.classes next)
    (NativeState.class_representation _ _ Hstate)(NativeState.class_representation _ _ Hnext));[|exact Hsets].
   apply(NativeBasicCommandInvariant.request_array arraydef_0__classes native request bs ns tail observations final trace
    Hshape Hsupported ltac:(unfold NativeBasicInvariant.Arrays.kind;tauto)
    ltac:(unfold NativeBasicInvariant.Arrays.unchanged;repeat split;intros;try discriminate;assumption)
    Hmeta Htoken Hpending Herror Hinput Hrun).
Qed.
Theorem axiom native logical request bs ns tail observations final trace reply next :
 Protocol.shape request -> Protocol.opcode request=11%nat ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> NativeState.represents final next -> Protocol.step logical request reply next ->
 SchemaEvaluationSetCell.sets(Protocol.classes logical) -> SchemaEvaluationSetCell.sets(Protocol.classes next).
Proof.
 intros Hshape Hop Hmeta Htoken Hpending Herror Hinput Hrun Hstate Hnext Hstep Hsets.
 pose proof(NativeGeneralCommandInvariant.axiom_class_count native logical request bs ns tail observations final trace next
  Hshape Hop Hmeta Htoken Hpending Herror Hinput Hrun Hstate Hnext) as Hcount.
 pose proof(LogicalStorageMonotone.classes _ _ (LogicalStorageMonotone.step _ _ _ _ Hstep)) as Hprefix.
 rewrite(prefix_same _ _ Hprefix Hcount). exact Hsets.
Qed.
Theorem node native logical request bs ns tail observations final trace next :
 Protocol.shape request -> Protocol.opcode request=22%nat ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> NativeState.represents final next ->
 SchemaEvaluationSetCell.sets(Protocol.classes logical) -> SchemaEvaluationSetCell.sets(Protocol.classes next).
Proof.
 intros Hshape Hop Hmeta Htoken Hpending Herror Hinput Hrun Hstate Hnext Hsets.
 destruct(NativeGeneralCommandInvariant.request_parts request Hshape ltac:(rewrite Hop;lia)) as(chars & sep & payload & Hencoding & Hsep & Hparts).
 rewrite Hparts,<-app_assoc in Hinput. change(stdin native=chars++sep::(payload++tail)) in Hinput.
 apply(array_transport native final(Protocol.formulas logical)(Protocol.formulas next)(Protocol.classes logical)(Protocol.classes next)
  (NativeState.class_representation _ _ Hstate)(NativeState.class_representation _ _ Hnext));[|exact Hsets].
 exact(NativeSchemaInvariant.canonical_array arraydef_0__classes(Protocol.opcode request) _ chars native bs ns sep(payload++tail)observations final trace
  eq_refl Hop Hop Hencoding Hmeta Htoken Hpending Herror Hsep Hinput Hrun).
Qed.
End NativeSetClassInvariant.
