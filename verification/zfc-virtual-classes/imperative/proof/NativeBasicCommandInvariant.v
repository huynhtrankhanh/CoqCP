From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash DecimalInput TokenByte NativeState NativeBasicDispatcher NativeBasicInvariant NativeBasicCountInvariant
 NativeSimpleCommands NativeSimpleInvariant NativeAllocationInvariant NativeNameGrowth NativeCommandBoundary NativeGeneralizeBoundary NativeTheoremBoundary
 LogicalNames LogicalHistory LogicalStorageMonotone LogicalRegistryBounds Representation ClassStorage ClassLookup FormulaTopology HashTable
 ClassSetInput ClassAbstractInput GeneralizeTotal ArenaFrame ReadOne ReadTwo HistoryRefinement HistoryLookup GeneralizeRefinement CommandGeneralize SemanticFrames ReplyNO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeBasicCommandInvariant.
Import IndexExecution SipHashExecution.
Lemma formula_count native logical : NativeState.represents native logical -> meta_value native 1=Z.of_nat(length(Protocol.formulas logical)).
Proof. intro Hstate. exact (proj1(proj2(proj1(NativeState.formula_representation _ _ Hstate)))). Qed.
Lemma arena_count native fs : NativeRepresentation.canonical_arena native fs -> meta_value native 1=Z.of_nat(length fs).
Proof. intro Harena. exact(proj1(proj2(proj1 Harena))). Qed.
Lemma same_formula_count native logical fs : NativeState.represents native logical -> NativeRepresentation.canonical_arena native fs ->
 length(Protocol.formulas logical)=length fs.
Proof. intros Hstate Harena. pose proof(formula_count _ _ Hstate). pose proof(arena_count _ _ Harena). lia. Qed.
Lemma request_parts request : Protocol.shape request -> NativeBasicDispatcher.supported (Protocol.opcode request) ->
 exists chars sep payload,
 decimalBytes (Protocol.opcode request)=NativeBasicDispatcher.first (Protocol.opcode request)::chars /\
 TokenByteExecution.separator sep /\ NativeBasicDispatcher.rest request=chars++sep::payload.
Proof.
 intros Hshape Hsupported. pose proof(NativeBasicDispatcher.supported_bound _ Hsupported) as Hbound.
 destruct (DecimalInput.decimal_word (Protocol.opcode request) ltac:(unfold maximum;lia)) as [_ [Hdigits Hlength]].
 destruct (decimalBytes (Protocol.opcode request)) as [|ch chars] eqn:Hdecimal;[cbn [length] in Hlength;lia|].
 assert (Hfirst:NativeBasicDispatcher.first (Protocol.opcode request)=ch) by (unfold NativeBasicDispatcher.first;now rewrite Hdecimal).
 assert (Hencoding:decimalBytes (Protocol.opcode request)=NativeBasicDispatcher.first (Protocol.opcode request)::chars) by congruence.
 rewrite Hdecimal in Hencoding. clear Hdigits Hlength Hbound Hfirst.
 destruct (NativeBasicDispatcher.shape_form request Hshape Hsupported) as
 [opcode a b Htag|opcode value Htag|opcode Htag|opcode value name Htag|opcode name Htag];cbn [Protocol.opcode] in Hdecimal,Hencoding.
 - exists chars,32,(decimalBytes a++32::decimalBytes b++[10]). split;[exact Hencoding|]. split;[unfold TokenByteExecution.separator;tauto|].
   pose proof(NativeBasicDispatcher.two_rest opcode a b [] Htag) as Hrest. rewrite app_nil_r,Hdecimal in Hrest. exact Hrest.
 - exists chars,32,(decimalBytes value++[10]). split;[exact Hencoding|]. split;[unfold TokenByteExecution.separator;tauto|].
   pose proof(NativeBasicDispatcher.one_rest opcode value [] Htag) as Hrest. rewrite app_nil_r,Hdecimal in Hrest. exact Hrest.
 - exists chars,10,[]. split;[exact Hencoding|]. split;[unfold TokenByteExecution.separator;tauto|].
   pose proof(NativeBasicDispatcher.zero_rest opcode [] Htag) as Hrest. rewrite app_nil_r,Hdecimal in Hrest. exact Hrest.
 - exists chars,32,(decimalBytes value++32::name++[10]). split;[exact Hencoding|]. split;[unfold TokenByteExecution.separator;tauto|].
   pose proof(NativeBasicDispatcher.named_rest opcode value name [] Htag) as Hrest. rewrite app_nil_r,Hdecimal in Hrest. exact Hrest.
 - exists chars,32,(name++[10]). split;[exact Hencoding|]. split;[unfold TokenByteExecution.separator;tauto|].
   pose proof(NativeBasicDispatcher.query_rest opcode name [] Htag) as Hrest. rewrite app_nil_r,Hdecimal in Hrest. exact Hrest.
Qed.
Lemma request_array watched native request bs ns tail observations final trace :
 Protocol.shape request -> NativeBasicDispatcher.supported (Protocol.opcode request) ->
 NativeBasicInvariant.Arrays.kind watched -> NativeBasicInvariant.Arrays.unchanged (Protocol.opcode request) watched ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 memory final watched=memory native watched.
Proof.
 intros Hshape Hsupported Hkind Hallowed Hmeta Htoken Hpending Herror Hinput Hrun.
 destruct(request_parts request Hshape Hsupported) as (chars & sep & payload & Hencoding & Hsep & Hparts).
 rewrite Hparts,<-app_assoc in Hinput. change(stdin native=chars++sep::(payload++tail)) in Hinput.
 exact(NativeBasicInvariant.canonical_array watched (Protocol.opcode request) _ chars native bs ns sep (payload++tail) observations final trace
 Hkind Hallowed Hsupported Hencoding Hmeta Htoken Hpending Herror Hsep Hinput Hrun).
Qed.
Lemma request_count native request bs ns tail observations final trace :
 Protocol.shape request -> NativeBasicDispatcher.supported (Protocol.opcode request) -> NativeBasicCountInvariant.unchanged (Protocol.opcode request) ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) -> meta_value final 1=meta_value native 1.
Proof.
 intros Hshape Hsupported Hallowed Hmeta Htoken Hpending Herror Hinput Hrun.
 destruct(request_parts request Hshape Hsupported) as (chars & sep & payload & Hencoding & Hsep & Hparts).
 rewrite Hparts,<-app_assoc in Hinput. change(stdin native=chars++sep::(payload++tail)) in Hinput.
 exact(NativeBasicCountInvariant.canonical_count (Protocol.opcode request) _ chars native bs ns sep (payload++tail) observations final trace
 Hallowed Hsupported Hencoding Hmeta Htoken Hpending Herror Hsep Hinput Hrun).
Qed.
Lemma readonly_top native logical request bs ns tail observations final trace next :
 Protocol.shape request -> NativeBasicDispatcher.supported (Protocol.opcode request) -> NativeBasicCountInvariant.unchanged (Protocol.opcode request) ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> NativeState.represents final next ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) ->
 FormulaTopology.ordered final(length(Protocol.formulas next)) /\ length(Protocol.formulas next)=length(Protocol.formulas logical).
Proof.
 intros Hshape Hsupported Hallowed Hmeta Htoken Hpending Herror Hinput Hrun Hstate Hnext Htop.
 pose proof(request_count native request bs ns tail observations final trace Hshape Hsupported Hallowed Hmeta Htoken Hpending Herror Hinput Hrun) as Hcount.
 pose proof(formula_count _ _ Hstate) as Hbefore. pose proof(formula_count _ _ Hnext) as Hafter.
 assert(Hlength:length(Protocol.formulas next)=length(Protocol.formulas logical)) by lia. split;[|exact Hlength].
 rewrite Hlength. eapply NativeSimpleInvariant.storage_top;[|exact Htop].
 eapply request_array;try eassumption.
 - unfold NativeBasicInvariant.Arrays.kind;tauto.
 - unfold NativeBasicInvariant.Arrays.unchanged,NativeBasicCountInvariant.unchanged in *;intuition congruence.
Qed.

Lemma class_count native logical : NativeState.represents native logical ->
 length(memory native arraydef_0__classes)=length(Protocol.classes logical).
Proof. intro Hstate. apply (ClassStorage.represents_length _ _ _ (NativeState.class_representation _ _ Hstate)). Qed.
Lemma class_model native logical final next : NativeState.represents native logical -> NativeState.represents final next ->
 (length(memory final arraydef_0__classes)<=S(length(memory native arraydef_0__classes)))%nat ->
 (length(Protocol.classes next)<=S(length(Protocol.classes logical)))%nat.
Proof. intros Hstate Hnext Hlength. rewrite <-(class_count _ _ Hstate),<-(class_count _ _ Hnext). exact Hlength. Qed.
Lemma class_post native logical request bs ns tail observations final trace next :
 Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 Z.of_nat(length(Protocol.classes logical))<maximum ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> NativeState.represents final next -> ClassLookup.wellformed native ->
 ClassLookup.wellformed final /\ (length(Protocol.classes next)<=S(length(Protocol.classes logical)))%nat.
Proof.
 intros Hshape Hsupported Hmeta Htoken Hprint Hpending Herror Hroom Hinput Hrun Hstate Hnext Hgood.
 destruct(Nat.eq_dec (Protocol.opcode request) 5%nat) as [H5|H5].
 - destruct request as [opcode values name]. cbn [Protocol.opcode] in H5. subst opcode.
   destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname. subst name.
   destruct values as [|value [|bad values]];cbn [length] in Hlen;try lia.
   inversion Hwords as [|value' values Hvalue Hnil];subst value' values.
   change(meta_value native 15=54) in Hpending.
   rewrite(NativeBasicDispatcher.one_rest 5 value tail ltac:(unfold NativeBasicDispatcher.one;tauto)) in Hinput.
   change(stdin native=32::decimalBytes value++10::tail) in Hinput.
   pose proof(ClassSetInput.generated_pending native bs ns (length(Protocol.classes logical)) value 32 10 tail observations
    Hmeta Htoken Hprint Hpending Herror (proj1(NativeState.class_representation _ _ Hstate)) Hroom Hvalue
    ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput) as Hmodel.
   assert(Hsame:final=ClassSetInput.result native (length(Protocol.classes logical)) value 10 tail) by (rewrite Hrun in Hmodel;congruence).
   split.
   + rewrite Hsame. exact(NativeAllocationInvariant.set_good native _ _ value 10 tail (NativeState.class_representation _ _ Hstate) Hgood Hvalue).
   + eapply class_model;[exact Hstate|exact Hnext|]. rewrite Hsame.
     unfold ClassSetInput.result. rewrite ClassStorage.result_classes,ClassStorage.written_app.
     * rewrite ClassSetInput.argument_other by discriminate. rewrite length_app;cbn [length];lia.
     * rewrite ClassSetInput.argument_other by discriminate. exact(class_count _ _ Hstate).
 - destruct(Nat.eq_dec (Protocol.opcode request) 6%nat) as [H6|H6].
   + destruct request as [opcode values name]. cbn [Protocol.opcode] in H6. subst opcode.
     destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname. subst name.
     destruct values as [|value [|bad values]];cbn [length] in Hlen;try lia.
     inversion Hwords as [|value' values Hvalue Hnil];subst value' values.
     change(meta_value native 15=55) in Hpending.
     rewrite(NativeBasicDispatcher.one_rest 6 value tail ltac:(unfold NativeBasicDispatcher.one;tauto)) in Hinput.
     change(stdin native=32::decimalBytes value++10::tail) in Hinput.
     pose proof(formula_count _ _ Hstate) as Hcount.
     destruct(Protocol.formula_at logical value) as [p|] eqn:Hlookup.
     * assert(Hreference:Z.of_nat value<meta_value native 1).
       { unfold Protocol.formula_at in Hlookup. assert(value<length(Protocol.formulas logical))%nat by (apply nth_error_Some;congruence). lia. }
       pose proof(ClassAbstractInput.generated_pending native bs ns (length(Protocol.classes logical)) value 32 10 tail observations
        Hmeta Htoken Hprint Hpending Herror (proj1(NativeState.class_representation _ _ Hstate)) Hroom Hvalue Hreference
        ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput) as Hmodel.
       assert(Hsame:final=ClassAbstractInput.result native (length(Protocol.classes logical)) value 10 tail) by (rewrite Hrun in Hmodel;congruence).
       split.
       -- rewrite Hsame. exact(NativeAllocationInvariant.abstract_good native _ _ value 10 tail (NativeState.class_representation _ _ Hstate) Hgood Hvalue).
       -- eapply class_model;[exact Hstate|exact Hnext|]. rewrite Hsame.
          unfold ClassAbstractInput.result,ClassAbstractInput.argument_state. rewrite ClassStorage.result_classes,ClassStorage.written_app.
          ++ rewrite ReadOne.argument_other by discriminate. rewrite length_app;cbn [length];lia.
          ++ rewrite ReadOne.argument_other by discriminate. exact(class_count _ _ Hstate).
     * assert(Hreference:meta_value native 1<=Z.of_nat value).
       { unfold Protocol.formula_at in Hlookup. apply nth_error_None in Hlookup. lia. }
       pose proof(ClassAbstractInput.generated_rejected native bs ns value 32 10 tail observations
        Hmeta Htoken Hprint Hpending Herror Hvalue Hreference
        ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput) as Hmodel.
       assert(Hsame:final=ClassAbstractInput.rejected native value 10 tail) by (rewrite Hrun in Hmodel;congruence).
       assert(Hraw:memory final arraydef_0__classes=memory native arraydef_0__classes).
       { rewrite Hsame. change(memory(ClassAbstractInput.argument_state native value 10 tail) arraydef_0__classes=memory native arraydef_0__classes).
         unfold ClassAbstractInput.argument_state. apply ReadOne.argument_other;discriminate. }
       split;[now apply (ClassLookup.transport native)|]. eapply class_model;[exact Hstate|exact Hnext|rewrite Hraw;lia].
   + assert(Hraw:memory final arraydef_0__classes=memory native arraydef_0__classes).
     { eapply request_array;try eassumption.
       - unfold NativeBasicInvariant.Arrays.kind;tauto.
       - unfold NativeBasicInvariant.Arrays.unchanged;intuition congruence. }
     split;[now apply (ClassLookup.transport native)|]. eapply class_model;[exact Hstate|exact Hnext|rewrite Hraw;lia].
Qed.

Lemma graph_transport final logical next source : NativeState.represents final logical -> NativeState.represents final next ->
 FormulaTopology.ordered final(length(Protocol.formulas logical)) ->
 (length(Protocol.formulas logical)<=S(length(Protocol.formulas source)))%nat ->
 FormulaTopology.ordered final(length(Protocol.formulas next)) /\ (length(Protocol.formulas next)<=S(length(Protocol.formulas source)))%nat.
Proof.
 intros Hmodel Hnext Htop Hgrowth.
 pose proof(formula_count _ _ Hmodel) as Hfirst. pose proof(formula_count _ _ Hnext) as Hsecond.
 assert(Hcount:length(Protocol.formulas next)=length(Protocol.formulas logical)) by lia. rewrite Hcount. split;assumption.
Qed.
Lemma simple_top native logical request bs ns tail observations final trace next :
 Protocol.shape request -> (1<=Protocol.opcode request<=4)%nat ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 Z.of_nat(length(Protocol.formulas logical))<=9223372036854775807 ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> NativeState.represents final next ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) ->
 FormulaTopology.ordered final(length(Protocol.formulas next)) /\ (length(Protocol.formulas next)<=S(length(Protocol.formulas logical)))%nat.
Proof.
 destruct request as [opcode values name]. intros Hshape Hrange Hmeta Htoken Hprint Hpending Herror Hroom Hinput Hrun Hstate Hnext Htop.
 cbn [Protocol.opcode] in Hrange.
 assert(Hopcode:opcode=1%nat \/ opcode=2%nat \/ opcode=3%nat \/ opcode=4%nat) by lia.
 destruct Hopcode as [->|[->|[->| ->]]].
 - destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname. subst name.
   destruct values as [|a [|b [|bad values]]];cbn [length] in Hlen;try lia.
   inversion Hwords as [|a' values Ha Hrest];subst a' values.
   inversion Hrest as [|b' values Hb Hnil];subst b' values.
   change(meta_value native 15=50) in Hpending.
   rewrite(NativeBasicDispatcher.two_rest 1 a b tail ltac:(unfold NativeBasicDispatcher.two;tauto)) in Hinput.
   change(stdin native=32::decimalBytes a++32::decimalBytes b++10::tail) in Hinput.
   destruct(NativeSimpleInvariant.Atoms.generated_protocol 1 49 [] native logical bs ns a b 32 32 10 tail observations
    ltac:(tauto) eq_refl Hmeta Htoken Hprint Hpending Herror Hroom Ha Hb Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
    as(model & index & fs & HmodelRun & Hstep & HmodelState & Hboundary & HmodelTop).
   assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
   eapply graph_transport;[exact HmodelState|exact Hnext|exact(HmodelTop Htop)|].
   exact(proj2(proj2(proj2(proj2(proj2(proj2 Hboundary)))))).
 - destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname. subst name.
   destruct values as [|a [|b [|bad values]]];cbn [length] in Hlen;try lia.
   inversion Hwords as [|a' values Ha Hrest];subst a' values.
   inversion Hrest as [|b' values Hb Hnil];subst b' values.
   change(meta_value native 15=51) in Hpending.
   rewrite(NativeBasicDispatcher.two_rest 2 a b tail ltac:(unfold NativeBasicDispatcher.two;tauto)) in Hinput.
   change(stdin native=32::decimalBytes a++32::decimalBytes b++10::tail) in Hinput.
   destruct(NativeSimpleInvariant.Atoms.generated_protocol 2 50 [] native logical bs ns a b 32 32 10 tail observations
    ltac:(tauto) eq_refl Hmeta Htoken Hprint Hpending Herror Hroom Ha Hb Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
    as(model & index & fs & HmodelRun & Hstep & HmodelState & Hboundary & HmodelTop).
   assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
   eapply graph_transport;[exact HmodelState|exact Hnext|exact(HmodelTop Htop)|].
   exact(proj2(proj2(proj2(proj2(proj2(proj2 Hboundary)))))).
 - destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname. subst name.
   destruct values as [|a [|b [|bad values]]];cbn [length] in Hlen;try lia.
   inversion Hwords as [|a' values Ha Hrest];subst a' values.
   inversion Hrest as [|b' values Hb Hnil];subst b' values.
   change(meta_value native 15=52) in Hpending.
   rewrite(NativeBasicDispatcher.two_rest 3 a b tail ltac:(unfold NativeBasicDispatcher.two;tauto)) in Hinput.
   change(stdin native=32::decimalBytes a++32::decimalBytes b++10::tail) in Hinput.
   destruct(NativeSimpleInvariant.Imp.generated_total_protocol 51 [] native logical bs ns a b 32 32 10 tail observations
    eq_refl Hmeta Htoken Hprint Hpending Herror Hroom Ha Hb Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
    as(model & reply & after & HmodelRun & Hstep & HmodelState & Hboundary & HmodelTop).
   assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
   eapply graph_transport;[exact HmodelState|exact Hnext|exact(HmodelTop Htop)|].
   exact(proj2(proj2(proj2(proj2(proj2(proj2 Hboundary)))))).
 - destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname. subst name.
   destruct values as [|value [|bad values]];cbn [length] in Hlen;try lia.
   inversion Hwords as [|value' values Hvalue Hnil];subst value' values.
   change(meta_value native 15=53) in Hpending.
   rewrite(NativeBasicDispatcher.one_rest 4 value tail ltac:(unfold NativeBasicDispatcher.one;tauto)) in Hinput.
   change(stdin native=32::decimalBytes value++10::tail) in Hinput.
   destruct(NativeSimpleInvariant.All.generated_total_protocol native logical bs ns value 32 10 tail observations
    Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
    as(model & reply & after & HmodelRun & Hstep & HmodelState & Hboundary & HmodelTop).
   assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
   eapply graph_transport;[exact HmodelState|exact Hnext|exact(HmodelTop Htop)|].
   exact(proj2(proj2(proj2(proj2(proj2(proj2 Hboundary)))))).
Qed.
Module Generalize.
Import NativeGeneralizeBoundary NativeTheoremBoundary GeneralizeRefinement.
Theorem generalize_rejected_top s logical bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> nth_error (Protocol.history logical) value = None ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 51 :: first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 13 [value] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\ HistoryRefinement.represents final logical /\ flow 1 s final Protocol.NO tail /\ (FormulaTopology.ordered s (length(Protocol.formulas logical)) -> FormulaTopology.ordered final(length(Protocol.formulas logical))).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Harena Hclasses Hhistory Hsep1 Hsep2 Hin.
  assert (Hopword : Z.of_nat 13 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadOne.generated_reads s (fun _ => false) (fun _ => 0) 13 49 [51] value first_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hvalue Hsep1 Hsep2 Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  set (arg := argument_state s value last_separator tail).
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_history : HistoryRefinement.represents arg logical) by now apply argument_history.
  assert (Hreference : meta_value arg 3 <= Z.of_nat value).
  { rewrite (proj1 Harg_history). apply nth_error_None in Hlookup. lia. }
  pose proof (CommandGeneralizeExecution.generated_rejected_command s bs ns _ arg (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference) as Hrun.
  rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state arg). split; [exact Hrun|].
  split; [apply GeneralizeTotal.logical_rejected; [exact Hlookup|now apply (SemanticFrames.arena_NoDup s)]|].
  split.
  - eapply ArenaFrame.storage_arena; [|exact Harena]. eapply ArenaFrame.storage_trans;
      [exact (ReadOne.argument_storage s 49 [51] value last_separator tail Hmeta)|apply ArenaFrame.storage_output].
  - split;[now apply argument_classes|]. split;[exact Harg_history|].
    split.
    + apply (flow_weaken 0 1 s _ Protocol.NO tail ltac:(lia)).
      apply no_flow;[exact (read_one_frame s 49 [51] value last_separator tail Hmeta Hinput Houtput)|exact Herror].
    + intro Htop. eapply NativeSimpleInvariant.storage_top;[|exact Htop].
      change(memory arg arraydef_0__formulas=memory s arraydef_0__formulas).
      unfold arg,argument_state. apply ReadOne.argument_other;discriminate.
Qed.
End Generalize.

Lemma generalize_top native logical value bs ns tail observations final trace next :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat -> meta_value native 15=50 -> meta_value native 8=0 ->
 Z.of_nat(length(Protocol.formulas logical))<=9223372036854775807 -> Z.of_nat(length(Protocol.history logical))<maximum ->
 Z.of_nat value<=maximum -> LogicalHistory.valid logical ->
 stdin native=51::32::decimalBytes value++10::tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> NativeState.represents final next ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) ->
 FormulaTopology.ordered final(length(Protocol.formulas next)) /\ (length(Protocol.formulas next)<=S(length(Protocol.formulas logical)))%nat.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hroom HhistoryRoom Hword Hhistory Hinput Hrun Hstate Hnext Htop.
 pose proof(NativeState.formula_representation _ _ Hstate) as Harena.
 pose proof(NativeState.class_representation _ _ Hstate) as Hclasses.
 pose proof(NativeState.history_representation _ _ Hstate) as Htheorems.
 destruct(nth_error(Protocol.history logical)value) as [fid|] eqn:Hlookup.
 - destruct(Hhistory value fid Hlookup) as [p Hp].
   assert(Htheorem:Protocol.theorem_at logical value=Some p) by (unfold Protocol.theorem_at;now rewrite Hlookup).
   destruct(NativeAllocationInvariant.generalize_protocol native logical bs ns value p 32 10 tail observations
     Hmeta Htoken Hprint Hpending Herror Hroom HhistoryRoom Hword Htop Htheorem Harena Hclasses Htheorems
     ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as(model & index & fs & HmodelRun & Hstep & HmodelArena & HmodelClasses & HmodelHistory & Hflow & HmodelTop).
   assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
   pose proof(same_formula_count _ _ _ Hnext HmodelArena) as Hcount.
   split;[now rewrite Hcount|].
   destruct Hflow as (Hin & Hout & Herror' & Hstop & Hgrowth & Hrest).
   pose proof(formula_count _ _ Hstate). pose proof(formula_count _ _ Hnext). lia.
 - destruct(Generalize.generalize_rejected_top native logical bs ns value 32 10 tail observations
     Hmeta Htoken Hprint Hpending Herror Hword Hlookup Harena Hclasses Htheorems
     ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as(model & HmodelRun & Hstep & HmodelArena & HmodelClasses & HmodelHistory & Hflow & HmodelTop).
   assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
   pose proof(same_formula_count _ _ _ Hnext HmodelArena) as Hcount.
   split;[rewrite Hcount;now apply HmodelTop|lia].
Qed.
Lemma supported_dec opcode : {NativeBasicDispatcher.named opcode}+{~NativeBasicDispatcher.named opcode}.
Proof. unfold NativeBasicDispatcher.named. solve_decision. Defined.
Lemma name_growth native logical request bs ns tail observations final trace :
 Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 Z.of_nat(length(Protocol.bindings logical))<maximum ->
 Z.of_nat(length(memory native arraydef_0__names)+length(Protocol.object_name request))<=maximum ->
 NativeState.represents native logical -> LogicalHistory.valid logical ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 (length(memory final arraydef_0__names)<=length(memory native arraydef_0__names)+length(Protocol.object_name request))%nat.
Proof.
 intros Hshape Hsupported Hmeta Htoken Hprint Hpending Herror HbindingRoom HnameRoom Hstate Hhistory Hinput Hrun.
 destruct(supported_dec (Protocol.opcode request)) as [Hnamed|Hnotnamed].
 - destruct request as [opcode values name]. cbn [Protocol.opcode] in Hnamed.
   unfold NativeBasicDispatcher.named in Hnamed. destruct Hnamed as [->|[->| ->]];
    destruct Hshape as [Hwords Hfields];cbn [Protocol.arguments Protocol.object_name] in Hwords,Hfields,HnameRoom;
    destruct Hfields as [Hlen Hname];destruct values as [|value [|bad values]];cbn [length] in Hlen;try lia;
    inversion Hwords as [|value' values Hvalue Hnil];subst value' values.
   + change(meta_value native 15=58) in Hpending.
     rewrite(NativeBasicDispatcher.named_rest 9 value name tail ltac:(unfold NativeBasicDispatcher.named;tauto)) in Hinput.
     change(stdin native=32::decimalBytes value++32::name++10::tail) in Hinput.
     destruct(NativeNameGrowth.Class.generated_total_protocol native logical bs ns value name 32 32 10 tail observations
      Hmeta Htoken Hprint Hpending Herror Hvalue Hname Hstate HbindingRoom HnameRoom ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
      as(model & reply & after & HmodelRun & Hstep & HmodelState & Hio & Hsafe & Hgrowth).
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. exact Hgrowth.
   + change(meta_value native 15=51) in Hpending.
     rewrite(NativeBasicDispatcher.named_rest 20 value name tail ltac:(unfold NativeBasicDispatcher.named;tauto)) in Hinput.
     change(stdin native=48::32::decimalBytes value++32::name++10::tail) in Hinput.
     destruct(NativeNameGrowth.TheoremName.generated_total_protocol native logical bs ns value name 32 32 10 tail observations
      Hmeta Htoken Hprint Hpending Herror Hvalue Hname Hhistory Hstate HbindingRoom HnameRoom ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
      as(model & reply & after & HmodelRun & Hstep & HmodelState & Hio & Hsafe & Hgrowth).
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. exact Hgrowth.
   + change(meta_value native 15=51) in Hpending.
     rewrite(NativeBasicDispatcher.named_rest 23 value name tail ltac:(unfold NativeBasicDispatcher.named;tauto)) in Hinput.
     change(stdin native=51::32::decimalBytes value++32::name++10::tail) in Hinput.
     destruct(NativeNameGrowth.Schema.generated_total_protocol native logical bs ns value name 32 32 10 tail observations
      Hmeta Htoken Hprint Hpending Herror Hvalue Hname Hstate HbindingRoom HnameRoom ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
      as(model & reply & after & HmodelRun & Hstep & HmodelState & Hio & Hsafe & Hgrowth).
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. exact Hgrowth.
 - assert(Hraw:memory final arraydef_0__names=memory native arraydef_0__names).
   { eapply request_array;try eassumption.
     - unfold NativeBasicInvariant.Arrays.kind;tauto.
     - unfold NativeBasicInvariant.Arrays.unchanged,NativeBasicDispatcher.named in *;intuition congruence. }
   rewrite Hraw;lia.
Qed.
Definition post (native:Machine) logical request (final:Machine) next :=
 FormulaTopology.ordered final(length(Protocol.formulas next)) /\
 nth_error(Protocol.formulas next)0=Some SetTheory.falsity /\ ClassLookup.wellformed final /\
 (length(Protocol.formulas next)<=S(length(Protocol.formulas logical)))%nat /\
 (length(Protocol.classes next)<=S(length(Protocol.classes logical)))%nat /\
 LogicalRegistryBounds.counts logical next 1 /\ LogicalRegistryBounds.unique next /\
 (length(memory final arraydef_0__names)<=length(memory native arraydef_0__names)+length(Protocol.object_name request))%nat.
Theorem preserves native logical request bs ns tail observations final trace reply next :
 Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical -> NativeBasicDispatcher.resources native logical request ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> LogicalRegistryBounds.unique logical ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 Protocol.step logical request reply next -> NativeState.represents final next -> post native logical request final next.
Proof.
 intros Hshape Hsupported Hmeta Htoken Hprint Hpending Herror Hstate Hsafe Hresources Htop Hfalse Hgood Hunique Hinput Hrun Hstep Hnext.
 destruct Hresources as [HformulaRoom HclassRoom HhistoryRoom HbindingRoom HnameRoom].
 pose proof(NativeBasicDispatcher.safe_history logical Hsafe) as Hhistory.
 assert(Hgraph:FormulaTopology.ordered final(length(Protocol.formulas next)) /\
   (length(Protocol.formulas next)<=S(length(Protocol.formulas logical)))%nat).
 { pose proof(NativeBasicDispatcher.supported_bound _ Hsupported) as Hbound.
   destruct(le_dec (Protocol.opcode request) 4) as [Hsimple|Hcomplex].
   - eapply simple_top;try eassumption;lia.
   - destruct(Nat.eq_dec (Protocol.opcode request) 13%nat) as [H13|H13].
     + destruct request as [opcode values name]. cbn [Protocol.opcode] in H13. subst opcode.
       destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname. subst name.
       destruct values as [|value [|bad values]];cbn [length] in Hlen;try lia.
       inversion Hwords as [|value' values Hvalue Hnil];subst value' values.
       change(meta_value native 15=50) in Hpending.
       rewrite(NativeBasicDispatcher.one_rest 13 value tail ltac:(unfold NativeBasicDispatcher.one;tauto)) in Hinput.
       change(stdin native=51::32::decimalBytes value++10::tail) in Hinput.
       eapply generalize_top;try eassumption.
     + destruct(readonly_top native logical request bs ns tail observations final trace next Hshape Hsupported
         ltac:(unfold NativeBasicCountInvariant.unchanged;repeat split;lia) Hmeta Htoken Hpending Herror Hinput Hrun Hstate Hnext Htop)
         as [HnextTop Hcount]. split;[exact HnextTop|lia]. }
 destruct(class_post native logical request bs ns tail observations final trace next Hshape Hsupported Hmeta Htoken Hprint
   Hpending Herror HclassRoom Hinput Hrun Hstate Hnext Hgood) as [HnextGood Hclasses].
 unfold post. split;[exact(proj1 Hgraph)|]. split.
 - exact(LogicalStorageMonotone.formula_lookup logical next 0 SetTheory.falsity (LogicalStorageMonotone.step _ _ _ _ Hstep) Hfalse).
 - split;[exact HnextGood|]. split;[exact(proj2 Hgraph)|]. split;[exact Hclasses|].
   split;[exact(LogicalRegistryBounds.step_counts _ _ _ _ Hstep)|].
   split;[exact(LogicalRegistryBounds.step_unique _ _ _ _ Hstep Hunique)|].
   exact(name_growth native logical request bs ns tail observations final trace Hshape Hsupported Hmeta Htoken Hprint
     Hpending Herror HbindingRoom HnameRoom Hstate Hhistory Hinput Hrun).
Qed.
Theorem generated_canonical native logical request bs ns tail observations :
 Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical -> NativeBasicDispatcher.resources native logical request ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> LogicalRegistryBounds.unique logical ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 exists final reply next,
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical request reply next /\ NativeState.represents final next /\
 NativeCommandBoundary.io native final reply tail /\ Guarantees.safe next /\ LogicalHistory.valid next /\ LogicalNames.valid next /\
 post native logical request final next.
Proof.
 intros Hshape Hsupported Hmeta Htoken Hprint Hpending Herror Hstate Hsafe Hresources Htop Hfalse Hgood Hunique Hinput.
 destruct(NativeBasicDispatcher.generated_canonical native logical request bs ns tail observations Hshape Hsupported Hmeta Htoken Hprint
 Hpending Herror Hstate Hsafe Hresources Hinput) as(final & reply & next & Hrun & Hstep & Hnext & Hio & Hsafe' & Hhistory & Hnames).
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hnext|]. split;[exact Hio|].
 split;[exact Hsafe'|]. split;[exact Hhistory|]. split;[exact Hnames|]. eapply preserves;eassumption.
Qed.
End NativeBasicCommandInvariant.
