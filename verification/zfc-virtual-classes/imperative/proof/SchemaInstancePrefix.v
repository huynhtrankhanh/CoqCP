From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl CommandChain CommandStructure
 SchemaInstanceArguments SchemaEvaluationArguments SchemaInstanceHandler ReadName ReadToken TokenByte ReadFour DecimalInput NameSearch NameRepresentation TypedNameLookup FormulaProjection Representation ClassStorage HistoryRefinement SchemaRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaInstancePrefix.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := SchemaInstanceHandler.Frame.
Definition LocalAction := SchemaInstanceHandler.LocalAction.
Definition arguments_loop : LocalAction unit := ltac:(
 let code:=eval cbv beta iota zeta delta [CommandChain.handler_for CommandStructure.handler_24] in (CommandChain.handler_for funcdef_0__readNat 24) in
 multimatch code with context [bind (bind (numberLocalGet _ _ _ vardef_0__command_a) ?loopfun) ?after]=>
 let nested:=eval cbn beta in(loopfun 0%Z) in
 lazymatch nested with loop _ _=>exact (bind (numberLocalGet _ _ _ vardef_0__command_a) loopfun) end end).
Definition with_suffix (work:LocalAction unit) : LocalAction unit := ltac:(
 let code:=eval cbv beta iota zeta delta [CommandChain.handler_for CommandStructure.handler_24] in (CommandChain.handler_for funcdef_0__readNat 24) in
 multimatch code with context [bind (bind (numberLocalGet _ _ _ vardef_0__command_a) ?loopfun) ?after]=>
 let nested:=eval cbn beta in(loopfun 0%Z) in
 lazymatch nested with loop _ _=>
 let family:=eval pattern after in code in
 lazymatch family with ?family _=>
 let replaced:=eval cbv beta in(family (fun _:unit=>work)) in
 let raw:=eval unfold arguments_loop in arguments_loop in
 let family:=eval pattern raw in replaced in
 lazymatch family with ?family _=>exact (family arguments_loop) end end end end).
Lemma actual_handler : CommandChain.handler_for funcdef_0__readNat 24=with_suffix SchemaInstanceHandler.suffix.
Proof. reflexivity. Qed.
Lemma generated_loop (f:Frame) count observations : nums f vardef_0__command_a=Z.of_nat count ->
 execLocalObserved arguments_loop (f,observations)=
 execLocalObserved (loop count (SchemaInstanceArguments.body (Z.of_nat count))) (f,observations).
Proof.
 intro Hcount. unfold arguments_loop.
 repeat first [progress cbn [optionBind fst snd]
  |NativePrimitives.primitive ltac:(fun frame name slot=>lia)
  |progress rewrite Hcount|progress rewrite Nat2Z.id].
 reflexivity.
Qed.
Definition prepared (f:Frame) looked counted count := setMachine
 (setNum (setNum f vardef_0__command_binding (meta_value looked 0)) vardef_0__command_a (Z.of_nat count))
 (store_meta counted 18 1).
Lemma prepared_count f looked counted count : nums (prepared f looked counted count) vardef_0__command_a=Z.of_nat count.
Proof. cbn [prepared nums setMachine setNum]. apply RenameMemoControl.updated_same. Qed.
Lemma generated_prefix (f:Frame) named looked counted args tail (work:LocalAction unit) observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
 execObserved (funcdef_0__readToken (fun _=>false) (fun _=>0)) (machine f,observations)=Some (tt,(named,observations)) ->
 (18<length (memory named arraydef_0__meta))%nat -> meta_value named 14=1 -> meta_value named 8=0 ->
 execObserved (funcdef_0__lookup (fun _=>false) (fun _=>0)) (named,observations)=Some (tt,(looked,observations)) ->
 (18<length (memory looked arraydef_0__meta))%nat -> meta_value looked 8=0 ->
 execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (looked,observations)=Some (tt,(counted,observations)) ->
 (18<length (memory counted arraydef_0__meta))%nat -> meta_value counted 14=1 -> meta_value counted 8=0 ->
 meta_value counted 11=Z.of_nat (length args) -> meta_value counted 15=0 ->
 (1024<=length (memory counted arraydef_0__token))%nat ->
 Forall (fun arg=>Z.of_nat arg<=maximum) args -> Z.of_nat (length args)<=maximum ->
 stdin counted=SchemaInstanceArguments.wire args++tail ->
 execLocalObserved (with_suffix work) (f,observations)=
 execLocalObserved work (SchemaInstanceArguments.consume (prepared f looked counted (length args)) 0 args tail,observations).
Proof.
 intros Hmeta Herror Hname Hnamed Hnamevalid Hnameerror Hlookup Hlooked Hlookuperror
 Hcount Hcounted Hcountvalid Hcounterror Hcountnumber Hpending Htoken Hwords Hlength Hin.
 set (start:=prepared f looked counted (length args)).
 assert (Hstartmeta:(18<length (memory (machine start) arraydef_0__meta))%nat).
 { unfold start,prepared. cbn [machine setMachine]. now rewrite store_meta_length. }
 assert (Hstarttoken:(1024<=length (memory (machine start) arraydef_0__token))%nat).
 { unfold start,prepared. cbn [machine setMachine]. now rewrite store_meta_other by discriminate. }
 assert (Hstartpending:meta_value (machine start) 15=0).
 { unfold start,prepared. cbn [machine setMachine]. now rewrite meta_store_other by discriminate. }
 assert (Hstarterror:meta_value (machine start) 8=0).
 { unfold start,prepared. cbn [machine setMachine]. now rewrite meta_store_other by discriminate. }
 assert (Hstartinput:stdin (machine start)=SchemaInstanceArguments.wire args++tail) by exact Hin.
 pose proof (proj1 (SchemaInstanceArguments.generated_arguments start args tail observations Hstartmeta Hstarttoken Hstartpending Hstarterror Hwords Hlength Hstartinput)) as Hargs.
 assert (Hloop:execLocalObserved arguments_loop (start,observations)=Some (tt,(SchemaInstanceArguments.consume start 0 args tail,observations))).
 { eapply eq_trans;[exact (generated_loop start (length args) observations (prepared_count f looked counted (length args)))|exact Hargs]. }
 unfold with_suffix.
 repeat first [progress cbn [optionBind fst snd bind machine setMachine setNum nums]
  |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];rewrite ?store_meta_length;lia)
  |progress rewrite Herror|progress rewrite Hnameerror|progress rewrite Hlookuperror|progress rewrite Hcounterror
  |progress rewrite Hnamevalid|progress rewrite Hcountvalid|progress rewrite Hcountnumber
  |progress rewrite RenameMemoControl.updated_same|progress rewrite RenameMemoControl.updated_other by discriminate
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 18) with 18%nat by reflexivity
  |multimatch goal with |-context[bool_decide ?P]=>first
   [progress rewrite (bool_decide_true P) by congruence|progress rewrite (bool_decide_false P) by congruence] end
  |match goal with |-context[@execObserved ?I ?T ?EI ?R (funcdef_0__readToken ?bs ?ns) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__readToken bs ns) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(named,observations))) by exact Hname;rewrite Hsame;clear Hsame end
  |match goal with |-context[@execObserved ?I ?T ?EI ?R (funcdef_0__lookup ?bs ?ns) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__lookup bs ns) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(looked,observations))) by exact Hlookup;rewrite Hsame;clear Hsame end
  |match goal with |-context[@execObserved ?I ?T ?EI ?R (funcdef_0__readNat ?bs ?ns) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__readNat bs ns) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(counted,observations))) by exact Hcount;rewrite Hsame;clear Hsame end
  |match goal with |-context[@execLocalObserved ?I ?T ?EI ?V ?EV ?R arguments_loop ?state]=>
   let expression:=constr:(@execLocalObserved I T EI V EV R arguments_loop state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(SchemaInstanceArguments.consume start 0 args tail,observations))) by exact Hloop;rewrite Hsame;clear Hsame end
  |progress rewrite SchemaInstanceHandler.option_unit].
 cbn [execLocalObserved]. repeat rewrite SchemaInstanceHandler.option_unit. reflexivity.
Qed.
Definition named (f:Frame) name args tail := ReadName.result (machine f) name
 (decimalBytes (length args)++SchemaInstanceArguments.separator_for args::(SchemaInstanceArguments.wire args++tail)).
Definition counted looked args tail := DecimalInput.encoded_result looked (length args) (SchemaInstanceArguments.wire args++tail).
Definition finished (f:Frame) looked args tail := SchemaInstanceArguments.consume
 (prepared f looked (counted looked args tail) (length args)) 0 args tail.
Theorem generated_canonical (f:Frame) bindings name args tail (work:LocalAction unit) observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 (1024<=length (memory (machine f) arraydef_0__token))%nat ->
 meta_value (machine f) 15=0 -> meta_value (machine f) 8=0 ->
 NameRepresentation.represents (machine f) bindings -> Protocol.valid_name name ->
 Forall (fun arg=>Z.of_nat arg<=maximum) args -> Z.of_nat (length args)<=maximum ->
 stdin (machine f)=name++32::(decimalBytes (length args)++SchemaInstanceArguments.separator_for args::(SchemaInstanceArguments.wire args++tail)) ->
 exists looked,
 NameSearchExecution.storage_frame (named f name args tail) looked /\
 TypedNameLookup.outcome looked bindings name /\
 execLocalObserved (with_suffix work) (f,observations)=execLocalObserved work (finished f looked args tail,observations) /\
 SchemaEvaluationArguments.represents (machine (finished f looked args tail)) args /\
 stdin (machine (finished f looked args tail))=tail /\ stdout (machine (finished f looked args tail))=stdout (machine f) /\
 meta_value (machine (finished f looked args tail)) 8=0 /\
 (meta_value (machine (finished f looked args tail)) 18=
  if forallb (fun id=>bool_decide (Z.of_nat id<meta_value (machine f) 2)) args then 1 else 0) /\
 length (memory looked arraydef_0__meta)=length (memory (named f name args tail) arraydef_0__meta).
Proof.
 intros Hmeta Htoken Hpending Herror Hbindings Hname Hwords Hlength Hin.
 set (rest:=decimalBytes (length args)++SchemaInstanceArguments.separator_for args::(SchemaInstanceArguments.wire args++tail)).
 set (nameState:=named f name args tail).
 assert (HreadName:execObserved (funcdef_0__readToken (fun _=>false) (fun _=>0)) (machine f,observations)=Some (tt,(nameState,observations))).
 { apply (ReadName.generated_token (machine f) (fun _=>false) (fun _=>0) name 32 rest observations ltac:(lia) Htoken Hpending Herror Hname ltac:(unfold TokenByteExecution.separator;auto) Hin). }
 assert (Hnamed:(18<length (memory nameState arraydef_0__meta))%nat).
 { unfold nameState,named,ReadName.result. now rewrite ReadTokenExecution.result_meta_length. }
 assert (Hnamevalid:meta_value nameState 14=1).
 { apply ReadTokenExecution.result_valid;lia. }
 assert (Hnameerror:meta_value nameState 8=0).
 { unfold nameState,named,ReadName.result. rewrite ReadTokenExecution.result_meta_other by lia. exact Herror. }
 assert (Hnamepending:meta_value nameState 15=0).
 { unfold nameState,named,ReadName.result. rewrite ReadTokenExecution.result_meta_other by lia. exact Hpending. }
 assert (HnameToken:(1024<=length (memory nameState arraydef_0__token))%nat).
 { unfold nameState,named. now rewrite ReadName.token_length. }
 assert (HnameRep:NameRepresentation.represents nameState bindings).
 { apply ReadName.bindings;[lia|exact Hbindings]. }
 assert (HnameBytes:NameRepresentation.token_rep nameState name).
 { apply (ReadName.token_rep (machine f) name rest ltac:(lia)). destruct Hname as [[Hpositive HlengthName] _]. exact (Nat.le_trans _ _ _ HlengthName Htoken). }
 destruct (TypedNameLookup.generated nameState (fun _=>false) (fun _=>0) bindings name observations ltac:(lia) HnameRep HnameBytes)
  as (looked & Hlookup & HlookRep & HlookLength & Hframe & Houtcome).
 assert (Hlooked:(18<length (memory looked arraydef_0__meta))%nat) by (rewrite HlookLength;exact Hnamed).
 destruct Hframe as [Harrays [Hcells [Hinput Houtput]]].
 assert (HlookError:meta_value looked 8=0) by (rewrite Hcells by lia;exact Hnameerror).
 assert (HlookPending:meta_value looked 15=0) by (rewrite Hcells by lia;exact Hnamepending).
 assert (HlookToken:(1024<=length (memory looked arraydef_0__token))%nat) by (rewrite Harrays by discriminate;exact HnameToken).
 assert (HlookInput:stdin looked=decimalBytes (length args)++SchemaInstanceArguments.separator_for args::(SchemaInstanceArguments.wire args++tail)).
 { rewrite Hinput. reflexivity. }
 destruct (ReadFour.encoded_read looked (length args) (SchemaInstanceArguments.separator_for args) (SchemaInstanceArguments.wire args++tail) observations
   ltac:(lia) HlookToken HlookPending HlookError Hlength (SchemaInstanceArguments.valid_separator args) HlookInput)
 as (HreadCount & HcountToken & HcountPending & HcountInput & HcountOutput).
 destruct HreadCount as [HcountRun [HcountMeta [HcountNumber [HcountValid HcountError]]]].
 set (countState:=counted looked args tail).
 assert (Hcounted:(18<length (memory countState arraydef_0__meta))%nat).
 { unfold countState,counted. rewrite DecimalInput.encoded_meta_length;exact Hlooked. }
 set (start:=prepared f looked countState (length args)).
 assert (HstartMeta:(18<length (memory (machine start) arraydef_0__meta))%nat).
 { unfold start,prepared. cbn [machine setMachine]. rewrite store_meta_length;exact Hcounted. }
 assert (HstartToken:(1024<=length (memory (machine start) arraydef_0__token))%nat).
 { unfold start,prepared. cbn [machine setMachine]. rewrite store_meta_other by discriminate. exact HcountToken. }
 assert (HstartPending:meta_value (machine start) 15=0).
 { unfold start,prepared. cbn [machine setMachine]. rewrite meta_store_other by discriminate. exact HcountPending. }
 assert (HstartError:meta_value (machine start) 8=0).
 { unfold start,prepared. cbn [machine setMachine]. rewrite meta_store_other by discriminate. exact HcountError. }
 assert (HstartInput:stdin (machine start)=SchemaInstanceArguments.wire args++tail) by exact HcountInput.
 destruct (SchemaInstanceArguments.generated_arguments start args tail observations HstartMeta HstartToken HstartPending HstartError Hwords Hlength HstartInput)
 as [Harguments [Hvector [Htail [Hstdout [HerrorFinal Hvalid]]]]].
 exists looked. split;[unfold NameSearchExecution.storage_frame;repeat split;assumption|]. split;[exact Houtcome|]. split.
 - exact (generated_prefix f nameState looked countState args tail work observations Hmeta Herror HreadName Hnamed Hnamevalid Hnameerror
    Hlookup Hlooked HlookError HcountRun Hcounted HcountValid HcountError HcountNumber HcountPending HcountToken Hwords Hlength HcountInput).
 - split;[exact Hvector|]. split;[exact Htail|]. split.
   + eapply eq_trans;[exact Hstdout|]. eapply eq_trans;[exact HcountOutput|]. eapply eq_trans;[exact Houtput|]. apply ReadTokenExecution.result_output.
   + split;[exact HerrorFinal|]. split;[|exact HlookLength].
     change (meta_value (machine (SchemaInstanceArguments.consume start 0 args tail)) 18=
       if forallb (fun id=>bool_decide (Z.of_nat id<meta_value (machine f) 2)) args then 1 else 0).
     rewrite Hvalid.
     assert (HstartClass:meta_value (machine start) 2=meta_value (machine f) 2).
     { unfold start,prepared. cbn [machine setMachine]. rewrite meta_store_other by discriminate.
       unfold countState,counted. rewrite DecimalInput.encoded_meta_other by (try lia).
       rewrite Hcells by lia. unfold nameState,named,ReadName.result. rewrite ReadTokenExecution.result_meta_other by lia. reflexivity. }
     assert (HstartValid:meta_value (machine start) 18=1).
     { unfold start,prepared. cbn [machine setMachine]. apply meta_store_same;exact Hcounted. }
     now rewrite HstartClass,HstartValid.
Qed.
Lemma consume_number args : forall (f:Frame) start tail watched,watched<>vardef_0__command_b ->
 nums (SchemaInstanceArguments.consume f start args tail) watched=nums f watched.
Proof.
 induction args as [|arg rest IH];intros f start tail watched Hwatched;[reflexivity|].
 cbn [SchemaInstanceArguments.consume]. rewrite IH by exact Hwatched.
 cbn [SchemaInstanceArguments.final_frame nums setMachine setNum]. now apply RenameMemoControl.updated_other.
Qed.
Lemma finished_binding f looked args tail : nums (finished f looked args tail) vardef_0__command_binding=meta_value looked 0.
Proof.
 unfold finished. rewrite consume_number by discriminate.
 cbn [prepared nums setMachine setNum]. rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same.
Qed.
Lemma finished_count f looked args tail : nums (finished f looked args tail) vardef_0__command_a=Z.of_nat (length args).
Proof. unfold finished. rewrite consume_number by discriminate. apply prepared_count. Qed.
Lemma finished_number f looked args tail watched :
 watched<>vardef_0__command_a -> watched<>vardef_0__command_b -> watched<>vardef_0__command_binding ->
 nums (finished f looked args tail) watched=nums f watched.
Proof.
 intros Ha Hb Hbinding. unfold finished. rewrite consume_number by exact Hb.
 cbn [prepared nums setMachine setNum]. repeat rewrite RenameMemoControl.updated_other by assumption. reflexivity.
Qed.
Lemma finished_other f looked args tail watched :
 watched<>arraydef_0__meta -> watched<>arraydef_0__token -> watched<>arraydef_0__schemaArguments ->
 memory (machine (finished f looked args tail)) watched=memory looked watched.
Proof.
 intros Hmeta Htoken Hargs. unfold finished. rewrite SchemaInstanceArguments.consume_other by assumption.
 cbn [prepared machine setMachine]. rewrite store_meta_other by exact Hmeta.
 unfold counted. apply DecimalInput.encoded_other;assumption.
Qed.
Lemma finished_meta_length f looked args tail :
 length (memory (machine (finished f looked args tail)) arraydef_0__meta)=length (memory looked arraydef_0__meta).
Proof.
 unfold finished. rewrite SchemaInstanceArguments.consume_meta_length. cbn [prepared machine setMachine].
 rewrite store_meta_length. unfold counted. apply DecimalInput.encoded_meta_length.
Qed.
Lemma finished_meta_other f looked args tail slot :
 (18<length (memory looked arraydef_0__meta))%nat ->
 slot<>6%nat -> slot<>11%nat -> slot<>14%nat -> slot<>17%nat -> slot<>18%nat ->
 meta_value (machine (finished f looked args tail)) slot=meta_value looked slot.
Proof.
 intros Hmeta H6 H11 H14 H17 H18. unfold finished.
 rewrite SchemaInstanceArguments.consume_meta_other by
   (try assumption;cbn [prepared machine setMachine];rewrite store_meta_length;unfold counted;rewrite DecimalInput.encoded_meta_length;exact Hmeta).
 cbn [prepared machine setMachine]. rewrite meta_store_other by exact H18.
 unfold counted. apply DecimalInput.encoded_meta_other;try assumption;lia.
Qed.
Theorem finished_outcome f looked args tail bindings name :
 (18<length (memory looked arraydef_0__meta))%nat -> TypedNameLookup.outcome looked bindings name ->
 TypedNameLookup.outcome (machine (finished f looked args tail)) bindings name.
Proof.
 intro Hmeta. unfold TypedNameLookup.outcome.
 destruct (Protocol.lookup name bindings) as [meaning|];
 rewrite finished_meta_other by (try exact Hmeta;lia).
 - rewrite !finished_other by discriminate. tauto.
 - tauto.
Qed.
Definition parsed_frame (before after:Machine) :=
 length (memory after arraydef_0__meta)=length (memory before arraydef_0__meta) /\
 (forall watched,watched<>arraydef_0__meta -> watched<>arraydef_0__token -> watched<>arraydef_0__schemaArguments -> memory after watched=memory before watched) /\
 (forall slot,slot<>0%nat -> slot<>6%nat -> slot<>11%nat -> slot<>14%nat -> slot<>17%nat -> slot<>18%nat -> meta_value after slot=meta_value before slot).
Theorem finished_frame (f:Frame) looked name args tail :
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 length (memory looked arraydef_0__meta)=length (memory (named f name args tail) arraydef_0__meta) ->
 NameSearchExecution.storage_frame (named f name args tail) looked ->
 parsed_frame (machine f) (machine (finished f looked args tail)).
Proof.
 intros Hmeta HlookLength [Harrays [Hcells Hio]].
 assert (Hlooked:(18<length (memory looked arraydef_0__meta))%nat).
 { rewrite HlookLength. unfold named,ReadName.result. rewrite ReadTokenExecution.result_meta_length. exact Hmeta. }
 split.
 - rewrite finished_meta_length,HlookLength. unfold named,ReadName.result. apply ReadTokenExecution.result_meta_length.
 - split.
   + intros watched Hm Ht Ha. rewrite finished_other by assumption. rewrite Harrays by exact Hm.
     unfold named,ReadName.result. apply ReadTokenExecution.result_other;assumption.
   + intros slot H0 H6 H11 H14 H17 H18.
     rewrite finished_meta_other by assumption. rewrite Hcells by exact H0.
     unfold named,ReadName.result. apply ReadTokenExecution.result_meta_other;try assumption;lia.
Qed.
Theorem parsed_representations s final logical : parsed_frame s final ->
 NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
 ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) ->
 HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) -> SchemaRepresentation.represents s logical ->
 NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
 ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
 HistoryRefinement.represents final logical /\ NameRepresentation.represents final (Protocol.bindings logical) /\ SchemaRepresentation.represents final logical.
Proof.
 intros [Hlength [Harrays Hcells]] Harena Hclasses Hhistory Hnames Hschemas.
 split.
 - apply (FormulaProjection.storage_arena s final (Protocol.formulas logical));[|exact Harena].
   split;[exact Hlength|]. split.
   + intros watched Hneeded. unfold FormulaProjection.needed in Hneeded.
     destruct Hneeded as [Hn|[Hn|[Hn|Hn]]];subst watched;apply Harrays;discriminate.
   + repeat split;apply Hcells;lia.
 - split.
   + unfold ClassStorage.represents. rewrite Hcells by lia. rewrite Harrays by discriminate. exact Hclasses.
   + split.
     * unfold HistoryRefinement.represents. rewrite Hcells by lia. rewrite Harrays by discriminate. exact Hhistory.
     * split.
       -- unfold NameRepresentation.represents. rewrite !Hcells by lia. rewrite !Harrays by discriminate. exact Hnames.
       -- apply (SchemaRepresentation.transport s final logical logical Hschemas);try reflexivity.
          ++ apply Hcells;lia.
          ++ apply Harrays;discriminate.
Qed.
Lemma finished_binding_result f looked args tail :
 (18<length (memory looked arraydef_0__meta))%nat ->
 nums (finished f looked args tail) vardef_0__command_binding=meta_value (machine (finished f looked args tail)) 0.
Proof. intro Hmeta. rewrite finished_binding,finished_meta_other by (try exact Hmeta;lia). reflexivity. Qed.
Theorem forallb_class_arguments logical args :
 forallb (fun id=>bool_decide (Z.of_nat id<Z.of_nat (length (Protocol.classes logical)))) args=true <->
 exists actual,Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) args actual.
Proof.
 induction args as [|id rest IH].
 - cbn [forallb]. split;[intro;exists [];constructor|intro;reflexivity].
 - cbn [forallb]. destruct (Protocol.class_at logical id) as [cls|] eqn:Hhead.
   + assert (Hbound:(id<length (Protocol.classes logical))%nat).
     { apply nth_error_Some. change (Protocol.class_at logical id<>None). congruence. }
     rewrite bool_decide_true by lia. cbn [andb]. split.
     * intro Hrest. destruct (proj1 IH Hrest) as [actual Hactual]. exists (cls::actual). constructor;assumption.
     * intros [actual Hactual]. inversion Hactual as [|id' cls' rest' actual' Hfirst Htail];subst.
       apply (proj2 IH). exists actual'. exact Htail.
   + assert (Hbound:(length (Protocol.classes logical)<=id)%nat).
     { apply nth_error_None. exact Hhead. }
     rewrite bool_decide_false by lia. cbn [andb]. split;[discriminate|].
     intros [actual Hactual]. inversion Hactual as [|id' cls' rest' actual' Hfirst Htail];subst. congruence.
Qed.
Theorem native_class_arguments native logical fs args : ClassStorage.represents native fs (Protocol.classes logical) ->
 (forallb (fun id=>bool_decide (Z.of_nat id<meta_value native 2)) args=true <->
 exists actual,Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) args actual).
Proof. intros [Hcount _]. rewrite Hcount. apply forallb_class_arguments. Qed.
End SchemaInstancePrefix.
