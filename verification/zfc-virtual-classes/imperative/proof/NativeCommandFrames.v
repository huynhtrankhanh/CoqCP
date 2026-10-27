From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal RenameMemoControl EffectFrame MetaCellFrame
 ImmutableHandlers CommandQuit CommandStructure CommandChain CommandDispatch NativeState NativeStateFrames
 Representation ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation CommandSchemaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Strings.String Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeCommandFrames.
Import IndexExecution SipHashExecution ObservedLocal CommandQuitExecution.
Module Opcode.
Definition safe_local (effect:WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) :=
 match effect with NumberLocalSet _ _ _ name _=>name<>vardef_0__command_op|_=>True end.
Fixpoint local_ro {R} (code:LocalAction R) : Prop := match code with
 |Done _ _ _ _=>True|Dispatch _ _ _ effect cont=>safe_local effect /\ forall response,local_ro (cont response) end.
Definition safe_within (effect:WithinLoop arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) :=
 match effect with DoWithLocalVariables _ _ _ effect=>safe_local effect|_=>True end.
Fixpoint within_ro {R} (code:Action (WithinLoop arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withinLoopReturnValue R) : Prop := match code with
 |Done _ _ _ _=>True|Dispatch _ _ _ effect cont=>safe_within effect /\ forall response,within_ro (cont response) end.
Lemma local_bind {A B} (code:LocalAction A) (next:A->LocalAction B) :
 local_ro code -> (forall value,local_ro (next value)) -> local_ro (code>>=next).
Proof. induction code as [value|effect cont IH];[intros _ H;apply H|]. intros [Hsafe Hcode] Hnext. split;[exact Hsafe|]. intro;apply IH;auto. Qed.
Lemma within_bind {A B} (code:Action (WithinLoop arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withinLoopReturnValue A) next :
 within_ro code -> (forall value,within_ro (next value)) -> within_ro (R:=B) (code>>=next).
Proof. induction code as [value|effect cont IH];[intros _ H;apply H|]. intros [Hsafe Hcode] Hnext. split;[exact Hsafe|]. intro;apply IH;auto. Qed.
Lemma local_lift {R} (code:Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue R) :
 local_ro (liftToWithLocalVariables code).
Proof. induction code;cbn [liftToWithLocalVariables Action_rect local_ro safe_local];auto. Qed.
Lemma within_lift {R} (code:LocalAction R) : local_ro code -> within_ro (liftToWithinLoop code).
Proof. induction code as [value|effect cont IH];[constructor|]. intros [Hsafe Hcont]. cbn [liftToWithinLoop Action_rect within_ro]. split;[exact Hsafe|]. intro;now apply IH. Qed.
Lemma drop_ro (code:Action (WithinLoop arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withinLoopReturnValue unit) :
 within_ro code -> local_ro (dropWithinLoop code).
Proof. induction code as [value|effect cont IH];[constructor|]. intros [Hsafe Hcont].
 destruct effect;cbn [dropWithinLoop Action_rect local_ro];try constructor;[exact Hsafe|intro;now apply IH]. Qed.
Lemma loop_ro count (body:nat->LocalAction LoopOutcome) :
 (forall index,local_ro (body index)) -> local_ro (loop count body).
Proof. intro Hbody. induction count as [|count IH];[constructor|]. rewrite loop_S. apply local_bind;[apply Hbody|]. intros [];[exact IH|constructor]. Qed.
Lemma string_ro str (body:Z->LocalAction LoopOutcome) :
 (forall ch,local_ro (body ch)) -> local_ro (loopString str body).
Proof. intro Hbody. induction str as [|ch tail IH];[constructor|]. cbn [loopString]. apply local_bind;[apply Hbody|]. intros [];[exact IH|constructor]. Qed.
Lemma step_preserves effect (f:Frame) observations value final after :
 safe_local effect -> localStepObserved effect (f,observations)=Some(value,(final,after)) ->
 nums final vardef_0__command_op=nums f vardef_0__command_op.
Proof.
 intros Hsafe Hrun. destruct effect as [effect|name|name value'|name|name value'];unfold localStepObserved in Hrun;cbn [fst snd] in Hrun.
 - destruct (observedStep effect (machine f,observations)) as [[response [middle trace]]|];[|discriminate].
   cbn [optionBind fst snd] in Hrun. injection Hrun as _ <- <-. reflexivity.
 - injection Hrun as _ <- <-. reflexivity.
 - injection Hrun as _ <- <-. reflexivity.
 - injection Hrun as _ <- <-. reflexivity.
 - injection Hrun as _ <- <-. cbn [nums setNum]. apply RenameMemoControl.updated_other. now cbn [safe_local] in Hsafe.
Qed.
Lemma preserves {R} (code:LocalAction R) (f:Frame) observations value final after :
 local_ro code -> execLocalObserved code (f,observations)=Some(value,(final,after)) ->
 nums final vardef_0__command_op=nums f vardef_0__command_op.
Proof.
 induction code as [result|effect cont IH] in f,observations|-*.
 - intros _ Hrun. injection Hrun as _ <- <-. reflexivity.
 - intros [Hsafe Hcode] Hrun. cbn [execLocalObserved] in Hrun.
   destruct (localStepObserved effect (f,observations)) as [[response [middle trace]]|] eqn:Hstep;[|discriminate].
   cbn [optionBind fst snd] in Hrun. rewrite (IH response middle trace (Hcode response) Hrun).
   eapply step_preserves;eassumption.
Qed.
Ltac ro := first
 [lazymatch goal with |- local_ro (Done _ _ _ _)=>exact I end
 |lazymatch goal with |- within_ro (Done _ _ _ _)=>exact I end
 |lazymatch goal with |- local_ro (bind _ _)=>apply local_bind;[ro|intro;ro] end
 |lazymatch goal with |- within_ro (bind _ _)=>apply within_bind;[ro|intro;ro] end
 |lazymatch goal with |- local_ro (liftToWithLocalVariables _)=>apply local_lift end
 |lazymatch goal with |- within_ro (liftToWithinLoop _)=>apply within_lift;ro end
 |lazymatch goal with |- local_ro (dropWithinLoop _)=>apply drop_ro;ro end
 |lazymatch goal with |- local_ro (loop _ _)=>apply loop_ro;intro;ro end
 |lazymatch goal with |- local_ro (loopString _ _)=>apply string_ro;intro;ro end
 |lazymatch goal with |- local_ro (if ?test then _ else _)=>destruct test;ro end
 |lazymatch goal with |- within_ro (if ?test then _ else _)=>destruct test;ro end
 |lazymatch goal with |- local_ro (Dispatch _ _ _ _ _)=>split;[cbn [safe_local];intuition congruence|intro;ro] end
 |lazymatch goal with |- within_ro (Dispatch _ _ _ _ _)=>split;[cbn [safe_within safe_local];intuition congruence|intro;ro] end
 |progress cbv beta iota zeta delta [numberLocalGet numberLocalSet booleanLocalGet booleanLocalSet retrieve store grow trap readChar writeChar flush shortCircuitAnd shortCircuitOr addInt subInt multInt andBits orBits xorBits shiftLeft shiftRight modIntUnsigned divIntUnsigned break continue];ro].
Local Opaque funcdef_0__intern funcdef_0__ok funcdef_0__no funcdef_0__readToken funcdef_0__readNat
 funcdef_0__lookup funcdef_0__bindName funcdef_0__appendTheorem funcdef_0__modusPonens funcdef_0__generalize
 funcdef_0__rename funcdef_0__predicate funcdef_0__classEqual funcdef_0__classMember funcdef_0__setness
 funcdef_0__axiom funcdef_0__schemaCheck funcdef_0__schemaNode funcdef_0__schemaInstance.
Theorem handler_ro opcode : (opcode<=26)%nat ->
 local_ro (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)).
Proof.
 intro Hbound.
 let rec cases count tag := lazymatch count with
 |O=>idtac|S ?rest=>let next:=fresh "opcode" in destruct tag as [|next];[idtac|cases rest next]
 end in cases 27%nat opcode.
 all:try lia.
 all:match goal with |-context[Z.of_nat ?tag]=>let value:=eval compute in (Z.of_nat tag) in change (Z.of_nat tag) with value end.
 all:unfold CommandChain.handler_for;cbn beta iota.
 all:unfold CommandStructure.handler_1,CommandStructure.handler_2,CommandStructure.handler_3,CommandStructure.handler_4,CommandStructure.handler_5,CommandStructure.handler_6,CommandStructure.handler_7,CommandStructure.handler_8,CommandStructure.handler_9,CommandStructure.handler_10,CommandStructure.handler_11,CommandStructure.handler_12,CommandStructure.handler_13,CommandStructure.handler_14,CommandStructure.handler_15,CommandStructure.handler_16,CommandStructure.handler_17,CommandStructure.handler_18,CommandStructure.handler_19,CommandStructure.handler_20,CommandStructure.handler_21,CommandStructure.handler_22,CommandStructure.handler_23,CommandStructure.handler_24,CommandStructure.handler_25,CommandStructure.handler_26.
 all:ro.
Qed.
End Opcode.
Lemma chain_skip_prefix handlers prefix suffix opcode (f:Frame) observations :
 nums f vardef_0__command_op=opcode -> Forall (fun n=>opcode<>n) prefix ->
 execLocalObserved (CommandChain.chain handlers (prefix++suffix)) (f,observations)=
 execLocalObserved (CommandChain.chain handlers suffix) (f,observations).
Proof.
 intros Hop Hprefix. induction Hprefix as [|head rest Hneq Hrest IH];[reflexivity|].
 cbn [List.app CommandChain.chain]. rewrite ObservedLocal.local_bind,(CommandChain.guard_skip head opcode _ _ f observations Hop Hneq).
 cbn [optionBind fst snd]. exact IH.
Qed.
Theorem chain_inverse opcode (f final:Frame) observations afterObservations :
 (1<=opcode<=26)%nat -> nums f vardef_0__command_op=Z.of_nat opcode ->
 meta_value (machine f) 8=0 -> (8<length(memory (machine f) arraydef_0__meta))%nat ->
 execLocalObserved (CommandChain.source_chain funcdef_0__readNat) (f,observations)=Some(tt,(final,afterObservations)) ->
 execLocalObserved (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)) (f,observations)=Some(tt,(final,afterObservations)).
Proof.
 intros Hbound Hop Herror Hmeta Hrun.
 destruct (list_elem_of_split _ _ (CommandChain.supported_member (Z.of_nat opcode) ltac:(lia))) as [prefix [suffix Hsplit]].
 pose proof CommandChain.tags_nodup as Hnodup. rewrite Hsplit in Hnodup.
 apply NoDup_app in Hnodup as [Hprefix [Hcross Hsuffix]]. apply NoDup_cons in Hsuffix as [Hnot Hsuffix].
 assert (Hprefix_skip:Forall (fun n=>Z.of_nat opcode<>n) prefix).
 { apply Forall_forall. intros n Hn Heq. subst n. apply (Hcross _ Hn). apply elem_of_cons;left;reflexivity. }
 assert (Hsuffix_skip:Forall (fun n=>Z.of_nat opcode<>n) suffix).
 { apply Forall_forall. intros n Hn Heq. apply Hnot. now rewrite Heq. }
 rewrite CommandChain.actual_chain,Hsplit,(chain_skip_prefix _ prefix _ _ f observations Hop Hprefix_skip) in Hrun.
 cbn [CommandChain.chain] in Hrun. rewrite ObservedLocal.local_bind,(CommandChain.guard_take _ _ f observations Hop Herror Hmeta) in Hrun.
 lazymatch type of Hrun with optionBind ?actual ?next= _ =>
   remember actual as outcome eqn:Hhandler in Hrun
 end.
 destruct outcome as [[[] [middle trace]]|];cbn [optionBind fst snd] in Hrun;[|discriminate]. symmetry in Hhandler.
 assert (Hmiddle:nums middle vardef_0__command_op=Z.of_nat opcode).
 { rewrite (Opcode.preserves _ f observations tt middle trace (Opcode.handler_ro opcode ltac:(lia)) Hhandler). exact Hop. }
 rewrite (CommandChain.chain_skips _ suffix _ middle trace Hmiddle Hsuffix_skip) in Hrun.
 injection Hrun as Hsame Htrace. subst final afterObservations. exact Hhandler.
Qed.
Definition postlude : LocalAction unit := ltac:(
 let code:=eval unfold funcdef_0__command_body in funcdef_0__command_body in
 lazymatch code with bind _ ?next=>
  let second:=eval cbv beta in (next tt) in
  lazymatch second with bind _ ?next=>
   let third:=eval cbv beta in (next tt) in
   lazymatch third with bind _ ?next=>exact (next tt) end
  end
 end).
Definition post_sequence (sequence:LocalAction unit) (f:Frame) observations :=
 optionBind (execLocalObserved sequence (f,observations))
  (fun response=>execLocalObserved postlude (snd response)).

Local Opaque funcdef_0__intern funcdef_0__ok funcdef_0__no funcdef_0__readToken funcdef_0__readNat
 funcdef_0__lookup funcdef_0__bindName funcdef_0__appendTheorem funcdef_0__modusPonens funcdef_0__generalize
 funcdef_0__rename funcdef_0__predicate funcdef_0__classEqual funcdef_0__classMember funcdef_0__setness
 funcdef_0__axiom funcdef_0__schemaCheck funcdef_0__schemaNode funcdef_0__schemaInstance.
Theorem positive_projection reader sequence (f:Frame) readstate opcode observations :
 execObserved (reader (fun _=>false) (fun _=>0)) (machine f,observations)=Some(tt,(readstate,observations)) ->
 (17<length(memory readstate arraydef_0__meta))%nat ->
 meta_value readstate 11=opcode -> meta_value readstate 14=1 -> meta_value readstate 8=0 ->
 1<=opcode<=26 ->
 execLocalObserved (CommandDispatch.with_chain reader sequence) (f,observations)=
 post_sequence sequence (CommandDispatch.opcode_frame f readstate opcode) observations.
Proof.
 intros Hreader Hmeta Hnumber Hvalid Herror Hrange.
 destruct f as [native bs ns]. cbn [machine] in Hreader.
 unfold CommandDispatch.with_chain. cbv beta iota zeta.
  repeat first [progress cbn [optionBind fst snd]
    |progress (match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state] =>
      lazymatch state with (?frame,?trace_now) =>
      let expression := constr:(@execLocalObserved I T EI V EV R code state) in
      let head := CommandDispatch.action_head code in
      first [constr_eq head (@Done) |constr_eq head (@bind) |constr_eq head (@numberLocalGet)
        |constr_eq head (@numberLocalSet) |constr_eq head (@retrieve) |constr_eq head (@store)
        |constr_eq head (@liftToWithLocalVariables) |constr_eq head (@shortCircuitAnd) |constr_eq head (@shortCircuitOr)];
      lazymatch head with
      | @Done => lazymatch code with @Done ?E ?F ?A ?value => change expression with (Some (value,state)) end
      | @bind => lazymatch code with bind ?first ?next =>
          let Hbind := fresh "Hbind" in
          assert (Hbind : expression = optionBind (execLocalObserved first state)
            (fun response => execLocalObserved (R := R) (next (fst response)) (snd response))) by
            (exact (local_bind first next state)); rewrite Hbind; clear Hbind end
      | @numberLocalGet => lazymatch code with numberLocalGet _ _ _ ?name =>
          change expression with (Some (nums frame name,state)) end
      | @numberLocalSet => lazymatch code with numberLocalSet _ _ _ ?name ?value =>
          change expression with (Some (tt,(setNum frame name value,trace_now))) end
      | @retrieve => lazymatch code with retrieve _ _ _ arraydef_0__meta ?slot =>
          let Hstep := fresh "Hstep" in
          assert (Hstep : expression = Some (meta_value (machine frame) (Z.to_nat slot),state)) by
            (exact (local_read_meta frame slot trace_now ltac:(cbn [machine setMachine]; first
              [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta]
              ])));
          rewrite Hstep; clear Hstep end
      | @liftToWithLocalVariables => lazymatch code with liftToWithLocalVariables ?callee =>
          let Hlift := fresh "Hlift" in
          assert (Hlift : expression = optionBind (execObserved callee (machine frame,trace_now))
            (fun response => Some (fst response,(setMachine frame (fst (snd response)),snd (snd response))))) by
            (exact (lift_correct callee frame trace_now)); rewrite Hlift; clear Hlift end
      | @shortCircuitAnd => unfold shortCircuitAnd at 1
      | @shortCircuitOr => unfold shortCircuitOr at 1
      end
      end
    end)
    |match goal with |- context [execObserved (reader _ _) _] => progress rewrite Hreader end
    |match goal with |- context [meta_value readstate 11] => progress rewrite Hnumber end
    |match goal with |- context [meta_value readstate 14] => progress rewrite Hvalid end
    |match goal with |- context [meta_value readstate 8] => progress rewrite Herror end
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. unfold post_sequence,CommandDispatch.opcode_frame,postlude. reflexivity.
Qed.
Lemma postlude_array watched : watched<>arraydef_0__meta -> EffectFrame.local_ro watched postlude.
Proof. intro Hwatched. unfold postlude. EffectFrame.ro. Qed.
Lemma postlude_cell slot : slot<>9%nat -> MetaCellFrame.local_ro slot postlude.
Proof. intro Hslot. unfold postlude. MetaCellFrame.ro. Qed.
Theorem postlude_registries (f final:Frame) observations after :
 execLocalObserved postlude (f,observations)=Some(tt,(final,after)) ->
 NativeStateFrames.registries (machine f) (machine final).
Proof.
 intro Hrun. constructor.
 - eapply NativeStateFrames.local_cell;[apply postlude_cell;lia|exact Hrun].
 - eapply NativeStateFrames.local_cell;[apply postlude_cell;lia|exact Hrun].
 - eapply NativeStateFrames.local_cell;[apply postlude_cell;lia|exact Hrun].
 - eapply ImmutableHandlers.local_observed_preserves;[apply postlude_array;discriminate|exact Hrun].
 - eapply ImmutableHandlers.local_observed_preserves;[apply postlude_array;discriminate|exact Hrun].
 - eapply ImmutableHandlers.local_observed_preserves;[apply postlude_array;discriminate|exact Hrun].
Qed.
Theorem generated_registries native bs ns readstate opcode observations final trace :
 (1<=opcode<=26)%nat -> opcode<>22%nat -> NativeStateFrames.nonbinding opcode ->
 execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (native,observations)=Some(tt,(readstate,observations)) ->
 (17<length (memory readstate arraydef_0__meta))%nat ->
 meta_value readstate 11=Z.of_nat opcode -> meta_value readstate 14=1 -> meta_value readstate 8=0 ->
 NativeStateFrames.registries native readstate ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 NativeStateFrames.registries native final.
Proof.
 intros Hrange HnotNode Hnonbinding Hreader Hmeta Hnumber Hvalid Herror Hparsed Hrun.
 unfold funcdef_0__command in Hrun.
 rewrite ObservedLocal.eliminate_correct,CommandQuitExecution.actual_body,CommandDispatch.actual_body in Hrun.
 change (optionBind (execLocalObserved (CommandDispatch.with_chain funcdef_0__readNat (CommandChain.source_chain funcdef_0__readNat))
  ({|machine:=native;bools:=bs;nums:=ns|},observations))
  (fun response=>Some(fst response,(machine (fst (snd response)),snd (snd response))))=Some(tt,(final,trace))) in Hrun.
 pose proof (f_equal (fun result=>optionBind result
   (fun response=>Some(fst response,(machine (fst (snd response)),snd (snd response)))))
   (positive_projection funcdef_0__readNat (CommandChain.source_chain funcdef_0__readNat)
   {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode) observations
   Hreader Hmeta Hnumber Hvalid Herror ltac:(lia))) as Hprojection.
 assert (Hreduced:optionBind (post_sequence (CommandChain.source_chain funcdef_0__readNat)
   (CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode)) observations)
   (fun response=>Some(fst response,(machine (fst (snd response)),snd (snd response))))=Some(tt,(final,trace))).
 { exact (eq_trans (eq_sym Hprojection) Hrun). }
 clear Hrun. rename Hreduced into Hrun.
 unfold post_sequence in Hrun.
 lazymatch type of Hrun with optionBind (optionBind ?actual ?post) ?projection=_=>
  remember actual as chainResult eqn:Hchain in Hrun end.
 destruct chainResult as [[[] [middle middleTrace]]|];cbn [optionBind fst snd] in Hrun;[|discriminate].
 symmetry in Hchain.
 lazymatch type of Hrun with optionBind ?actual ?projection=_=>
  remember actual as postResult eqn:Hpost in Hrun end.
 destruct postResult as [[[] [finished finalTrace]]|];cbn [optionBind fst snd] in Hrun;[|discriminate].
 symmetry in Hpost.
 injection Hrun as Hfinal Htrace. subst final trace.
 eapply NativeStateFrames.trans;[exact Hparsed|].
 eapply NativeStateFrames.trans;[|exact (postlude_registries middle finished middleTrace finalTrace Hpost)].
 assert (Hhandler:execLocalObserved (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode))
   (CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode),observations)=Some(tt,(middle,middleTrace))).
 { refine (chain_inverse opcode
     (CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode))
     middle observations middleTrace Hrange _ Herror _ Hchain).
   - unfold CommandDispatch.opcode_frame. cbn [nums setNum]. apply RenameMemoControl.updated_same.
   - change (8<length (memory readstate arraydef_0__meta))%nat;lia. }
 exact (NativeStateFrames.generated_registries opcode
   (CommandDispatch.opcode_frame {|machine:=native;bools:=bs;nums:=ns|} readstate (Z.of_nat opcode))
   middle observations middleTrace ltac:(lia) HnotNode Hnonbinding Hhandler).
Qed.
Theorem generated_preserves native bs ns readstate opcode observations final trace logical request reply next :
 (1<=opcode<=26)%nat -> opcode<>22%nat -> NativeStateFrames.nonbinding opcode -> Protocol.opcode request=opcode ->
 execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (native,observations)=Some(tt,(readstate,observations)) ->
 (17<length (memory readstate arraydef_0__meta))%nat ->
 meta_value readstate 11=Z.of_nat opcode -> meta_value readstate 14=1 -> meta_value readstate 8=0 ->
 NativeStateFrames.registries native readstate ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> Protocol.step logical request reply next ->
 NativeRepresentation.canonical_arena final (Protocol.formulas next) ->
 ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) -> HistoryRefinement.represents final next ->
 NativeState.represents final next.
Proof.
 intros Hrange HnotNode Hnonbinding Hopcode Hreader Hmeta Hnumber Hvalid Herror Hparsed Hrun Hstate Hstep Harena Hclasses Hhistory.
 eapply NativeStateFrames.finish;[exact Hstate| |exact Hstep|now rewrite Hopcode| |exact Harena|exact Hclasses|exact Hhistory].
 - eapply generated_registries;eassumption.
 - eapply NativeStateFrames.step_bindings;[now rewrite Hopcode|exact Hstep].
Qed.
End NativeCommandFrames.
