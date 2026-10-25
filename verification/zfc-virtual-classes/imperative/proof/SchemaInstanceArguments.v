From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl CommandChain CommandStructure
 DecimalInput ReadFour ReadNameOne TokenByte InternTail SchemaEvaluationArguments FormulaProjection Representation ClassStorage
 HistoryRefinement NameRepresentation SchemaRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaInstanceArguments.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withLocalVariablesReturnValue R.
Definition body total remaining : LocalAction LoopOutcome := ltac:(
 let code:=eval cbv beta iota zeta delta [CommandChain.handler_for CommandStructure.handler_24] in (CommandChain.handler_for funcdef_0__readNat 24) in
 multimatch code with context[bind (numberLocalGet _ _ _ vardef_0__command_a) ?next]=>
 let nested:=eval cbn beta in(next total) in
 lazymatch nested with loop _ ?body=>exact (body remaining) end end).
Definition checked (s:Machine) (arg:Z) : Machine := if bool_decide (arg<meta_value s 2) then s else store_meta s 18 0.
Definition written (s:Machine) (index:nat) (arg:Z) : Machine := withMemory s (modifyArray
 (growArrays (memory s) arraydef_0__schemaArguments (S index) 0) arraydef_0__schemaArguments index arg).
Definition result s index arg tail := written (checked (DecimalInput.encoded_result s arg tail) (Z.of_nat arg)) index (Z.of_nat arg).
Definition final_frame (f:Frame) index arg tail := setMachine
 (setNum f vardef_0__command_b (Z.of_nat arg)) (result (machine f) index arg tail).
Lemma generated_body (f:Frame) total remaining index arg sep tail observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 (1024<=length (memory (machine f) arraydef_0__token))%nat ->
 meta_value (machine f) 15=0 -> meta_value (machine f) 8=0 ->
 Z.of_nat arg<=maximum -> Z.of_nat (S index)<=maximum ->
 total-Z.of_nat remaining-1=Z.of_nat index -> TokenByteExecution.separator sep ->
 stdin (machine f)=decimalBytes arg++sep::tail ->
 execLocalObserved (body total remaining) (f,observations)=Some (KeepGoing,(final_frame f index arg tail,observations)).
Proof.
 intros Hmeta Htoken Hpending Herror Harg Hword Hindex Hsep Hin.
 destruct (ReadFour.encoded_read (machine f) arg sep tail observations ltac:(lia) Htoken Hpending Herror Harg Hsep Hin)
  as (Hread & Htoken' & Hpending' & Hinput & Houtput).
 destruct Hread as [Hrun [Hmeta' [Hnumber [Hvalid Herror']]]].
 assert (Harg':coerceInt (Z.of_nat index+1) 64=Z.of_nat (S index)).
 { rewrite Nat2Z.inj_succ. apply coerce_word. unfold word;lia. }
 unfold body.
 Ltac run_steps Hindex Harg' Herror Herror' Hvalid Hnumber Hrun f arg tail observations := repeat first [progress cbn [optionBind fst snd negb bind machine setMachine setNum nums]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];rewrite ?store_meta_length,?DecimalInput.encoded_meta_length;
     first [lia|cbn [memory withMemory];rewrite growArrays_same,growList_length,?Nat2Z.id;lia])
 |progress unfold addInt at 1
 |progress rewrite Hindex|progress rewrite Harg'|progress rewrite Nat2Z.id
 |progress rewrite Herror|progress rewrite Herror'|progress rewrite Hvalid|progress rewrite Hnumber
 |progress rewrite RenameMemoControl.updated_same|progress rewrite RenameMemoControl.updated_other by discriminate
 |progress replace (Z.to_nat 8) with 8%nat by reflexivity
 |progress replace (Z.to_nat 14) with 14%nat by reflexivity
 |progress replace (Z.to_nat 11) with 11%nat by reflexivity
 |progress replace (Z.to_nat 2) with 2%nat by reflexivity
 |match goal with |- context[@execObserved ?I ?T ?EI ?R (funcdef_0__readNat ?bs ?ns) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__readNat bs ns) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(DecimalInput.encoded_result (machine f) arg tail,observations))) by exact Hrun;rewrite Hsame;clear Hsame end
 |multimatch goal with |-context[bool_decide ?P]=>first
  [progress rewrite (bool_decide_true P) by congruence|progress rewrite (bool_decide_false P) by congruence] end
 |progress cbn [dropWithinLoop Action_rect]
 ].
 run_steps Hindex Harg' Herror Herror' Hvalid Hnumber Hrun f arg tail observations.
 destruct (bool_decide (Z.of_nat arg<meta_value (DecimalInput.encoded_result (machine f) arg tail) 2)) eqn:Hbranch;
   run_steps Hindex Harg' Herror Herror' Hvalid Hnumber Hrun f arg tail observations;unfold final_frame,result,checked,written;rewrite Hbranch;reflexivity.
Qed.
Lemma written_other s index arg name : name<>arraydef_0__schemaArguments -> memory (written s index arg) name=memory s name.
Proof. intro Hname. unfold written. cbn [memory withMemory]. rewrite InternTailExecution.modify_other by exact Hname. now apply growArrays_other. Qed.
Lemma written_arguments s index arg : memory (written s index arg) arraydef_0__schemaArguments=
 <[index:=arg]> (growList (memory s arraydef_0__schemaArguments) (S index) 0).
Proof. unfold written. cbn [memory withMemory]. now rewrite InternTailExecution.modify_same,growArrays_same. Qed.
Lemma result_meta_length s index arg tail : length (memory (result s index arg tail) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold result. rewrite written_other by discriminate. unfold checked. destruct (bool_decide _);rewrite ?store_meta_length;apply DecimalInput.encoded_meta_length. Qed.
Lemma result_token_length s index arg tail : length (memory (result s index arg tail) arraydef_0__token)=length (memory s arraydef_0__token).
Proof. unfold result. rewrite written_other by discriminate. unfold checked. destruct (bool_decide _);rewrite ?store_meta_other by discriminate;apply DecimalInput.encoded_token_length. Qed.
Lemma result_meta_other s index arg tail slot :
 (18<length (memory s arraydef_0__meta))%nat ->
 slot<>6%nat -> slot<>11%nat -> slot<>14%nat -> slot<>17%nat -> slot<>18%nat ->
 meta_value (result s index arg tail) slot=meta_value s slot.
Proof.
 intros Hmeta H6 H11 H14 H17 H18. unfold result,meta_value. rewrite written_other by discriminate.
 change (meta_value (checked (DecimalInput.encoded_result s arg tail) (Z.of_nat arg)) slot=meta_value s slot).
 unfold checked. destruct (bool_decide _);rewrite ?meta_store_other by exact H18;
   apply DecimalInput.encoded_meta_other;try assumption;lia.
Qed.
Lemma result_io s index arg tail : (17<length (memory s arraydef_0__meta))%nat -> Z.of_nat arg<=maximum ->
 stdin (result s index arg tail)=tail /\ stdout (result s index arg tail)=stdout s.
Proof.
 intros Hmeta Harg. destruct (DecimalInput.encoded_result_correct s arg tail Hmeta Harg) as [_ Hio].
 unfold result,checked,written. destruct (bool_decide _);exact Hio.
Qed.
Definition separator_for (rest:list nat) : Z := match rest with []=>10|_=>32 end.
Fixpoint wire (args:list nat) : list Z := match args with []=>[]|arg::rest=>decimalBytes arg++separator_for rest::wire rest end.
Lemma valid_separator rest : TokenByteExecution.separator (separator_for rest).
Proof. destruct rest;unfold separator_for,TokenByteExecution.separator;auto. Qed.
Fixpoint consume (f:Frame) start args tail : Frame := match args with
 | []=>f|arg::rest=>consume (final_frame f start arg (wire rest++tail)) (S start) rest tail end.
Theorem generated_loop args : forall (f:Frame) total start tail observations,
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 (1024<=length (memory (machine f) arraydef_0__token))%nat ->
 meta_value (machine f) 15=0 -> meta_value (machine f) 8=0 ->
 Forall (fun arg=>Z.of_nat arg<=maximum) args -> Z.of_nat (start+length args)<=maximum ->
 total=Z.of_nat (start+length args) -> stdin (machine f)=wire args++tail ->
 execLocalObserved (loop (length args) (body total)) (f,observations)=Some (tt,(consume f start args tail,observations)).
Proof.
 induction args as [|arg rest IH];intros f total start tail observations Hmeta Htoken Hpending Herror Hargs Hword Htotal Hin.
 - reflexivity.
 - inversion Hargs as [|value values Harg Hrest];subst value values.
   assert (Hinput:stdin (machine f)=decimalBytes arg++separator_for rest::(wire rest++tail)).
   { cbn [wire] in Hin. now rewrite <-app_assoc in Hin. }
   pose proof (generated_body f total (length rest) start arg (separator_for rest) (wire rest++tail) observations Hmeta Htoken Hpending Herror Harg
     ltac:(cbn [length] in Hword;lia) ltac:(cbn [length] in Htotal;lia) (valid_separator rest) Hinput) as Hfirst.
   change (length (arg::rest)) with (S (length rest)).
   rewrite loop_S,local_bind,Hfirst. cbn [optionBind fst snd consume].
   apply IH.
   + unfold final_frame. cbn [machine setMachine setNum]. rewrite result_meta_length. exact Hmeta.
   + unfold final_frame. cbn [machine setMachine setNum]. rewrite result_token_length. exact Htoken.
   + unfold final_frame. cbn [machine setMachine setNum]. rewrite result_meta_other by (try exact Hmeta;lia). exact Hpending.
   + unfold final_frame. cbn [machine setMachine setNum]. rewrite result_meta_other by (try exact Hmeta;lia). exact Herror.
   + exact Hrest.
   + cbn [length] in Hword. lia.
   + cbn [length] in Htotal. lia.
   + unfold final_frame. cbn [machine setMachine setNum]. exact (proj1 (result_io (machine f) start arg (wire rest++tail) ltac:(lia) Harg)).
Qed.
Lemma nth_error_insert_same {A} (xs:list A) index value : (index<length xs)%nat ->
 nth_error (<[index:=value]>xs) index=Some value.
Proof. induction xs as [|head rest IH] in index|-*;[cbn;lia|]. destruct index;cbn;[reflexivity|intro H;apply IH;lia]. Qed.
Lemma nth_error_insert_other {A} (xs:list A) index value other : other<>index ->
 nth_error (<[index:=value]>xs) other=nth_error xs other.
Proof. induction xs as [|head rest IH] in index,other|-*;[destruct index,other;reflexivity|]. destruct index,other;cbn;try congruence;intro H;apply IH;lia. Qed.
Lemma written_same s index value : nth_error (memory (written s index value) arraydef_0__schemaArguments) index=Some value.
Proof. rewrite written_arguments. apply nth_error_insert_same. rewrite growList_length;lia. Qed.
Lemma written_preserves s index value other previous : other<>index ->
 nth_error (memory s arraydef_0__schemaArguments) other=Some previous ->
 nth_error (memory (written s index value) arraydef_0__schemaArguments) other=Some previous.
Proof.
 intros Hother Hlookup. rewrite written_arguments,nth_error_insert_other by exact Hother.
 unfold growList. rewrite nth_error_app1;[exact Hlookup|apply nth_error_Some;congruence].
Qed.
Lemma result_same s index arg tail : nth_error (memory (result s index arg tail) arraydef_0__schemaArguments) index=Some (Z.of_nat arg).
Proof. apply written_same. Qed.
Lemma result_preserves s index arg tail other previous : other<>index ->
 nth_error (memory s arraydef_0__schemaArguments) other=Some previous ->
 nth_error (memory (result s index arg tail) arraydef_0__schemaArguments) other=Some previous.
Proof.
 intros Hother Hlookup. apply written_preserves;[exact Hother|]. unfold checked. destruct (bool_decide _);
 rewrite ?store_meta_other,DecimalInput.encoded_other by discriminate;exact Hlookup.
Qed.
Lemma consume_preserves args : forall (f:Frame) start tail other previous,(other<start)%nat ->
 nth_error (memory (machine f) arraydef_0__schemaArguments) other=Some previous ->
 nth_error (memory (machine (consume f start args tail)) arraydef_0__schemaArguments) other=Some previous.
Proof.
 induction args as [|arg rest IH];intros f start tail other previous Hbound Hlookup;[exact Hlookup|].
 cbn [consume]. apply IH;[lia|]. apply result_preserves;[lia|exact Hlookup].
Qed.
Theorem consume_arguments args : forall (f:Frame) start tail offset id,nth_error args offset=Some id ->
 nth_error (memory (machine (consume f start args tail)) arraydef_0__schemaArguments) (start+offset)=Some (Z.of_nat id).
Proof.
 induction args as [|arg rest IH];intros f start tail offset id Hlookup;[destruct offset;discriminate|].
 destruct offset as [|offset].
 - injection Hlookup as <-. cbn [consume]. rewrite Nat.add_0_r. apply consume_preserves;[lia|]. apply result_same.
 - cbn [consume]. replace (start+S offset)%nat with (S start+offset)%nat by lia. now apply IH.
Qed.
Theorem consume_represents args (f:Frame) tail :
 SchemaEvaluationArguments.represents (machine (consume f 0 args tail)) args.
Proof. intros index id Hlookup. exact (consume_arguments args f 0 tail index id Hlookup). Qed.
Lemma result_valid s index arg tail : (18<length (memory s arraydef_0__meta))%nat ->
 meta_value (result s index arg tail) 18=
   if bool_decide (Z.of_nat arg<meta_value s 2) then meta_value s 18 else 0.
Proof.
 intro Hmeta. unfold result,meta_value. rewrite written_other by discriminate.
 change (meta_value (checked (DecimalInput.encoded_result s arg tail) (Z.of_nat arg)) 18=
   if bool_decide (Z.of_nat arg<meta_value s 2) then meta_value s 18 else 0).
 unfold checked. rewrite (DecimalInput.encoded_meta_other s arg tail 2 ltac:(lia)) by lia.
 destruct (bool_decide (Z.of_nat arg<meta_value s 2)).
 - apply DecimalInput.encoded_meta_other;lia.
 - apply meta_store_same. rewrite DecimalInput.encoded_meta_length;exact Hmeta.
Qed.
Lemma consume_meta_length args : forall (f:Frame) start tail,
 length (memory (machine (consume f start args tail)) arraydef_0__meta)=length (memory (machine f) arraydef_0__meta).
Proof. induction args as [|arg rest IH];intros f start tail;[reflexivity|]. cbn [consume]. rewrite IH. apply result_meta_length. Qed.
Lemma consume_meta_other args : forall (f:Frame) start tail slot,
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 slot<>6%nat -> slot<>11%nat -> slot<>14%nat -> slot<>17%nat -> slot<>18%nat ->
 meta_value (machine (consume f start args tail)) slot=meta_value (machine f) slot.
Proof.
 induction args as [|arg rest IH];intros f start tail slot Hmeta H6 H11 H14 H17 H18;[reflexivity|].
 cbn [consume]. rewrite IH by (try assumption;cbn [final_frame machine setMachine setNum];rewrite result_meta_length;exact Hmeta).
 apply result_meta_other;assumption.
Qed.
Theorem consume_valid args : forall (f:Frame) start tail,
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 meta_value (machine (consume f start args tail)) 18=
  if forallb (fun id=>bool_decide (Z.of_nat id<meta_value (machine f) 2)) args then meta_value (machine f) 18 else 0.
Proof.
 induction args as [|arg rest IH];intros f start tail Hmeta;[reflexivity|].
 cbn [consume]. rewrite IH by (cbn [final_frame machine setMachine setNum];rewrite result_meta_length;exact Hmeta).
 cbn [final_frame machine setMachine setNum].
 rewrite result_meta_other by (try exact Hmeta;lia). rewrite result_valid by exact Hmeta.
 cbn [forallb]. destruct (bool_decide (Z.of_nat arg<meta_value (machine f) 2)),
   (forallb (fun id=>bool_decide (Z.of_nat id<meta_value (machine f) 2)) rest);reflexivity.
Qed.
Lemma result_other s index arg tail name : name<>arraydef_0__meta -> name<>arraydef_0__token -> name<>arraydef_0__schemaArguments ->
 memory (result s index arg tail) name=memory s name.
Proof.
 intros Hmeta Htoken Hargs. unfold result. rewrite written_other by exact Hargs.
 unfold checked. destruct (bool_decide _);rewrite ?store_meta_other by exact Hmeta;
 apply DecimalInput.encoded_other;assumption.
Qed.
Lemma consume_other args : forall (f:Frame) start tail name,
 name<>arraydef_0__meta -> name<>arraydef_0__token -> name<>arraydef_0__schemaArguments ->
 memory (machine (consume f start args tail)) name=memory (machine f) name.
Proof.
 induction args as [|arg rest IH];intros f start tail name Hmeta Htoken Hargs;[reflexivity|].
 cbn [consume]. rewrite IH by assumption. apply result_other;assumption.
Qed.
Lemma consume_projection args (f:Frame) start tail : (18<length (memory (machine f) arraydef_0__meta))%nat ->
 FormulaProjection.storage (machine f) (machine (consume f start args tail)).
Proof.
 intro Hmeta. split;[apply consume_meta_length|]. split.
 - intros name Hneeded. unfold FormulaProjection.needed in Hneeded.
   destruct Hneeded as [Hn|[Hn|[Hn|Hn]]];subst name;apply consume_other;discriminate.
 - repeat split;apply consume_meta_other;try exact Hmeta;lia.
Qed.
Theorem consume_representations args (f:Frame) start tail logical :
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 NativeRepresentation.canonical_arena (machine f) (Protocol.formulas logical) ->
 ClassStorage.represents (machine f) (Protocol.formulas logical) (Protocol.classes logical) ->
 HistoryRefinement.represents (machine f) logical -> NameRepresentation.represents (machine f) (Protocol.bindings logical) ->
 SchemaRepresentation.represents (machine f) logical ->
 NativeRepresentation.canonical_arena (machine (consume f start args tail)) (Protocol.formulas logical) /\
 ClassStorage.represents (machine (consume f start args tail)) (Protocol.formulas logical) (Protocol.classes logical) /\
 HistoryRefinement.represents (machine (consume f start args tail)) logical /\
 NameRepresentation.represents (machine (consume f start args tail)) (Protocol.bindings logical) /\
 SchemaRepresentation.represents (machine (consume f start args tail)) logical.
Proof.
 intros Hmeta Harena Hclasses Hhistory Hnames Hschemas. split.
 - eapply FormulaProjection.storage_arena;[apply consume_projection;exact Hmeta|exact Harena].
 - split.
   + unfold ClassStorage.represents in *. rewrite consume_meta_other by (try exact Hmeta;lia).
     rewrite consume_other by discriminate. exact Hclasses.
   + split.
     * unfold HistoryRefinement.represents in *. rewrite consume_meta_other by (try exact Hmeta;lia).
       rewrite consume_other by discriminate. exact Hhistory.
     * split.
       -- unfold NameRepresentation.represents in *. rewrite !consume_meta_other by (try exact Hmeta;lia).
          rewrite !consume_other by discriminate. exact Hnames.
       -- eapply SchemaRepresentation.transport;[exact Hschemas| | |reflexivity|reflexivity|reflexivity].
          ++ apply consume_meta_other;try exact Hmeta;lia.
          ++ apply consume_other;discriminate.
Qed.
Lemma consume_io args : forall (f:Frame) start tail,
 (18<length (memory (machine f) arraydef_0__meta))%nat -> Forall (fun arg=>Z.of_nat arg<=maximum) args ->
 stdin (machine f)=wire args++tail ->
 stdin (machine (consume f start args tail))=tail /\ stdout (machine (consume f start args tail))=stdout (machine f).
Proof.
 induction args as [|arg rest IH];intros f start tail Hmeta Hwords Hin.
 - split;[exact Hin|reflexivity].
 - inversion Hwords as [|value values Harg Hrest];subst value values.
   destruct (result_io (machine f) start arg (wire rest++tail) ltac:(lia) Harg) as [Hinput Houtput].
   destruct (IH (final_frame f start arg (wire rest++tail)) (S start) tail
     ltac:(cbn [final_frame machine setMachine setNum];rewrite result_meta_length;exact Hmeta) Hrest Hinput) as [Htail Hout].
   split;[exact Htail|]. cbn [consume]. rewrite Hout. exact Houtput.
Qed.
Theorem generated_arguments (f:Frame) args tail observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 (1024<=length (memory (machine f) arraydef_0__token))%nat ->
 meta_value (machine f) 15=0 -> meta_value (machine f) 8=0 ->
 Forall (fun arg=>Z.of_nat arg<=maximum) args -> Z.of_nat (length args)<=maximum ->
 stdin (machine f)=wire args++tail ->
 let after:=consume f 0 args tail in
 execLocalObserved (loop (length args) (body (Z.of_nat (length args)))) (f,observations)=Some (tt,(after,observations)) /\
 SchemaEvaluationArguments.represents (machine after) args /\
 stdin (machine after)=tail /\ stdout (machine after)=stdout (machine f) /\
 meta_value (machine after) 8=0 /\
 meta_value (machine after) 18=
  if forallb (fun id=>bool_decide (Z.of_nat id<meta_value (machine f) 2)) args then meta_value (machine f) 18 else 0.
Proof.
 intros Hmeta Htoken Hpending Herror Hwords Hcount Hin after.
 split;[eapply generated_loop;try eassumption;reflexivity|].
 split;[apply consume_represents|]. destruct (consume_io args f 0 tail Hmeta Hwords Hin) as [Hinput Houtput].
 split;[exact Hinput|]. split;[exact Houtput|]. split.
 - unfold after. rewrite consume_meta_other by (try exact Hmeta;lia). exact Herror.
 - apply consume_valid;exact Hmeta.
Qed.
Lemma wire_nonempty args : args<>[] -> wire args=Protocol.join_tokens (Protocol.number_tokens args)++[10].
Proof.
 induction args as [|arg rest IH];[contradiction|]. intro Hnonempty.
 destruct rest as [|next rest].
 - cbn [wire separator_for Protocol.number_tokens Protocol.join_tokens map]. reflexivity.
 - change (decimalBytes arg++32::wire (next::rest)=
     (decimalBytes arg++32::Protocol.join_tokens (Protocol.number_tokens (next::rest)))++[10]).
   rewrite IH by discriminate. now rewrite <-app_assoc.
Qed.
Lemma request_wire args name :
 Protocol.request_bytes (Protocol.Req 24 args name)=decimalBytes 24++32::name++32::decimalBytes (length args)++
   match args with []=>[10]|_=>32::wire args end.
Proof.
 destruct args as [|arg rest].
 - unfold Protocol.request_bytes. cbn [Protocol.request_bytes Protocol.opcode Protocol.arguments Protocol.object_name Protocol.join_tokens Protocol.number_tokens map length].
   repeat rewrite <-app_assoc;reflexivity.
 - rewrite wire_nonempty by discriminate. unfold Protocol.request_bytes.
   cbn [Protocol.request_bytes Protocol.opcode Protocol.arguments Protocol.object_name Protocol.number_tokens map Protocol.join_tokens].
   repeat rewrite <-app_assoc;reflexivity.
Qed.
End SchemaInstanceArguments.
