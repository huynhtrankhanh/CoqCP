From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl CommandChain CommandStructure
 DecimalInput ReadFour ReadNameOne TokenByte InternTail SchemaEvaluationArguments FormulaProjection Representation ClassStorage
 HistoryRefinement NameRepresentation SchemaRepresentation.
From NativeProof Require Import SchemaInstanceArguments NativeArgumentReadsFour NativeArgumentWhitespace NativeArgumentReadsTwo.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaArguments.
Import IndexExecution SipHashExecution ObservedLocal SchemaInstanceArguments.
Lemma generated_body (f:Frame) total remaining index arg spaces sep tail observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 (1024<=length (memory (machine f) arraydef_0__token))%nat ->
 meta_value (machine f) 15=0 -> meta_value (machine f) 8=0 ->
 Z.of_nat arg<=maximum -> Z.of_nat (S index)<=maximum ->
 total-Z.of_nat remaining-1=Z.of_nat index -> TokenByteExecution.separator sep -> Forall TokenByteExecution.separator spaces ->
 stdin (machine f)=spaces++decimalBytes arg++sep::tail ->
 execLocalObserved (body total remaining) (f,observations)=Some (KeepGoing,(final_frame f index arg tail,observations)).
Proof.
 intros Hmeta Htoken Hpending Herror Harg Hword Hindex Hsep Hspaces Hin.
 destruct (NativeArgumentReadsFour.read_leading (machine f) arg spaces sep tail observations ltac:(lia) Htoken Hpending Herror Harg Hsep Hspaces Hin)
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
Definition field := (list Z * nat)%type.
Fixpoint spaced_wire (args:list field) : list Z := match args with
 | []=>[] | (spaces,arg)::rest=>spaces++decimalBytes arg++separator_for (map snd rest)::spaced_wire rest end.
Fixpoint consume_spaced (f:Frame) start (args:list field) tail : Frame := match args with
 | []=>f | (_,arg)::rest=>consume_spaced (final_frame f start arg (spaced_wire rest++tail)) (S start) rest tail end.
Theorem generated_loop args : forall (f:Frame) total start tail observations,
 (18<length(memory(machine f)arraydef_0__meta))%nat -> (1024<=length(memory(machine f)arraydef_0__token))%nat ->
 meta_value(machine f)15=0 -> meta_value(machine f)8=0 ->
 Forall (fun item=>Forall TokenByteExecution.separator (fst item) /\ Z.of_nat(snd item)<=maximum) args ->
 Z.of_nat(start+length args)<=maximum -> total=Z.of_nat(start+length args) -> stdin(machine f)=spaced_wire args++tail ->
 execLocalObserved(loop(length args)(body total))(f,observations)=Some(tt,(consume_spaced f start args tail,observations)).
Proof.
 induction args as [|[spaces arg] rest IH];intros f total start tail observations Hmeta Htoken Hpending Herror Hargs Hword Htotal Hin.
 - reflexivity.
 - inversion Hargs as [|item items Hitem Hrest];subst item items. cbn [fst snd] in Hitem. destruct Hitem as [Hspaces Harg].
   assert(Hinput:stdin(machine f)=spaces++decimalBytes arg++separator_for(map snd rest)::(spaced_wire rest++tail)).
   { cbn [spaced_wire] in Hin. repeat rewrite <-app_assoc in Hin. exact Hin. }
   pose proof(generated_body f total (length rest) start arg spaces (separator_for(map snd rest)) (spaced_wire rest++tail) observations
     Hmeta Htoken Hpending Herror Harg ltac:(cbn [length] in Hword;lia) ltac:(cbn [length] in Htotal;lia)
     (valid_separator(map snd rest)) Hspaces Hinput) as Hfirst.
   change(length((spaces,arg)::rest)) with (S(length rest)). rewrite loop_S,local_bind,Hfirst. cbn [optionBind fst snd consume_spaced].
   apply IH.
   + unfold final_frame. cbn [machine setMachine setNum]. rewrite result_meta_length. exact Hmeta.
   + unfold final_frame. cbn [machine setMachine setNum]. rewrite result_token_length. exact Htoken.
   + unfold final_frame. cbn [machine setMachine setNum]. rewrite result_meta_other by (try exact Hmeta;lia). exact Hpending.
   + unfold final_frame. cbn [machine setMachine setNum]. rewrite result_meta_other by (try exact Hmeta;lia). exact Herror.
   + exact Hrest.
   + cbn [length] in Hword. lia.
   + cbn [length] in Htotal. lia.
   + unfold final_frame. cbn [machine setMachine setNum]. exact(proj1(result_io (machine f) start arg (spaced_wire rest++tail) ltac:(lia) Harg)).
Qed.
Lemma result_input s input index arg tail : result(withInput s input)index arg tail=result s index arg tail.
Proof. unfold result. now rewrite NativeArgumentWhitespace.encoded_result_input. Qed.
Lemma result_suffix s index arg tail1 tail2 : result s index arg tail1=withInput(result s index arg tail2)tail1.
Proof.
 unfold result. rewrite(NativeArgumentReadsTwo.encoded_suffix s arg tail1 tail2).
 unfold checked,written,meta_value. cbn [memory withInput withMemory].
 destruct(bool_decide (_<_));destruct s;reflexivity.
Qed.
Lemma frame_input (f:Frame) input index arg tail :
 final_frame (setMachine f (withInput(machine f)input)) index arg tail=final_frame f index arg tail.
Proof. destruct f as [s bs ns]. unfold final_frame. cbn [machine setMachine setNum]. rewrite result_input. reflexivity. Qed.
Lemma frame_suffix (f:Frame) index arg tail1 tail2 :
 final_frame f index arg tail1=setMachine(final_frame f index arg tail2)(withInput(machine(final_frame f index arg tail2))tail1).
Proof. destruct f as [s bs ns]. unfold final_frame. cbn [machine setMachine setNum]. rewrite (result_suffix s index arg tail1 tail2). reflexivity. Qed.
Lemma consume_spaced_input args : forall (f:Frame) input start tail,
 args<>[] -> consume_spaced (setMachine f (withInput(machine f)input)) start args tail=consume_spaced f start args tail.
Proof. destruct args as [|[spaces arg] rest];intros f input start tail Hnonempty;[contradiction|]. cbn [consume_spaced]. now rewrite frame_input. Qed.
Theorem consume_canonical args : forall (f:Frame) start tail,
 consume_spaced f start args tail=SchemaInstanceArguments.consume f start (map snd args) tail.
Proof.
 induction args as [|[spaces arg] rest IH];intros f start tail;[reflexivity|].
 cbn [consume_spaced map SchemaInstanceArguments.consume].
 destruct rest as [|item rest].
 - reflexivity.
 - rewrite(frame_suffix f start arg (spaced_wire(item::rest)++tail) (SchemaInstanceArguments.wire(map snd(item::rest))++tail)).
   rewrite consume_spaced_input by discriminate. apply IH.
Qed.
End NativeWhitespaceSchemaArguments.
