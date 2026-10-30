From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl CommandChain CommandStructure
 SchemaInstanceArguments SchemaEvaluationArguments SchemaInstanceHandler ReadName ReadToken TokenByte ReadFour DecimalInput NameSearch NameRepresentation TypedNameLookup FormulaProjection Representation ClassStorage HistoryRefinement SchemaRepresentation.
From NativeProof Require Import SchemaInstancePrefix NativeWhitespaceSchemaArguments.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaPrefix.
Import IndexExecution SipHashExecution ObservedLocal SchemaInstancePrefix.
Lemma generated_prefix (f:Frame) named looked counted fields tail (work:LocalAction unit) observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
 execObserved (funcdef_0__readToken (fun _=>false) (fun _=>0)) (machine f,observations)=Some (tt,(named,observations)) ->
 (18<length (memory named arraydef_0__meta))%nat -> meta_value named 14=1 -> meta_value named 8=0 ->
 execObserved (funcdef_0__lookup (fun _=>false) (fun _=>0)) (named,observations)=Some (tt,(looked,observations)) ->
 (18<length (memory looked arraydef_0__meta))%nat -> meta_value looked 8=0 ->
 execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (looked,observations)=Some (tt,(counted,observations)) ->
 (18<length (memory counted arraydef_0__meta))%nat -> meta_value counted 14=1 -> meta_value counted 8=0 ->
 meta_value counted 11=Z.of_nat (length fields) -> meta_value counted 15=0 ->
 (1024<=length (memory counted arraydef_0__token))%nat ->
 Forall (fun item=>Forall TokenByteExecution.separator (fst item) /\ Z.of_nat(snd item)<=maximum) fields -> Z.of_nat (length fields)<=maximum ->
 stdin counted=NativeWhitespaceSchemaArguments.spaced_wire fields++tail ->
 execLocalObserved (with_suffix work) (f,observations)=
 execLocalObserved work (SchemaInstanceArguments.consume (prepared f looked counted (length fields)) 0 (map snd fields) tail,observations).
Proof.
 intros Hmeta Herror Hname Hnamed Hnamevalid Hnameerror Hlookup Hlooked Hlookuperror
 Hcount Hcounted Hcountvalid Hcounterror Hcountnumber Hpending Htoken Hwords Hlength Hin.
 set (start:=prepared f looked counted (length fields)).
 assert (Hstartmeta:(18<length (memory (machine start) arraydef_0__meta))%nat).
 { unfold start,prepared. cbn [machine setMachine]. now rewrite store_meta_length. }
 assert (Hstarttoken:(1024<=length (memory (machine start) arraydef_0__token))%nat).
 { unfold start,prepared. cbn [machine setMachine]. now rewrite store_meta_other by discriminate. }
 assert (Hstartpending:meta_value (machine start) 15=0).
 { unfold start,prepared. cbn [machine setMachine]. now rewrite meta_store_other by discriminate. }
 assert (Hstarterror:meta_value (machine start) 8=0).
 { unfold start,prepared. cbn [machine setMachine]. now rewrite meta_store_other by discriminate. }
 assert (Hstartinput:stdin (machine start)=NativeWhitespaceSchemaArguments.spaced_wire fields++tail) by exact Hin.
 assert(Hargs:execLocalObserved (loop (length fields) (SchemaInstanceArguments.body (Z.of_nat (length fields)))) (start,observations)=Some(tt,(SchemaInstanceArguments.consume start 0 (map snd fields) tail,observations))).
 { pose proof(NativeWhitespaceSchemaArguments.generated_loop fields start (Z.of_nat(length fields)) 0 tail observations
    Hstartmeta Hstarttoken Hstartpending Hstarterror Hwords ltac:(lia) ltac:(cbn;lia) Hstartinput) as Hrun.
   rewrite NativeWhitespaceSchemaArguments.consume_canonical in Hrun. exact Hrun. }
 assert (Hloop:execLocalObserved arguments_loop (start,observations)=Some (tt,(SchemaInstanceArguments.consume start 0 (map snd fields) tail,observations))).
 { eapply eq_trans;[exact (generated_loop start (length fields) observations (prepared_count f looked counted (length fields)))|exact Hargs]. }
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
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(SchemaInstanceArguments.consume start 0 (map snd fields) tail,observations))) by exact Hloop;rewrite Hsame;clear Hsame end
  |progress rewrite SchemaInstanceHandler.option_unit].
 cbn [execLocalObserved]. repeat rewrite SchemaInstanceHandler.option_unit. reflexivity.
Qed.
End NativeWhitespaceSchemaPrefix.
