From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives CommandQuit CommandStructure CommandChain CommandDispatch ReplyOK ReplyNO RenameMemoControl ArrayFacts Overflow InternTail.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module ClassCertifyCommand.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Definition arguments cls := update (fun _=>0) vardef_0__setness_cls cls.
Definition certified (s : Machine) binding (offset size : Z) cls := withMemory s
  (modifyArray (memory s) arraydef_0__bindings binding (offset,size,Z.of_nat cls,1,0)).
Definition result s binding offset size cls (matches : bool) :=
  if matches then ReplyOKExecution.reply_state (certified s binding offset size cls) cls
  else ReplyNOExecution.reply_state s.
Definition reply cls (matches : bool) := if matches then Protocol.OK cls else Protocol.NO.
Definition frame_after (f : Frame) s binding tid offset size cls matches :=
  setMachine (setNum (setNum f vardef_0__command_binding (Z.of_nat binding)) vardef_0__command_a (Z.of_nat tid))
    (result s binding offset size cls matches).
Local Opaque funcdef_0__ok funcdef_0__no funcdef_0__setness funcdef_0__readToken funcdef_0__lookup Imperative.update.
Theorem generated_handler reader (f : Frame) named looked parsed built binding tid cls offset size flag formula matches observations :
  (17<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
  execObserved (funcdef_0__readToken (fun _=>false) (fun _=>0)) (machine f,observations)=Some (tt,(named,observations)) ->
  (17<length (memory named arraydef_0__meta))%nat -> meta_value named 14=1 -> meta_value named 8=0 ->
  execObserved (funcdef_0__lookup (fun _=>false) (fun _=>0)) (named,observations)=Some (tt,(looked,observations)) ->
  (17<length (memory looked arraydef_0__meta))%nat -> meta_value looked 0=Z.of_nat binding -> meta_value looked 8=0 ->
  execObserved (reader (fun _=>false) (fun _=>0)) (looked,observations)=Some (tt,(parsed,observations)) ->
  (17<length (memory parsed arraydef_0__meta))%nat ->
  meta_value parsed 11=Z.of_nat tid -> meta_value parsed 14=1 -> meta_value parsed 8=0 ->
  Z.of_nat binding<>18446744073709551615 -> (binding<length (memory parsed arraydef_0__bindings))%nat ->
  nth_error (memory parsed arraydef_0__bindings) binding=Some (offset,size,Z.of_nat cls,flag,0) ->
  Z.of_nat tid<meta_value parsed 3 ->
  execObserved (funcdef_0__setness (fun _=>false) (arguments (Z.of_nat cls))) (parsed,observations)=Some (tt,(built,observations)) ->
  (17<length (memory built arraydef_0__meta))%nat -> meta_value built 8=0 ->
  (tid<length (memory built arraydef_0__theorems))%nat -> nth_error (memory built arraydef_0__theorems) tid=Some formula ->
  (binding<length (memory built arraydef_0__bindings))%nat ->
  nth_error (memory built arraydef_0__bindings) binding=Some (offset,size,Z.of_nat cls,flag,0) ->
  (matches=true -> meta_value built 0=formula) -> (matches=false -> meta_value built 0<>formula) ->
  (20<=length (memory built arraydef_0__printBuffer))%nat -> Z.of_nat cls<=maximum ->
  execLocalObserved (CommandStructure.handler_14 reader) (f,observations)=
    Some (tt,(frame_after f built binding tid offset size cls matches,
      observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes (reply cls matches);unreadInput:=stdin built|}])).
Proof.
  intros Hinitial Hinitialerror Htoken Hnamed Hvalid Hnamederror Hlookup Hlooked Hbinding Hlookederror Hread Hparsed
    Htid Hparsedvalid Hparsederror Hsentinel Hbound Hrecord Htidcount Hsetness Hbuilt Herror Htheorembound Htheorem
    Hbuiltbound Hbuiltrecord Hyes Hno Hbuffer Hword.
  pose proof (List.nth_error_nth _ _ (0,0,0,0,0) Hrecord) as Hnth.
  pose proof (List.nth_error_nth _ _ (0,0,0,0,0) Hbuiltrecord) as Hbuilt_nth.
  pose proof (List.nth_error_nth _ _ 0 Htheorem) as Htheorem_nth.
  assert (Hcertbound : (binding<length (memory (certified built binding offset size cls) arraydef_0__bindings))%nat).
  { change (binding<length (<[binding:=(offset,size,Z.of_nat cls,1%Z,0%Z)]>(memory built arraydef_0__bindings)))%nat.
    rewrite length_insert. exact Hbuiltbound. }
  assert (Hcertnth : List.nth binding (memory (certified built binding offset size cls) arraydef_0__bindings) (0,0,0,0,0)=
    (offset,size,Z.of_nat cls,1,0)).
  { change (List.nth binding (<[binding:=(offset,size,Z.of_nat cls,1%Z,0%Z)]>(memory built arraydef_0__bindings)) (0,0,0,0,0)=(offset,size,Z.of_nat cls,1,0)).
    apply OverflowExecution.nth_insert_same. exact Hbuiltbound. }
  destruct matches eqn:Hmatches; [specialize (Hyes eq_refl)|specialize (Hno eq_refl)];
    destruct f as [s bs ns]; cbn [machine] in *; unfold CommandStructure.handler_14.
  all: repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id;
      lazymatch name with
      |arraydef_0__meta => first [eapply Nat.le_lt_trans with (m:=17%nat); [cbn;lia|exact Hbuilt]
        |eapply Nat.le_lt_trans with (m:=17%nat); [cbn;lia|exact Hparsed]
        |eapply Nat.le_lt_trans with (m:=17%nat); [cbn;lia|exact Hlooked]
        |eapply Nat.le_lt_trans with (m:=17%nat); [cbn;lia|exact Hnamed]
        |eapply Nat.le_lt_trans with (m:=17%nat); [cbn;lia|exact Hinitial]]
      |arraydef_0__bindings => first [exact Hbound|exact Hbuiltbound|exact Hcertbound]
      |arraydef_0__theorems => exact Htheorembound end)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (?callee ?bo ?no) ?state] =>
       let expression:=constr:(@execObserved I T EI R (callee bo no) state) in
       let Hrun:=fresh in first
         [assert (Hrun:expression=Some (tt,(named,observations))) by exact Htoken
         |assert (Hrun:expression=Some (tt,(looked,observations))) by exact Hlookup
         |assert (Hrun:expression=Some (tt,(parsed,observations))) by exact Hread
         |assert (Hrun:expression=Some (tt,(built,observations))) by exact Hsetness]; rewrite Hrun;clear Hrun end
    |match goal with |- context [List.nth ?i (memory ?source arraydef_0__bindings) ?zero] =>
       let expression:=constr:(List.nth i (memory source arraydef_0__bindings) zero) in
       let Hraw:=fresh in first
         [assert (Hraw:expression=(offset,size,Z.of_nat cls,flag,0)) by exact Hnth
         |assert (Hraw:expression=(offset,size,Z.of_nat cls,flag,0)) by exact Hbuilt_nth
         |assert (Hraw:expression=(offset,size,Z.of_nat cls,1,0)) by exact Hcertnth];
       rewrite Hraw;clear Hraw end
    |match goal with |- context [List.nth ?i (memory ?source arraydef_0__theorems) ?zero] =>
       let expression:=constr:(List.nth i (memory source arraydef_0__theorems) zero) in
       let Hraw:=fresh in assert (Hraw:expression=formula) by exact Htheorem_nth;rewrite Hraw;clear Hraw end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__ok ?bo ?no) (?current,?trace)] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__ok bo no) (current,trace)) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(ReplyOKExecution.reply_state current cls,
         trace++[{|flushedOutput:=stdout current++Protocol.reply_bytes (Protocol.OK cls);unreadInput:=stdin current|}]))) by
         (apply ReplyOKExecution.generated_ok; [reflexivity|exact Hword|exact Hbuffer]);rewrite Hrun;clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bo ?no) (?current,?trace)] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__no bo no) (current,trace)) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(ReplyNOExecution.reply_state current,
         trace++[{|flushedOutput:=stdout current++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin current|}]))) by
         (apply ReplyNOExecution.generated_no);rewrite Hrun;clear Hrun end
    |progress rewrite Hinitialerror |progress rewrite Hvalid |progress rewrite Hnamederror
    |progress rewrite Hbinding |progress rewrite Hlookederror |progress rewrite Htid
    |progress rewrite Hparsedvalid |progress rewrite Hparsederror |progress rewrite Herror
    |progress rewrite Nat2Z.id
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 3) with 3%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
    |progress rewrite RenameMemoControl.updated_same |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ].
  all: unfold frame_after,result,reply,certified; reflexivity.
Qed.
Lemma certified_other s binding offset size cls name : name<>arraydef_0__bindings ->
  memory (certified s binding offset size cls) name=memory s name.
Proof. intro Hname. unfold certified. cbn [memory withMemory]. now apply InternTailExecution.modify_other. Qed.
Lemma certified_record s binding offset size cls : (binding<length (memory s arraydef_0__bindings))%nat ->
  nth_error (memory (certified s binding offset size cls) arraydef_0__bindings) binding=Some (offset,size,Z.of_nat cls,1,0).
Proof.
  intro Hbound. change (nth_error (<[binding:=(offset,size,Z.of_nat cls,1,0)]>(memory s arraydef_0__bindings)) binding=Some (offset,size,Z.of_nat cls,1,0)).
  rewrite nth_error_nth' with (d:=(0,0,0,0,0)) by (rewrite length_insert;exact Hbound).
  f_equal. apply OverflowExecution.nth_insert_same. exact Hbound.
Qed.
Lemma result_meta s binding offset size cls matches :
  memory (result s binding offset size cls matches) arraydef_0__meta=memory s arraydef_0__meta.
Proof.
  destruct matches; cbn [result]; [rewrite ReplyOKExecution.reply_other by discriminate; apply certified_other; discriminate|
    apply ReplyNOExecution.reply_memory].
Qed.
Theorem generated_command s bs ns opstate named looked parsed built binding tid cls offset size flag formula matches observations :
  execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (s,observations)=Some (tt,(opstate,observations)) ->
  (17<length (memory opstate arraydef_0__meta))%nat ->
  meta_value opstate 11=14 -> meta_value opstate 14=1 -> meta_value opstate 8=0 ->
  execObserved (funcdef_0__readToken (fun _=>false) (fun _=>0)) (opstate,observations)=Some (tt,(named,observations)) ->
  (17<length (memory named arraydef_0__meta))%nat -> meta_value named 14=1 -> meta_value named 8=0 ->
  execObserved (funcdef_0__lookup (fun _=>false) (fun _=>0)) (named,observations)=Some (tt,(looked,observations)) ->
  (17<length (memory looked arraydef_0__meta))%nat -> meta_value looked 0=Z.of_nat binding -> meta_value looked 8=0 ->
  execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (looked,observations)=Some (tt,(parsed,observations)) ->
  (17<length (memory parsed arraydef_0__meta))%nat ->
  meta_value parsed 11=Z.of_nat tid -> meta_value parsed 14=1 -> meta_value parsed 8=0 ->
  Z.of_nat binding<>18446744073709551615 -> (binding<length (memory parsed arraydef_0__bindings))%nat ->
  nth_error (memory parsed arraydef_0__bindings) binding=Some (offset,size,Z.of_nat cls,flag,0) ->
  Z.of_nat tid<meta_value parsed 3 ->
  execObserved (funcdef_0__setness (fun _=>false) (arguments (Z.of_nat cls))) (parsed,observations)=Some (tt,(built,observations)) ->
  (17<length (memory built arraydef_0__meta))%nat -> meta_value built 8=0 ->
  (tid<length (memory built arraydef_0__theorems))%nat -> nth_error (memory built arraydef_0__theorems) tid=Some formula ->
  (binding<length (memory built arraydef_0__bindings))%nat ->
  nth_error (memory built arraydef_0__bindings) binding=Some (offset,size,Z.of_nat cls,flag,0) ->
  (matches=true -> meta_value built 0=formula) -> (matches=false -> meta_value built 0<>formula) ->
  (20<=length (memory built arraydef_0__printBuffer))%nat -> Z.of_nat cls<=maximum ->
  execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(result built binding offset size cls matches,
    observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes (reply cls matches);unreadInput:=stdin built|}])).
Proof.
  intros Hopcode Hopmeta Hopnumber Hopvalid Hoperror Htoken Hnamed Hvalid Hnamederror Hlookup Hlooked Hbinding Hlookederror Hread Hparsed
    Htid Hparsedvalid Hparsederror Hsentinel Hbound Hrecord Htidcount Hsetness Hbuilt Herror Htheorembound Htheorem
    Hbuiltbound Hbuiltrecord Hyes Hno Hbuffer Hword.
  set (initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} opstate 14).
  set (after:=frame_after initial built binding tid offset size cls matches).
  apply (CommandDispatch.generated_positive_command s bs ns after opstate 14 observations
    (observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes (reply cls matches);unreadInput:=stdin built|}])) ; try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandChain.handler_for funcdef_0__readNat 14) (initial,observations)=
      Some (tt,(after,observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes (reply cls matches);unreadInput:=stdin built|}]))).
    eapply generated_handler with (named:=named) (looked:=looked) (parsed:=parsed) (formula:=formula); eassumption.
  - change (8<length (memory (result built binding offset size cls matches) arraydef_0__meta))%nat.
    rewrite result_meta. lia.
  - change (meta_value (result built binding offset size cls matches) 8=0).
    unfold meta_value. rewrite result_meta. exact Herror.
Qed.
End ClassCertifyCommand.
