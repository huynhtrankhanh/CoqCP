From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives CommandQuit CommandStructure CommandChain CommandDispatch
  ReplyNO RenameMemoControl ArrayFacts Overflow InternTail.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module ClassCertifyRejectedCommand.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Definition frame_after (f : Frame) parsed (found : bool) binding tid :=
  setMachine (setNum (setNum f vardef_0__command_binding (if found then Z.of_nat binding else maximum))
    vardef_0__command_a (Z.of_nat tid)) (ReplyNOExecution.reply_state parsed).
Local Opaque funcdef_0__no funcdef_0__readToken funcdef_0__lookup Imperative.update.
Theorem generated_handler reader (f : Frame) named looked parsed (found : bool) binding tid offset size value flag kind observations :
  (17<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
  execObserved (funcdef_0__readToken (fun _=>false) (fun _=>0)) (machine f,observations)=Some (tt,(named,observations)) ->
  (17<length (memory named arraydef_0__meta))%nat -> meta_value named 14=1 -> meta_value named 8=0 ->
  execObserved (funcdef_0__lookup (fun _=>false) (fun _=>0)) (named,observations)=Some (tt,(looked,observations)) ->
  (17<length (memory looked arraydef_0__meta))%nat -> meta_value looked 0=(if found then Z.of_nat binding else maximum) -> meta_value looked 8=0 ->
  execObserved (reader (fun _=>false) (fun _=>0)) (looked,observations)=Some (tt,(parsed,observations)) ->
  (17<length (memory parsed arraydef_0__meta))%nat ->
  meta_value parsed 11=Z.of_nat tid -> meta_value parsed 14=1 -> meta_value parsed 8=0 ->
  (found=true -> Z.of_nat binding<>maximum) ->
  (found=true -> binding<length (memory parsed arraydef_0__bindings))%nat ->
  (found=true -> nth_error (memory parsed arraydef_0__bindings) binding=Some (offset,size,value,flag,kind)) ->
  (found=false \/ kind<>0 \/ meta_value parsed 3<=Z.of_nat tid) ->
  execLocalObserved (CommandStructure.handler_14 reader) (f,observations)=
    Some (tt,(frame_after f parsed found binding tid,
      observations++[{|flushedOutput:=stdout parsed++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin parsed|}])).
Proof.
  intros Hinitial Hinitialerror Htoken Hnamed Hvalid Hnamederror Hlookup Hlooked Hbinding Hlookederror Hread Hparsed
    Htid Hparsedvalid Hparsederror Hsentinel Hbound Hrecord Hinvalid.
  assert (Hnth : found=true -> List.nth binding (memory parsed arraydef_0__bindings) (0,0,0,0,0)=(offset,size,value,flag,kind)).
  { intro Hfound. exact (List.nth_error_nth _ _ (0,0,0,0,0) (Hrecord Hfound)). }
  unfold maximum in *.
  destruct found eqn:Hfound; [destruct (Z.eq_dec kind 0) as [Hkind|Hkind]|];
    try subst kind; try specialize (Hsentinel eq_refl);
    destruct f as [s bs ns]; cbn [machine] in *; unfold CommandStructure.handler_14.
  all: repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id;
      lazymatch name with
      |arraydef_0__meta => first [eapply Nat.le_lt_trans with (m:=17%nat); [cbn;lia|exact Hparsed]
        |eapply Nat.le_lt_trans with (m:=17%nat); [cbn;lia|exact Hlooked]
        |eapply Nat.le_lt_trans with (m:=17%nat); [cbn;lia|exact Hnamed]
        |eapply Nat.le_lt_trans with (m:=17%nat); [cbn;lia|exact Hinitial]]
      |arraydef_0__bindings => exact Hbound
      end)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (?callee ?bo ?no) ?state] =>
       let expression:=constr:(@execObserved I T EI R (callee bo no) state) in
       let Hrun:=fresh in first
         [assert (Hrun:expression=Some (tt,(named,observations))) by exact Htoken
         |assert (Hrun:expression=Some (tt,(looked,observations))) by exact Hlookup
         |assert (Hrun:expression=Some (tt,(parsed,observations))) by exact Hread
         ]; rewrite Hrun;clear Hrun end
    |progress rewrite Hnth
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bo ?no) (?current,?trace)] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__no bo no) (current,trace)) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(ReplyNOExecution.reply_state current,
         trace++[{|flushedOutput:=stdout current++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin current|}]))) by
         (apply ReplyNOExecution.generated_no);rewrite Hrun;clear Hrun end
    |progress rewrite Hinitialerror |progress rewrite Hvalid |progress rewrite Hnamederror
    |progress rewrite Hbinding |progress rewrite Hlookederror |progress rewrite Htid
    |progress rewrite Hparsedvalid |progress rewrite Hparsederror 
    |progress rewrite Nat2Z.id
    |progress specialize (Hbound eq_refl) |progress specialize (Hrecord eq_refl)
    |progress specialize (Hnth eq_refl)
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 3) with 3%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; intuition lia)
       |progress rewrite (bool_decide_false P) by (try congruence; intuition lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
    |progress rewrite RenameMemoControl.updated_same |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ].
  all: unfold frame_after; rewrite ?Hfound; reflexivity.
Qed.
Theorem generated_command s bs ns opstate named looked parsed (found : bool) binding tid offset size value flag kind observations :
  execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (s,observations)=Some (tt,(opstate,observations)) ->
  (17<length (memory opstate arraydef_0__meta))%nat -> meta_value opstate 11=14 -> meta_value opstate 14=1 -> meta_value opstate 8=0 ->
  execObserved (funcdef_0__readToken (fun _=>false) (fun _=>0)) (opstate,observations)=Some (tt,(named,observations)) ->
  (17<length (memory named arraydef_0__meta))%nat -> meta_value named 14=1 -> meta_value named 8=0 ->
  execObserved (funcdef_0__lookup (fun _=>false) (fun _=>0)) (named,observations)=Some (tt,(looked,observations)) ->
  (17<length (memory looked arraydef_0__meta))%nat -> meta_value looked 0=(if found then Z.of_nat binding else maximum) -> meta_value looked 8=0 ->
  execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (looked,observations)=Some (tt,(parsed,observations)) ->
  (17<length (memory parsed arraydef_0__meta))%nat ->
  meta_value parsed 11=Z.of_nat tid -> meta_value parsed 14=1 -> meta_value parsed 8=0 ->
  (found=true -> Z.of_nat binding<>maximum) ->
  (found=true -> binding<length (memory parsed arraydef_0__bindings))%nat ->
  (found=true -> nth_error (memory parsed arraydef_0__bindings) binding=Some (offset,size,value,flag,kind)) ->
  (found=false \/ kind<>0 \/ meta_value parsed 3<=Z.of_nat tid) ->
  execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(ReplyNOExecution.reply_state parsed,
    observations++[{|flushedOutput:=stdout parsed++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin parsed|}])).
Proof.
  intros Hopcode Hopmeta Hopnumber Hopvalid Hoperror Htoken Hnamed Hvalid Hnamederror Hlookup Hlooked Hbinding Hlookederror Hread Hparsed
    Htid Hparsedvalid Hparsederror Hsentinel Hbound Hrecord Hinvalid.
  set (initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} opstate 14).
  set (after:=frame_after initial parsed found binding tid).
  apply (CommandDispatch.generated_positive_command s bs ns after opstate 14 observations
    (observations++[{|flushedOutput:=stdout parsed++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin parsed|}])) ; try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandChain.handler_for funcdef_0__readNat 14) (initial,observations)=
      Some (tt,(after,observations++[{|flushedOutput:=stdout parsed++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin parsed|}]))).
    eapply generated_handler with (named:=named) (looked:=looked) (offset:=offset) (size:=size) (value:=value) (flag:=flag) (kind:=kind); eassumption.
  - change (8<length (memory (ReplyNOExecution.reply_state parsed) arraydef_0__meta))%nat.
    rewrite ReplyNOExecution.reply_memory. lia.
Qed.
End ClassCertifyRejectedCommand.
