From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Schemata Protocol Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives TokenByte ReadFour ReadTwo ReadOne DecimalInput CommandArgs
  AxiomCommand AxiomDispatch AxiomReject AxiomReferenceReject CommandQuit CommandStructure CommandDispatch CommandChain RenameMemoControl
  ArenaFrame FormulaProjection Representation ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation SemanticFrames
  ReplyNO FormulaTopology HashTable InternInvariant.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomRejectionProtocol.
Import IndexExecution SipHashExecution ObservedLocal.

Local Opaque funcdef_0__axiom funcdef_0__appendTheorem funcdef_0__no Imperative.update.
Theorem generated_handler reader (f:AxiomCommand.Frame) first second third fourth built tag a b c observations :
  (17<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
  AxiomCommand.read_result reader (machine f) first tag observations ->
  AxiomCommand.read_result reader first second a observations ->
  AxiomCommand.read_result reader second third b observations ->
  AxiomCommand.read_result reader third fourth c observations ->
  execObserved (funcdef_0__axiom (fun _=>false) (AxiomCommand.arguments tag a b c)) (fourth,observations)=Some (tt,(built,observations)) ->
  (17<length (memory built arraydef_0__meta))%nat -> meta_value built 13=0 -> meta_value built 8=0 ->
  execLocalObserved (CommandStructure.handler_11 reader) (f,observations)=
    Some (tt,(setMachine (AxiomCommand.locals f tag a b c) (ReplyNOExecution.reply_state built),
      observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin built|}])).
Proof.
  intros Hinitial Herror [Hread1 [Hmeta1 [Hvalue1 [Hvalid1 Herror1]]]]
    [Hread2 [Hmeta2 [Hvalue2 [Hvalid2 Herror2]]]]
    [Hread3 [Hmeta3 [Hvalue3 [Hvalid3 Herror3]]]]
    [Hread4 [Hmeta4 [Hvalue4 [Hvalid4 Herror4]]]] Haxiom Hbuilt Hsuccess Hbuilt_error.
  destruct f as [s bs ns]; cbn [machine] in *; unfold CommandStructure.handler_11.
  all: repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hbuilt]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta4]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta3]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta2]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta1]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (?callee ?bo ?no) ?state] =>
       let expression:=constr:(@execObserved I T EI R (callee bo no) state) in
       let Hrun:=fresh in first
         [assert (Hrun:expression=Some (tt,(first,observations))) by exact Hread1
         |assert (Hrun:expression=Some (tt,(second,observations))) by exact Hread2
         |assert (Hrun:expression=Some (tt,(third,observations))) by exact Hread3
         |assert (Hrun:expression=Some (tt,(fourth,observations))) by exact Hread4
         |assert (Hrun:expression=Some (tt,(built,observations))) by exact Haxiom]; rewrite Hrun;clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bo ?no) (?current,?trace)] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__no bo no) (current,trace)) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(ReplyNOExecution.reply_state current,
         trace++[{|flushedOutput:=stdout current++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin current|}]))) by
         apply ReplyNOExecution.generated_no;rewrite Hrun;clear Hrun end
    |progress rewrite Herror |progress rewrite Herror1 |progress rewrite Herror2 |progress rewrite Herror3 |progress rewrite Herror4
    |progress rewrite Hvalid1 |progress rewrite Hvalid2 |progress rewrite Hvalid3 |progress rewrite Hvalid4
    |progress rewrite Hvalue1 |progress rewrite Hvalue2 |progress rewrite Hvalue3 |progress rewrite Hvalue4
    |progress rewrite Hsuccess
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 13) with 13%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence |progress rewrite (bool_decide_false P) by congruence] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence |progress rewrite (decide_False (P:=P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ].
  unfold AxiomCommand.locals;reflexivity.
Qed.
Theorem generated_command s bs ns opstate first second third fourth built tag a b c observations :
  AxiomCommand.read_result funcdef_0__readNat s opstate 11 observations ->
  AxiomCommand.read_result funcdef_0__readNat opstate first tag observations ->
  AxiomCommand.read_result funcdef_0__readNat first second a observations ->
  AxiomCommand.read_result funcdef_0__readNat second third b observations ->
  AxiomCommand.read_result funcdef_0__readNat third fourth c observations ->
  execObserved (funcdef_0__axiom (fun _=>false) (AxiomCommand.arguments tag a b c)) (fourth,observations)=Some (tt,(built,observations)) ->
  (17<length (memory built arraydef_0__meta))%nat -> meta_value built 13=0 -> meta_value built 8=0 ->
  execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(ReplyNOExecution.reply_state built,
    observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin built|}])).
Proof.
  intros [Hopcode [Hopmeta [Hopnumber [Hopvalid Hoperror]]]] Hfirst Hsecond Hthird Hfourth
    Haxiom Hbuilt Hsuccess Herror.
  set (initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} opstate 11).
  set (after:=setMachine (AxiomCommand.locals initial tag a b c) (ReplyNOExecution.reply_state built)).
  apply (CommandDispatch.generated_positive_command s bs ns after opstate 11 observations
    (observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin built|}])) ; try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandChain.handler_for funcdef_0__readNat 11) (initial,observations)=
      Some (tt,(after,observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin built|}]))).
    eapply generated_handler; eassumption.
  - change (8<length (memory (ReplyNOExecution.reply_state built) arraydef_0__meta))%nat.
    rewrite ReplyNOExecution.reply_memory. lia.
Qed.

Lemma valid_concrete s logical tag a b c :
  meta_value s 1=Z.of_nat (length (Protocol.formulas logical)) ->
  (tag<18)%nat ->
  AxiomDispatch.references_valid {|machine:=s;bools:=fun _=>false;nums:=AxiomCommand.arguments (Z.of_nat tag) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)|} (Z.of_nat tag) ->
  exists formula, Protocol.concrete_axiom logical tag a b c=Some formula.
Proof.
  intros Hcount Htag Hvalid.
  unfold AxiomDispatch.references_valid in Hvalid. cbn [machine] in Hvalid.
  rewrite Hcount in Hvalid.
  let rec cases count tag := lazymatch count with
  | O=>idtac
  | S ?rest=>let next:=fresh "tag" in destruct tag as [|next];[idtac|cases rest next]
  end in cases 18%nat tag.
  all: try lia.
  all: cbn [AxiomDispatch.reference_names nums AxiomCommand.arguments] in Hvalid.
  all: repeat rewrite RenameMemoControl.updated_same in Hvalid.
  all: repeat rewrite RenameMemoControl.updated_other in Hvalid by discriminate.
  all: repeat match goal with H:Forall _ (_::_) |- _ => inversion H;clear H;subst end.
  all: unfold Protocol.concrete_axiom,Protocol.formula_at;cbn [existsb Nat.eqb].
  all: repeat match goal with |- context[nth_error (Protocol.formulas logical) ?index] =>
    let value:=fresh "formula" in let Hlookup:=fresh "Hlookup" in
    destruct (nth_error (Protocol.formulas logical) index) as [value|] eqn:Hlookup;
      [|apply nth_error_None in Hlookup;exfalso;lia] end.
  all: eexists;reflexivity.
Qed.
Lemma rejection_cases s logical tag a b c :
  meta_value s 1=Z.of_nat (length (Protocol.formulas logical)) ->
  Protocol.concrete_axiom logical tag a b c=None ->
  (18<=tag)%nat \/
  ~AxiomDispatch.references_valid {|machine:=s;bools:=fun _=>false;nums:=AxiomCommand.arguments (Z.of_nat tag) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)|} (Z.of_nat tag).
Proof.
  intros Hcount Hnone. destruct (lt_dec tag 18) as [Hsupported|Hunsupported];[right|left;lia].
  intro Hvalid. destruct (valid_concrete s logical tag a b c Hcount Hsupported Hvalid) as [formula Hsome]. congruence.
Qed.
Lemma accepted_impossible logical tag a b c : Protocol.concrete_axiom logical tag a b c=None ->
  forall reply next, ~Protocol.accepted logical (Protocol.Req 11 [tag;a;b;c] []) reply next.
Proof.
  intros Hnone reply next Haccepted. inversion Haccepted;subst;
    first [match goal with H:Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H:Protocol.proof_request _ _ _ |- _ => inversion H;subst;congruence end].
Qed.
Theorem logical_rejected logical tag a b c : Protocol.concrete_axiom logical tag a b c=None ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 11 [tag;a;b;c] []) Protocol.NO logical.
Proof. intros Hnone Hunique. apply Protocol.step_reject;[now apply accepted_impossible|now apply HistoryRefinement.retained_refl]. Qed.
End AxiomRejectionProtocol.
