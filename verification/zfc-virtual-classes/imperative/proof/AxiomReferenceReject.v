From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal AxiomDispatch AxiomReject.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomReferenceReject.
Import IndexExecution SipHashExecution ObservedLocal AxiomDispatch.

Definition tests (f:Frame) names := forallb (fun name=>bool_decide (nums f name<meta_value (machine f) 1)) names.

Lemma tests_true f names : tests f names=true <-> Forall (fun name=>nums f name<meta_value (machine f) 1) names.
Proof.
  induction names as [|name names IH];unfold tests in *;cbn [forallb].
  - split;[intro;constructor|intro;reflexivity].
  - rewrite Bool.andb_true_iff,IH. split.
    + intros [Hname Hnames]. constructor;[now apply bool_decide_eq_true in Hname|exact Hnames].
    + intro Hnames. inversion Hnames;subst. split;[now apply bool_decide_eq_true|assumption].
Qed.

Lemma checked_result condition names (f:Frame) observations answer :
  (1<length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved condition (f,observations)=Some (answer,(f,observations)) ->
  execLocalObserved (checked condition names) (f,observations)=Some (andb answer (tests f names),(f,observations)).
Proof.
  intros Hmeta Hcondition. induction names as [|name names IH] in condition,answer,Hcondition|-*.
  - cbn [checked tests forallb]. now rewrite Bool.andb_true_r.
  - cbn [checked].
    assert (Hnext:execLocalObserved (shortCircuitAnd condition (reference_test name)) (f,observations)=
      Some (andb answer (bool_decide (nums f name<meta_value (machine f) 1)),(f,observations))).
    { unfold shortCircuitAnd. rewrite local_bind,Hcondition. destruct answer;cbn [optionBind fst snd];
        [apply reference_evaluates;exact Hmeta|reflexivity]. }
    rewrite (IH _ _ Hnext). unfold tests. cbn [forallb]. now rewrite Bool.andb_assoc.
Qed.

Lemma guard_result selector (f:Frame) observations :
  (1<length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved (selector_guard selector) (f,observations)=
    Some (andb (bool_decide (nums f vardef_0__axiom_tag=selector))
      (tests f (reference_names selector)),(f,observations)).
Proof.
  intro Hmeta. unfold selector_guard. destruct (reference_names selector) as [|name names].
  - unfold shortCircuitAnd. rewrite local_bind,tag_evaluates. destruct (bool_decide _);reflexivity.
  - apply checked_result;[exact Hmeta|apply tag_evaluates].
Qed.

Lemma guard_reject selector (f:Frame) observations :
  (1<length (memory (machine f) arraydef_0__meta))%nat -> ~references_valid f selector ->
  execLocalObserved (selector_guard selector) (f,observations)=Some (false,(f,observations)).
Proof.
  intros Hmeta Hinvalid. rewrite guard_result by exact Hmeta.
  assert (Htests:tests f (reference_names selector)=false).
  { destruct (tests f (reference_names selector)) eqn:Htests;[|reflexivity].
    exfalso. apply Hinvalid. now apply tests_true in Htests. }
  rewrite Htests,Bool.andb_false_r. reflexivity.
Qed.

Lemma chain_reject handlers codes selector (f:Frame) observations :
  (1<length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__axiom_tag=selector -> ~references_valid f selector ->
  execLocalObserved (chain handlers codes) (f,observations)=Some (tt,(f,observations)).
Proof.
  intros Hmeta Htag Hinvalid. induction codes as [|code codes IH];[reflexivity|].
  cbn [chain]. rewrite local_bind.
  destruct (Z.eq_dec selector code) as [<-|Hdifferent].
  - unfold clause. rewrite local_bind,(guard_reject selector f observations Hmeta Hinvalid). exact IH.
  - rewrite (clause_skip handlers code selector f observations Htag Hdifferent). exact IH.
Qed.

Theorem generated_body (f:Frame) observations :
  (13<length (memory (machine f) arraydef_0__meta))%nat ->
  ~references_valid f (nums f vardef_0__axiom_tag) ->
  execLocalObserved funcdef_0__axiom_body (f,observations)=Some (tt,(cleared_frame f,observations)).
Proof.
  intros Hmeta Hinvalid. rewrite actual_body,local_bind,(clear_generated f observations Hmeta).
  cbn [optionBind fst snd]. eapply chain_reject.
  - unfold cleared_frame. cbn [machine setMachine]. rewrite store_meta_length. lia.
  - reflexivity.
  - unfold references_valid,cleared_frame. cbn [machine setMachine nums].
    rewrite meta_store_other by lia. exact Hinvalid.
Qed.

Theorem generated s bs ns observations :
  (13<length (memory s arraydef_0__meta))%nat ->
  ~references_valid {|machine:=s;bools:=bs;nums:=ns|} (ns vardef_0__axiom_tag) ->
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomReject.result s,observations)).
Proof.
  intros Hmeta Hinvalid. unfold funcdef_0__axiom. rewrite eliminate_correct.
  pose proof (generated_body {|machine:=s;bools:=bs;nums:=ns|} observations Hmeta Hinvalid) as Hrun.
  exact (f_equal (fun response=>optionBind response (fun r=>Some (fst r,(machine (fst (snd r)),snd (snd r))))) Hrun).
Qed.
End AxiomReferenceReject.
