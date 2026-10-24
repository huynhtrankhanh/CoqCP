From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal SchemaNode SchemaNodeCommand RenameMemoControl ReplyNO.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaNodeRejection.
Import IndexExecution SipHashExecution ObservedLocal.
Definition invalid s kind a :=
  (kind=0%nat /\ Z.of_nat a=maximum) \/
  (kind=1%nat /\ meta_value s 2<=Z.of_nat a) \/
  (kind=2%nat /\ meta_value s 1<=Z.of_nat a) \/
  (kind=11%nat /\ meta_value s 3<=Z.of_nat a) \/ (12<=kind)%nat.
Definition state s := store_meta (SchemaNode.initialized s) 18 0.
Definition typ kind : Z := if bool_decide (kind=2%nat) then 1 else if bool_decide (kind=11%nat) then 2 else 0.
Theorem generated_prefix (f:SchemaNode.Frame) kind a observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__schemaNode_kind=Z.of_nat kind -> nums f vardef_0__schemaNode_a=Z.of_nat a ->
  invalid (machine f) kind a ->
  execLocalObserved SchemaNode.prefix (f,observations)=Some (tt,(
    setMachine (SchemaNode.typed_frame f (typ kind)) (state (machine f)),observations)).
Proof.
  intros Hmeta Hkind Ha Hinvalid.
  destruct Hinvalid as [[Hcase Hbad]|[[Hcase Hbad]|[[Hcase Hbad]|[[Hcase Hbad]|Hlarge]]]];
    try subst kind;unfold maximum in *;
    destruct f as [s bs ns];cbn [machine nums] in *;
    unfold SchemaNode.prefix,SchemaNode.parts;cbn [SchemaNode.prepend];
    unfold typ,SchemaNode.typed_frame,state;
    repeat first [progress SchemaNode.validation_steps Hmeta|progress rewrite Hkind|progress rewrite Ha];reflexivity.
Qed.
Theorem generated_rejected s bs ns kind a observations :
  (19<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__schemaNode_kind=Z.of_nat kind -> ns vardef_0__schemaNode_a=Z.of_nat a ->
  invalid s kind a ->
  execObserved (funcdef_0__schemaNode bs ns) (s,observations)=Some (tt,(
    ReplyNOExecution.reply_state (state s),
    observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin s|}])).
Proof.
  intros Hmeta Hkind Ha Hinvalid.
  set (validated:=setMachine (SchemaNode.typed_frame {|machine:=s;bools:=bs;nums:=ns|} (typ kind)) (state s)).
  pose proof (generated_prefix {|machine:=s;bools:=bs;nums:=ns|} kind a observations Hmeta Hkind Ha Hinvalid) as Hprefix.
  pose proof (SchemaNode.generated_after_prefix_rejected s bs ns validated observations Hprefix
    ltac:(unfold validated;cbn [machine setMachine];unfold state;rewrite store_meta_length,SchemaNode.initialized_length;exact Hmeta)
    ltac:(unfold validated;cbn [machine setMachine];unfold state;apply meta_store_same;rewrite SchemaNode.initialized_length;lia)) as Hrun.
  exact Hrun.
Qed.
End SchemaNodeRejection.
