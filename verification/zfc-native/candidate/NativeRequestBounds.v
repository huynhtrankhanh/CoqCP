From CoqCP Require Import Options.
From Trusted Require Import Protocol.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From stdpp Require Import numbers list.

Module NativeRequestBounds.
Fixpoint numbers_max values := match values with []=>0%nat|value::rest=>Nat.max value (numbers_max rest) end.
Fixpoint maximum requests := match requests with
 | []=>0%nat | request::rest=>Nat.max (numbers_max(Protocol.arguments request)) (maximum rest) end.
Lemma numbers_bounded values bound : (numbers_max values<=bound)%nat -> Forall(fun value=>(value<=bound)%nat)values.
Proof. induction values as [|value values IH];cbn [numbers_max];intro H;constructor;[lia|apply IH;lia]. Qed.
Lemma requests_bounded requests bound : (maximum requests<=bound)%nat ->
 Forall(fun request=>Forall(fun value=>(value<=bound)%nat)(Protocol.arguments request))requests.
Proof.
 induction requests as [|request requests IH];cbn [maximum];intro H;constructor.
 - apply numbers_bounded;lia.
 - apply IH;lia.
Qed.
Lemma initial_request_bound requests :
 Forall(fun request=>Forall(fun value=>(value<=maximum requests)%nat)(Protocol.arguments request))requests.
Proof. apply requests_bounded;reflexivity. Qed.
Lemma accepted_expressions source request reply after : Protocol.accepted source request reply after ->
 Protocol.opcode request<>22%nat -> Protocol.expressions after=Protocol.expressions source.
Proof.
 intros Haccepted Hopcode. destruct Haccepted;
 cbn [Protocol.opcode] in Hopcode;try contradiction;reflexivity.
Qed.
Theorem step_expressions source request reply after : Protocol.step source request reply after ->
 Protocol.opcode request<>22%nat -> Protocol.expressions after=Protocol.expressions source.
Proof.
 intros Hstep Hopcode. destruct Hstep as [reply middle after Haccepted Hretained|after Hnone Hretained];
 destruct Hretained as [Hfs [Hunique [Hcs [Hhistory [Hnames Hexpressions]]]]];rewrite Hexpressions.
 - now apply(accepted_expressions source request reply middle Haccepted).
 - reflexivity.
Qed.
Definition expression_increment request := if Nat.eqb(Protocol.opcode request)22 then 1%nat else 0%nat.
Lemma accepted_expression_count source request reply after : Protocol.accepted source request reply after ->
 (length(Protocol.expressions after)<=length(Protocol.expressions source)+expression_increment request)%nat.
Proof.
 intro Haccepted. destruct Haccepted;unfold expression_increment;
 cbn [Protocol.expressions Protocol.with_history Protocol.opcode];try lia.
 rewrite length_app. cbn [length Nat.eqb];lia.
Qed.
Theorem step_expression_count source request reply after : Protocol.step source request reply after ->
 (length(Protocol.expressions after)<=length(Protocol.expressions source)+expression_increment request)%nat.
Proof.
 intro Hstep. destruct Hstep as [reply middle after Haccepted Hretained|after Hnone Hretained];
 destruct Hretained as [Hfs [Hunique [Hcs [Hhistory [Hnames Hexpressions]]]]];rewrite Hexpressions.
 - exact(accepted_expression_count _ _ _ _ Haccepted).
 - lia.
Qed.
End NativeRequestBounds.
