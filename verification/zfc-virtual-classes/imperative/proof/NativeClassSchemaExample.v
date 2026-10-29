From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Schemata Protocol Guarantees Spec.
From NativeProof Require Import Index SipHash NativeState NativeSetBudgetPlan NativeSetSchemaSession NativeGeneralExamples SeedBootstrap.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeClassSchemaExample.
Import IndexExecution SipHashExecution.
Definition schema_name : list Z := [115;101;116;95;107].
Definition left := Schemata.metavariable 0.
Definition right := Schemata.metavariable 1.
Definition equality := Schemata.template_equal left left.
Definition membership := Schemata.template_member left right.
Definition certificate := Schemata.template_ax
 (Schemata.template_axiom 0 equality membership Protocol.empty_template 2 3 0).
Definition nodes := [Protocol.CE left;Protocol.CE right;Protocol.FE equality;
 Protocol.FE membership;Protocol.PE certificate].
Definition requests :=
 [Protocol.Req 5 [0]%nat [];Protocol.Req 5 [1]%nat [];
  Protocol.Req 22 [0;0;0;0;0]%nat [];
  Protocol.Req 22 [0;1;0;0;0]%nat [];
  Protocol.Req 22 [4;0;0;0;0]%nat [];
  Protocol.Req 22 [5;0;1;0;0]%nat [];
  Protocol.Req 22 [8;0;2;3;0]%nat [];
  Protocol.Req 23 [4]%nat schema_name;
  Protocol.Req 24 [0;1]%nat schema_name;Protocol.Req 0 []%nat []].
Lemma requests_shape : Forall Protocol.shape requests.
Proof.
 unfold requests,schema_name. repeat constructor;unfold Protocol.shape,Protocol.valid_name;
 cbn [Protocol.opcode Protocol.arguments Protocol.object_name length];
 repeat constructor;unfold Protocol.maximum;lia.
Qed.
Lemma requests_capacity : NativeSetBudgetPlan.domain requests.
Proof. vm_compute. reflexivity. Qed.
Lemma actual_arity : Schemata.proof_arity certificate=2%nat.
Proof. reflexivity. Qed.
Lemma actual_infer rho :
 Schemata.infer rho 0 certificate=Some(SetTheory.axiom_formula
 (SetTheory.K (Schemata.instantiate_formula rho 0 equality)
 (Schemata.instantiate_formula rho 0 membership))).
Proof. reflexivity. Qed.
Lemma set_step logical i reply after :
 Protocol.step logical (Protocol.Req 5 [i]%nat []) reply after ->
 (S(length(Protocol.classes logical))<=length(Protocol.classes after))%nat /\
 Protocol.history after=Protocol.history logical /\ Protocol.bindings after=Protocol.bindings logical /\
 Protocol.expressions after=Protocol.expressions logical /\ NoDup(Protocol.formulas after).
Proof.
 intro Hstep.
 destruct(NativeGeneralExamples.step_possible logical _ reply after Hstep
 (ex_intro _ _ (ex_intro _ _ (Protocol.accept_set logical i)))) as [middle [Haccepted Hretained]].
 inversion Haccepted;subst;try NativeGeneralExamples.impossible_requests.
 destruct Hretained as [Hfs [Hdistinct [[extra Hcs] [Hhs [Hbs Hes]]]]].
 cbn [Protocol.classes Protocol.history Protocol.bindings Protocol.expressions] in Hcs,Hhs,Hbs,Hes.
 split;[rewrite Hcs,!app_length;cbn;lia|]. repeat split;assumption.
Qed.
Lemma node_step logical args expression reply after :
 Protocol.builds_node logical args expression ->
 (forall other,Protocol.builds_node logical args other -> other=expression) ->
 Protocol.step logical (Protocol.Req 22 args []) reply after ->
 (length(Protocol.classes logical)<=length(Protocol.classes after))%nat /\
 Protocol.history after=Protocol.history logical /\ Protocol.bindings after=Protocol.bindings logical /\
 Protocol.expressions after=Protocol.expressions logical++[expression] /\ NoDup(Protocol.formulas after).
Proof.
 intros Hnode Hunique Hstep.
 assert(Hpossible:exists result target,Protocol.accepted logical (Protocol.Req 22 args []) result target).
 { eexists;eexists. exact(Protocol.accept_node logical args expression Hnode). }
 destruct(NativeGeneralExamples.step_possible logical _ reply after Hstep Hpossible) as [middle [Haccepted Hretained]].
 inversion Haccepted;subst;try NativeGeneralExamples.impossible_requests.
 match goal with H:Protocol.builds_node logical args _ |- _=>
  pose proof(Hunique _ H) as Heq;subst end.
 destruct Hretained as [Hfs [Hdistinct [[extra Hcs] [Hhs [Hbs Hes]]]]].
 cbn [Protocol.classes Protocol.history Protocol.bindings Protocol.expressions] in Hcs,Hhs,Hbs,Hes.
 split;[rewrite Hcs,app_length;lia|]. repeat split;assumption.
Qed.
Lemma meta_node logical i : (Z.of_nat i<Protocol.maximum) ->
 Protocol.builds_node logical [0;i;0;0;0]%nat (Protocol.CE(Schemata.metavariable i)) /\
 (forall e,Protocol.builds_node logical [0;i;0;0;0]%nat e -> e=Protocol.CE(Schemata.metavariable i)).
Proof. intro Hindex. split;[now apply Protocol.node_meta|]. intros e Hnode;inversion Hnode;reflexivity. Qed.
Lemma equal_node logical :
 Protocol.expressions logical=[Protocol.CE left;Protocol.CE right] ->
 Protocol.builds_node logical [4;0;0;0;0]%nat (Protocol.FE equality) /\
 (forall e,Protocol.builds_node logical [4;0;0;0;0]%nat e -> e=Protocol.FE equality).
Proof.
 intro Hes. assert(Hcf:Protocol.cf logical 0=Some left) by (unfold Protocol.cf;now rewrite Hes).
 split;[exact(Protocol.node_equal logical 0 0 0 0 left left Hcf Hcf)|].
 intros e Hnode;inversion Hnode;subst.
 repeat match goal with H:Protocol.cf logical 0=Some _ |- _=>rewrite Hcf in H;injection H as <- end.
 reflexivity.
Qed.
Lemma member_node logical :
 Protocol.expressions logical=[Protocol.CE left;Protocol.CE right;Protocol.FE equality] ->
 Protocol.builds_node logical [5;0;1;0;0]%nat (Protocol.FE membership) /\
 (forall e,Protocol.builds_node logical [5;0;1;0;0]%nat e -> e=Protocol.FE membership).
Proof.
 intro Hes. assert(Hcf0:Protocol.cf logical 0=Some left) by (unfold Protocol.cf;now rewrite Hes).
 assert(Hcf1:Protocol.cf logical 1=Some right) by (unfold Protocol.cf;now rewrite Hes).
 split;[exact(Protocol.node_member logical 0 1 0 0 left right Hcf0 Hcf1)|].
 intros e Hnode;inversion Hnode;subst.
 repeat match goal with
 | H:Protocol.cf logical 0=Some _ |- _=>rewrite Hcf0 in H;injection H as <-
 | H:Protocol.cf logical 1=Some _ |- _=>rewrite Hcf1 in H;injection H as <- end.
 reflexivity.
Qed.
Lemma ax_node logical :
 Protocol.expressions logical=[Protocol.CE left;Protocol.CE right;Protocol.FE equality;Protocol.FE membership] ->
 Protocol.builds_node logical [8;0;2;3;0]%nat (Protocol.PE certificate) /\
 (forall e,Protocol.builds_node logical [8;0;2;3;0]%nat e -> e=Protocol.PE certificate).
Proof.
 intro Hes. assert(Hax:Protocol.axiom_expression logical 0 2 3 0=Some certificate).
 { unfold Protocol.axiom_expression,Protocol.formula_argument,Protocol.ff. rewrite Hes. reflexivity. }
 split;[now apply Protocol.node_ax|]. intros e Hnode;inversion Hnode;subst.
 match goal with H:Protocol.axiom_expression logical 0 2 3 0=Some _ |- _=>
 rewrite Hax in H;injection H as <- end. reflexivity.
Qed.
Lemma name_step logical reply after :
 Protocol.expressions logical=nodes -> Protocol.bindings logical=[] ->
 Protocol.step logical (Protocol.Req 23[4]%nat schema_name) reply after ->
 (length(Protocol.classes logical)<=length(Protocol.classes after))%nat /\
 Protocol.expressions after=nodes /\
 Protocol.bindings after=[(schema_name,Protocol.schema_binding 4)] /\
 Protocol.history after=Protocol.history logical /\ NoDup(Protocol.formulas after).
Proof.
 intros Hes Hbs Hstep.
 assert(Hpf:Protocol.pf logical 4=Some certificate) by (unfold Protocol.pf;rewrite Hes;reflexivity).
 assert(Hpossible:exists result target,Protocol.accepted logical (Protocol.Req 23[4]%nat schema_name) result target).
 { eexists;eexists. apply(Protocol.accept_name_schema logical schema_name 4 certificate Hpf).
 unfold Protocol.lookup;now rewrite Hbs. }
 destruct(NativeGeneralExamples.step_possible logical _ reply after Hstep Hpossible) as [middle [Haccepted Hretained]].
 inversion Haccepted;subst;try NativeGeneralExamples.impossible_requests.
 destruct Hretained as [Hfs [Hdistinct [[extra Hcs] [Hhs [Hbs' Hes']]]]].
 cbn [Protocol.classes Protocol.history Protocol.bindings Protocol.expressions] in Hcs,Hhs,Hbs',Hes'.
 split;[rewrite Hcs,app_length;lia|]. split;[now rewrite Hes',Hes|].
 split;[now rewrite Hbs',Hbs|]. split;assumption.
Qed.
Lemma instance_accepted logical reply after :
 (2<=length(Protocol.classes logical))%nat -> Protocol.expressions logical=nodes ->
 Protocol.bindings logical=[(schema_name,Protocol.schema_binding 4)] ->
 Protocol.history logical=[] -> NoDup(Protocol.formulas logical) ->
 Protocol.step logical (Protocol.Req 24[0;1]%nat schema_name) reply after -> reply=Protocol.OK 0.
Proof.
 intros Hclasses Hes Hbs Hhs Hdistinct Hstep.
 destruct(nth_error (Protocol.classes logical) 0) as [c0|] eqn:Hc0.
 2:{ apply nth_error_None in Hc0;lia. }
 destruct(nth_error (Protocol.classes logical) 1) as [c1|] eqn:Hc1.
 2:{ apply nth_error_None in Hc1;lia. }
 assert(Hproof:Protocol.proof_request logical (Protocol.Req 24[0;1]%nat schema_name)
  (SetTheory.axiom_formula (SetTheory.K
   (Schemata.instantiate_formula (fun i=>List.nth i [c0;c1] (VirtualClasses.set 0)) 0 equality)
   (Schemata.instantiate_formula (fun i=>List.nth i [c0;c1] (VirtualClasses.set 0)) 0 membership)))).
 { eapply(Protocol.req_instance logical schema_name 4 certificate [0;1]%nat [c0;c1]);
   [rewrite Hbs;reflexivity|unfold Protocol.pf;rewrite Hes;reflexivity|reflexivity| |apply actual_infer].
   constructor;[exact Hc0|]. constructor;[exact Hc1|constructor]. }
 destruct(NativeGeneralExamples.step_possible logical _ reply after Hstep
  (NativeGeneralExamples.proof_possible logical _ _ Hdistinct Hproof)) as [middle [Haccepted Hretained]].
 inversion Haccepted;subst;try NativeGeneralExamples.impossible_requests. now rewrite Hhs.
Qed.
Theorem dialogue_instantiates replies final remaining :
 Protocol.dialogue Protocol.initial requests replies final remaining ->
 nth_error replies 8=Some(Protocol.OK 0).
Proof.
 intro Hdialogue. unfold requests in Hdialogue.
 destruct(NativeGeneralExamples.dialogue_head _ (Protocol.Req 5 [0]%nat []) _ _ _ _ ltac:(discriminate) Hdialogue)
  as(r1 & s1 & rs1 & Hr1 & Hstep1 & Hd1).
 destruct(set_step Protocol.initial 0 r1 s1 Hstep1) as(Hc1 & Hh1 & Hb1 & He1 & Hf1).
 destruct(NativeGeneralExamples.dialogue_head _ (Protocol.Req 5 [1]%nat []) _ _ _ _ ltac:(discriminate) Hd1)
  as(r2 & s2 & rs2 & Hr2 & Hstep2 & Hd2).
 destruct(set_step s1 1 r2 s2 Hstep2) as(Hc2 & Hh2 & Hb2 & He2 & Hf2).
 assert(Hc2min:(2<=length(Protocol.classes s2))%nat) by (cbn in Hc1;lia).
 assert(Hh2empty:Protocol.history s2=[]) by (rewrite Hh2,Hh1;reflexivity).
 assert(Hb2empty:Protocol.bindings s2=[]) by (rewrite Hb2,Hb1;reflexivity).
 assert(He2empty:Protocol.expressions s2=[]) by (rewrite He2,He1;reflexivity).
 destruct(NativeGeneralExamples.dialogue_head _ (Protocol.Req 22 [0;0;0;0;0]%nat []) _ _ _ _ ltac:(discriminate) Hd2)
  as(r3 & s3 & rs3 & Hr3 & Hstep3 & Hd3).
 destruct(meta_node s2 0 ltac:(unfold Protocol.maximum;lia)) as(Hnode3 & Hunique3).
 destruct(node_step s2 _ _ r3 s3 Hnode3 Hunique3 Hstep3) as(Hc3 & Hh3 & Hb3 & He3 & Hf3).
 assert(He3value:Protocol.expressions s3=[Protocol.CE left]) by (rewrite He3,He2empty;reflexivity).
 destruct(NativeGeneralExamples.dialogue_head _ (Protocol.Req 22 [0;1;0;0;0]%nat []) _ _ _ _ ltac:(discriminate) Hd3)
  as(r4 & s4 & rs4 & Hr4 & Hstep4 & Hd4).
 destruct(meta_node s3 1 ltac:(unfold Protocol.maximum;lia)) as(Hnode4 & Hunique4).
 destruct(node_step s3 _ _ r4 s4 Hnode4 Hunique4 Hstep4) as(Hc4 & Hh4 & Hb4 & He4 & Hf4).
 assert(He4value:Protocol.expressions s4=[Protocol.CE left;Protocol.CE right]) by (rewrite He4,He3value;reflexivity).
 destruct(NativeGeneralExamples.dialogue_head _ (Protocol.Req 22 [4;0;0;0;0]%nat []) _ _ _ _ ltac:(discriminate) Hd4)
  as(r5 & s5 & rs5 & Hr5 & Hstep5 & Hd5).
 destruct(equal_node s4 He4value) as(Hnode5 & Hunique5).
 destruct(node_step s4 _ _ r5 s5 Hnode5 Hunique5 Hstep5) as(Hc5 & Hh5 & Hb5 & He5 & Hf5).
 assert(He5value:Protocol.expressions s5=[Protocol.CE left;Protocol.CE right;Protocol.FE equality]) by (rewrite He5,He4value;reflexivity).
 destruct(NativeGeneralExamples.dialogue_head _ (Protocol.Req 22 [5;0;1;0;0]%nat []) _ _ _ _ ltac:(discriminate) Hd5)
  as(r6 & s6 & rs6 & Hr6 & Hstep6 & Hd6).
 destruct(member_node s5 He5value) as(Hnode6 & Hunique6).
 destruct(node_step s5 _ _ r6 s6 Hnode6 Hunique6 Hstep6) as(Hc6 & Hh6 & Hb6 & He6 & Hf6).
 assert(He6value:Protocol.expressions s6=[Protocol.CE left;Protocol.CE right;Protocol.FE equality;Protocol.FE membership]) by (rewrite He6,He5value;reflexivity).
 destruct(NativeGeneralExamples.dialogue_head _ (Protocol.Req 22 [8;0;2;3;0]%nat []) _ _ _ _ ltac:(discriminate) Hd6)
  as(r7 & s7 & rs7 & Hr7 & Hstep7 & Hd7).
 destruct(ax_node s6 He6value) as(Hnode7 & Hunique7).
 destruct(node_step s6 _ _ r7 s7 Hnode7 Hunique7 Hstep7) as(Hc7 & Hh7 & Hb7 & He7 & Hf7).
 assert(He7value:Protocol.expressions s7=nodes) by (rewrite He7,He6value;reflexivity).
 assert(Hb7empty:Protocol.bindings s7=[]) by (rewrite Hb7,Hb6,Hb5,Hb4,Hb3,Hb2empty;reflexivity).
 destruct(NativeGeneralExamples.dialogue_head _ (Protocol.Req 23 [4]%nat schema_name) _ _ _ _ ltac:(discriminate) Hd7)
  as(r8 & s8 & rs8 & Hr8 & Hstep8 & Hd8).
 destruct(name_step s7 r8 s8 He7value Hb7empty Hstep8) as(Hc8 & He8 & Hb8 & Hh8 & Hf8).
 assert(Hc8min:(2<=length(Protocol.classes s8))%nat) by lia.
 assert(Hh8empty:Protocol.history s8=[]) by (rewrite Hh8,Hh7,Hh6,Hh5,Hh4,Hh3,Hh2empty;reflexivity).
 destruct(NativeGeneralExamples.dialogue_head _ (Protocol.Req 24 [0;1]%nat schema_name) _ _ _ _ ltac:(discriminate) Hd8)
  as(r9 & s9 & rs9 & Hr9 & Hstep9 & Hd9).
 pose proof(instance_accepted s8 r9 s9 Hc8min He8 Hb8 Hh8empty Hf8 Hstep9) as Hr9value.
 rewrite Hr1,Hr2,Hr3,Hr4,Hr5,Hr6,Hr7,Hr8,Hr9,Hr9value. reflexivity.
Qed.
Theorem checked_session bs ns :
 exists replies final logical remaining,
 Protocol.dialogue Protocol.initial requests replies logical remaining /\
 Guarantees.safe logical /\ nth_error replies 8=Some(Protocol.OK 0) /\
 execObserved(funcdef_0__main bs ns)
   (SeedBootstrapExecution.initial 1 2 (Protocol.wire requests)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes 1 2++Protocol.wire requests|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=Protocol.wire requests|}]++
 Protocol.flush_schedule requests replies Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=remaining.
Proof.
 destruct(NativeSetSchemaSession.required bs ns 1%nat 2%nat requests
   ltac:(unfold Protocol.maximum;lia) ltac:(unfold Protocol.maximum;lia) requests_shape requests_capacity)
 as(replies & final & logical & remaining & Hdialogue & Hsafe & Hrun & Hout & Hin).
 exists replies,final,logical,remaining. split;[exact Hdialogue|]. split;[exact Hsafe|].
 split;[exact(dialogue_instantiates replies logical remaining Hdialogue)|].
 split;[exact Hrun|]. split;assumption.
Qed.
End NativeClassSchemaExample.
