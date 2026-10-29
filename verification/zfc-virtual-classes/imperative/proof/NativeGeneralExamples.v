From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Schemata Protocol Guarantees Spec.
From NativeProof Require Import Index SipHash NativeState LogicalStorageMonotone NativeBudgetPlan NativeGeneralSession SeedBootstrap.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeGeneralExamples.
Import IndexExecution SipHashExecution.
Definition requests :=
 [Protocol.Req 5 [0]%nat [];
  Protocol.Req 9 [0]%nat [65];
  Protocol.Req 11 [5;0;0;0]%nat [];
  Protocol.Req 22 [11;0;0;0;0]%nat [];
  Protocol.Req 23 [0]%nat [83];
  Protocol.Req 24 []%nat [83];
  Protocol.Req 20 [1]%nat [84];
  Protocol.Req 21 []%nat [84];
  Protocol.Req 14 [0]%nat [65];
  Protocol.Req 25 []%nat [83];
  Protocol.Req 26 []%nat [83];
  Protocol.Req 0 []%nat []].
Lemma requests_shape : Forall Protocol.shape requests.
Proof.
 unfold requests. repeat constructor;unfold Protocol.shape,Protocol.valid_name;
 cbn [Protocol.opcode Protocol.arguments Protocol.object_name length];
 repeat constructor;unfold Protocol.maximum;lia.
Qed.
Lemma reflexivity_axiom logical :
 Protocol.concrete_axiom logical 5 0 0 0=Some(SetTheory.equal 0 0).
Proof. reflexivity. Qed.
Lemma proof_allocation logical p : NoDup(Protocol.formulas logical) ->
 exists fs index,Protocol.allocation logical fs (Protocol.classes logical) index p.
Proof.
 intro Hdistinct. destruct(List.in_dec SetTheory.formula_eq_dec p (Protocol.formulas logical)) as [Hin|Hfresh].
 - apply List.In_nth_error in Hin as [index Hlookup]. exists(Protocol.formulas logical),index.
   split;[exists [];now rewrite app_nil_r|]. split;[exact Hdistinct|].
   split;[exact Hlookup|exists [];now rewrite app_nil_r].
 - exists(Protocol.formulas logical++[p]),(length(Protocol.formulas logical)).
   split;[exists [p];reflexivity|]. split.
   + apply NoDup_app. split;[exact Hdistinct|]. split.
     * intros value Hin Hsingleton. apply list_elem_of_In in Hin,Hsingleton.
       cbn in Hsingleton. destruct Hsingleton as [->|[]]. contradiction.
     * constructor;[apply not_elem_of_nil|constructor].
   + split;[rewrite nth_error_app2 by lia;rewrite Nat.sub_diag;reflexivity|exists [];now rewrite app_nil_r].
Qed.
Lemma proof_possible logical request p : NoDup(Protocol.formulas logical) ->
 Protocol.proof_request logical request p -> exists reply after,Protocol.accepted logical request reply after.
Proof.
 intros Hdistinct Hproof. destruct(proof_allocation logical p Hdistinct) as [fs [index Halloc]].
 eexists; eexists. eapply Protocol.accept_proof;[exact Hproof|exact Halloc].
Qed.
Lemma step_possible logical request reply after :
 Protocol.step logical request reply after ->
 (exists result target,Protocol.accepted logical request result target) ->
 exists middle,Protocol.accepted logical request reply middle /\ Protocol.retained_storage middle after.
Proof.
 intros Hstep [result [target Hpossible]]. destruct Hstep as [reply middle after Haccepted Hretained|after Hnone Hretained].
 - exists middle. split;assumption.
 - exfalso. exact(Hnone result target Hpossible).
Qed.
Ltac impossible_requests :=
 repeat match goal with
 | H:Protocol.formula_request _ _ _ |- _=>inversion H;subst;clear H
 | H:Protocol.proof_request _ _ _ |- _=>inversion H;subst;clear H
 end.
Lemma first_class logical reply after :
 Protocol.classes logical=[] -> Protocol.step logical (Protocol.Req 5 [0]%nat []) reply after ->
 reply=Protocol.OK 0 /\ Protocol.class_at after 0=Some(VirtualClasses.set 0) /\
 Protocol.history after=Protocol.history logical /\ Protocol.bindings after=Protocol.bindings logical /\
 Protocol.expressions after=Protocol.expressions logical /\ NoDup(Protocol.formulas after).
Proof.
 intros Hclasses Hstep.
 destruct(step_possible logical _ reply after Hstep (ex_intro _ _ (ex_intro _ _ (Protocol.accept_set logical 0)))) as [middle [Haccepted Hretained]].
 inversion Haccepted;subst;try impossible_requests.
 destruct Hretained as [Hfs [Hdistinct [[extra Hcs] [Hhs [Hbs Hes]]]]].
 cbn [Protocol.classes Protocol.history Protocol.bindings Protocol.expressions] in Hcs,Hhs,Hbs,Hes.
 split;[now rewrite Hclasses|]. split.
 - unfold Protocol.class_at. rewrite Hcs,Hclasses. reflexivity.
 - repeat split;assumption.
Qed.
Lemma named_class logical reply after :
 Protocol.class_at logical 0=Some(VirtualClasses.set 0) -> Protocol.bindings logical=[] ->
 Protocol.step logical (Protocol.Req 9 [0]%nat [65]) reply after ->
 Protocol.history after=Protocol.history logical /\
 Protocol.bindings after=[([65],Protocol.class_binding 0 false)] /\
 Protocol.expressions after=Protocol.expressions logical /\ NoDup(Protocol.formulas after).
Proof.
 intros Hclass Hbindings Hstep.
 assert(Hpossible:exists result target,Protocol.accepted logical (Protocol.Req 9[0]%nat[65]) result target).
 { eexists;eexists. apply(Protocol.accept_name_class logical [65] 0 (VirtualClasses.set 0) Hclass).
   unfold Protocol.lookup. now rewrite Hbindings. }
 destruct(step_possible logical _ reply after Hstep Hpossible) as [middle [Haccepted Hretained]].
 inversion Haccepted;subst;try impossible_requests.
 destruct Hretained as [Hfs [Hdistinct [Hcs [Hhs [Hbs Hes]]]]].
 cbn [Protocol.history Protocol.bindings Protocol.expressions] in Hhs,Hbs,Hes.
 rewrite Hbindings in Hbs. repeat split;assumption.
Qed.
Lemma first_proof logical reply after :
 NoDup(Protocol.formulas logical) -> Protocol.history logical=[] ->
 Protocol.step logical (Protocol.Req 11 [5;0;0;0]%nat []) reply after ->
 (exists fid,Protocol.history after=[fid] /\ Protocol.formula_at after fid=Some(SetTheory.equal 0 0)) /\
 Protocol.bindings after=Protocol.bindings logical /\
 Protocol.expressions after=Protocol.expressions logical /\ NoDup(Protocol.formulas after).
Proof.
 intros Hdistinct Hhistory Hstep.
 assert(Hproof:Protocol.proof_request logical (Protocol.Req 11[5;0;0;0]%nat[]) (SetTheory.equal 0 0)).
 { apply Protocol.req_axiom. apply reflexivity_axiom. }
 destruct(step_possible logical _ reply after Hstep (proof_possible logical _ _ Hdistinct Hproof)) as [middle [Haccepted Hretained]].
 inversion Haccepted;subst;try impossible_requests.
 match goal with H:Protocol.concrete_axiom _ 5 0 0 0=Some _ |- _=>
   rewrite reflexivity_axiom in H;injection H as <- end.
 match goal with H:Protocol.allocation _ _ _ _ _ |- _=>
   destruct H as [Hprefix [Hunique [Hlookup HclassPrefix]]] end.
 destruct Hretained as [[extra Hfs] [Hdistinct' [Hcs [Hhs [Hbs Hes]]]]].
 cbn [Protocol.formulas Protocol.history Protocol.bindings Protocol.expressions] in Hfs,Hhs,Hbs,Hes.
 split.
 - eexists. split;[now rewrite Hhs,Hhistory|]. unfold Protocol.formula_at. rewrite Hfs.
   apply Guarantees.nth_error_extend. exact Hlookup.
 - repeat split;assumption.
Qed.
Lemma saved_node logical reply after fid :
 Protocol.history logical=[fid] -> Protocol.formula_at logical fid=Some(SetTheory.equal 0 0) ->
 Protocol.expressions logical=[] ->
 Protocol.step logical (Protocol.Req 22 [11;0;0;0;0]%nat []) reply after ->
 (exists cert,Protocol.pf after 0=Some cert /\ Schemata.proof_arity cert=0%nat /\
   forall rho,Schemata.infer rho 0 cert=Some(SetTheory.equal 0 0)) /\
 Protocol.history after=Protocol.history logical /\ Protocol.bindings after=Protocol.bindings logical /\
 NoDup(Protocol.formulas after).
Proof.
 intros Hhistory Hformula Hexpressions Hstep.
 assert(Htheorem:Protocol.theorem_at logical 0=Some(SetTheory.equal 0 0)).
 { unfold Protocol.theorem_at. rewrite Hhistory. exact Hformula. }
 assert(Hpossible:exists result target,Protocol.accepted logical (Protocol.Req 22[11;0;0;0;0]%nat[]) result target).
 { eexists;eexists. apply Protocol.accept_node.
   exact(Protocol.node_saved logical 0 0 0 0 (SetTheory.equal 0 0) (SetTheory.d_refl 0) Htheorem). }
 destruct(step_possible logical _ reply after Hstep Hpossible) as [middle [Haccepted Hretained]].
 inversion Haccepted;subst;try impossible_requests.
 match goal with H:Protocol.builds_node _ _ _ |- _=>inversion H;subst;clear H end.
 match goal with H:Protocol.theorem_at logical 0=Some _ |- _=>
   rewrite Htheorem in H;injection H as <- end.
 destruct Hretained as [Hfs [Hdistinct [Hcs [Hhs [Hbs Hes]]]]].
 cbn [Protocol.history Protocol.bindings Protocol.expressions] in Hhs,Hbs,Hes.
 split.
 - eexists. split;[unfold Protocol.pf;rewrite Hes,Hexpressions;reflexivity|]. split;[reflexivity|].
   intro rho. reflexivity.
 - repeat split;assumption.
Qed.
Lemma named_schema logical reply after cert :
 Protocol.pf logical 0=Some cert -> Protocol.bindings logical=[([65],Protocol.class_binding 0 false)] ->
 Protocol.step logical (Protocol.Req 23[0]%nat[83]) reply after ->
 Protocol.pf after 0=Some cert /\
 Protocol.bindings after=[([65],Protocol.class_binding 0 false);([83],Protocol.schema_binding 0)] /\
 Protocol.history after=Protocol.history logical /\ NoDup(Protocol.formulas after).
Proof.
 intros Hproof Hbindings Hstep.
 assert(Hpossible:exists result target,Protocol.accepted logical (Protocol.Req 23[0]%nat[83]) result target).
 { eexists;eexists. apply(Protocol.accept_name_schema logical [83] 0 cert Hproof).
   unfold Protocol.lookup. rewrite Hbindings. reflexivity. }
 destruct(step_possible logical _ reply after Hstep Hpossible) as [middle [Haccepted Hretained]].
 inversion Haccepted;subst;try impossible_requests.
 destruct Hretained as [Hfs [Hdistinct [Hcs [Hhs [Hbs Hes]]]]].
 cbn [Protocol.history Protocol.bindings Protocol.expressions] in Hhs,Hbs,Hes.
 split;[unfold Protocol.pf in *;now rewrite Hes|].
 split;[now rewrite Hbs,Hbindings|]. split;assumption.
Qed.
Lemma instance_accepted logical reply after cert :
 NoDup(Protocol.formulas logical) -> length(Protocol.history logical)=1%nat ->
 Protocol.lookup [83](Protocol.bindings logical)=Some(Protocol.schema_binding 0) ->
 Protocol.pf logical 0=Some cert -> Schemata.proof_arity cert=0%nat ->
 (forall rho,Schemata.infer rho 0 cert=Some(SetTheory.equal 0 0)) ->
 Protocol.step logical (Protocol.Req 24 []%nat [83]) reply after -> reply=Protocol.OK 1.
Proof.
 intros Hdistinct Hhistory Hlookup Hproof Harity Hinfer Hstep.
 assert(Hrequest:Protocol.proof_request logical (Protocol.Req 24[]%nat[83]) (SetTheory.equal 0 0)).
 { eapply(Protocol.req_instance logical [83] 0 cert [] [] (SetTheory.equal 0 0));try eassumption.
   - now rewrite Harity.
   - constructor.
   - apply Hinfer. }
 destruct(step_possible logical _ reply after Hstep (proof_possible logical _ _ Hdistinct Hrequest)) as [middle [Haccepted Hretained]].
 inversion Haccepted;subst;try impossible_requests. now rewrite Hhistory.
Qed.
Lemma dialogue_head logical request tail replies final remaining :
 Protocol.opcode request<>0%nat -> Protocol.dialogue logical (request::tail) replies final remaining ->
 exists reply next rest,replies=reply::rest /\ Protocol.step logical request reply next /\
 Protocol.dialogue next tail rest final remaining.
Proof.
 intros Hpositive Hdialogue. inversion Hdialogue;subst;[contradiction|].
 eexists;eexists;eexists. repeat split;eassumption || reflexivity.
Qed.
Theorem dialogue_instantiates replies final remaining : Protocol.dialogue Protocol.initial requests replies final remaining ->
 nth_error replies 5=Some(Protocol.OK 1).
Proof.
 intro Hdialogue. unfold requests in Hdialogue.
 destruct(dialogue_head _ (Protocol.Req 5[0]%nat[]) _ _ _ _ ltac:(discriminate) Hdialogue)
   as(r1 & s1 & rs1 & Hr1 & Hstep1 & Hd1).
 destruct(first_class Protocol.initial r1 s1 eq_refl Hstep1)
   as(Hr1value & Hclass1 & Hhistory1 & Hbindings1 & Hexpressions1 & Hdistinct1).
 destruct(dialogue_head _ (Protocol.Req 9[0]%nat[65]) _ _ _ _ ltac:(discriminate) Hd1)
   as(r2 & s2 & rs2 & Hr2 & Hstep2 & Hd2).
 destruct(named_class s1 r2 s2 Hclass1 Hbindings1 Hstep2)
   as(Hhistory2 & Hbindings2 & Hexpressions2 & Hdistinct2).
 assert(Hhistory2empty:Protocol.history s2=[]) by (rewrite Hhistory2,Hhistory1;reflexivity).
 destruct(dialogue_head _ (Protocol.Req 11[5;0;0;0]%nat[]) _ _ _ _ ltac:(discriminate) Hd2)
   as(r3 & s3 & rs3 & Hr3 & Hstep3 & Hd3).
 destruct(first_proof s2 r3 s3 Hdistinct2 Hhistory2empty Hstep3)
   as([fid [Hhistory3 Hformula3]] & Hbindings3 & Hexpressions3 & Hdistinct3).
 assert(Hexpressions3empty:Protocol.expressions s3=[]) by (rewrite Hexpressions3,Hexpressions2,Hexpressions1;reflexivity).
 destruct(dialogue_head _ (Protocol.Req 22[11;0;0;0;0]%nat[]) _ _ _ _ ltac:(discriminate) Hd3)
   as(r4 & s4 & rs4 & Hr4 & Hstep4 & Hd4).
 destruct(saved_node s3 r4 s4 fid Hhistory3 Hformula3 Hexpressions3empty Hstep4)
   as([cert [Hproof4 [Harity Hinfer]]] & Hhistory4 & Hbindings4 & Hdistinct4).
 assert(Hbindings4named:Protocol.bindings s4=[([65],Protocol.class_binding 0 false)]).
 { now rewrite Hbindings4,Hbindings3,Hbindings2. }
 destruct(dialogue_head _ (Protocol.Req 23[0]%nat[83]) _ _ _ _ ltac:(discriminate) Hd4)
   as(r5 & s5 & rs5 & Hr5 & Hstep5 & Hd5).
 destruct(named_schema s4 r5 s5 cert Hproof4 Hbindings4named Hstep5)
   as(Hproof5 & Hbindings5 & Hhistory5 & Hdistinct5).
 assert(Hhistory5length:length(Protocol.history s5)=1%nat) by (rewrite Hhistory5,Hhistory4,Hhistory3;reflexivity).
 assert(Hlookup5:Protocol.lookup [83](Protocol.bindings s5)=Some(Protocol.schema_binding 0)).
 { rewrite Hbindings5. reflexivity. }
 destruct(dialogue_head _ (Protocol.Req 24[]%nat[83]) _ _ _ _ ltac:(discriminate) Hd5)
   as(r6 & s6 & rs6 & Hr6 & Hstep6 & Hd6).
 pose proof(instance_accepted s5 r6 s6 cert Hdistinct5 Hhistory5length Hlookup5 Hproof5 Harity Hinfer Hstep6) as Hr6value.
 rewrite Hr1,Hr2,Hr3,Hr4,Hr5,Hr6,Hr6value. reflexivity.
Qed.
Lemma requests_capacity : NativeBudgetPlan.domain requests.
Proof. vm_compute. reflexivity. Qed.
Definition caps_after count := fold_left
 (fun before request=>NativeBudgetPlan.step 11 request before)
 (firstn count requests) (NativeBudgetPlan.initial 11).
Lemma concrete_formula_caps :
 NativeBudgetPlan.formulas(caps_after 5)=2%nat /\
 NativeBudgetPlan.formulas(caps_after 6)=56%nat /\
 NativeBudgetPlan.formulas(caps_after 9)=3202%nat.
Proof. vm_compute. repeat split;reflexivity. Qed.
Theorem checked_session bs ns :
 exists replies final logical remaining,
 Protocol.dialogue Protocol.initial requests replies logical remaining /\
 Guarantees.safe logical /\ nth_error replies 5=Some(Protocol.OK 1) /\
 execObserved(funcdef_0__main bs ns)
   (SeedBootstrapExecution.initial 0 0 (Protocol.wire requests)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes 0 0++Protocol.wire requests|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=Protocol.wire requests|}]++
 Protocol.flush_schedule requests replies Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=remaining.
Proof.
 destruct(NativeGeneralSession.required bs ns 0%nat 0%nat requests
   ltac:(unfold Protocol.maximum;lia) ltac:(unfold Protocol.maximum;lia) requests_shape requests_capacity)
 as(replies & final & logical & remaining & Hdialogue & Hsafe & Hrun & Hout & Hin).
 exists replies,final,logical,remaining. split;[exact Hdialogue|]. split;[exact Hsafe|].
 split;[exact(dialogue_instantiates replies logical remaining Hdialogue)|].
 split;[exact Hrun|]. split;assumption.
Qed.
End NativeGeneralExamples.
