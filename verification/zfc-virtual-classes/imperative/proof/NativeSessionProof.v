From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeStartup NativeSimpleCommands NativeSession
 Representation ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation
 CommandLoop Dialogue CommandQuit QuitLoop SeedBootstrap AxiomReflProtocol NativeAxiomCommands TokenByte.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeSessionProof.
Import IndexExecution SipHashExecution.
Definition follows native observations after trace := forall final final_trace,
 DialogueExecution.run after trace final final_trace -> DialogueExecution.run native observations final final_trace.
Definition refines logical requests replies next := forall tail responses final remaining,
 Protocol.dialogue next tail responses final remaining ->
 Protocol.dialogue logical (requests++tail) (replies++responses) final remaining.
Fixpoint schedule initial requests replies suffix := match requests,replies with
 | request::rest,reply::replies=>
   {|flushedOutput:=initial++Protocol.reply_bytes reply;unreadInput:=Protocol.wire rest++suffix|}::
   schedule (initial++Protocol.reply_bytes reply) rest replies suffix
 | _,_=>[] end.

Lemma simple_history logical request reply next : NativeSession.valid_request request ->
 Protocol.step logical request reply next -> Protocol.history next=Protocol.history logical.
Proof.
 intros [Hshape Hrest] Hstep.
 assert (Hcode:(1<=Protocol.opcode request<=4)%nat).
 { destruct Hshape as [[Htag Hargs]|[Htag Hargs]].
   - destruct Htag as [Htag|[Htag|Htag]];rewrite Htag;lia.
   - rewrite Htag;lia. }
 inversion Hstep as [r t u Haccepted Hstorage|t Hrejected Hstorage];subst.
 - destruct Hstorage as [_ [_ [_ [Hhistory HrestStorage]]]]. rewrite Hhistory.
   inversion Haccepted;subst;cbn [Protocol.history Protocol.with_history Protocol.opcode] in *;try reflexivity;try lia.
   all: match goal with Hproof:Protocol.proof_request _ _ _|-_=>inversion Hproof;subst;cbn [Protocol.opcode] in Hcode;lia end.
 - exact (proj1 (proj2 (proj2 (proj2 Hstorage)))).
Qed.

Theorem generated_prefix requests reserve : forall native logical suffix observations,
 Forall NativeSession.valid_request requests ->
 Z.of_nat (length (Protocol.formulas logical)+length requests+reserve)<=9223372036854775807 ->
 NativeState.represents native logical ->
 (1024<=length (memory native arraydef_0__token))%nat -> (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 8=0 -> meta_value native 9=0 -> stdin native=Protocol.wire requests++suffix ->
 exists final replies target,
 length replies=length requests /\
 follows native observations final (observations++schedule (stdout native) requests replies suffix) /\
 refines logical requests replies target /\ NativeState.represents final target /\ stdin final=suffix /\
 stdout final=NativeSession.output (stdout native) replies /\
 (1024<=length (memory final arraydef_0__token))%nat /\ (20<=length (memory final arraydef_0__printBuffer))%nat /\
 meta_value final 8=0 /\ meta_value final 9=0 /\ Protocol.history target=Protocol.history logical /\
 Z.of_nat (length (Protocol.formulas target)+reserve)<=9223372036854775807.
Proof.
 induction requests as [|request requests IH];intros native logical suffix observations Hvalid Hbudget Hstate Htoken Hprint Herror Hstop Hinput.
 - exists native,[],logical. split;[reflexivity|]. split.
   + unfold follows. intros final trace Hrun. now rewrite app_nil_r in Hrun.
   + split;[unfold refines;intros;assumption|]. split;[exact Hstate|]. split;[exact Hinput|].
     split;[reflexivity|]. split;[exact Htoken|]. split;[exact Hprint|]. split;[exact Herror|]. split;[exact Hstop|].
     split;[reflexivity|]. now rewrite Nat.add_0_r in Hbudget.
 - inversion Hvalid as [|request' requests' Hrequest Hrequests];subst request' requests'.
   destruct (NativeSession.request_encoding request Hrequest) as (ch & Hencoding & Hbyte & Hopcode).
   set (unread:=32::NativeSimpleCommands.argument_input (Protocol.arguments request) 32 10 (Protocol.wire requests++suffix)).
   assert (Hbytes:stdin native=ch::unread).
   { rewrite Hinput. change ((Protocol.request_bytes request++Protocol.wire requests)++suffix=ch::unread). rewrite <-app_assoc.
     rewrite (NativeSession.request_wire request ch (Protocol.wire requests++suffix) Hrequest Hencoding). reflexivity. }
   set (pending:=CommandLoopExecution.pending_state (withInput native unread) ch).
   pose proof (NativeSession.represented_meta native logical Hstate) as Hmeta.
   assert (HpendingMeta:(17<length (memory pending arraydef_0__meta))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. change (17<length (memory native arraydef_0__meta))%nat;lia. }
   assert (HpendingToken:(1024<=length (memory pending arraydef_0__token))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
   assert (HpendingPrint:(20<=length (memory pending arraydef_0__printBuffer))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Hprint. }
   assert (Hpending:meta_value pending 15=ch+1).
   { unfold pending,CommandLoopExecution.pending_state. apply meta_store_same. change (15<length (memory native arraydef_0__meta))%nat;lia. }
   assert (HpendingError:meta_value pending 8=0).
   { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
   assert (HpendingStop:meta_value pending 9=0).
   { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Hstop. }
   assert (HpendingState:NativeState.represents pending logical).
   { unfold pending,CommandLoopExecution.pending_state. apply NativeSession.state_meta;try lia. now apply NativeSession.state_input. }
   pose proof Hrequest as [Hshape [Hname Hwords]].
   assert (HcurrentBudget:Z.of_nat (length (Protocol.formulas logical))<=9223372036854775807).
   { cbn [length] in Hbudget. rewrite !Nat2Z.inj_add in Hbudget. lia. }
   destruct (NativeSimpleCommands.generated_boundary (Protocol.opcode request) (Protocol.arguments request) ch [] pending logical
    (fun _=>false) (fun _=>0) 32 32 10 (Protocol.wire requests++suffix) observations
    Hshape Hencoding HpendingMeta HpendingToken HpendingPrint Hpending HpendingError HcurrentBudget Hwords HpendingState
    ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
    ltac:(unfold TokenByteExecution.separator;tauto) eq_refl)
   as (after & reply & next & Hcommand & Hstep & HnextState & Hboundary).
   destruct Hboundary as (Hin & Hout & HnextToken & HnextPrint & Hclear & HnextStop & Hgrowth).
   assert (HrequestEq:Protocol.Req (Protocol.opcode request) (Protocol.arguments request) []=request).
   { destruct request;cbn [Protocol.opcode Protocol.arguments Protocol.object_name] in *. now subst. }
   rewrite HrequestEq in Hstep.
   assert (HnextBudget:Z.of_nat (length (Protocol.formulas next)+length requests+reserve)<=9223372036854775807).
   { cbn [length] in Hbudget. apply Nat2Z.inj_le in Hgrowth. rewrite Nat2Z.inj_succ in Hgrowth.
     rewrite !Nat2Z.inj_add in *. lia. }
   destruct (IH after next suffix
      (observations++[{|flushedOutput:=stdout pending++Protocol.reply_bytes reply;unreadInput:=Protocol.wire requests++suffix|}])
      Hrequests HnextBudget HnextState HnextToken HnextPrint Hclear ltac:(congruence) Hin)
   as (final & replies & target & Hlength & Hfollows & Hrefines & Hfinal & HfinalInput & HfinalOutput & HfinalToken & HfinalPrint & HfinalClear & HfinalStop & Hhistory & Hremaining).
   assert (HpendingOutput:stdout pending=stdout native) by reflexivity.
   rewrite HpendingOutput in Hcommand,Hout,Hfollows.
   exists final,(reply::replies),target. split;[cbn [length];congruence|]. split.
   + unfold follows in *. intros final' trace Hsuffix. cbn [schedule] in Hsuffix |- *.
     eapply DialogueExecution.next with (ch:=ch) (tail:=unread) (after:=after).
     * exact Hbyte.
     * exact Hbytes.
     * lia.
     * exact Hcommand.
     * pose proof (NativeSession.represented_meta after next HnextState). lia.
     * congruence.
     * apply Hfollows. rewrite Hout,<-app_assoc. exact Hsuffix.
   + split.
     * unfold refines in *. intros tail responses final' remaining Hdialogue. cbn [app].
       eapply Protocol.dialogue_step;[exact Hopcode|exact Hstep|]. apply Hrefines;exact Hdialogue.
     * split;[exact Hfinal|]. split;[exact HfinalInput|]. split.
       -- cbn [NativeSession.output]. now rewrite Hout in HfinalOutput.
       -- split;[exact HfinalToken|]. split;[exact HfinalPrint|]. split;[exact HfinalClear|]. split;[exact HfinalStop|].
          split;[rewrite Hhistory;exact (simple_history logical request reply next Hrequest Hstep)|exact Hremaining].
Qed.
Definition reflexivity (variable:nat) := Protocol.Req 11 [5;variable;0;0]%nat [].
Definition proof_input variable tail := Protocol.request_bytes (reflexivity variable)++NativeSession.input [] tail.
Definition proof_schedule output history tail :=
 [{|flushedOutput:=output++Protocol.reply_bytes (Protocol.OK history);unreadInput:=NativeSession.input [] tail|};
  {|flushedOutput:=output++Protocol.reply_bytes (Protocol.OK history)++CommandQuitExecution.bye_bytes;unreadInput:=tail|}].
Lemma proof_wire variable tail : proof_input variable tail=
 49::49::32::decimalBytes 5++32::decimalBytes variable++32::decimalBytes 0++32::decimalBytes 0++10::NativeSession.input [] tail.
Proof.
 unfold proof_input,reflexivity,Protocol.request_bytes,Protocol.number_tokens.
 cbn [Protocol.opcode Protocol.arguments Protocol.object_name map Protocol.join_tokens].
 change ((([49;49]++[32]++decimalBytes 5++[32]++decimalBytes variable++[32]++decimalBytes 0++[32]++decimalBytes 0)++[10])++NativeSession.input [] tail=49::49::32::decimalBytes 5++32::decimalBytes variable++32::decimalBytes 0++32::decimalBytes 0++10::NativeSession.input [] tail).
 repeat rewrite <-app_assoc. reflexivity.
Qed.
Theorem generated_reflexivity_quit native logical variable tail observations :
 NativeState.represents native logical ->
 (1024<=length (memory native arraydef_0__token))%nat -> (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 8=0 -> meta_value native 9=0 ->
 Z.of_nat variable<=maximum -> Z.of_nat (length (Protocol.history logical))<maximum ->
 Z.of_nat (length (Protocol.formulas logical)+1)<=9223372036854775807 ->
 stdin native=proof_input variable tail ->
 exists final next,
 DialogueExecution.run native observations final (observations++proof_schedule (stdout native) (length (Protocol.history logical)) tail) /\
 Protocol.dialogue logical [reflexivity variable;NativeSession.quit] [Protocol.OK (length (Protocol.history logical));Protocol.BYE] next [] /\
 NativeState.represents final next /\
 Protocol.theorem_at next (length (Protocol.history logical))=Some (SetTheory.equal variable variable) /\
 stdin final=tail /\ stdout final=stdout native++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)))++CommandQuitExecution.bye_bytes /\
 meta_value final 9=1 /\ meta_value final 8=0.
Proof.
 intros Hstate Htoken Hprint Herror Hstop Hvariable Hhistory Hbudget Hinput.
 pose proof (NativeSession.represented_meta native logical Hstate) as Hmeta.
 set (unread:=49::32::decimalBytes 5++32::decimalBytes variable++32::decimalBytes 0++32::decimalBytes 0++10::NativeSession.input [] tail).
 assert (Hbytes:stdin native=49::unread) by (rewrite Hinput,proof_wire;reflexivity).
 set (pending:=CommandLoopExecution.pending_state (withInput native unread) 49).
 assert (HpendingState:NativeState.represents pending logical).
 { unfold pending,CommandLoopExecution.pending_state. apply NativeSession.state_meta;try lia. now apply NativeSession.state_input. }
 assert (HpendingMeta:(17<length (memory pending arraydef_0__meta))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. change (17<length (memory native arraydef_0__meta))%nat;lia. }
 assert (HpendingToken:(1024<=length (memory pending arraydef_0__token))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
 assert (HpendingPrint:(20<=length (memory pending arraydef_0__printBuffer))%nat).
 { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Hprint. }
 assert (Hpending:meta_value pending 15=50).
 { unfold pending,CommandLoopExecution.pending_state. apply meta_store_same. change (15<length (memory native arraydef_0__meta))%nat;lia. }
 assert (HpendingError:meta_value pending 8=0).
 { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
 assert (HpendingStop:meta_value pending 9=0).
 { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Hstop. }
 destruct (NativeAxiomCommands.generated_reflexivity pending logical (fun _=>false) (fun _=>0) 49 [49] variable 0 0
   32 32 32 32 10 (NativeSession.input [] tail) observations eq_refl HpendingMeta HpendingToken HpendingPrint Hpending HpendingError
   Hbudget Hhistory Hvariable ltac:(unfold maximum;lia) ltac:(unfold maximum;lia) HpendingState
   ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
   ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
   ltac:(unfold TokenByteExecution.separator;tauto) eq_refl)
 as (after & index & fs & Hcommand & Hstep & Hformula & Hderive & HafterState & Hin & Hout & HafterToken & HafterPrint & Hclear & HafterStop & Hsafe).
 assert (HpendingOutput:stdout pending=stdout native) by reflexivity.
 rewrite HpendingOutput in Hcommand,Hout.
 set (trace:=observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)));unreadInput:=NativeSession.input [] tail|}]).
 destruct (NativeSession.generated_quit after (NativeAxiomCommands.logical_after logical fs index) tail trace HafterState HafterToken Hclear Hin)
 as (Hquit & HfinalState & HfinalIn & HfinalOut & HfinalStop & HfinalError).
 set (next:=NativeAxiomCommands.logical_after logical fs index).
 exists (QuitLoopExecution.loop_result after tail),next. split.
 - unfold proof_schedule. eapply DialogueExecution.next with (ch:=49) (tail:=unread) (after:=after).
   + lia.
   + exact Hbytes.
   + lia.
   + exact Hcommand.
   + pose proof (NativeSession.represented_meta after next HafterState);lia.
   + congruence.
   + unfold trace in Hquit. cbn [NativeSession.schedule] in Hquit.
     rewrite Hout in Hquit. repeat rewrite <-app_assoc in Hquit. exact Hquit.
 - split.
   + apply Protocol.dialogue_step with (t:=next);[discriminate|exact Hstep|apply Protocol.dialogue_quit].
   + split;[exact HfinalState|]. split.
     * unfold next,NativeAxiomCommands.logical_after,AxiomReflProtocol.logical_after,AxiomReflProtocol.before_append,Protocol.theorem_at.
       cbn [Protocol.with_history Protocol.history Protocol.formulas].
       rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. cbn [nth_error]. exact Hformula.
     * split;[exact HfinalIn|]. split.
       -- exact (eq_trans HfinalOut (eq_trans (f_equal (fun bytes=>bytes++CommandQuitExecution.bye_bytes) Hout)
            (eq_sym (app_assoc (stdout native) (Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)))) CommandQuitExecution.bye_bytes)))).
       -- split;assumption.
Qed.
(** A complete theorem-producing main session, preceded by any finite canonical
    formula-construction session. The sole capacity premise reserves one new
    formula per construction and one for the final reflexivity theorem. *)
Theorem generated_seed_simple_reflexivity_quit key0 key1 requests variable tail bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Z.of_nat variable<=maximum ->
 Forall NativeSession.valid_request requests -> Z.of_nat (length requests+2)<=9223372036854775807 ->
 exists final replies logical,
 length replies=length requests /\
 execObserved (funcdef_0__main bs ns)
  (SeedBootstrapExecution.initial key0 key1 (Protocol.wire requests++proof_input variable tail) [],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++(Protocol.wire requests++proof_input variable tail)|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=Protocol.wire requests++proof_input variable tail|}]++
 (schedule Protocol.handshake_output requests replies (proof_input variable tail)++
 proof_schedule (NativeSession.output Protocol.handshake_output replies) 0 tail))) /\
 Protocol.dialogue Protocol.initial (requests++[reflexivity variable;NativeSession.quit])
   (replies++[Protocol.OK 0;Protocol.BYE]) logical [] /\
 NativeState.represents final logical /\ Guarantees.safe logical /\
 Protocol.theorem_at logical 0=Some(SetTheory.equal variable variable) /\ SetTheory.derives (SetTheory.equal variable variable) /\
 stdin final=tail /\ stdout final=NativeSession.output Protocol.handshake_output replies++Protocol.reply_bytes (Protocol.OK 0)++CommandQuitExecution.bye_bytes /\
 meta_value final 9=1 /\ meta_value final 8=0.
Proof.
 intros Hkey0 Hkey1 Hvariable Hvalid Hbudget.
 set (input:=Protocol.wire requests++proof_input variable tail).
 destruct (NativeStartup.main_to_commands key0 key1 input bs ns Hkey0 Hkey1)
 as (ready & Hstate & Htop & Hmeta32 & Hsip1 & Hzero & Herror & Hmeta & Htoken & Hprint & Hstop & Hhistory & Hinput & Houtput & Hmain).
 set (observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++input|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=input|}]).
 assert (HinitialBudget:Z.of_nat (length (Protocol.formulas Protocol.initial)+length requests+1)<=9223372036854775807).
 { cbn [Protocol.initial Protocol.formulas length]. rewrite !Nat2Z.inj_add in *;lia. }
 destruct (generated_prefix requests 1 ready Protocol.initial (proof_input variable tail) observations Hvalid HinitialBudget
   Hstate Htoken Hprint Herror Hstop Hinput)
 as (middle & replies & target & Hlength & Hfollows & Hrefines & Hmiddle & Hin & Hout & HmiddleToken & HmiddlePrint & Hclear & HmiddleStop & HhistoryEqual & Hremaining).
 assert (HzeroHistory:Protocol.history target=[]) by exact HhistoryEqual.
 assert (HhistoryRoom:Z.of_nat (length (Protocol.history target))<maximum) by (rewrite HzeroHistory;unfold maximum;cbn;lia).
 set (prefixTrace:=observations++schedule (stdout ready) requests replies (proof_input variable tail)).
 destruct (generated_reflexivity_quit middle target variable tail prefixTrace Hmiddle HmiddleToken HmiddlePrint Hclear HmiddleStop
   Hvariable HhistoryRoom Hremaining Hin)
 as (final & logical & HproofRun & Hdialogue & Hfinal & Htheorem & HfinalIn & HfinalOut & HfinalStop & HfinalError).
 rewrite HzeroHistory in HproofRun,Hdialogue,Htheorem,HfinalOut.
 cbn [length] in HproofRun,Hdialogue,Htheorem,HfinalOut.
 assert (Hrun:DialogueExecution.run ready observations final
   (observations++(schedule (stdout ready) requests replies (proof_input variable tail)++
    proof_schedule (NativeSession.output (stdout ready) replies) 0 tail))).
 { unfold follows in Hfollows. apply Hfollows. unfold prefixTrace in HproofRun.
   rewrite Hout in HproofRun. repeat rewrite <-app_assoc in HproofRun. exact HproofRun. }
 assert (Hfull:Protocol.dialogue Protocol.initial (requests++[reflexivity variable;NativeSession.quit])
   (replies++[Protocol.OK 0;Protocol.BYE]) logical []).
 { exact (Hrefines _ _ _ _ Hdialogue). }
 pose proof (DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 rewrite Houtput in Hcommands. rewrite Houtput in Hout.
 exists final,replies,logical. split;[exact Hlength|]. split.
 - etransitivity;[exact Hmain|exact Hcommands].
 - split;[exact Hfull|]. split;[exact Hfinal|]. split;[exact (Guarantees.initial_dialogue_safe _ _ _ _ Hfull)|].
   split;[exact Htheorem|]. split;[apply SetTheory.d_refl|]. split;[exact HfinalIn|]. split.
   + exact (eq_trans HfinalOut (f_equal (fun bytes=>bytes++Protocol.reply_bytes (Protocol.OK 0)++CommandQuitExecution.bye_bytes) Hout)).
   + split;assumption.
Qed.
End NativeSessionProof.

