From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees Spec.
From NativeProof Require Import Index SipHash NativeState NativeSession NativeStartup
 CommandLoop Dialogue CommandQuit QuitLoop SeedBootstrap FormulaTopology.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeDialogueComposition.
Import IndexExecution SipHashExecution.
(** The shared command-boundary invariant. Additional mathematical storage or
    resource invariants belong in [extra]; [capacity] describes the remaining
    logical requests. Neither definition assumes execution. *)
Record boundary (native:Machine) (logical:Protocol.state) : Prop := Boundary {
 state : NativeState.represents native logical;
 token : (1024<=length (memory native arraydef_0__token))%nat;
 print : (20<=length (memory native arraydef_0__printBuffer))%nat;
 error : meta_value native 8=0;
 running : meta_value native 9=0
}.

(** This is an explicit theorem interface to be discharged for concrete
    handlers. The generic composition results below retain it as a premise;
    they do not assert that the full checker already meets this interface. *)
Definition command_spec (extra:Machine->Protocol.state->Prop)
 (capacity:Protocol.state->list Protocol.request->Prop) :=
 forall native logical request requests observations,
 boundary native logical -> extra native logical -> capacity logical (request::requests) ->
 Protocol.shape request -> Protocol.opcode request<>0%nat ->
 stdin native=Protocol.wire (request::requests) ->
 exists ch unread after reply next,
 0<=ch<256 /\ stdin native=ch::unread /\
 execObserved (funcdef_0__command (fun _=>false) (fun _=>0))
   (CommandLoopExecution.pending_state (withInput native unread) ch,observations)=
 Some(tt,(after,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;
   unreadInput:=Protocol.wire requests|}])) /\
 Protocol.step logical request reply next /\ boundary after next /\ extra after next /\
 capacity next requests /\ stdin after=Protocol.wire requests /\
 stdout after=stdout native++Protocol.reply_bytes reply.

Lemma quit_shape request : Protocol.shape request -> Protocol.opcode request=0%nat -> request=NativeSession.quit.
Proof.
 destruct request as [opcode arguments name]. intros [_ Hshape] Hopcode.
 cbn [Protocol.opcode] in Hopcode. subst opcode. cbn [Protocol.shape Protocol.arguments Protocol.object_name] in Hshape.
 destruct Hshape as [-> ->]. reflexivity.
Qed.

Lemma no_replies requests prefix : Protocol.flush_schedule requests [] prefix=[].
Proof. destruct requests;reflexivity. Qed.

Theorem generated_finite extra capacity : command_spec extra capacity ->
 forall requests native logical observations,
 Forall Protocol.shape requests -> boundary native logical -> extra native logical -> capacity logical requests ->
 stdin native=Protocol.wire requests ->
 exists final replies target remaining,
 DialogueExecution.run native observations final
   (observations++Protocol.flush_schedule requests replies (stdout native)) /\
 Protocol.dialogue logical requests replies target remaining /\
 NativeState.represents final target /\ meta_value final 8=0 /\
 stdout final=stdout native++concat (map Protocol.reply_bytes replies) /\ stdin final=remaining.
Proof.
 intros Hcommands requests. induction requests as [|request requests IH];
   intros native logical observations Hshape Hboundary Hextra Hcapacity Hinput.
 - exists native,[],logical,[]. split.
   + cbn [Protocol.flush_schedule]. rewrite app_nil_r. apply DialogueExecution.eof;exact Hinput.
   + split;[apply Protocol.dialogue_eof|]. split;[exact (state _ _ Hboundary)|].
     split;[exact (error _ _ Hboundary)|]. split;[now rewrite app_nil_r|exact Hinput].
 - inversion Hshape as [|request' requests' Hrequest Hrequests];subst request' requests'.
   destruct (Nat.eq_dec (Protocol.opcode request) 0%nat) as [Hquit|Hcontinue].
   + pose proof (quit_shape request Hrequest Hquit) as ->.
     assert (HquitInput:stdin native=NativeSession.input [] (Protocol.wire requests)).
     { exact Hinput. }
     destruct (NativeSession.generated_quit native logical (Protocol.wire requests) observations
       (state _ _ Hboundary) (token _ _ Hboundary) (error _ _ Hboundary) HquitInput)
       as (Hrun & Hstate & Hin & Hout & Hstop & Herror).
     exists (QuitLoopExecution.loop_result native (Protocol.wire requests)),[Protocol.BYE],logical,(Protocol.wire requests).
     split.
     * cbn [Protocol.flush_schedule]. rewrite no_replies. exact Hrun.
     * split;[apply Protocol.dialogue_quit|]. split;[exact Hstate|]. split;[exact Herror|].
       split;[|exact Hin]. cbn [map concat]. rewrite app_nil_r. exact Hout.
   + destruct (Hcommands native logical request requests observations Hboundary Hextra Hcapacity Hrequest Hcontinue Hinput)
       as (ch & unread & after & reply & next & Hbyte & Hbytes & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
     destruct (IH after next
       (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=Protocol.wire requests|}])
       Hrequests HnextBoundary HnextExtra HnextCapacity Hin)
       as (final & replies & target & remaining & Hrun & Hdialogue & Hstate & Hclear & HfinalOut & HfinalIn).
     exists final,(reply::replies),target,remaining. split.
     * cbn [Protocol.flush_schedule].
       eapply DialogueExecution.next with (ch:=ch) (tail:=unread) (after:=after).
       -- exact Hbyte.
       -- exact Hbytes.
       -- pose proof (NativeSession.represented_meta native logical (state _ _ Hboundary));lia.
       -- exact Hcommand.
       -- pose proof (NativeSession.represented_meta after next (state _ _ HnextBoundary));lia.
       -- exact (running _ _ HnextBoundary).
       -- rewrite Hout in Hrun. now rewrite <-app_assoc in Hrun.
     * split;[eapply Protocol.dialogue_step;[exact Hcontinue|exact Hstep|exact Hdialogue]|].
       split;[exact Hstate|]. split;[exact Hclear|]. split;[|exact HfinalIn].
       cbn [map concat]. exact (eq_trans HfinalOut (eq_trans
         (f_equal (fun bytes=>bytes++concat (map Protocol.reply_bytes replies)) Hout)
         (eq_sym (app_assoc (stdout native) (Protocol.reply_bytes reply) (concat (map Protocol.reply_bytes replies)))))).
Qed.

(** A pure initialization obligation, stated in terms of the actual startup
    invariants rather than a successful execution of the requested commands. *)
Definition initialized (extra:Machine->Protocol.state->Prop)
 (capacity:Protocol.state->list Protocol.request->Prop) :=
 forall requests ready,
 Forall Protocol.shape requests -> capacity Protocol.initial requests ->
 boundary ready Protocol.initial -> FormulaTopology.ordered ready 1 ->
 length (memory ready arraydef_0__meta)=32%nat -> length (memory ready arraydef_0__sipState)=1%nat ->
 stdin ready=Protocol.wire requests -> stdout ready=Protocol.handshake_output -> extra ready Protocol.initial.

Theorem generated_main extra capacity : command_spec extra capacity -> initialized extra capacity ->
 forall key0 key1 requests bs ns,
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum ->
 Forall Protocol.shape requests -> capacity Protocol.initial requests ->
 exists replies final logical remaining,
 Protocol.dialogue Protocol.initial requests replies logical remaining /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved (funcdef_0__main bs ns)
   (SeedBootstrapExecution.initial key0 key1 (Protocol.wire requests) [],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++Protocol.wire requests|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=Protocol.wire requests|}]++
 Protocol.flush_schedule requests replies Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat (map Protocol.reply_bytes replies) /\ stdin final=remaining.
Proof.
 intros Hcommands Hinitialized key0 key1 requests bs ns Hkey0 Hkey1 Hshape Hcapacity.
 destruct (NativeStartup.main_to_commands key0 key1 (Protocol.wire requests) bs ns Hkey0 Hkey1)
 as (ready & Hstate & Htop & Hmeta32 & Hsip1 & Hzero & Herror & Hmeta & Htoken & Hprint & Hstop & Hhistory & Hinput & Houtput & Hmain).
 assert (Hboundary:boundary ready Protocol.initial) by (constructor;assumption).
 pose proof (Hinitialized requests ready Hshape Hcapacity Hboundary Htop Hmeta32 Hsip1 Hinput Houtput) as Hextra.
 set (observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++Protocol.wire requests|};
   {|flushedOutput:=Protocol.handshake_output;unreadInput:=Protocol.wire requests|}]).
 destruct (generated_finite extra capacity Hcommands requests ready Protocol.initial observations
   Hshape Hboundary Hextra Hcapacity Hinput)
 as (final & replies & logical & remaining & Hrun & Hdialogue & Hfinal & Hclear & Hout & Hin).
 pose proof (DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as HcommandsRun.
 rewrite Houtput in HcommandsRun,Hout.
 exists replies,final,logical,remaining. split;[exact Hdialogue|].
 split;[exact (Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|]. split;[exact Hfinal|]. split;[exact Hclear|].
 split;[etransitivity;[exact Hmain|exact HcommandsRun]|]. split;assumption.
Qed.

(** Exact standalone end-to-end contract, conditional on discharging the
    explicit concrete command and initialization interfaces above. *)
Theorem required extra capacity bs ns : command_spec extra capacity -> initialized extra capacity ->
 Spec.required (funcdef_0__main bs ns) (arrays _ environment1) (capacity Protocol.initial).
Proof.
 intros Hcommands Hinitialized key0 key1 requests Hkey0 Hkey1 Hshape Hcapacity.
 destruct (generated_main extra capacity Hcommands Hinitialized key0 key1 requests bs ns Hkey0 Hkey1 Hshape Hcapacity)
 as (replies & final & logical & remaining & Hdialogue & Hsafe & Hstate & Herror & Hrun & Hout & Hin).
 exists replies,final,logical,remaining. split;[exact Hdialogue|]. split;[exact Hsafe|].
 split;[exact Hrun|]. split;assumption.
Qed.
End NativeDialogueComposition.
