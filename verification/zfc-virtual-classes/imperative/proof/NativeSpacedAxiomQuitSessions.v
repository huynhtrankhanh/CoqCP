From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash HashTable TokenByte NativeState NativeSession NativeAxiomTotal NativeWhitespaceAxiomInvariant NativeCommandLengths NativeCommandBoundary FormulaTopology ClassLookup CommandLoop Dialogue SeedBootstrap NativeStartupCompact NativeWhitespaceEOFDialogue NativeWhitespaceQuit CommandQuit QuitLoop NativeDialogueComposition NativeWhitespaceDialogue NativeSeedInputTransport NativeCommandWhitespace NativePointwiseState MachinePointwise ReadNat.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSpacedAxiomQuitSessions.
Import IndexExecution SipHashExecution.
Record frame := Frame { before_opcode:list Z; tag:nat; a:nat; b:nat; c:nat; sep0:Z; sp1:list Z; sep1:Z; sp2:list Z; sep2:Z; sp3:list Z; sep3:Z; sp4:list Z; sep4:Z }.
Definition request f := Protocol.Req 11 [tag f;a f;b f;c f] [].
Definition valid f := Forall TokenByteExecution.separator(before_opcode f) /\ Z.of_nat(tag f)<=maximum /\ Z.of_nat(a f)<=maximum /\ Z.of_nat(b f)<=maximum /\ Z.of_nat(c f)<=maximum /\
 TokenByteExecution.separator(sep0 f) /\ TokenByteExecution.separator(sep1 f) /\ TokenByteExecution.separator(sep2 f) /\ TokenByteExecution.separator(sep3 f) /\ TokenByteExecution.separator(sep4 f) /\
 Forall TokenByteExecution.separator(sp1 f) /\ Forall TokenByteExecution.separator(sp2 f) /\ Forall TokenByteExecution.separator(sp3 f) /\ Forall TokenByteExecution.separator(sp4 f).
Definition frame_bytes f := before_opcode f++[49;49;sep0 f]++sp1 f++decimalBytes(tag f)++sep1 f::sp2 f++decimalBytes(a f)++sep2 f::sp3 f++decimalBytes(b f)++sep3 f::sp4 f++decimalBytes(c f)++[sep4 f].
Fixpoint wire fs := match fs with []=>[] | f::rest=>frame_bytes f++wire rest end.
Fixpoint schedule fs replies quit_prefix suffix output := match fs,replies with
 | _::rest,r::rs=>let next:=output++Protocol.reply_bytes r in {|flushedOutput:=next;unreadInput:=wire rest++quit_prefix++[48;10]++suffix|}::schedule rest rs quit_prefix suffix next
 | [],[]=>[{|flushedOutput:=output++CommandQuitExecution.bye_bytes;unreadInput:=suffix|}]
 | _,_=>[] end.
Inductive capacity : Protocol.state -> list frame -> Prop :=
| capacity_nil s : capacity s []
| capacity_cons s f fs : Z.of_nat(length(Protocol.history s))<maximum -> NativeAxiomTotal.resources s (tag f)(a f)(b f)(c f) ->
 (forall reply next, Protocol.step s (request f) reply next -> capacity next fs) -> capacity s (f::fs).
Theorem generated_finite frames quit_prefix suffix : forall native logical observations,
 Forall valid frames -> Forall TokenByteExecution.separator quit_prefix -> capacity logical frames ->
 NativeDialogueComposition.boundary native logical -> Guarantees.safe logical ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 FormulaTopology.ordered native (length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity -> ClassLookup.wellformed native ->
 stdin native=wire frames++quit_prefix++[48;10]++suffix ->
 exists final replies target,
 length replies=length frames /\ DialogueExecution.run native observations final (observations++schedule frames replies quit_prefix suffix (stdout native)) /\
 Protocol.dialogue logical (map request frames++[NativeSession.quit]) (replies++[Protocol.BYE]) target [] /\ Guarantees.safe target /\ NativeState.represents final target /\ meta_value final 8=0 /\
 stdout final=NativeSession.output (stdout native) replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix /\ meta_value final 9=1.
Proof.
 induction frames as [|f frames IH];intros native logical observations Hvalid Hending Hcapacity Hboundary Hsafe Hmeta Hsip Htop Hfalse Hgood Hin.
 all: set(ending:=quit_prefix++[48;10]++suffix) in *.
 - destruct quit_prefix as [|ch prefix].
   + change(stdin native=NativeSession.input [] suffix) in Hin.
     destruct(NativeSession.generated_quit native logical suffix observations (NativeDialogueComposition.state _ _ Hboundary)
       (NativeDialogueComposition.token _ _ Hboundary) (NativeDialogueComposition.error _ _ Hboundary) Hin)
       as(Hrun & Hstate & Hinput & Houtput & Hstop & Herror).
     exists(QuitLoopExecution.loop_result native suffix),[],logical. split;[reflexivity|]. split;[exact Hrun|].
     split;[apply Protocol.dialogue_quit|]. repeat first[assumption|split].
   + inversion Hending as [|? ? Hch Hprefix];subst.
     assert(Hchbyte:0<=ch<256) by (unfold TokenByteExecution.separator in Hch;lia).
     destruct(NativeWhitespaceQuit.generated native logical ch prefix suffix observations Hboundary Hchbyte Hch Hprefix)
       as(after & Hcommand & Hstate & Hinput & Houtput & Hstop & Herror & Hlength).
     exists after,[],logical. split;[reflexivity|]. split.
     * cbn [schedule]. eapply DialogueExecution.stop with (ch:=ch) (tail:=prefix++[48;10]++suffix).
       -- exact Hchbyte.
       -- exact Hin.
       -- pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia.
       -- exact Hcommand.
       -- exact Hlength.
       -- rewrite Hstop;discriminate.
     * split;[apply Protocol.dialogue_quit|]. repeat first[assumption|split].
 - inversion Hvalid as [|? ? Hf Htail];subst. destruct Hf as (Hleading & Htag & Ha & Hb & Hc & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hp1 & Hp2 & Hp3 & Hp4).
   inversion Hcapacity as [|? ? ? Hhistory Hresources HcapacityNext];subst.
   set(tail:=wire frames++ending).
   set(rest:=49::sep0 f::sp1 f++decimalBytes(tag f)++sep1 f::sp2 f++decimalBytes(a f)++sep2 f::sp3 f++decimalBytes(b f)++sep3 f::sp4 f++decimalBytes(c f)++sep4 f::tail).
   assert(Hwire:stdin native=before_opcode f++49::rest).
   { cbn [wire] in Hin. unfold frame_bytes in Hin. unfold rest,tail. repeat first [progress cbn [app] in Hin | rewrite <-app_assoc in Hin]. exact Hin. }
   set(pending:=CommandLoopExecution.pending_state(withInput native rest)49).
   assert(Hpm:(31<length(memory pending arraydef_0__meta))%nat) by (unfold pending,CommandLoopExecution.pending_state;rewrite store_meta_length;exact Hmeta).
   assert(Hps:(0<length(memory pending arraydef_0__sipState))%nat) by (unfold pending,CommandLoopExecution.pending_state;rewrite store_meta_other by discriminate;exact Hsip).
   assert(Hpt:(1024<=length(memory pending arraydef_0__token))%nat) by (unfold pending,CommandLoopExecution.pending_state;rewrite store_meta_other by discriminate;exact(NativeDialogueComposition.token _ _ Hboundary)).
   assert(Hpp:(20<=length(memory pending arraydef_0__printBuffer))%nat) by (unfold pending,CommandLoopExecution.pending_state;rewrite store_meta_other by discriminate;exact(NativeDialogueComposition.print _ _ Hboundary)).
   assert(Hpv:meta_value pending 15=50) by (unfold pending,CommandLoopExecution.pending_state;rewrite meta_store_same by (cbn [memory withInput];lia);reflexivity).
   assert(Hpe:meta_value pending 8=0) by (unfold pending,CommandLoopExecution.pending_state;rewrite meta_store_other by lia;exact(NativeDialogueComposition.error _ _ Hboundary)).
   assert(Hpstop:meta_value pending 9=0) by (unfold pending,CommandLoopExecution.pending_state;rewrite meta_store_other by lia;exact(NativeDialogueComposition.running _ _ Hboundary)).
   assert(Hpstate:NativeState.represents pending logical) by (unfold pending,CommandLoopExecution.pending_state;apply NativeSession.state_meta;try lia;apply NativeSession.state_input;exact(NativeDialogueComposition.state _ _ Hboundary)).
   assert(Hptop:FormulaTopology.ordered pending (length(Protocol.formulas logical))).
   { eapply FormulaTopology.same;[exact Htop|]. intros parent _. unfold HashTableInvariant.tuple_at,pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. reflexivity. }
   assert(Hpgood:ClassLookup.wellformed pending) by (unfold ClassLookup.wellformed,pending,CommandLoopExecution.pending_state in *;rewrite store_meta_other by discriminate;exact Hgood).
   destruct(NativeWhitespaceAxiomInvariant.generated_total pending logical (fun _=>false)(fun _=>0) 49 [49] (tag f)(a f)(b f)(c f)
     (sep0 f)(sp1 f)(sep1 f)(sp2 f)(sep2 f)(sp3 f)(sep3 f)(sp4 f)(sep4 f) tail observations
     ltac:(vm_compute;reflexivity) Hpm Hps Hpt Hpp Hpv Hpe Hhistory Htag Ha Hb Hc Hpstate Hptop Hfalse Hpgood Hresources Hs0 Hs1 Hs2 Hs3 Hs4 Hp1 Hp2 Hp3 Hp4
     ltac:(unfold pending,CommandLoopExecution.pending_state,rest;reflexivity))
    as(after & reply & next & Hcommand & Hstep & Hstate & Hio & HsafeNext & HtopNext & HgoodNext & Hprefix & Hgrowth).
   destruct Hio as (Hnextin & Hnextout & Hnexttoken & Hnextprint & Hnexterror & Hnextstop).
   assert(HnextBoundary:NativeDialogueComposition.boundary after next) by (constructor;try assumption;now rewrite Hnextstop,Hpstop).
   assert(Hnextmeta:(31<length(memory after arraydef_0__meta))%nat).
   { rewrite (NativeCommandLengths.generated arraydef_0__meta pending (fun _=>false)(fun _=>0) after observations _ NativeCommandLengths.meta_protected Hcommand). exact Hpm. }
   assert(Hnextsip:(0<length(memory after arraydef_0__sipState))%nat).
   { rewrite (NativeCommandLengths.generated arraydef_0__sipState pending (fun _=>false)(fun _=>0) after observations _ NativeCommandLengths.sipState_protected Hcommand). exact Hps. }
   assert(Hnextfalse:nth_error(Protocol.formulas next)0=Some SetTheory.falsity).
   { destruct Hprefix as [more Hprefix]. rewrite Hprefix,nth_error_app1;[exact Hfalse|]. apply nth_error_Some. congruence. }
   assert(Hactual:exists first input_tail actual,
     0<=first<256 /\ stdin native=first::input_tail /\
     execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(CommandLoopExecution.pending_state(withInput native input_tail)first,observations)=
     Some(tt,(actual,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
     NativeDialogueComposition.boundary actual next /\ stdin actual=tail /\ stdout actual=stdout native++Protocol.reply_bytes reply /\
     (31<length(memory actual arraydef_0__meta))%nat /\ (0<length(memory actual arraydef_0__sipState))%nat /\
     FormulaTopology.ordered actual (length(Protocol.formulas next)) /\ ClassLookup.wellformed actual).
   { destruct(before_opcode f) as [|first leading] eqn:Hbefore.
     - cbn [app] in Hwire. exists 49,rest,after. split;[lia|]. split;[exact Hwire|]. split;[exact Hcommand|].
       split;[exact HnextBoundary|]. split;[exact Hnextin|]. split;[exact Hnextout|]. repeat split;assumption.
     - inversion Hleading as [|? ? Hfirst Hlead];subst. assert(Hfirstbyte:0<=first<256) by (unfold TokenByteExecution.separator in Hfirst;lia).
       set(argtail:=sp1 f++decimalBytes(tag f)++sep1 f::sp2 f++decimalBytes(a f)++sep2 f::sp3 f++decimalBytes(b f)++sep3 f::sp4 f++decimalBytes(c f)++sep4 f::tail).
       assert(Hrest:rest=49::sep0 f::argtail) by reflexivity.
       assert(Hcanonical:execObserved(funcdef_0__command (fun _=>false)(fun _=>0))
        (NativeCommandWhitespace.canonical native 49 [49] (sep0 f) argtail,observations)=
        Some(tt,(after,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}]))).
       { unfold NativeCommandWhitespace.canonical,pending,CommandLoopExecution.pending_state in *. cbn [app] in *. now rewrite <-Hrest. }
       destruct(NativeCommandWhitespace.generated native (fun _=>false)(fun _=>0) first leading 49 [49] (sep0 f) argtail observations after _
        ltac:(lia) (NativeDialogueComposition.token _ _ Hboundary) (NativeDialogueComposition.error _ _ Hboundary) Hfirstbyte Hfirst Hlead
        ltac:(cbn;lia) ltac:(repeat constructor;lia) ltac:(unfold ReadNatExecution.number_from,maximum;cbn;lia) Hs0 Hcanonical)
        as(actual & Hrun & Hsame).
       exists first,(leading++49::rest),actual. split;[exact Hfirstbyte|]. split;[exact Hwire|]. split.
       + unfold NativeCommandWhitespace.spaced in Hrun. cbn [app] in Hrun. rewrite <-Hrest in Hrun. exact Hrun.
       + split;[exact(NativePointwiseState.boundary _ _ _ Hsame HnextBoundary)|].
         pose proof Hsame as (Hsin & Hsout & Hmemory). split;[now rewrite <-Hsin|]. split;[now rewrite <-Hsout|].
         split;[now rewrite <-Hmemory|]. split;[now rewrite <-Hmemory|]. split.
         * eapply FormulaTopology.same;[exact HtopNext|]. intros parent _. unfold HashTableInvariant.tuple_at. now rewrite <-Hmemory.
         * apply(ClassLookup.transport after actual);[symmetry;apply Hmemory|exact HgoodNext]. }
   destruct Hactual as(first & input_tail & actual & Hfirst & HactualInput & HactualCommand & HactualBoundary & Hactualin & Hactualout & Hactualmeta & Hactualsip & Hactualtop & Hactualgood).
   destruct(IH actual next (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])
     Htail Hending (HcapacityNext reply next Hstep) HactualBoundary (HsafeNext Hsafe) Hactualmeta Hactualsip Hactualtop Hnextfalse Hactualgood Hactualin)
     as(final & replies & target & Hlength & Hrun & Hdialogue & HsafeFinal & HstateFinal & Herror & Hout & Hfinalin & Hstop).
   exists final,(reply::replies),target. split;[cbn [length];congruence|]. split.
   + cbn [schedule]. eapply DialogueExecution.next with (ch:=first) (tail:=input_tail) (after:=actual).
     * exact Hfirst.
     * exact HactualInput.
     * lia.
     * exact HactualCommand.
     * pose proof(NativeSession.represented_meta actual next (NativeDialogueComposition.state _ _ HactualBoundary));lia.
     * exact(NativeDialogueComposition.running _ _ HactualBoundary).
     * rewrite Hactualout,<-app_assoc in Hrun. exact Hrun.
   + split;[cbn [map];eapply Protocol.dialogue_step;[unfold request;cbn;lia|exact Hstep|exact Hdialogue]|].
     split;[exact HsafeFinal|]. split;[exact HstateFinal|]. split;[exact Herror|]. split;[|now split].
     cbn [NativeSession.output]. now rewrite Hactualout in Hout.
Qed.
Theorem generated_main key0 key1 frames quit_prefix suffix bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames -> Forall TokenByteExecution.separator quit_prefix -> capacity Protocol.initial frames ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map request frames++[NativeSession.quit]) (replies++[Protocol.BYE]) logical [] /\ Guarantees.safe logical /\ NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire frames++quit_prefix++[48;10]++suffix)[],[])=
 Some(tt,(final,[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames++quit_prefix++[48;10]++suffix|};{|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++quit_prefix++[48;10]++suffix|}]++schedule frames replies quit_prefix suffix Protocol.handshake_output)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix /\ meta_value final 9=1.
Proof.
 intros Hkey0 Hkey1 Hvalid Hending Hcapacity.
 destruct(NativeStartupCompact.main_to_commands key0 key1(wire frames++quit_prefix++[48;10]++suffix)bs ns Hkey0 Hkey1)
 as(ready & Hstate & Htop & Hmeta & Hsip & Hzero & Herror & Hmetab & Htoken & Hprint & Hstop & Hhistory & Hin & Hout & Hmain & Hempty).
 assert(Hboundary:NativeDialogueComposition.boundary ready Protocol.initial) by (constructor;assumption).
 assert(Hgood:ClassLookup.wellformed ready) by (apply ClassLookup.empty;exact(NativeState.empty_classes _ Hempty)).
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames++quit_prefix++[48;10]++suffix|};{|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++quit_prefix++[48;10]++suffix|}]).
 destruct(generated_finite frames quit_prefix suffix ready Protocol.initial observations Hvalid Hending Hcapacity Hboundary Guarantees.initial_safe ltac:(lia) ltac:(lia) Htop eq_refl Hgood Hin)
 as(final & replies & logical & Hlength & Hrun & Hdialogue & Hsafe & Hfinal & Hclear & Hfinalout & Hfinalin & Hfinalstop).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 rewrite Hout in Hcommands,Hfinalout. exists replies,final,logical. repeat first [assumption|split]. etransitivity;[exact Hmain|exact Hcommands].
Qed.
Theorem flexible_seeds key0 key1 prefix0 prefix1 seed0 seed1 frames quit_prefix suffix bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> TokenByteExecution.separator seed0 -> TokenByteExecution.separator seed1 ->
 Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 -> Forall valid frames -> Forall TokenByteExecution.separator quit_prefix -> capacity Protocol.initial frames ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map request frames++[NativeSession.quit]) (replies++[Protocol.BYE]) logical [] /\ Guarantees.safe logical /\ NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 seed0 seed1(wire frames++quit_prefix++[48;10]++suffix),[])=
 Some(tt,(final,[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++seed0::(prefix1++decimalBytes key1++seed1::(wire frames++quit_prefix++[48;10]++suffix))|};{|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++quit_prefix++[48;10]++suffix|}]++schedule frames replies quit_prefix suffix Protocol.handshake_output)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix /\ meta_value final 9=1.
Proof.
 intros Hkey0 Hkey1 Hseed0 Hseed1 Hprefix0 Hprefix1 Hvalid Hending Hcapacity.
 destruct(generated_main key0 key1 frames quit_prefix suffix bs ns Hkey0 Hkey1 Hvalid Hending Hcapacity)
 as(replies & final & logical & Hlength & Hdialogue & Hsafe & Hstate & Herror & Hrun & Hout & Hin & Hfinalstop).
 exists replies,final,logical. repeat first [assumption|split]. eapply NativeSeedInputTransport.generated;eassumption.
Qed.
End NativeSpacedAxiomQuitSessions.
