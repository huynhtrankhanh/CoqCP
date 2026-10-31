From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash HashTable TokenByte NativeState NativeSession NativeAxiomTotal NativeWhitespaceAxiom NativeCommandBoundary FormulaTopology CommandLoop Dialogue SeedBootstrap NativeStartupCompact NativeWhitespaceDialogue NativeSeedInputTransport NativeWhitespaceMPDialogue LogicalHistory NativeDialogueComposition.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeAxiomFirstMixedDialogue.
Import IndexExecution SipHashExecution.
Definition wire tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4 :=
 [49;49;sep0]++sp1++decimalBytes tag++sep1::sp2++decimalBytes a++sep2::sp3++decimalBytes b++sep3::sp4++decimalBytes c++[sep4].
Theorem generated_main key0 key1 tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4 frames ending bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum ->
 Z.of_nat tag<=maximum -> Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum ->
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 -> TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
 Forall TokenByteExecution.separator sp1 -> Forall TokenByteExecution.separator sp2 -> Forall TokenByteExecution.separator sp3 -> Forall TokenByteExecution.separator sp4 ->
 NativeAxiomTotal.resources Protocol.initial tag a b c ->
 Forall NativeWhitespaceMPDialogue.valid frames -> Forall TokenByteExecution.separator ending ->
 (forall reply logical, Protocol.step Protocol.initial (Protocol.Req 11 [tag;a;b;c] []) reply logical ->
  Z.of_nat(length(Protocol.history logical)+length frames)<maximum /\
  Z.of_nat(length(Protocol.formulas logical)+length frames)<=9223372036854775807) ->
 exists final reply logical replies target,
 Protocol.step Protocol.initial (Protocol.Req 11 [tag;a;b;c] []) reply logical /\
 length replies=length frames /\ Protocol.dialogue logical (map NativeWhitespaceMPDialogue.request frames) replies target [] /\ Guarantees.safe target /\ NativeState.represents final target /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4++NativeWhitespaceMPDialogue.wire frames++ending)[],[])=
 Some(tt,(final,[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4++NativeWhitespaceMPDialogue.wire frames++ending|};
 {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4++NativeWhitespaceMPDialogue.wire frames++ending|};
 {|flushedOutput:=Protocol.handshake_output++Protocol.reply_bytes reply;unreadInput:=NativeWhitespaceMPDialogue.wire frames++ending|}]++
 NativeWhitespaceMPDialogue.schedule frames replies (Protocol.handshake_output++Protocol.reply_bytes reply) ending)) /\
 stdout final=(Protocol.handshake_output++Protocol.reply_bytes reply)++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 intros Hk0 Hk1 Htag Ha Hb Hc Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsp1 Hsp2 Hsp3 Hsp4 Hresources Hvalid Hending Hbounds.
 set(tail:=NativeWhitespaceMPDialogue.wire frames++ending).
 set(input:=wire tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4++tail).
 destruct(NativeStartupCompact.main_to_commands key0 key1 input bs ns Hk0 Hk1)
 as(ready & Hstate & Htop & Hmeta & Hsip & Hzero & Herror & Hmetab & Htoken & Hprint & Hstop & Hhistory & Hin & Hout & Hmain & Hempty).
 set(rest:=49::sep0::sp1++decimalBytes tag++sep1::sp2++decimalBytes a++sep2::sp3++decimalBytes b++sep3::sp4++decimalBytes c++sep4::tail).
 assert(Hwire:stdin ready=49::rest) by (rewrite Hin;unfold input,wire,rest;repeat first [progress cbn [app] | rewrite <-app_assoc];reflexivity).
 set(pending:=CommandLoopExecution.pending_state(withInput ready rest)49).
 assert(Hpm:(31<length(memory pending arraydef_0__meta))%nat) by (unfold pending,CommandLoopExecution.pending_state;rewrite store_meta_length;cbn [memory withInput];lia).
 assert(Hps:(0<length(memory pending arraydef_0__sipState))%nat) by (unfold pending,CommandLoopExecution.pending_state;rewrite store_meta_other by discriminate;exact ltac:(cbn [memory withInput];lia)).
 assert(Hpt:(1024<=length(memory pending arraydef_0__token))%nat) by (unfold pending,CommandLoopExecution.pending_state;rewrite store_meta_other by discriminate;exact Htoken).
 assert(Hpp:(20<=length(memory pending arraydef_0__printBuffer))%nat) by (unfold pending,CommandLoopExecution.pending_state;rewrite store_meta_other by discriminate;exact Hprint).
 assert(Hpv:meta_value pending 15=50) by (unfold pending,CommandLoopExecution.pending_state;rewrite meta_store_same by (cbn [memory withInput];lia);reflexivity).
 assert(Hpe:meta_value pending 8=0) by (unfold pending,CommandLoopExecution.pending_state;rewrite meta_store_other by lia;exact Herror).
 assert(Hpstop:meta_value pending 9=0) by (unfold pending,CommandLoopExecution.pending_state;rewrite meta_store_other by lia;exact Hstop).
 assert(Hpstate:NativeState.represents pending Protocol.initial) by (unfold pending,CommandLoopExecution.pending_state;apply NativeSession.state_meta;try lia;apply NativeSession.state_input;exact Hstate).
 assert(Hptop:FormulaTopology.ordered pending (length(Protocol.formulas Protocol.initial))).
 { cbn [Protocol.initial Protocol.formulas length]. eapply FormulaTopology.same;[exact Htop|]. intros parent _. unfold HashTableInvariant.tuple_at,pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. reflexivity. }
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++input|};{|flushedOutput:=Protocol.handshake_output;unreadInput:=input|}]).
 destruct(NativeWhitespaceAxiom.generated_total pending Protocol.initial (fun _=>false)(fun _=>0) 49 [49] tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4 tail observations
 ltac:(vm_compute;reflexivity) Hpm Hps Hpt Hpp Hpv Hpe ltac:(cbn [Protocol.initial Protocol.history length];unfold maximum;lia)
 Htag Ha Hb Hc Hpstate Hptop eq_refl Hresources Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsp1 Hsp2 Hsp3 Hsp4
 ltac:(unfold pending,CommandLoopExecution.pending_state,rest;cbn [stdin withInput store_meta];reflexivity))
 as(final & reply & logical & Hcommand & Hstep & Hfinal & Hio & Hsafe).
 destruct Hio as (Hfinalin & Hfinalout & Hfinaltoken & Hfinalprint & Hfinalerror & Hfinalstop).
 assert(HnextBoundary:NativeDialogueComposition.boundary final logical).
 { constructor;try assumption. now rewrite Hfinalstop,Hpstop. }
 destruct(Hbounds reply logical Hstep) as (HhistoryBound & HformulaBound).
 pose proof(LogicalHistory.step_valid _ _ _ _ Hstep LogicalHistory.initial_valid) as HhistoryValid.
 set(nextobservations:=observations++[{|flushedOutput:=stdout ready++Protocol.reply_bytes reply;unreadInput:=tail|}]).
 destruct(NativeWhitespaceMPDialogue.generated_finite frames ending final logical nextobservations Hvalid Hending HnextBoundary HhistoryValid HhistoryBound HformulaBound Hfinalin)
 as(last & replies & target & Hlength & Htailrun & Hdialogue & Hlast & Hlasterror & Hlastout & Hlastin).
 assert(Hrun:DialogueExecution.run ready observations last (nextobservations++NativeWhitespaceMPDialogue.schedule frames replies (stdout final) ending)).
 { eapply DialogueExecution.next with (ch:=49) (tail:=rest) (after:=final);[lia|exact Hwire|lia|exact Hcommand| | |exact Htailrun].
   - pose proof(NativeSession.represented_meta final logical Hfinal);lia.
   - rewrite Hfinalstop,Hpstop;reflexivity. }
 pose proof(DialogueExecution.generated_commands ready observations last _ bs ns Hrun) as Hcommands.
 exists last,reply,logical,replies,target. split;[exact Hstep|]. split;[exact Hlength|]. split;[exact Hdialogue|].
 split;[eapply Guarantees.dialogue_safe;[exact Hdialogue|apply Hsafe;exact Guarantees.initial_safe]|]. split;[exact Hlast|]. split;[exact Hlasterror|].
 split.
 - rewrite Hmain. unfold nextobservations,observations in Hcommands. rewrite Hout in Hcommands. change(stdout final=stdout ready++Protocol.reply_bytes reply) in Hfinalout. rewrite Hfinalout,Hout in Hcommands. exact Hcommands.
 - split;[rewrite Hlastout;change(stdout final=stdout ready++Protocol.reply_bytes reply) in Hfinalout;now rewrite Hfinalout,Hout|exact Hlastin].
Qed.
End NativeAxiomFirstMixedDialogue.
