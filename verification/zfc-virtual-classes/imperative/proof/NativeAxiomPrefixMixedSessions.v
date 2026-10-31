From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash HashTable TokenByte NativeState NativeSession NativeAxiomTotal NativeWhitespaceAxiomInvariant NativeCommandLengths NativeCommandBoundary FormulaTopology ClassLookup CommandLoop Dialogue SeedBootstrap NativeStartupCompact NativeWhitespaceEOFDialogue NativeDialogueComposition NativeWhitespaceDialogue NativeSeedInputTransport NativeWhitespaceMPDialogue LogicalHistory NativeCommandWhitespace NativePointwiseState MachinePointwise ReadNat.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeAxiomPrefixMixedSessions.
Import IndexExecution SipHashExecution.
Record frame := Frame { before_opcode:list Z; tag:nat; a:nat; b:nat; c:nat; sep0:Z; sp1:list Z; sep1:Z; sp2:list Z; sep2:Z; sp3:list Z; sep3:Z; sp4:list Z; sep4:Z }.
Definition request f := Protocol.Req 11 [tag f;a f;b f;c f] [].
Definition valid f := Forall TokenByteExecution.separator(before_opcode f) /\ Z.of_nat(tag f)<=maximum /\ Z.of_nat(a f)<=maximum /\ Z.of_nat(b f)<=maximum /\ Z.of_nat(c f)<=maximum /\
 TokenByteExecution.separator(sep0 f) /\ TokenByteExecution.separator(sep1 f) /\ TokenByteExecution.separator(sep2 f) /\ TokenByteExecution.separator(sep3 f) /\ TokenByteExecution.separator(sep4 f) /\
 Forall TokenByteExecution.separator(sp1 f) /\ Forall TokenByteExecution.separator(sp2 f) /\ Forall TokenByteExecution.separator(sp3 f) /\ Forall TokenByteExecution.separator(sp4 f).
Definition frame_bytes f := before_opcode f++[49;49;sep0 f]++sp1 f++decimalBytes(tag f)++sep1 f::sp2 f++decimalBytes(a f)++sep2 f::sp3 f++decimalBytes(b f)++sep3 f::sp4 f++decimalBytes(c f)++[sep4 f].
Fixpoint wire fs := match fs with []=>[] | f::rest=>frame_bytes f++wire rest end.
Fixpoint schedule fs replies output ending := match fs,replies with
 | _::rest,r::rs=>let next:=output++Protocol.reply_bytes r in {|flushedOutput:=next;unreadInput:=wire rest++ending|}::schedule rest rs next ending
 | _,_=>[] end.
Inductive capacity : Protocol.state -> list frame -> Prop :=
| capacity_nil s : capacity s []
| capacity_cons s f fs : Z.of_nat(length(Protocol.history s))<maximum -> NativeAxiomTotal.resources s (tag f)(a f)(b f)(c f) ->
 (forall reply next, Protocol.step s (request f) reply next -> capacity next fs) -> capacity s (f::fs).
Definition suffix_bounds logical frames (more:list NativeWhitespaceMPDialogue.frame) := forall replies target,
 Protocol.dialogue logical (map request frames) replies target [] ->
 Z.of_nat(length(Protocol.history target)+length more)<maximum /\
 Z.of_nat(length(Protocol.formulas target)+length more)<=9223372036854775807.
Theorem generated_finite frames more ending : forall native logical observations,
 Forall valid frames -> Forall NativeWhitespaceMPDialogue.valid more -> Forall TokenByteExecution.separator ending -> capacity logical frames -> suffix_bounds logical frames more ->
 NativeDialogueComposition.boundary native logical -> Guarantees.safe logical -> LogicalHistory.valid logical ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 FormulaTopology.ordered native (length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity -> ClassLookup.wellformed native ->
 stdin native=wire frames++NativeWhitespaceMPDialogue.wire more++ending ->
 exists final replies middle more_replies target,
 length replies=length frames /\ length more_replies=length more /\
 DialogueExecution.run native observations final (observations++schedule frames replies (stdout native) (NativeWhitespaceMPDialogue.wire more++ending)++
 NativeWhitespaceMPDialogue.schedule more more_replies (stdout native++concat(map Protocol.reply_bytes replies)) ending) /\
 Protocol.dialogue logical (map request frames) replies middle [] /\ Protocol.dialogue middle (map NativeWhitespaceMPDialogue.request more) more_replies target [] /\
 Guarantees.safe target /\ NativeState.represents final target /\ meta_value final 8=0 /\
 stdout final=stdout native++concat(map Protocol.reply_bytes replies)++concat(map Protocol.reply_bytes more_replies) /\ stdin final=[].
Proof.
 induction frames as [|f frames IH];intros native logical observations Hvalid Hmore Hending Hcapacity Hsuffix Hboundary Hsafe HhistoryValid Hmeta Hsip Htop Hfalse Hgood Hin.
 - destruct(Hsuffix [] logical (Protocol.dialogue_eof logical)) as (HhistoryBound & HformulaBound).
   destruct(NativeWhitespaceMPDialogue.generated_finite more ending native logical observations Hmore Hending Hboundary HhistoryValid HhistoryBound HformulaBound Hin)
    as(final & more_replies & target & Hlength & Hrun & Hdialogue & Hstate & Herror & Hout & Hinput).
   exists final,[],logical,more_replies,target. split;[reflexivity|]. split;[exact Hlength|]. split.
   + cbn [schedule map concat]. now rewrite !app_nil_r.
   + split;[apply Protocol.dialogue_eof|]. split;[exact Hdialogue|]. split;[eapply Guarantees.dialogue_safe;eassumption|].
     split;[exact Hstate|]. split;[exact Herror|]. split;[exact Hout|exact Hinput].
 - inversion Hvalid as [|? ? Hf Htail];subst. destruct Hf as (Hleading & Htag & Ha & Hb & Hc & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hp1 & Hp2 & Hp3 & Hp4).
   inversion Hcapacity as [|? ? ? Hhistory Hresources HcapacityNext];subst.
   set(tail:=wire frames++NativeWhitespaceMPDialogue.wire more++ending).
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
   { destruct Hprefix as [extra Hprefix]. rewrite Hprefix,nth_error_app1;[exact Hfalse|]. apply nth_error_Some. congruence. }
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
   assert(HsuffixNext:suffix_bounds next frames more).
   { intros rs target Hdialogue. apply(Hsuffix (reply::rs) target). cbn [map]. eapply Protocol.dialogue_step;[unfold request;cbn;lia|exact Hstep|exact Hdialogue]. }
   destruct(IH actual next (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])
     Htail Hmore Hending (HcapacityNext reply next Hstep) HsuffixNext HactualBoundary (HsafeNext Hsafe) (LogicalHistory.step_valid _ _ _ _ Hstep HhistoryValid) Hactualmeta Hactualsip Hactualtop Hnextfalse Hactualgood Hactualin)
     as(final & replies & middle & more_replies & target & Hlength & Hmorelength & Hrun & Hdialogue & Hmoredialogue & HsafeFinal & HstateFinal & Herror & Hout & Hfinalin).
   exists final,(reply::replies),middle,more_replies,target. split;[cbn [length];congruence|]. split;[exact Hmorelength|]. split.
   + cbn [schedule]. eapply DialogueExecution.next with (ch:=first) (tail:=input_tail) (after:=actual).
     * exact Hfirst.
     * exact HactualInput.
     * lia.
     * exact HactualCommand.
     * pose proof(NativeSession.represented_meta actual next (NativeDialogueComposition.state _ _ HactualBoundary));lia.
     * exact(NativeDialogueComposition.running _ _ HactualBoundary).
     * rewrite Hactualout in Hrun. cbn [map concat]. repeat rewrite <-app_assoc in *. exact Hrun.
   + split;[cbn [map];eapply Protocol.dialogue_step;[unfold request;cbn;lia|exact Hstep|exact Hdialogue]|].
     split;[exact Hmoredialogue|]. split;[exact HsafeFinal|]. split;[exact HstateFinal|]. split;[exact Herror|]. split;[|exact Hfinalin].
     cbn [map concat]. rewrite Hout,Hactualout. repeat rewrite <-app_assoc. reflexivity.
Qed.
Theorem generated_main key0 key1 frames more ending bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames -> Forall NativeWhitespaceMPDialogue.valid more -> Forall TokenByteExecution.separator ending ->
 capacity Protocol.initial frames -> suffix_bounds Protocol.initial frames more ->
 exists final replies middle more_replies target,
 length replies=length frames /\ length more_replies=length more /\
 Protocol.dialogue Protocol.initial (map request frames) replies middle [] /\ Protocol.dialogue middle (map NativeWhitespaceMPDialogue.request more) more_replies target [] /\ Guarantees.safe target /\ NativeState.represents final target /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire frames++NativeWhitespaceMPDialogue.wire more++ending)[],[])=
 Some(tt,(final,[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames++NativeWhitespaceMPDialogue.wire more++ending|};{|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++NativeWhitespaceMPDialogue.wire more++ending|}]++
 schedule frames replies Protocol.handshake_output (NativeWhitespaceMPDialogue.wire more++ending)++NativeWhitespaceMPDialogue.schedule more more_replies (Protocol.handshake_output++concat(map Protocol.reply_bytes replies)) ending)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++concat(map Protocol.reply_bytes more_replies) /\ stdin final=[].
Proof.
 intros Hkey0 Hkey1 Hvalid Hmore Hending Hcapacity Hsuffix.
 destruct(NativeStartupCompact.main_to_commands key0 key1(wire frames++NativeWhitespaceMPDialogue.wire more++ending)bs ns Hkey0 Hkey1)
 as(ready & Hstate & Htop & Hmeta & Hsip & Hzero & Herror & Hmetab & Htoken & Hprint & Hstop & Hhistory & Hin & Hout & Hmain & Hempty).
 assert(Hboundary:NativeDialogueComposition.boundary ready Protocol.initial) by (constructor;assumption).
 assert(Hgood:ClassLookup.wellformed ready) by (apply ClassLookup.empty;exact(NativeState.empty_classes _ Hempty)).
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames++NativeWhitespaceMPDialogue.wire more++ending|};{|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++NativeWhitespaceMPDialogue.wire more++ending|}]).
 destruct(generated_finite frames more ending ready Protocol.initial observations Hvalid Hmore Hending Hcapacity Hsuffix Hboundary Guarantees.initial_safe LogicalHistory.initial_valid ltac:(lia) ltac:(lia) Htop eq_refl Hgood Hin)
 as(final & replies & middle & more_replies & target & Hlength & Hmorelength & Hrun & Hdialogue & Hmoredialogue & Hsafe & Hfinal & Hclear & Hfinalout & Hfinalin).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 rewrite Hout in Hcommands,Hfinalout. exists final,replies,middle,more_replies,target. repeat first [assumption|split]. etransitivity;[exact Hmain|exact Hcommands].
Qed.
Theorem flexible_seeds key0 key1 prefix0 prefix1 seed0 seed1 frames more ending bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> TokenByteExecution.separator seed0 -> TokenByteExecution.separator seed1 ->
 Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 -> Forall valid frames -> Forall NativeWhitespaceMPDialogue.valid more -> Forall TokenByteExecution.separator ending ->
 capacity Protocol.initial frames -> suffix_bounds Protocol.initial frames more ->
 exists final replies middle more_replies target,
 length replies=length frames /\ length more_replies=length more /\
 Protocol.dialogue Protocol.initial (map request frames) replies middle [] /\ Protocol.dialogue middle (map NativeWhitespaceMPDialogue.request more) more_replies target [] /\ Guarantees.safe target /\ NativeState.represents final target /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 seed0 seed1(wire frames++NativeWhitespaceMPDialogue.wire more++ending),[])=
 Some(tt,(final,[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++seed0::(prefix1++decimalBytes key1++seed1::(wire frames++NativeWhitespaceMPDialogue.wire more++ending))|};{|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++NativeWhitespaceMPDialogue.wire more++ending|}]++
 schedule frames replies Protocol.handshake_output (NativeWhitespaceMPDialogue.wire more++ending)++NativeWhitespaceMPDialogue.schedule more more_replies (Protocol.handshake_output++concat(map Protocol.reply_bytes replies)) ending)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++concat(map Protocol.reply_bytes more_replies) /\ stdin final=[].
Proof.
 intros Hkey0 Hkey1 Hseed0 Hseed1 Hprefix0 Hprefix1 Hvalid Hmore Hending Hcapacity Hsuffix.
 destruct(generated_main key0 key1 frames more ending bs ns Hkey0 Hkey1 Hvalid Hmore Hending Hcapacity Hsuffix)
 as(final & replies & middle & more_replies & target & Hlength & Hmorelength & Hdialogue & Hmoredialogue & Hsafe & Hstate & Herror & Hrun & Hout & Hin).
 exists final,replies,middle,more_replies,target. repeat first [assumption|split]. eapply NativeSeedInputTransport.generated;eassumption.
Qed.
End NativeAxiomPrefixMixedSessions.
