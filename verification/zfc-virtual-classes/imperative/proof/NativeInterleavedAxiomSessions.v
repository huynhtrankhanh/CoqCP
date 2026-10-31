From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash HashTable TokenByte NativeState NativeSession NativeAxiomTotal NativeWhitespaceAxiomInvariant NativeSpacedSimpleInvariant NativeSimpleCommands NativeBasicInvariant NativeBasicDispatcher LogicalStorageMonotone NativeCommandLengths NativeCommandBoundary FormulaTopology ClassLookup CommandLoop Dialogue SeedBootstrap NativeStartupCompact NativeWhitespaceEOFDialogue NativeDialogueComposition NativeWhitespaceDialogue NativeSeedInputTransport NativeCommandWhitespace NativePointwiseState MachinePointwise ReadNat.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeInterleavedAxiomSessions.
Import IndexExecution SipHashExecution.
Inductive kind := equality | membership | implication | quantify | axiom.
Record frame := Frame { operation:kind; before_opcode:list Z; tag:nat; a:nat; b:nat; c:nat; sep0:Z; sp1:list Z; sep1:Z; sp2:list Z; sep2:Z; sp3:list Z; sep3:Z; sp4:list Z; sep4:Z }.
Definition opcode f := match operation f with equality=>1%nat | membership=>2%nat | implication=>3%nat | quantify=>4%nat | axiom=>11%nat end.
Definition digit f := match operation f with equality=>49 | membership=>50 | implication=>51 | quantify=>52 | axiom=>49 end.
Definition digits f := match operation f with axiom=>[49] | _=>[] end.
Definition request f := Protocol.Req (opcode f) (match operation f with quantify=>[a f] | axiom=>[tag f;a f;b f;c f] | _=>[a f;b f] end) [].
Definition valid f := Forall TokenByteExecution.separator(before_opcode f) /\ Z.of_nat(tag f)<=maximum /\ Z.of_nat(a f)<=maximum /\ Z.of_nat(b f)<=maximum /\ Z.of_nat(c f)<=maximum /\
 TokenByteExecution.separator(sep0 f) /\ TokenByteExecution.separator(sep1 f) /\ TokenByteExecution.separator(sep2 f) /\ TokenByteExecution.separator(sep3 f) /\ TokenByteExecution.separator(sep4 f) /\
 Forall TokenByteExecution.separator(sp1 f) /\ Forall TokenByteExecution.separator(sp2 f) /\ Forall TokenByteExecution.separator(sp3 f) /\ Forall TokenByteExecution.separator(sp4 f).
Definition argument_bytes f := sep0 f::sp1 f++match operation f with
 | axiom=>decimalBytes(tag f)++sep1 f::sp2 f++decimalBytes(a f)++sep2 f::sp3 f++decimalBytes(b f)++sep3 f::sp4 f++decimalBytes(c f)++[sep4 f]
 | quantify=>decimalBytes(a f)++[sep4 f]
 | _=>decimalBytes(a f)++sep1 f::sp2 f++decimalBytes(b f)++[sep4 f] end.
Definition frame_bytes f := before_opcode f++digit f::digits f++argument_bytes f.
Fixpoint wire fs := match fs with []=>[] | f::rest=>frame_bytes f++wire rest end.
Fixpoint schedule fs replies output ending := match fs,replies with
 | _::rest,r::rs=>let next:=output++Protocol.reply_bytes r in {|flushedOutput:=next;unreadInput:=wire rest++ending|}::schedule rest rs next ending
 | _,_=>[] end.
Inductive capacity : Protocol.state -> list frame -> Prop :=
| capacity_nil s : capacity s []
| capacity_cons s f fs : Z.of_nat(length(Protocol.history s))<maximum -> Z.of_nat(length(Protocol.formulas s))<=9223372036854775807 ->
 (operation f=axiom -> NativeAxiomTotal.resources s (tag f)(a f)(b f)(c f)) ->
 (forall reply next, Protocol.step s (request f) reply next -> capacity next fs) -> capacity s (f::fs).
Lemma decimal_opcode f : decimalBytes(opcode f)=digit f::digits f.
Proof. destruct f as [k leading tag a b c s0 p1 s1 p2 s2 p3 s3 p4 s4]. destruct k;vm_compute;reflexivity. Qed.
Lemma simple_good native opcode ch chars sep payload bs ns observations final trace :
 (opcode=1%nat \/ opcode=2%nat \/ opcode=3%nat \/ opcode=4%nat) -> decimalBytes opcode=ch::chars ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> TokenByteExecution.separator sep -> stdin native=chars++sep::payload ->
 ClassLookup.wellformed native -> execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) -> ClassLookup.wellformed final.
Proof.
 intros Hop Henc Hmeta Htoken Hpending Herror Hsep Hin Hgood Hrun.
 apply(ClassLookup.transport native);[|exact Hgood].
 eapply NativeBasicInvariant.canonical_array with (opcode:=opcode)(ch:=ch)(chars:=chars)(separator:=sep)(payload:=payload)(observations:=observations)(trace:=trace);try eassumption.
 - unfold NativeBasicInvariant.Arrays.kind;tauto.
 - unfold NativeBasicInvariant.Arrays.unchanged;intuition congruence.
 - unfold NativeBasicDispatcher.supported,NativeBasicDispatcher.two,NativeBasicDispatcher.one;tauto.
Qed.
Theorem generated_finite frames ending : forall native logical observations,
 Forall valid frames -> Forall TokenByteExecution.separator ending -> capacity logical frames ->
 NativeDialogueComposition.boundary native logical -> Guarantees.safe logical ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 FormulaTopology.ordered native (length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity -> ClassLookup.wellformed native ->
 stdin native=wire frames++ending ->
 exists final replies target,
 length replies=length frames /\ DialogueExecution.run native observations final (observations++schedule frames replies (stdout native) ending) /\
 Protocol.dialogue logical (map request frames) replies target [] /\ Guarantees.safe target /\ NativeState.represents final target /\ meta_value final 8=0 /\
 stdout final=stdout native++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 induction frames as [|f frames IH];intros native logical observations Hvalid Hending Hcapacity Hboundary Hsafe Hmeta Hsip Htop Hfalse Hgood Hin.
 - destruct(NativeWhitespaceEOFDialogue.generated native logical ending observations Hboundary Hending Hin) as(final & Hrun & Hstate & Hinput & Houtput & Herror).
   exists final,[],logical. split;[reflexivity|]. split;[cbn [schedule];now rewrite app_nil_r|].
   split;[apply Protocol.dialogue_eof|]. split;[exact Hsafe|]. split;[exact Hstate|]. split;[exact Herror|]. split;[now rewrite app_nil_r|exact Hinput].
 - inversion Hvalid as [|? ? Hf Htail];subst. destruct Hf as (Hleading & Htag & Ha & Hb & Hc & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hp1 & Hp2 & Hp3 & Hp4).
   inversion Hcapacity as [|? ? ? Hhistory Hroom Hresources HcapacityNext];subst.
   set(tail:=wire frames++ending).
   set(rest:=digits f++argument_bytes f++tail).
   assert(Hwire:stdin native=before_opcode f++digit f::rest).
   { cbn [wire] in Hin. unfold frame_bytes in Hin. unfold rest,tail. repeat first [progress cbn [app] in Hin | rewrite <-app_assoc in Hin]. exact Hin. }
   set(pending:=CommandLoopExecution.pending_state(withInput native rest)(digit f)).
   assert(Hpm:(31<length(memory pending arraydef_0__meta))%nat) by (unfold pending,CommandLoopExecution.pending_state;rewrite store_meta_length;exact Hmeta).
   assert(Hps:(0<length(memory pending arraydef_0__sipState))%nat) by (unfold pending,CommandLoopExecution.pending_state;rewrite store_meta_other by discriminate;exact Hsip).
   assert(Hpt:(1024<=length(memory pending arraydef_0__token))%nat) by (unfold pending,CommandLoopExecution.pending_state;rewrite store_meta_other by discriminate;exact(NativeDialogueComposition.token _ _ Hboundary)).
   assert(Hpp:(20<=length(memory pending arraydef_0__printBuffer))%nat) by (unfold pending,CommandLoopExecution.pending_state;rewrite store_meta_other by discriminate;exact(NativeDialogueComposition.print _ _ Hboundary)).
   assert(Hpv:meta_value pending 15=digit f+1) by (unfold pending,CommandLoopExecution.pending_state;rewrite meta_store_same by (cbn [memory withInput];lia);reflexivity).
   assert(Hpe:meta_value pending 8=0) by (unfold pending,CommandLoopExecution.pending_state;rewrite meta_store_other by lia;exact(NativeDialogueComposition.error _ _ Hboundary)).
   assert(Hpstop:meta_value pending 9=0) by (unfold pending,CommandLoopExecution.pending_state;rewrite meta_store_other by lia;exact(NativeDialogueComposition.running _ _ Hboundary)).
   assert(Hpstate:NativeState.represents pending logical) by (unfold pending,CommandLoopExecution.pending_state;apply NativeSession.state_meta;try lia;apply NativeSession.state_input;exact(NativeDialogueComposition.state _ _ Hboundary)).
   assert(Hptop:FormulaTopology.ordered pending (length(Protocol.formulas logical))).
   { eapply FormulaTopology.same;[exact Htop|]. intros parent _. unfold HashTableInvariant.tuple_at,pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. reflexivity. }
   assert(Hpgood:ClassLookup.wellformed pending) by (unfold ClassLookup.wellformed,pending,CommandLoopExecution.pending_state in *;rewrite store_meta_other by discriminate;exact Hgood).
   assert(Hinput:stdin pending=digits f++sep0 f::(tl(argument_bytes f)++tail)).
   { unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes. destruct(operation f);cbn [stdin withInput store_meta app tl];repeat rewrite <-app_assoc;reflexivity. }
   assert(Hresult:exists after reply next,
     execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(after,observations++[{|flushedOutput:=stdout pending++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
     Protocol.step logical (request f) reply next /\ NativeState.represents after next /\ NativeCommandBoundary.io pending after reply tail /\
     (Guarantees.safe logical->Guarantees.safe next) /\ FormulaTopology.ordered after(length(Protocol.formulas next)) /\ ClassLookup.wellformed after).
   { destruct(operation f) eqn:Hop.
     - assert(Hcase:opcode f=1%nat \/ opcode f=2%nat) by (unfold opcode;rewrite Hop;tauto).
       assert(HgoodResult:forall after trace, execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(after,trace))->ClassLookup.wellformed after).
       { intros after trace Hrun. eapply(simple_good pending (opcode f) (digit f) (digits f) (sep0 f) (tl(argument_bytes f)++tail));try eassumption;try lia;try (unfold opcode;rewrite Hop;tauto);try exact(decimal_opcode f). }
       destruct(NativeSpacedSimpleInvariant.Atoms.generated_protocol (opcode f) (digit f)(digits f) pending logical (fun _=>false)(fun _=>0) (a f)(b f) (sep0 f)(sp1 f)(sep1 f)(sp2 f)(sep4 f) tail observations
        Hcase (decimal_opcode f) ltac:(lia) Hpt Hpp Hpv Hpe Hroom Ha Hb Hpstate Hs0 Hs1 Hs4 Hp1 Hp2
        ltac:(unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes,digits;cbn [stdin withInput store_meta];rewrite Hop;repeat first [progress cbn [app]|rewrite <-app_assoc];reflexivity))
       as(after & index & fs & Hrun & Hstep & Hstate & Hsimple & HtopFun).
       exists after,(Protocol.OK index),(NativeSimpleCommands.Atoms.logical_after logical fs). split;[exact Hrun|]. split;[unfold request;rewrite Hop;exact Hstep|]. split;[exact Hstate|].
       split;[unfold NativeCommandBoundary.io,NativeSimpleCommands.boundary in *;intuition|]. split;[intro Hsafe';eapply Guarantees.step_safe;eassumption|]. split;[exact(HtopFun Hptop)|exact (HgoodResult after _ Hrun)].
     - assert(Hcase:opcode f=1%nat \/ opcode f=2%nat) by (unfold opcode;rewrite Hop;tauto).
       assert(HgoodResult:forall after trace, execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(after,trace))->ClassLookup.wellformed after).
       { intros after trace Hrun. eapply(simple_good pending (opcode f) (digit f) (digits f) (sep0 f) (tl(argument_bytes f)++tail));try eassumption;try lia;try (unfold opcode;rewrite Hop;tauto);try exact(decimal_opcode f). }
       destruct(NativeSpacedSimpleInvariant.Atoms.generated_protocol (opcode f) (digit f)(digits f) pending logical (fun _=>false)(fun _=>0) (a f)(b f) (sep0 f)(sp1 f)(sep1 f)(sp2 f)(sep4 f) tail observations
        Hcase (decimal_opcode f) ltac:(lia) Hpt Hpp Hpv Hpe Hroom Ha Hb Hpstate Hs0 Hs1 Hs4 Hp1 Hp2
        ltac:(unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes,digits;cbn [stdin withInput store_meta];rewrite Hop;repeat first [progress cbn [app]|rewrite <-app_assoc];reflexivity))
       as(after & index & fs & Hrun & Hstep & Hstate & Hsimple & HtopFun).
       exists after,(Protocol.OK index),(NativeSimpleCommands.Atoms.logical_after logical fs). split;[exact Hrun|]. split;[unfold request;rewrite Hop;exact Hstep|]. split;[exact Hstate|].
       split;[unfold NativeCommandBoundary.io,NativeSimpleCommands.boundary in *;intuition|]. split;[intro Hsafe';eapply Guarantees.step_safe;eassumption|]. split;[exact(HtopFun Hptop)|exact (HgoodResult after _ Hrun)].
     - assert(Henc:decimalBytes 3%nat=digit f::digits f) by (pose proof(decimal_opcode f) as H;unfold opcode in H;now rewrite Hop in H).
       assert(HgoodResult:forall after trace, execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(after,trace))->ClassLookup.wellformed after).
       { intros after trace Hrun. eapply(simple_good pending 3 (digit f) (digits f) (sep0 f) (tl(argument_bytes f)++tail));try eassumption;try lia;try tauto;try exact Henc. }
       destruct(NativeSpacedSimpleInvariant.Imp.generated_total_protocol (digit f)(digits f) pending logical (fun _=>false)(fun _=>0) (a f)(b f) (sep0 f)(sp1 f)(sep1 f)(sp2 f)(sep4 f) tail observations
        Henc ltac:(lia) Hpt Hpp Hpv Hpe Hroom Ha Hb Hpstate Hs0 Hs1 Hs4 Hp1 Hp2
        ltac:(unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes,digits;cbn [stdin withInput store_meta];rewrite Hop;repeat first [progress cbn [app]|rewrite <-app_assoc];reflexivity))
       as(after & reply & next & Hrun & Hstep & Hstate & Hsimple & HtopFun).
       exists after,reply,next. unfold request,opcode. rewrite Hop. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hstate|].
       split;[unfold NativeCommandBoundary.io,NativeSimpleCommands.boundary in *;intuition|]. split;[intro Hsafe';eapply Guarantees.step_safe;eassumption|]. split;[exact(HtopFun Hptop)|exact (HgoodResult after _ Hrun)].
     - assert(Hdigit4:digit f=52) by (unfold digit;now rewrite Hop).
       assert(Hpending4:meta_value pending 15=53) by (rewrite Hpv,Hdigit4;reflexivity).
       assert(Henc:decimalBytes 4%nat=digit f::digits f) by (pose proof(decimal_opcode f) as H;unfold opcode in H;now rewrite Hop in H).
       assert(HgoodResult:forall after trace, execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=Some(tt,(after,trace))->ClassLookup.wellformed after).
       { intros after trace Hrun. eapply(simple_good pending 4 (digit f) (digits f) (sep0 f) (tl(argument_bytes f)++tail));try eassumption;try lia;try tauto;try exact Henc. }
       destruct(NativeSpacedSimpleInvariant.All.generated_total_protocol pending logical (fun _=>false)(fun _=>0) (a f) (sep0 f)(sp1 f)(sep4 f) tail observations
        ltac:(lia) Hpt Hpp Hpending4 Hpe Hroom Ha Hpstate Hs0 Hs4 Hp1
        ltac:(unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes,digits;cbn [stdin withInput store_meta];rewrite Hop;repeat first [progress cbn [app]|rewrite <-app_assoc];reflexivity))
       as(after & reply & next & Hrun & Hstep & Hstate & Hsimple & HtopFun).
       exists after,reply,next. unfold request,opcode. rewrite Hop. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hstate|].
       split;[unfold NativeCommandBoundary.io,NativeSimpleCommands.boundary in *;intuition|]. split;[intro Hsafe';eapply Guarantees.step_safe;eassumption|]. split;[exact(HtopFun Hptop)|exact (HgoodResult after _ Hrun)].
     - assert(Henc:decimalBytes 11%nat=digit f::digits f) by (pose proof(decimal_opcode f) as H;unfold opcode in H;now rewrite Hop in H).
       destruct(NativeWhitespaceAxiomInvariant.generated_total pending logical (fun _=>false)(fun _=>0) (digit f)(digits f) (tag f)(a f)(b f)(c f)
        (sep0 f)(sp1 f)(sep1 f)(sp2 f)(sep2 f)(sp3 f)(sep3 f)(sp4 f)(sep4 f) tail observations
        Henc Hpm Hps Hpt Hpp Hpv Hpe Hhistory Htag Ha Hb Hc Hpstate Hptop Hfalse Hpgood (Hresources eq_refl) Hs0 Hs1 Hs2 Hs3 Hs4 Hp1 Hp2 Hp3 Hp4
        ltac:(unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes,digits;cbn [stdin withInput store_meta];rewrite Hop;repeat first [progress cbn [app]|rewrite <-app_assoc];reflexivity))
       as(after & reply & next & Hrun & Hstep & Hstate & Hio & HsafeNext & HtopNext & HgoodNext & Hprefix & Hgrowth).
       exists after,reply,next. unfold request,opcode. rewrite Hop. repeat first [assumption|split]. }
   destruct Hresult as(after & reply & next & Hcommand & Hstep & Hstate & Hio & HsafeNext & HtopNext & HgoodNext).
   pose proof(LogicalStorageMonotone.formulas _ _ (LogicalStorageMonotone.step _ _ _ _ Hstep)) as Hprefix.
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
     - cbn [app] in Hwire. exists (digit f),rest,after. split;[unfold digit;destruct(operation f);lia|]. split;[exact Hwire|]. split;[exact Hcommand|].
       split;[exact HnextBoundary|]. split;[exact Hnextin|]. split;[exact Hnextout|]. repeat split;assumption.
     - inversion Hleading as [|? ? Hfirst Hlead];subst. assert(Hfirstbyte:0<=first<256) by (unfold TokenByteExecution.separator in Hfirst;lia).
       set(argtail:=tl(argument_bytes f)++tail).
       assert(Hrest:rest=digits f++sep0 f::argtail) by (unfold rest,argtail,argument_bytes;destruct(operation f);cbn [digits app tl];repeat rewrite <-app_assoc;reflexivity).
       assert(Hcanonical:execObserved(funcdef_0__command (fun _=>false)(fun _=>0))
        (NativeCommandWhitespace.canonical native (digit f) (digits f) (sep0 f) argtail,observations)=
        Some(tt,(after,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}]))).
       { unfold NativeCommandWhitespace.canonical,pending,CommandLoopExecution.pending_state in *. cbn [app] in *. now rewrite <-Hrest. }
       destruct(NativeCommandWhitespace.generated native (fun _=>false)(fun _=>0) first leading (digit f) (digits f) (sep0 f) argtail observations after _
        ltac:(lia) (NativeDialogueComposition.token _ _ Hboundary) (NativeDialogueComposition.error _ _ Hboundary) Hfirstbyte Hfirst Hlead
        ltac:(unfold digits;destruct(operation f);cbn;lia) ltac:(unfold digit,digits;destruct(operation f);repeat constructor;lia) ltac:(unfold ReadNatExecution.number_from,digit,digits,maximum;destruct(operation f);cbn;lia) Hs0 Hcanonical)
        as(actual & Hrun & Hsame).
       exists first,(leading++digit f::rest),actual. split;[exact Hfirstbyte|]. split;[exact Hwire|]. split.
       + unfold NativeCommandWhitespace.spaced in Hrun. cbn [app] in Hrun. rewrite <-Hrest in Hrun. exact Hrun.
       + split;[exact(NativePointwiseState.boundary _ _ _ Hsame HnextBoundary)|].
         pose proof Hsame as (Hsin & Hsout & Hmemory). split;[now rewrite <-Hsin|]. split;[now rewrite <-Hsout|].
         split;[now rewrite <-Hmemory|]. split;[now rewrite <-Hmemory|]. split.
         * eapply FormulaTopology.same;[exact HtopNext|]. intros parent _. unfold HashTableInvariant.tuple_at. now rewrite <-Hmemory.
         * apply(ClassLookup.transport after actual);[symmetry;apply Hmemory|exact HgoodNext]. }
   destruct Hactual as(first & input_tail & actual & Hfirst & HactualInput & HactualCommand & HactualBoundary & Hactualin & Hactualout & Hactualmeta & Hactualsip & Hactualtop & Hactualgood).
   destruct(IH actual next (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])
     Htail Hending (HcapacityNext reply next Hstep) HactualBoundary (HsafeNext Hsafe) Hactualmeta Hactualsip Hactualtop Hnextfalse Hactualgood Hactualin)
     as(final & replies & target & Hlength & Hrun & Hdialogue & HsafeFinal & HstateFinal & Herror & Hout & Hfinalin).
   exists final,(reply::replies),target. split;[cbn [length];congruence|]. split.
   + cbn [schedule]. eapply DialogueExecution.next with (ch:=first) (tail:=input_tail) (after:=actual).
     * exact Hfirst.
     * exact HactualInput.
     * lia.
     * exact HactualCommand.
     * pose proof(NativeSession.represented_meta actual next (NativeDialogueComposition.state _ _ HactualBoundary));lia.
     * exact(NativeDialogueComposition.running _ _ HactualBoundary).
     * rewrite Hactualout,<-app_assoc in Hrun. exact Hrun.
   + split;[cbn [map];eapply Protocol.dialogue_step;[unfold request,opcode;destruct(operation f);cbn;lia|exact Hstep|exact Hdialogue]|].
     split;[exact HsafeFinal|]. split;[exact HstateFinal|]. split;[exact Herror|]. split;[|exact Hfinalin].
     cbn [map concat]. rewrite Hout,Hactualout. now rewrite app_assoc.
Qed.
Theorem generated_main key0 key1 frames ending bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames -> Forall TokenByteExecution.separator ending -> capacity Protocol.initial frames ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map request frames) replies logical [] /\ Guarantees.safe logical /\ NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire frames++ending)[],[])=
 Some(tt,(final,[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames++ending|};{|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++ending|}]++schedule frames replies Protocol.handshake_output ending)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 intros Hkey0 Hkey1 Hvalid Hending Hcapacity.
 destruct(NativeStartupCompact.main_to_commands key0 key1(wire frames++ending)bs ns Hkey0 Hkey1)
 as(ready & Hstate & Htop & Hmeta & Hsip & Hzero & Herror & Hmetab & Htoken & Hprint & Hstop & Hhistory & Hin & Hout & Hmain & Hempty).
 assert(Hboundary:NativeDialogueComposition.boundary ready Protocol.initial) by (constructor;assumption).
 assert(Hgood:ClassLookup.wellformed ready) by (apply ClassLookup.empty;exact(NativeState.empty_classes _ Hempty)).
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames++ending|};{|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++ending|}]).
 destruct(generated_finite frames ending ready Protocol.initial observations Hvalid Hending Hcapacity Hboundary Guarantees.initial_safe ltac:(lia) ltac:(lia) Htop eq_refl Hgood Hin)
 as(final & replies & logical & Hlength & Hrun & Hdialogue & Hsafe & Hfinal & Hclear & Hfinalout & Hfinalin).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 rewrite Hout in Hcommands,Hfinalout. exists replies,final,logical. repeat first [assumption|split]. etransitivity;[exact Hmain|exact Hcommands].
Qed.
Theorem flexible_seeds key0 key1 prefix0 prefix1 seed0 seed1 frames ending bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> TokenByteExecution.separator seed0 -> TokenByteExecution.separator seed1 ->
 Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 -> Forall valid frames -> Forall TokenByteExecution.separator ending -> capacity Protocol.initial frames ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map request frames) replies logical [] /\ Guarantees.safe logical /\ NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 seed0 seed1(wire frames++ending),[])=
 Some(tt,(final,[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++seed0::(prefix1++decimalBytes key1++seed1::(wire frames++ending))|};{|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++ending|}]++schedule frames replies Protocol.handshake_output ending)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 intros Hkey0 Hkey1 Hseed0 Hseed1 Hprefix0 Hprefix1 Hvalid Hending Hcapacity.
 destruct(generated_main key0 key1 frames ending bs ns Hkey0 Hkey1 Hvalid Hending Hcapacity)
 as(replies & final & logical & Hlength & Hdialogue & Hsafe & Hstate & Herror & Hrun & Hout & Hin).
 exists replies,final,logical. repeat first [assumption|split]. eapply NativeSeedInputTransport.generated;eassumption.
Qed.
End NativeInterleavedAxiomSessions.
