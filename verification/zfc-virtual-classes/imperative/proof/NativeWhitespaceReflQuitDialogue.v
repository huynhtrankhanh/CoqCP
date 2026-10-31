From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeSimpleCommands NativeWhitespaceAtoms NativeWhitespaceImp NativeWhitespaceAll NativeWhitespaceGeneralizeBoundary NativeWhitespaceMPBoundary NativeWhitespaceReflFlow NativeTheoremBoundary NativeCommandBoundary LogicalHistory NativeDialogueComposition NativeCommandWhitespace NativePointwiseState MachinePointwise ReadNat NativeWhitespaceEOFDialogue NativeWhitespaceQuit CommandQuit QuitLoop CommandLoop Dialogue SeedBootstrap NativeStartupCompact NativeWhitespaceDialogue NativeSeedInputTransport.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceReflQuitDialogue.
Import IndexExecution SipHashExecution.
Inductive kind := equality | membership | implication | quantify | generalize | modusponens | reflexivity_axiom.
Record frame := Frame { operation : kind; left_arg : nat; right_arg : nat; before_opcode : list Z; first_sep : Z; first_prefix : list Z; second_sep : Z; second_prefix : list Z; third_arg : nat; third_sep : Z; third_prefix : list Z; fourth_sep : Z; fourth_prefix : list Z; last_sep : Z }.
Definition opcode f := match operation f with equality=>1%nat | membership=>2%nat | implication=>3%nat | quantify=>4%nat | generalize=>13%nat | modusponens=>12%nat | reflexivity_axiom=>11%nat end.
Definition digit f := match operation f with equality=>49 | membership=>50 | implication=>51 | quantify=>52 | generalize=>49 | modusponens=>49 | reflexivity_axiom=>49 end.
Definition digits f := match operation f with generalize=>[51] | modusponens=>[50] | reflexivity_axiom=>[49] | _=>[] end.
Definition request f := Protocol.Req (opcode f) (match operation f with quantify | generalize=>[left_arg f] | reflexivity_axiom=>[5;left_arg f;right_arg f;third_arg f]%nat | _=>[left_arg f;right_arg f] end) [].
Definition valid f := Forall TokenByteExecution.separator(before_opcode f) /\ Z.of_nat(left_arg f)<=maximum /\ Z.of_nat(right_arg f)<=maximum /\ Z.of_nat(third_arg f)<=maximum /\
 TokenByteExecution.separator(third_sep f) /\ TokenByteExecution.separator(fourth_sep f) /\ Forall TokenByteExecution.separator(third_prefix f) /\ Forall TokenByteExecution.separator(fourth_prefix f) /\
 TokenByteExecution.separator(first_sep f) /\ TokenByteExecution.separator(second_sep f) /\ TokenByteExecution.separator(last_sep f) /\
 Forall TokenByteExecution.separator(first_prefix f) /\ Forall TokenByteExecution.separator(second_prefix f).
Definition argument_bytes f := first_sep f :: first_prefix f ++
 match operation f with
 | reflexivity_axiom=>decimalBytes 5++second_sep f::second_prefix f++decimalBytes(left_arg f)++third_sep f::third_prefix f++decimalBytes(right_arg f)++fourth_sep f::fourth_prefix f++decimalBytes(third_arg f)++[last_sep f]
 | quantify | generalize=>decimalBytes(left_arg f)++[last_sep f]
 | _=>decimalBytes(left_arg f)++second_sep f::second_prefix f++decimalBytes(right_arg f)++[last_sep f]
 end.
Definition frame_bytes f := before_opcode f ++ digit f :: digits f ++ argument_bytes f.
Fixpoint wire frames := match frames with []=>[] | f::tail=>frame_bytes f++wire tail end.
Fixpoint schedule frames replies quit_prefix suffix output := match frames,replies with
 | _::tail,reply::rest=>let next:=output++Protocol.reply_bytes reply in {|flushedOutput:=next;unreadInput:=wire tail++quit_prefix++[48;10]++suffix|}::schedule tail rest quit_prefix suffix next
 | [],[]=>[{|flushedOutput:=output++CommandQuitExecution.bye_bytes;unreadInput:=suffix|}]
 | _,_=>[] end.
Lemma history_growth s q reply target : Protocol.step s q reply target ->
 (length(Protocol.history target)<=S(length(Protocol.history s)))%nat.
Proof.
 intros Hstep. destruct Hstep as [reply prior target Haccepted Hretained|target Hreject Hretained];
 destruct Hretained as (_ & _ & _ & Hhist & _ & _);rewrite Hhist.
 - inversion Haccepted;subst;cbn [Protocol.history Protocol.with_history];repeat rewrite length_app in *;cbn in *;try lia.
   match goal with H : Protocol.history s = _ ++ [_] |- _ => rewrite H, length_app;cbn;lia end.
 - lia.
Qed.
Lemma decimal_opcode f : decimalBytes(opcode f)=digit f::digits f.
Proof. destruct f as [k a b leading x xs y ys c z zs w ws last]. destruct k;vm_compute;reflexivity. Qed.
Theorem generated_finite frames quit_prefix suffix : forall native logical observations,
 Forall valid frames -> Forall TokenByteExecution.separator quit_prefix ->
 NativeDialogueComposition.boundary native logical -> LogicalHistory.valid logical ->
 Z.of_nat(length(Protocol.history logical)+length frames)<maximum ->
 Z.of_nat(length(Protocol.formulas logical)+length frames)<=9223372036854775807 ->
 stdin native=wire frames++quit_prefix++[48;10]++suffix ->
 exists final replies target,
 length replies=length frames /\ DialogueExecution.run native observations final (observations++schedule frames replies quit_prefix suffix (stdout native)) /\
 Protocol.dialogue logical (map request frames++[NativeSession.quit]) (replies++[Protocol.BYE]) target [] /\ NativeState.represents final target /\
 meta_value final 8=0 /\ stdout final=NativeSession.output (stdout native) replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix /\ meta_value final 9=1.
Proof.
 induction frames as [|f frames IH]; intros native logical observations Hvalid Hending Hboundary HhistoryValid HhistoryBound Hbound Hin.
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
 - inversion Hvalid as [|? ? Hf Htail];subst. destruct Hf as (Hleading & Ha & Hb & Hc & HsepThird & HsepFourth & HprefixThird & HprefixFourth & Hsep1 & Hsep2 & Hsep3 & Hprefix1 & Hprefix2).
   pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary)) as Hmeta.
   assert(Hdigit:0<=digit f<256) by (unfold digit;destruct (operation f);lia).
   set(rest:=argument_bytes f++wire frames++ending).
   assert(Hinput:stdin native=before_opcode f++digit f::digits f++rest).
   { unfold rest. cbn [wire] in Hin. unfold frame_bytes in Hin. repeat first [progress cbn [app] in Hin | rewrite <-app_assoc in Hin]. exact Hin. }
   set(pending:=CommandLoopExecution.pending_state(withInput native(digits f++rest))(digit f)).
   assert(Hpendingmeta:(17<length(memory pending arraydef_0__meta))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. cbn [memory withInput]. lia. }
   assert(Hpendingtoken:(1024<=length(memory pending arraydef_0__token))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact(NativeDialogueComposition.token _ _ Hboundary). }
   assert(Hpendingprint:(20<=length(memory pending arraydef_0__printBuffer))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact(NativeDialogueComposition.print _ _ Hboundary). }
   assert(Hpendingvalue:meta_value pending 15=digit f+1).
   { unfold pending,CommandLoopExecution.pending_state. apply meta_store_same. cbn [memory withInput]. lia. }
   assert(Hpendingerror:meta_value pending 8=0).
   { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact(NativeDialogueComposition.error _ _ Hboundary). }
   assert(Hpendingstop:meta_value pending 9=0).
   { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact(NativeDialogueComposition.running _ _ Hboundary). }
   assert(Hpendingstate:NativeState.represents pending logical).
   { unfold pending,CommandLoopExecution.pending_state. apply NativeSession.state_meta;try lia. apply NativeSession.state_input. exact(NativeDialogueComposition.state _ _ Hboundary). }
   assert(Hcommandstep:exists after reply next,
     execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(pending,observations)=
       Some(tt,(after,observations++[{|flushedOutput:=stdout pending++Protocol.reply_bytes reply;unreadInput:=wire frames++ending|}])) /\
     Protocol.step logical (request f) reply next /\ NativeState.represents after next /\
     NativeSimpleCommands.boundary pending logical after reply next (wire frames++ending)).
   { destruct(operation f) eqn:Hop.
     - assert(Hcase:opcode f=1%nat \/ opcode f=2%nat) by (unfold opcode;rewrite Hop;tauto).
       destruct(NativeWhitespaceAtoms.generated_protocol (opcode f) (digit f) [] pending logical (fun _=>false)(fun _=>0) (left_arg f)(right_arg f)
          (first_sep f)(first_prefix f)(second_sep f)(second_prefix f)(last_sep f)(wire frames++ending) observations
          Hcase ltac:(pose proof(decimal_opcode f) as H;unfold digits in H;rewrite Hop in H;exact H) Hpendingmeta Hpendingtoken Hpendingprint Hpendingvalue Hpendingerror ltac:(lia) Ha Hb Hpendingstate
          Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 ltac:(unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes,digits;cbn [stdin withInput store_meta];rewrite Hop;repeat first [progress cbn [app]|rewrite <-app_assoc];reflexivity))
         as(after & index & fs & Hcommand & Hstep & Hnextstate & Hnext).
       exists after,(Protocol.OK index),(NativeSimpleCommands.Atoms.logical_after logical fs). split;[exact Hcommand|]. split;[unfold request;rewrite Hop;exact Hstep|]. split;assumption.
     - assert(Hcase:opcode f=1%nat \/ opcode f=2%nat) by (unfold opcode;rewrite Hop;tauto).
       destruct(NativeWhitespaceAtoms.generated_protocol (opcode f) (digit f) [] pending logical (fun _=>false)(fun _=>0) (left_arg f)(right_arg f)
          (first_sep f)(first_prefix f)(second_sep f)(second_prefix f)(last_sep f)(wire frames++ending) observations
          Hcase ltac:(pose proof(decimal_opcode f) as H;unfold digits in H;rewrite Hop in H;exact H) Hpendingmeta Hpendingtoken Hpendingprint Hpendingvalue Hpendingerror ltac:(lia) Ha Hb Hpendingstate
          Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 ltac:(unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes,digits;cbn [stdin withInput store_meta];rewrite Hop;repeat first [progress cbn [app]|rewrite <-app_assoc];reflexivity))
         as(after & index & fs & Hcommand & Hstep & Hnextstate & Hnext).
       exists after,(Protocol.OK index),(NativeSimpleCommands.Atoms.logical_after logical fs). split;[exact Hcommand|]. split;[unfold request;rewrite Hop;exact Hstep|]. split;assumption.
     - assert(Henc:decimalBytes 3%nat = digit f::[]) by (pose proof(decimal_opcode f) as H;unfold opcode,digits in H;now rewrite Hop in H).
       destruct(NativeWhitespaceImp.generated_total_protocol (digit f) [] pending logical (fun _=>false)(fun _=>0) (left_arg f)(right_arg f)
          (first_sep f)(first_prefix f)(second_sep f)(second_prefix f)(last_sep f)(wire frames++ending) observations
          Henc Hpendingmeta Hpendingtoken Hpendingprint Hpendingvalue Hpendingerror ltac:(lia) Ha Hb Hpendingstate
          Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 ltac:(unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes,digits;cbn [stdin withInput store_meta];rewrite Hop;repeat first [progress cbn [app]|rewrite <-app_assoc];reflexivity))
         as(after & reply & next & Hcommand & Hstep & Hnextstate & Hnext).
       exists after,reply,next. unfold request,opcode. rewrite Hop. split;[exact Hcommand|]. split;[exact Hstep|]. split;assumption.
     - assert(Hdigit4:digit f=52) by (unfold digit;now rewrite Hop).
       assert(Hpending4:meta_value pending 15=53) by (rewrite Hpendingvalue,Hdigit4;reflexivity).
       destruct(NativeWhitespaceAll.generated_total_protocol pending logical (fun _=>false)(fun _=>0) (left_arg f)
          (first_sep f)(first_prefix f)(last_sep f)(wire frames++ending) observations
          Hpendingmeta Hpendingtoken Hpendingprint Hpending4 Hpendingerror ltac:(lia) Ha Hpendingstate
          Hsep1 Hsep3 Hprefix1 ltac:(unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes,digits;cbn [stdin withInput store_meta];rewrite Hop;repeat first [progress cbn [app]|rewrite <-app_assoc];reflexivity))
         as(after & reply & next & Hcommand & Hstep & Hnextstate & Hnext).
       exists after,reply,next. unfold request,opcode. rewrite Hop. split;[exact Hcommand|]. split;[exact Hstep|]. split;assumption.
     - assert(Hdigit13:digit f=49) by (unfold digit;now rewrite Hop).
       assert(Hpending13:meta_value pending 15=50) by (rewrite Hpendingvalue,Hdigit13;reflexivity).
       destruct(NativeWhitespaceGeneralizeBoundary.generated_generalize pending logical (fun _=>false)(fun _=>0) (left_arg f)
          (first_sep f)(first_prefix f)(last_sep f)(wire frames++ending) observations
          Hpendingmeta Hpendingtoken Hpendingprint Hpending13 Hpendingerror ltac:(lia) ltac:(unfold maximum in *;lia) Ha HhistoryValid Hpendingstate
          Hsep1 Hsep3 Hprefix1 ltac:(unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes,digits;cbn [stdin withInput store_meta];rewrite Hop;repeat first [progress cbn [app]|rewrite <-app_assoc];reflexivity))
         as(after & reply & next & Hcommand & Hstep & Hnextstate & HvalidNext & HsafeNext & Hcontrol).
       destruct Hcontrol as (Hio & Hformulagrowth & HclassesSame & Hhistorygrowth).
       exists after,reply,next. unfold request,opcode. rewrite Hop. split;[exact Hcommand|]. split;[exact Hstep|]. split;[exact Hnextstate|].
       unfold NativeCommandBoundary.io in Hio. unfold NativeSimpleCommands.boundary. destruct Hio as (H1 & H2 & H3 & H4 & H5 & H6). repeat split;try assumption;lia.
     - assert(Hdigit12:digit f=49) by (unfold digit;now rewrite Hop).
       assert(Hpending12:meta_value pending 15=50) by (rewrite Hpendingvalue,Hdigit12;reflexivity).
       destruct(NativeWhitespaceMPBoundary.generated_MP pending logical (fun _=>false)(fun _=>0) (left_arg f)(right_arg f)
          (first_sep f)(first_prefix f)(second_sep f)(second_prefix f)(last_sep f)(wire frames++ending) observations
          Hpendingmeta Hpendingtoken Hpendingprint Hpending12 Hpendingerror Ha Hb ltac:(unfold maximum in *;lia) HhistoryValid Hpendingstate
          Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 ltac:(unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes,digits;cbn [stdin withInput store_meta];rewrite Hop;repeat first [progress cbn [app]|rewrite <-app_assoc];reflexivity))
         as(after & reply & next & Hcommand & Hstep & Hnextstate & HvalidNext & HsafeNext & Hcontrol & Hsameformulas).
       destruct Hcontrol as (Hio & Hformulagrowth & HclassesSame & Hhistorygrowth).
       exists after,reply,next. unfold request,opcode. rewrite Hop. split;[exact Hcommand|]. split;[exact Hstep|]. split;[exact Hnextstate|].
       unfold NativeCommandBoundary.io in Hio. unfold NativeSimpleCommands.boundary. destruct Hio as (H1 & H2 & H3 & H4 & H5 & H6). repeat split;try assumption;lia.
     - assert(Henc:decimalBytes 11%nat=digit f::digits f) by (pose proof(decimal_opcode f) as H;unfold opcode in H;now rewrite Hop in H).
       destruct(NativeWhitespaceReflFlow.generated pending logical (fun _=>false)(fun _=>0) (digit f)(digits f) (left_arg f)(right_arg f)(third_arg f)
         (first_sep f)(first_prefix f)(second_sep f)(second_prefix f)(third_sep f)(third_prefix f)(fourth_sep f)(fourth_prefix f)(last_sep f)(wire frames++ending) observations
         Henc Hpendingmeta Hpendingtoken Hpendingprint Hpendingvalue Hpendingerror ltac:(cbn [length] in Hbound;repeat rewrite Nat2Z.inj_add in *;cbn [Nat2Z.inj_succ] in *;lia) ltac:(unfold maximum in *;lia) Ha Hb Hc Hpendingstate
         Hsep1 Hsep2 HsepThird HsepFourth Hsep3 Hprefix1 Hprefix2 HprefixThird HprefixFourth
         ltac:(unfold pending,CommandLoopExecution.pending_state,rest,argument_bytes,digits;cbn [stdin withInput store_meta];rewrite Hop;repeat first [progress cbn [app]|rewrite <-app_assoc];reflexivity))
        as(after & index & fs & Hcommand & Hstep & Hnextstate & Hcontrol).
       destruct Hcontrol as (Hio & Hformulagrowth & HclassesSame & Hhistorygrowth).
       exists after,(Protocol.OK(length(Protocol.history logical))),(NativeWhitespaceReflFlow.logical_after logical fs index).
       unfold request,opcode. rewrite Hop. split;[exact Hcommand|]. split;[exact Hstep|]. split;[exact Hnextstate|].
       unfold NativeCommandBoundary.io in Hio. unfold NativeSimpleCommands.boundary. destruct Hio as (H1 & H2 & H3 & H4 & H5 & H6). repeat split;try assumption. change (length fs<=length(Protocol.formulas logical)+1)%nat in Hformulagrowth. change (length fs<=S(length(Protocol.formulas logical)))%nat. lia. }
   destruct Hcommandstep as (after & reply & next & Hcommand & Hstep & Hnextstate & Hnext).
   destruct Hnext as (Hnextin & Hnextout & Hnexttoken & Hnextprint & Hnexterror & Hnextstop & Hgrowth).
   assert(HnextBoundary:NativeDialogueComposition.boundary after next).
   { constructor;try assumption. now rewrite Hnextstop. }
   assert(Hactual:exists ch input_tail actual,
      0<=ch<256 /\ stdin native=ch::input_tail /\
      execObserved(funcdef_0__command (fun _=>false)(fun _=>0))
        (CommandLoopExecution.pending_state(withInput native input_tail)ch,observations)=
        Some(tt,(actual,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire frames++ending|}])) /\
      NativeDialogueComposition.boundary actual next /\ stdin actual=wire frames++ending /\ stdout actual=stdout native++Protocol.reply_bytes reply).
   { destruct (before_opcode f) as [|ch prefix] eqn:Hbefore.
     - cbn [app] in Hinput. exists (digit f),(digits f++rest),after.
       split;[exact Hdigit|]. split;[exact Hinput|]. split;[exact Hcommand|].
       split;[exact HnextBoundary|]. split;assumption.
     - inversion Hleading as [|? ? Hsep Hprefix];subst.
       assert(Hch:0<=ch<256) by (unfold TokenByteExecution.separator in Hsep;lia).
       set(argtail:=tl(argument_bytes f)++wire frames++ending).
       assert(Hrest:rest=first_sep f::argtail).
       { unfold rest,argtail,argument_bytes. destruct(operation f);repeat first [progress cbn [app tl] | rewrite <-app_assoc];reflexivity. }
       assert(Hcanonical:execObserved(funcdef_0__command (fun _=>false)(fun _=>0))
          (NativeCommandWhitespace.canonical native (digit f) (digits f) (first_sep f) argtail,observations)=
          Some(tt,(after,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire frames++ending|}]))).
       { unfold NativeCommandWhitespace.canonical,pending,CommandLoopExecution.pending_state in *. cbn [app] in *. now rewrite <-Hrest. }
       destruct(NativeCommandWhitespace.generated native (fun _=>false)(fun _=>0) ch prefix (digit f) (digits f) (first_sep f) argtail observations after _
        ltac:(lia) (NativeDialogueComposition.token _ _ Hboundary) (NativeDialogueComposition.error _ _ Hboundary) Hch Hsep Hprefix
        ltac:(unfold digits;destruct(operation f);cbn;lia) ltac:(unfold digit,digits;destruct(operation f);repeat constructor;lia)
        ltac:(unfold ReadNatExecution.number_from,digit,digits,maximum;destruct(operation f);cbn;lia) Hsep1 Hcanonical)
        as(actual & Hrun & Hsame).
       exists ch,(prefix++digit f::digits f++rest),actual. split;[exact Hch|]. split.
       + exact Hinput.
       + split.
         * unfold NativeCommandWhitespace.spaced in Hrun. cbn [app] in Hrun. rewrite <-Hrest in Hrun. exact Hrun.
         * split;[exact(NativePointwiseState.boundary _ _ _ Hsame HnextBoundary)|].
           destruct Hsame as (Hsamein & Hsameout & Hmemory). split;[rewrite <-Hsamein;exact Hnextin|rewrite <-Hsameout;exact Hnextout]. }
   destruct Hactual as (first & input_tail & actual & Hfirst & HactualInput & HactualCommand & HactualBoundary & Hactualin & Hactualout).
   assert(Hnextbound:Z.of_nat(length(Protocol.formulas next)+length frames)<=9223372036854775807).
   { cbn [length] in Hbound. repeat rewrite Nat2Z.inj_add in *. cbn [Nat2Z.inj_succ] in *. lia. }
   destruct(IH actual next
     (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes(reply);unreadInput:=wire frames++ending|}])
     Htail Hending HactualBoundary (LogicalHistory.step_valid _ _ _ _ Hstep HhistoryValid) ltac:(pose proof(history_growth _ _ _ _ Hstep);cbn [length] in HhistoryBound;repeat rewrite Nat2Z.inj_add in *;cbn [Nat2Z.inj_succ] in *;lia) Hnextbound Hactualin) as(final & replies & target & Hlength & Hrun & Hdialogue & Hstate & Herror & Hout & Hfinalin & Hstop).
   exists final,(reply::replies),target. split;[cbn [length];congruence|]. split.
   + cbn [schedule]. eapply DialogueExecution.next with (ch:=first) (tail:=input_tail) (after:=actual).
     * exact Hfirst.
     * exact HactualInput.
     * lia.
     * exact HactualCommand.
     * pose proof(NativeSession.represented_meta actual _ (NativeDialogueComposition.state _ _ HactualBoundary)). lia.
     * exact(NativeDialogueComposition.running _ _ HactualBoundary).
     * rewrite Hactualout,<-app_assoc in Hrun. exact Hrun.
   + split;[cbn [map];eapply Protocol.dialogue_step;[unfold request,opcode;destruct(operation f);cbn;lia|exact Hstep|exact Hdialogue]|].
     split;[exact Hstate|]. split;[exact Herror|]. split;[|now split].
     cbn [NativeSession.output]. now rewrite Hactualout in Hout.
Qed.
Theorem generated_main key0 key1 frames quit_prefix suffix bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames -> Forall TokenByteExecution.separator quit_prefix ->
 Z.of_nat(length(Protocol.history Protocol.initial)+length frames)<maximum ->
 Z.of_nat(length(Protocol.formulas Protocol.initial)+length frames)<=9223372036854775807 ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map request frames++[NativeSession.quit]) (replies++[Protocol.BYE]) logical [] /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire frames++quit_prefix++[48;10]++suffix)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames++quit_prefix++[48;10]++suffix|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++quit_prefix++[48;10]++suffix|}]++schedule frames replies quit_prefix suffix Protocol.handshake_output)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix /\ meta_value final 9=1.
Proof.
 intros Hkey0 Hkey1 Hvalid Hending HhistoryBound Hbound.
 destruct(NativeStartupCompact.main_to_commands key0 key1(wire frames++quit_prefix++[48;10]++suffix)bs ns Hkey0 Hkey1)
  as(ready & Hstate & Htop & Hmeta32 & Hsip1 & Hzero & Herror & Hmeta & Htoken & Hprint & Hstop & Hhistory & Hinput & Houtput & Hmain & Hempty).
 assert(Hboundary:NativeDialogueComposition.boundary ready Protocol.initial) by (constructor;assumption).
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames++quit_prefix++[48;10]++suffix|};
 {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++quit_prefix++[48;10]++suffix|}]).
 destruct(generated_finite frames quit_prefix suffix ready Protocol.initial observations Hvalid Hending Hboundary LogicalHistory.initial_valid HhistoryBound Hbound Hinput)
 as(final & replies & logical & Hlength & Hrun & Hdialogue & Hfinal & Hclear & Hout & Hin & Hfinalstop).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 rewrite Houtput in Hcommands,Hout.
 exists replies,final,logical. split;[exact Hlength|]. split;[exact Hdialogue|].
 split;[exact(Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|]. split;[exact Hfinal|]. split;[exact Hclear|].
 split;[etransitivity;[exact Hmain|exact Hcommands]|]. repeat first [assumption|split].
Qed.
Theorem generated_main_flexible_seeds key0 key1 prefix0 prefix1 sep0 sep1 frames quit_prefix suffix bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 ->
 Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 ->
 Forall valid frames -> Forall TokenByteExecution.separator quit_prefix ->
 Z.of_nat(length(Protocol.history Protocol.initial)+length frames)<maximum ->
 Z.of_nat(length(Protocol.formulas Protocol.initial)+length frames)<=9223372036854775807 ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map request frames++[NativeSession.quit]) (replies++[Protocol.BYE]) logical [] /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep0 sep1(wire frames++quit_prefix++[48;10]++suffix),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++sep0::(prefix1++decimalBytes key1++sep1::(wire frames++quit_prefix++[48;10]++suffix))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++quit_prefix++[48;10]++suffix|}]++schedule frames replies quit_prefix suffix Protocol.handshake_output)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix /\ meta_value final 9=1.
Proof.
 intros Hkey0 Hkey1 Hsep0 Hsep1 Hprefix0 Hprefix1 Hvalid Hending HhistoryBound Hbound.
 destruct(generated_main key0 key1 frames quit_prefix suffix bs ns Hkey0 Hkey1 Hvalid Hending HhistoryBound Hbound)
 as(replies & final & logical & Hlength & Hdialogue & Hsafe & Hstate & Herror & Hrun & Hout & Hin & Hfinalstop).
 exists replies,final,logical. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
End NativeWhitespaceReflQuitDialogue.
