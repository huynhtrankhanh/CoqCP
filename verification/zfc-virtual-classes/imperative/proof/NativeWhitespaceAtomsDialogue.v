From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeSimpleCommands NativeWhitespaceAtoms NativeDialogueComposition NativeWhitespaceEOFDialogue CommandLoop Dialogue SeedBootstrap NativeStartupCompact NativeWhitespaceDialogue NativeSeedInputTransport.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceAtomsDialogue.
Import IndexExecution SipHashExecution.
Record frame := Frame { equality : bool; left_arg : nat; right_arg : nat; first_sep : Z; first_prefix : list Z; second_sep : Z; second_prefix : list Z; last_sep : Z }.
Definition opcode f := if equality f then 1%nat else 2%nat.
Definition digit f := if equality f then 49 else 50.
Definition request f := Protocol.Req (opcode f) [left_arg f;right_arg f] [].
Definition valid f := Z.of_nat(left_arg f)<=maximum /\ Z.of_nat(right_arg f)<=maximum /\
 TokenByteExecution.separator(first_sep f) /\ TokenByteExecution.separator(second_sep f) /\ TokenByteExecution.separator(last_sep f) /\
 Forall TokenByteExecution.separator(first_prefix f) /\ Forall TokenByteExecution.separator(second_prefix f).
Definition frame_bytes f := digit f :: first_sep f :: first_prefix f ++ decimalBytes(left_arg f) ++ second_sep f :: second_prefix f ++ decimalBytes(right_arg f) ++ [last_sep f].
Fixpoint wire frames := match frames with []=>[] | f::tail=>frame_bytes f++wire tail end.
Fixpoint schedule frames replies output ending := match frames,replies with
 | _::tail,reply::rest=>let next:=output++Protocol.reply_bytes reply in {|flushedOutput:=next;unreadInput:=wire tail++ending|}::schedule tail rest next ending
 | _,_=>[] end.
Lemma decimal_opcode f : decimalBytes(opcode f)=[digit f].
Proof. destruct f as [b a c x xs y ys z]. destruct b;vm_compute;reflexivity. Qed.
Theorem generated_finite frames ending : forall native logical observations,
 Forall valid frames -> Forall TokenByteExecution.separator ending ->
 NativeDialogueComposition.boundary native logical ->
 Z.of_nat(length(Protocol.formulas logical)+length frames)<=9223372036854775807 ->
 stdin native=wire frames++ending ->
 exists final replies target,
 length replies=length frames /\ DialogueExecution.run native observations final (observations++schedule frames replies(stdout native)ending) /\
 Protocol.dialogue logical (map request frames) replies target [] /\ NativeState.represents final target /\
 meta_value final 8=0 /\ stdout final=stdout native++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 induction frames as [|f frames IH]; intros native logical observations Hvalid Hending Hboundary Hbound Hin.
 - destruct(NativeWhitespaceEOFDialogue.generated native logical ending observations Hboundary Hending Hin) as(final & Hrun & Hstate & Hinput & Houtput & Herror).
   exists final,[],logical. split;[reflexivity|]. split;[cbn [schedule];now rewrite app_nil_r|].
   split;[apply Protocol.dialogue_eof|]. split;[exact Hstate|]. split;[exact Herror|]. split;[now rewrite app_nil_r|exact Hinput].
 - inversion Hvalid as [|? ? Hf Htail];subst. destruct Hf as (Ha & Hb & Hsep1 & Hsep2 & Hsep3 & Hprefix1 & Hprefix2).
   pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary)) as Hmeta.
   assert(Hdigit:0<=digit f<256) by (unfold digit;destruct (equality f);lia).
   set(rest:=first_sep f :: first_prefix f ++ decimalBytes(left_arg f) ++ second_sep f :: second_prefix f ++ decimalBytes(right_arg f) ++ last_sep f :: (wire frames++ending)).
   assert(Hinput:stdin native=digit f::rest).
   { unfold rest. cbn [wire] in Hin. unfold frame_bytes in Hin. repeat first [progress cbn [app] in Hin | rewrite <-app_assoc in Hin]. exact Hin. }
   set(pending:=CommandLoopExecution.pending_state(withInput native rest)(digit f)).
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
   assert(Hcase:opcode f=1%nat \/ opcode f=2%nat) by (unfold opcode;destruct(equality f);tauto).
   destruct(NativeWhitespaceAtoms.generated_protocol (opcode f) (digit f) [] pending logical (fun _=>false)(fun _=>0) (left_arg f)(right_arg f)
      (first_sep f)(first_prefix f)(second_sep f)(second_prefix f)(last_sep f)(wire frames++ending) observations
      Hcase (decimal_opcode f) Hpendingmeta Hpendingtoken Hpendingprint Hpendingvalue Hpendingerror ltac:(lia) Ha Hb Hpendingstate
      Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 eq_refl)
     as(after & index & fs & Hcommand & Hstep & Hnextstate & Hnext).
   destruct Hnext as (Hnextin & Hnextout & Hnexttoken & Hnextprint & Hnexterror & Hnextstop & Hgrowth).
   assert(HnextBoundary:NativeDialogueComposition.boundary after (NativeSimpleCommands.Atoms.logical_after logical fs)).
   { constructor;try assumption. now rewrite Hnextstop. }
   assert(Hnextbound:Z.of_nat(length(Protocol.formulas(NativeSimpleCommands.Atoms.logical_after logical fs))+length frames)<=9223372036854775807).
   { cbn [length] in Hbound. repeat rewrite Nat2Z.inj_add in *. cbn [Nat2Z.inj_succ] in *. lia. }
   destruct(IH after (NativeSimpleCommands.Atoms.logical_after logical fs)
     (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes(Protocol.OK index);unreadInput:=wire frames++ending|}])
     Htail Hending HnextBoundary Hnextbound Hnextin) as(final & replies & target & Hlength & Hrun & Hdialogue & Hstate & Herror & Hout & Hfinalin).
   exists final,(Protocol.OK index::replies),target. split;[cbn [length];congruence|]. split.
   + cbn [schedule]. eapply DialogueExecution.next with (ch:=digit f) (tail:=rest) (after:=after).
     * exact Hdigit.
     * exact Hinput.
     * lia.
     * exact Hcommand.
     * pose proof(NativeSession.represented_meta after _ Hnextstate). lia.
     * now rewrite Hnextstop.
     * rewrite Hnextout,<-app_assoc in Hrun. exact Hrun.
   + split;[cbn [map];eapply Protocol.dialogue_step;[unfold request,opcode;destruct(equality f);cbn;lia|exact Hstep|exact Hdialogue]|].
     split;[exact Hstate|]. split;[exact Herror|]. split;[|exact Hfinalin].
     cbn [map concat]. rewrite Hout,Hnextout. now rewrite app_assoc.
Qed.
Theorem generated_main key0 key1 frames ending bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames -> Forall TokenByteExecution.separator ending ->
 Z.of_nat(length(Protocol.formulas Protocol.initial)+length frames)<=9223372036854775807 ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map request frames) replies logical [] /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire frames++ending)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames++ending|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++ending|}]++schedule frames replies Protocol.handshake_output ending)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 intros Hkey0 Hkey1 Hvalid Hending Hbound.
 destruct(NativeStartupCompact.main_to_commands key0 key1(wire frames++ending)bs ns Hkey0 Hkey1)
  as(ready & Hstate & Htop & Hmeta32 & Hsip1 & Hzero & Herror & Hmeta & Htoken & Hprint & Hstop & Hhistory & Hinput & Houtput & Hmain & Hempty).
 assert(Hboundary:NativeDialogueComposition.boundary ready Protocol.initial) by (constructor;assumption).
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames++ending|};
 {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++ending|}]).
 destruct(generated_finite frames ending ready Protocol.initial observations Hvalid Hending Hboundary Hbound Hinput)
 as(final & replies & logical & Hlength & Hrun & Hdialogue & Hfinal & Hclear & Hout & Hin).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 rewrite Houtput in Hcommands,Hout.
 exists replies,final,logical. split;[exact Hlength|]. split;[exact Hdialogue|].
 split;[exact(Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|]. split;[exact Hfinal|]. split;[exact Hclear|].
 split;[etransitivity;[exact Hmain|exact Hcommands]|]. split;assumption.
Qed.
Theorem generated_main_flexible_seeds key0 key1 prefix0 prefix1 sep0 sep1 frames ending bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 ->
 Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 ->
 Forall valid frames -> Forall TokenByteExecution.separator ending ->
 Z.of_nat(length(Protocol.formulas Protocol.initial)+length frames)<=9223372036854775807 ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map request frames) replies logical [] /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep0 sep1(wire frames++ending),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++sep0::(prefix1++decimalBytes key1++sep1::(wire frames++ending))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames++ending|}]++schedule frames replies Protocol.handshake_output ending)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 intros Hkey0 Hkey1 Hsep0 Hsep1 Hprefix0 Hprefix1 Hvalid Hending Hbound.
 destruct(generated_main key0 key1 frames ending bs ns Hkey0 Hkey1 Hvalid Hending Hbound)
 as(replies & final & logical & Hlength & Hdialogue & Hsafe & Hstate & Herror & Hrun & Hout & Hin).
 exists replies,final,logical. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
End NativeWhitespaceAtomsDialogue.
