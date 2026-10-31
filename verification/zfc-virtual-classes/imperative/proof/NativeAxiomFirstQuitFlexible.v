From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash HashTable TokenByte NativeState NativeSession NativeAxiomTotal NativeWhitespaceAxiom NativeCommandBoundary FormulaTopology CommandLoop Dialogue SeedBootstrap NativeStartupCompact NativeWhitespaceDialogue NativeSeedInputTransport NativeAxiomFirstMixedQuit CommandQuit NativeWhitespaceMPQuitDialogue LogicalHistory NativeDialogueComposition.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeAxiomFirstQuitFlexible.
Import IndexExecution SipHashExecution NativeAxiomFirstMixedQuit.
Theorem generated_main key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4 frames quit_prefix suffix bs ns :
 TokenByteExecution.separator seed_sep0 -> TokenByteExecution.separator seed_sep1 ->
 Forall TokenByteExecution.separator seed_prefix0 -> Forall TokenByteExecution.separator seed_prefix1 ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum ->
 Z.of_nat tag<=maximum -> Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum ->
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 -> TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
 Forall TokenByteExecution.separator sp1 -> Forall TokenByteExecution.separator sp2 -> Forall TokenByteExecution.separator sp3 -> Forall TokenByteExecution.separator sp4 ->
 NativeAxiomTotal.resources Protocol.initial tag a b c ->
 Forall NativeWhitespaceMPQuitDialogue.valid frames -> Forall TokenByteExecution.separator quit_prefix ->
 (forall reply logical, Protocol.step Protocol.initial (Protocol.Req 11 [tag;a;b;c] []) reply logical ->
  Z.of_nat(length(Protocol.history logical)+length frames)<maximum /\
  Z.of_nat(length(Protocol.formulas logical)+length frames)<=9223372036854775807) ->
 exists final reply logical replies target,
 Protocol.step Protocol.initial (Protocol.Req 11 [tag;a;b;c] []) reply logical /\
 length replies=length frames /\ Protocol.dialogue logical (map NativeWhitespaceMPQuitDialogue.request frames++[NativeSession.quit]) (replies++[Protocol.BYE]) target [] /\ Guarantees.safe target /\ NativeState.represents final target /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1(wire tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4++NativeWhitespaceMPQuitDialogue.wire frames++quit_prefix++[48;10]++suffix),[])=
 Some(tt,(final,[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=seed_prefix0++decimalBytes key0++seed_sep0::(seed_prefix1++decimalBytes key1++seed_sep1::(wire tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4++NativeWhitespaceMPQuitDialogue.wire frames++quit_prefix++[48;10]++suffix))|};
 {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4++NativeWhitespaceMPQuitDialogue.wire frames++quit_prefix++[48;10]++suffix|};
 {|flushedOutput:=Protocol.handshake_output++Protocol.reply_bytes reply;unreadInput:=NativeWhitespaceMPQuitDialogue.wire frames++quit_prefix++[48;10]++suffix|}]++
 NativeWhitespaceMPQuitDialogue.schedule frames replies quit_prefix suffix (Protocol.handshake_output++Protocol.reply_bytes reply))) /\
 stdout final=NativeSession.output (Protocol.handshake_output++Protocol.reply_bytes reply) replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix /\ meta_value final 9=1.
Proof.
 intros Hs0 Hs1 Hp0 Hp1 Hk0 Hk1 Htag Ha Hb Hc Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsp1 Hsp2 Hsp3 Hsp4 Hresources Hvalid Hending Hbounds.
 destruct(NativeAxiomFirstMixedQuit.generated_main key0 key1 tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4 frames quit_prefix suffix bs ns
  Hk0 Hk1 Htag Ha Hb Hc Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsp1 Hsp2 Hsp3 Hsp4 Hresources Hvalid Hending Hbounds)
 as(final & reply & logical & replies & target & Hstep & Hlength & Hdialogue & Hsafe & Hstate & Herror & Hrun & Hout & Hin & Hstop).
 exists final,reply,logical,replies,target. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
End NativeAxiomFirstQuitFlexible.
