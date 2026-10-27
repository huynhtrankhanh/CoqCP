From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeStartup NativeSimpleCommands
 Representation ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation ArenaFrame
 CommandInput CommandLoop CommandQuit QuitInput QuitLoop Dialogue SeedBootstrap SeedInput Startup
 ReadNat ReadToken TokenByte.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeSession.
Import IndexExecution SipHashExecution.
Definition quit := Protocol.Req 0 [] [].
Definition valid_request request :=
 (((Protocol.opcode request=1%nat \/ Protocol.opcode request=2%nat \/ Protocol.opcode request=3%nat) /\
   exists a b,Protocol.arguments request=[a;b]) \/
  (Protocol.opcode request=4%nat /\ exists value,Protocol.arguments request=[value])) /\
 Protocol.object_name request=[] /\
 Forall (fun value=>Z.of_nat value<=maximum) (Protocol.arguments request).
Definition input requests tail := Protocol.wire requests++[48;10]++tail.
Fixpoint output initial replies := match replies with
 | []=>initial | reply::rest=>output (initial++Protocol.reply_bytes reply) rest end.
Fixpoint schedule initial requests replies tail := match requests,replies with
 | [],[]=>[{|flushedOutput:=initial++CommandQuitExecution.bye_bytes;unreadInput:=tail|}]
 | request::rest,reply::replies=>
   {|flushedOutput:=initial++Protocol.reply_bytes reply;unreadInput:=input rest tail|}::
   schedule (initial++Protocol.reply_bytes reply) rest replies tail
 | _,_=>[] end.

Lemma state_input native logical bytes : NativeState.represents native logical ->
 NativeState.represents (withInput native bytes) logical.
Proof.
 intros [Harena Hclasses Hhistory Hnames Hschemas]. constructor;try assumption.
 exact (ArenaFrame.storage_arena native _ _ (ArenaFrame.storage_input native bytes) Harena).
Qed.
Lemma state_meta native logical slot value :
 slot<>1%nat -> slot<>2%nat -> slot<>3%nat -> slot<>4%nat -> slot<>5%nat ->
 slot<>16%nat -> slot<>20%nat -> slot<>26%nat -> slot<>27%nat ->
 NativeState.represents native logical -> NativeState.represents (store_meta native slot value) logical.
Proof.
 intros H1 H2 H3 H4 H5 H16 H20 H26 H27 [Harena Hclasses Hhistory Hnames Hschemas]. constructor.
 - exact (ArenaFrame.storage_arena native _ _ (ArenaFrame.storage_meta native slot value H1 H20 H26 H27) Harena).
 - unfold ClassStorage.represents. rewrite meta_store_other by congruence. rewrite store_meta_other by discriminate. exact Hclasses.
 - unfold HistoryRefinement.represents. rewrite meta_store_other by congruence. rewrite store_meta_other by discriminate. exact Hhistory.
 - unfold NameRepresentation.represents. rewrite !meta_store_other by congruence. rewrite !store_meta_other by discriminate. exact Hnames.
 - eapply SchemaRepresentation.transport;[exact Hschemas| | |reflexivity|reflexivity|reflexivity].
   + apply meta_store_other;congruence.
   + apply store_meta_other;discriminate.
Qed.
Lemma state_parsed native ch chars tail logical : NativeState.represents native logical ->
 NativeState.represents (CommandInput.parsed native ch chars tail) logical.
Proof.
 intros [Harena Hclasses Hhistory Hnames Hschemas]. constructor.
 - exact (ArenaFrame.storage_arena _ _ _ (CommandInput.parsed_storage native ch chars tail) Harena).
 - unfold ClassStorage.represents. rewrite CommandInput.parsed_meta_other by lia.
   rewrite CommandInput.parsed_other by discriminate. exact Hclasses.
 - unfold HistoryRefinement.represents. rewrite CommandInput.parsed_meta_other by lia.
   rewrite CommandInput.parsed_other by discriminate. exact Hhistory.
 - unfold NameRepresentation.represents. rewrite !CommandInput.parsed_meta_other by lia.
   rewrite !CommandInput.parsed_other by discriminate. exact Hnames.
 - eapply SchemaRepresentation.transport;[exact Hschemas| | |reflexivity|reflexivity|reflexivity].
   + apply CommandInput.parsed_meta_other;lia.
   + apply CommandInput.parsed_other;discriminate.
Qed.
Lemma quit_state native logical tail : NativeState.represents native logical ->
 NativeState.represents (QuitLoopExecution.loop_result native tail) logical.
Proof.
 intro Hstate. unfold QuitLoopExecution.loop_result,QuitLoopExecution.callback_result,CommandQuitExecution.quit_state.
 apply NativeState.output. apply state_meta;try lia.
 change (NativeState.represents (CommandInput.parsed (store_meta (withInput native (10%Z::tail)) 15 49) 48 [] tail) logical).
 apply state_parsed. apply state_meta;try lia. now apply state_input.
Qed.
Lemma represented_meta native logical : NativeState.represents native logical ->
 (28<length (memory native arraydef_0__meta))%nat.
Proof. intro Hstate. exact (proj1 (proj1 (proj1 (NativeState.formula_representation _ _ Hstate)))). Qed.

Lemma input_cons request requests tail :
 input (request::requests) tail=Protocol.request_bytes request++input requests tail.
Proof. unfold input,Protocol.wire. cbn [map concat]. now rewrite <-app_assoc. Qed.
Lemma request_encoding request : valid_request request ->
 exists ch,decimalBytes (Protocol.opcode request)=[ch] /\ 0<=ch<256 /\ Protocol.opcode request<>0%nat.
Proof.
 intros [Hshape Hrest]. destruct Hshape as [[Htag Hargs]|[Htag Hargs]].
 - destruct Htag as [Htag|[Htag|Htag]];rewrite Htag;[exists 49|exists 50|exists 51];repeat split;try reflexivity;lia.
 - rewrite Htag. exists 52. repeat split;try reflexivity;lia.
Qed.

Lemma generated_quit native logical tail observations :
 NativeState.represents native logical ->
 (1024<=length (memory native arraydef_0__token))%nat -> meta_value native 8=0 ->
 stdin native=input [] tail ->
 DialogueExecution.run native observations (QuitLoopExecution.loop_result native tail)
  (observations++schedule (stdout native) [] [] tail) /\
 NativeState.represents (QuitLoopExecution.loop_result native tail) logical /\
 stdin (QuitLoopExecution.loop_result native tail)=tail /\
 stdout (QuitLoopExecution.loop_result native tail)=stdout native++CommandQuitExecution.bye_bytes /\
 meta_value (QuitLoopExecution.loop_result native tail) 9=1 /\ meta_value (QuitLoopExecution.loop_result native tail) 8=0.
Proof.
 intros Hstate Htoken Herror Hinput. pose proof (represented_meta native logical Hstate) as Hmeta.
 assert (HpendingMeta:(17<length (memory (CommandLoopExecution.pending_state (withInput native (10%Z::tail)) 48%Z) arraydef_0__meta))%nat).
 { unfold CommandLoopExecution.pending_state. rewrite store_meta_length. change (17<length (memory native arraydef_0__meta))%nat;lia. }
 assert (HpendingToken:(1024<=length (memory (CommandLoopExecution.pending_state (withInput native (10%Z::tail)) 48%Z) arraydef_0__token))%nat).
 { unfold CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
 assert (Hpending:meta_value (CommandLoopExecution.pending_state (withInput native (10%Z::tail)) 48%Z) 15=49).
 { unfold CommandLoopExecution.pending_state. apply meta_store_same;change (15<length (memory native arraydef_0__meta))%nat;lia. }
 assert (HpendingError:meta_value (CommandLoopExecution.pending_state (withInput native (10%Z::tail)) 48%Z) 8=0).
 { unfold CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
 pose proof (QuitInputExecution.generated_quit_pending
  (CommandLoopExecution.pending_state (withInput native (10%Z::tail)) 48%Z) (fun _=>false) (fun _=>0) 10 tail observations
  HpendingMeta HpendingToken Hpending HpendingError ltac:(unfold TokenByteExecution.separator;tauto) eq_refl) as Hrun.
 split.
 - eapply DialogueExecution.stop with (ch:=48) (tail:=10::tail).
   + lia.
   + exact Hinput.
   + lia.
   + exact Hrun.
   + rewrite QuitLoopExecution.callback_meta_length. change (9<length (memory native arraydef_0__meta))%nat;lia.
   + rewrite QuitLoopExecution.loop_stop by lia. discriminate.
 - split;[now apply quit_state|]. split;[apply QuitLoopExecution.loop_input|].
   split;[apply QuitLoopExecution.loop_output|]. split;[apply QuitLoopExecution.loop_stop;lia|].
   now rewrite QuitLoopExecution.loop_error.
Qed.

Lemma request_wire request ch tail : valid_request request ->
 decimalBytes (Protocol.opcode request)=[ch] ->
 Protocol.request_bytes request++tail=ch::32::NativeSimpleCommands.argument_input (Protocol.arguments request) 32 10 tail.
Proof.
 destruct request as [opcode values name]. intros [Hshape [Hname Hvalues]] Hencoding.
 cbn [Protocol.opcode Protocol.arguments Protocol.object_name] in *. subst name.
 destruct Hshape as [[Htag [a [b Hargs]]]|[Htag [value Hargs]]];subst values.
 - destruct Htag as [Htag|[Htag|Htag]];subst opcode.
   all: first [change ([49]=[ch]) in Hencoding|change ([50]=[ch]) in Hencoding|change ([51]=[ch]) in Hencoding].
   all: injection Hencoding as <-.
   all: unfold Protocol.request_bytes,Protocol.number_tokens;cbn [Protocol.opcode Protocol.arguments Protocol.object_name Protocol.number_tokens Protocol.join_tokens NativeSimpleCommands.argument_input map].
   all: repeat first [progress rewrite <-app_assoc|progress cbn [List.app]];reflexivity.
 - subst opcode. change ([52]=[ch]) in Hencoding. injection Hencoding as <-.
   unfold Protocol.request_bytes,Protocol.number_tokens;cbn [Protocol.opcode Protocol.arguments Protocol.object_name Protocol.number_tokens Protocol.join_tokens NativeSimpleCommands.argument_input map].
   repeat first [progress rewrite <-app_assoc|progress cbn [List.app]];reflexivity.
Qed.

Theorem generated_finite requests : forall native logical tail observations,
 Forall valid_request requests ->
 Z.of_nat (length (Protocol.formulas logical)+length requests)<=9223372036854775807 ->
 NativeState.represents native logical ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 8=0 -> meta_value native 9=0 -> stdin native=input requests tail ->
 exists final replies target,
 length replies=length requests /\
 DialogueExecution.run native observations final (observations++schedule (stdout native) requests replies tail) /\
 Protocol.dialogue logical (requests++[quit]) (replies++[Protocol.BYE]) target [] /\
 NativeState.represents final target /\ stdin final=tail /\
 stdout final=output (stdout native) replies++CommandQuitExecution.bye_bytes /\
 meta_value final 9=1 /\ meta_value final 8=0.
Proof.
 induction requests as [|request requests IH];intros native logical tail observations Hvalid Hbudget Hstate Htoken Hprint Herror Hstop Hinput.
 - destruct (generated_quit native logical tail observations Hstate Htoken Herror Hinput)
    as (Hrun & Hfinal & Hin & Hout & HstopFinal & Hclear).
   exists (QuitLoopExecution.loop_result native tail),[],logical.
   split;[reflexivity|]. split;[exact Hrun|]. split.
   + apply Protocol.dialogue_quit.
   + repeat first [assumption|split].
 - inversion Hvalid as [|request' requests' Hrequest Hrequests];subst request' requests'.
   destruct (request_encoding request Hrequest) as (ch & Hencoding & Hbyte & Hopcode).
   set (unread:=32::NativeSimpleCommands.argument_input (Protocol.arguments request) 32 10 (input requests tail)).
   assert (Hbytes:stdin native=ch::unread).
   { rewrite Hinput,input_cons,(request_wire request ch (input requests tail) Hrequest Hencoding). reflexivity. }
   set (pending:=CommandLoopExecution.pending_state (withInput native unread) ch).
   pose proof (represented_meta native logical Hstate) as Hmeta.
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
   { unfold pending,CommandLoopExecution.pending_state. apply state_meta;try lia. now apply state_input. }
   pose proof Hrequest as [Hshape [Hname Hwords]].
   assert (HcurrentBudget:Z.of_nat (length (Protocol.formulas logical))<=9223372036854775807).
   { cbn [length] in Hbudget. rewrite Nat2Z.inj_add in Hbudget. lia. }
   destruct (NativeSimpleCommands.generated_boundary (Protocol.opcode request) (Protocol.arguments request) ch [] pending logical
    (fun _=>false) (fun _=>0) 32 32 10 (input requests tail) observations
    Hshape Hencoding HpendingMeta HpendingToken HpendingPrint Hpending HpendingError HcurrentBudget Hwords HpendingState
    ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
    ltac:(unfold TokenByteExecution.separator;tauto) eq_refl)
   as (after & reply & next & Hcommand & Hstep & HnextState & Hboundary).
   destruct Hboundary as (Hin & Hout & HnextToken & HnextPrint & Hclear & HnextStop & Hgrowth).
   assert (HrequestEq:Protocol.Req (Protocol.opcode request) (Protocol.arguments request) []=request).
   { destruct request;cbn [Protocol.opcode Protocol.arguments Protocol.object_name] in *. now subst. }
   rewrite HrequestEq in Hstep.
   assert (HnextBudget:Z.of_nat (length (Protocol.formulas next)+length requests)<=9223372036854775807).
   { cbn [length] in Hbudget. apply Nat2Z.inj_le in Hgrowth. rewrite Nat2Z.inj_succ in Hgrowth.
     rewrite Nat2Z.inj_add in *. lia. }
   destruct (IH after next tail
      (observations++[{|flushedOutput:=stdout pending++Protocol.reply_bytes reply;unreadInput:=input requests tail|}])
      Hrequests HnextBudget HnextState HnextToken HnextPrint Hclear ltac:(congruence) Hin)
   as (final & replies & target & Hlength & Hrun & Hdialogue & Hfinal & HfinalInput & HfinalOutput & HfinalStop & HfinalClear).
   assert (HpendingOutput:stdout pending=stdout native) by reflexivity.
   rewrite HpendingOutput in Hcommand,Hout,Hrun.
   exists final,(reply::replies),target. split;[cbn [length];congruence|]. split.
   + cbn [schedule]. eapply DialogueExecution.next with (ch:=ch) (tail:=unread) (after:=after).
     * exact Hbyte.
     * exact Hbytes.
     * lia.
     * exact Hcommand.
     * pose proof (represented_meta after next HnextState). lia.
     * congruence.
     * rewrite Hout,<-app_assoc in Hrun. exact Hrun.
   + split.
     * apply Protocol.dialogue_step with (t:=next);[exact Hopcode|exact Hstep|exact Hdialogue].
     * split;[exact Hfinal|]. split;[exact HfinalInput|]. split.
       -- cbn [output]. now rewrite Hout in HfinalOutput.
       -- split;assumption.
Qed.

(** Canonical finite formula sessions, including the actual seed handshake and
    terminating quit. The sole allocation bound reserves one arena entry for
    each request; invalid formula references may produce NO and still continue. *)
Theorem generated_seed_simple_quit key0 key1 requests tail bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum ->
 Forall valid_request requests -> Z.of_nat (S (length requests))<=9223372036854775807 ->
 exists final replies logical,
 length replies=length requests /\
 execObserved (funcdef_0__main bs ns) (SeedBootstrapExecution.initial key0 key1 (input requests tail) [],[])=
 Some (tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++input requests tail|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=input requests tail|}]++
 schedule Protocol.handshake_output requests replies tail)) /\
 Protocol.dialogue Protocol.initial (requests++[quit]) (replies++[Protocol.BYE]) logical [] /\
 NativeState.represents final logical /\ Guarantees.safe logical /\ stdin final=tail /\
 stdout final=output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\
 meta_value final 9=1 /\ meta_value final 8=0.
Proof.
 intros Hkey0 Hkey1 Hvalid Hbudget.
 destruct (NativeStartup.main_to_commands key0 key1 (input requests tail) bs ns Hkey0 Hkey1)
 as (ready & Hstate & Htop & Hmeta32 & Hsip1 & Hzero & Herror & Hmeta & Htoken & Hprint & Hstop & Hhistory & Hinput & Houtput & Hmain).
 set (observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++input requests tail|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=input requests tail|}]).
 destruct (generated_finite requests ready Protocol.initial tail observations Hvalid Hbudget Hstate Htoken Hprint Herror Hstop Hinput)
 as (final & replies & logical & Hlength & Hrun & Hdialogue & Hfinal & Hin & Hout & HfinalStop & Hclear).
 pose proof (DialogueExecution.generated_commands ready observations final
  (observations++schedule (stdout ready) requests replies tail) bs ns Hrun) as Hcommands.
 rewrite Houtput in Hcommands,Hout.
 exists final,replies,logical. split;[exact Hlength|]. split.
 - etransitivity;[exact Hmain|exact Hcommands].
 - split;[exact Hdialogue|]. split;[exact Hfinal|]. split.
   + exact (Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue).
   + split;[exact Hin|]. split;[exact Hout|]. split;assumption.
Qed.
End NativeSession.


