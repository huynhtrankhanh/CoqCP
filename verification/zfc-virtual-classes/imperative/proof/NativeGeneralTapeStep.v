From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeSession NativeDialogueComposition
 NativeBasicDispatcher NativeFullDispatcher NativeGeneralDispatcher NativeFullTapeStep NativeCommandBoundary NativeCommandLengths CommandLoop
 FormulaTopology HashTable ClassLookup LogicalRegistryBounds LogicalStorageMonotone.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeGeneralTapeStep.
Import IndexExecution SipHashExecution NativeFullTapeStep.
Theorem generated native logical request bs ns tail observations :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 NativeDialogueComposition.boundary native logical ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 Guarantees.safe logical -> FormulaTopology.ordered native (length(Protocol.formulas logical)) ->
 nth_error(Protocol.formulas logical)0=Some SetTheory.falsity -> ClassLookup.wellformed native ->
 LogicalRegistryBounds.unique logical -> NativeGeneralDispatcher.resources (entered native request tail) logical request ->
 stdin native=Protocol.request_bytes request++tail ->
 exists ch unread final reply next,
 0<=ch<256 /\ stdin native=ch::unread /\
 execObserved(funcdef_0__command bs ns)
  (CommandLoopExecution.pending_state(withInput native unread)ch,observations)=Some(tt,(final,
  observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical request reply next /\ NativeDialogueComposition.boundary final next /\
 NativeCommandBoundary.io native final reply tail /\ Guarantees.safe next /\
 LogicalRegistryBounds.unique next /\ LogicalRegistryBounds.counts logical next 1 /\
 LogicalStorageMonotone.extends logical next /\
 nth_error(Protocol.formulas next)0=Some SetTheory.falsity /\
 length(memory final arraydef_0__meta)=length(memory native arraydef_0__meta) /\
 length(memory final arraydef_0__sipState)=length(memory native arraydef_0__sipState).
Proof.
 intros Hshape Hrange Hboundary Hmeta Hsip Hsafe Htop Hfalse Hgood Hunique Hresources Hinput.
 destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning].
 destruct(NativeFullDispatcher.request_encoding request Hrange) as [Hwire Hbyte].
 set(pending:=entered native request tail).
 assert(HpendingState:NativeState.represents pending logical).
 { unfold pending,entered,CommandLoopExecution.pending_state. apply NativeSession.state_meta;try lia.
   now apply NativeSession.state_input. }
 assert(HpendingMeta:(31<length(memory pending arraydef_0__meta))%nat).
 { unfold pending. now rewrite entered_meta_length. }
 assert(HpendingValue:meta_value pending 15=NativeBasicDispatcher.first(Protocol.opcode request)+1).
 { unfold pending,entered,CommandLoopExecution.pending_state. apply meta_store_same.
   change(15<length(memory native arraydef_0__meta))%nat;lia. }
 assert(HpendingError:meta_value pending 8=0).
 { unfold pending,entered,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
 assert(HpendingTop:FormulaTopology.ordered pending(length(Protocol.formulas logical))).
 { eapply FormulaTopology.same;[exact Htop|]. intros parent Hparent.
   unfold HashTableInvariant.tuple_at,pending. now rewrite entered_arrays by discriminate. }
 assert(HpendingGood:ClassLookup.wellformed pending).
 { eapply ClassLookup.transport;[|exact Hgood]. unfold pending. apply entered_arrays;discriminate. }
 destruct(NativeGeneralDispatcher.generated_canonical pending logical request bs ns tail observations Hshape Hrange HpendingMeta
  ltac:(unfold pending;rewrite entered_arrays by discriminate;exact Hsip)
  ltac:(unfold pending;rewrite entered_arrays by discriminate;exact Htoken)
  ltac:(unfold pending;rewrite entered_arrays by discriminate;exact Hprint)
  HpendingValue HpendingError HpendingState Hsafe HpendingTop Hfalse HpendingGood Hunique Hresources eq_refl)
 as(final & reply & next & Hrun & Hstep & HnextState & Hio & HnextSafe & Hhistory & Hnames).
 assert(HnativeOutput:stdout pending=stdout native) by reflexivity.
 assert(Hstop:meta_value pending 9=meta_value native 9).
 { unfold pending,entered,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. reflexivity. }
 assert(HfinalIO:NativeCommandBoundary.io native final reply tail).
 { destruct Hio as(Hin & Hout & Ht & Hp & He & Hs). unfold NativeCommandBoundary.io.
   rewrite HnativeOutput in Hout. rewrite Hstop in Hs. repeat split;assumption. }
 assert(HnextBoundary:NativeDialogueComposition.boundary final next).
 { destruct HfinalIO as(Hin & Hout & Ht & Hp & He & Hs). constructor;try assumption. now rewrite Hs. }
 pose proof(LogicalStorageMonotone.step _ _ _ _ Hstep) as Hextends.
 exists(NativeBasicDispatcher.first(Protocol.opcode request)),(NativeBasicDispatcher.rest request++tail),final,reply,next.
 split;[exact Hbyte|]. split;[rewrite Hinput,Hwire;reflexivity|].
 split;[exact Hrun|]. split;[exact Hstep|]. split;[exact HnextBoundary|]. split;[exact HfinalIO|].
 split;[exact HnextSafe|]. split;[exact(LogicalRegistryBounds.step_unique _ _ _ _ Hstep Hunique)|].
 split;[exact(LogicalRegistryBounds.step_counts _ _ _ _ Hstep)|]. split;[exact Hextends|].
 split;[exact(LogicalStorageMonotone.formula_lookup _ _ _ _ Hextends Hfalse)|]. split.
 - exact(eq_trans(NativeCommandLengths.generated arraydef_0__meta pending bs ns final observations _ NativeCommandLengths.meta_protected Hrun)
    (entered_meta_length native request tail)).
 - exact(eq_trans(NativeCommandLengths.generated arraydef_0__sipState pending bs ns final observations _ NativeCommandLengths.sipState_protected Hrun)
    (f_equal (fun values=>length values) (entered_arrays native request tail arraydef_0__sipState ltac:(discriminate)))).
Qed.
End NativeGeneralTapeStep.
