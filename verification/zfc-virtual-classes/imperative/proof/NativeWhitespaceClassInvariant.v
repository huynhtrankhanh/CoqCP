From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeWhitespaceClassBoundary NativeWhitespaceClassSetInput NativeWhitespaceClassAbstractInput NativeAllocationInvariant NativeCommandBoundary ClassStorage ClassSetInput ClassSetRefinement ClassAbstractInput ClassAbstractRefinement ClassLookup FormulaTopology HashTable ReadOne ReplyNO Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceClassInvariant.
Import IndexExecution SipHashExecution.
Theorem generated_set native logical bs ns value first spaces last tail observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat -> (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=54 -> meta_value native 8=0 -> Z.of_nat(length(Protocol.classes logical))<maximum -> Z.of_nat value<=maximum ->
 NativeState.represents native logical -> FormulaTopology.ordered native(length(Protocol.formulas logical)) -> ClassLookup.wellformed native ->
 TokenByteExecution.separator first -> TokenByteExecution.separator last -> Forall TokenByteExecution.separator spaces -> stdin native=first::spaces++decimalBytes value++last::tail ->
 exists final,
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes(Protocol.OK(length(Protocol.classes logical)));unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 5 [value] []) (Protocol.OK(length(Protocol.classes logical))) (ClassSetRefinement.logical_after logical value) /\
 NativeState.represents final (ClassSetRefinement.logical_after logical value) /\ NativeCommandBoundary.io native final (Protocol.OK(length(Protocol.classes logical))) tail /\
 FormulaTopology.ordered final(length(Protocol.formulas(ClassSetRefinement.logical_after logical value))) /\ ClassLookup.wellformed final.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hstate Htop Hgood Hfirst Hlast Hspaces Hinput.
 destruct(NativeWhitespaceClassBoundary.generated_set native logical bs ns value first spaces last tail observations Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hstate Hfirst Hlast Hspaces Hinput)
 as(final & Hrun & Hstep & Hfinal & Hboundary).
 pose proof(NativeWhitespaceClassSetInput.generated_pending native bs ns (length(Protocol.classes logical)) value first spaces last tail observations
 Hmeta Htoken Hprint Hpending Herror (proj1(NativeState.class_representation _ _ Hstate)) Hroom Hvalue Hfirst Hlast Hspaces Hinput) as Hexpected.
 assert(Hsame:final=ClassSetInput.result native (length(Protocol.classes logical)) value last tail) by congruence.
 exists final. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hfinal|]. split.
 - exact(proj1 Hboundary).
 - split.
   + rewrite Hsame. change(FormulaTopology.ordered(ClassSetInput.result native(length(Protocol.classes logical))value last tail)(length(Protocol.formulas logical))). now apply NativeAllocationInvariant.set_top.
   + rewrite Hsame. exact(NativeAllocationInvariant.set_good native (Protocol.formulas logical)(Protocol.classes logical) value last tail (NativeState.class_representation _ _ Hstate) Hgood Hvalue).
Qed.
Theorem generated_abstract native logical bs ns value first spaces last tail observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat -> (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=55 -> meta_value native 8=0 -> Z.of_nat(length(Protocol.classes logical))<maximum -> Z.of_nat value<=maximum ->
 NativeState.represents native logical -> FormulaTopology.ordered native(length(Protocol.formulas logical)) -> ClassLookup.wellformed native ->
 TokenByteExecution.separator first -> TokenByteExecution.separator last -> Forall TokenByteExecution.separator spaces -> stdin native=first::spaces++decimalBytes value++last::tail ->
 exists final reply next,
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 6 [value] []) reply next /\ NativeState.represents final next /\ NativeCommandBoundary.io native final reply tail /\
 FormulaTopology.ordered final(length(Protocol.formulas next)) /\ ClassLookup.wellformed final.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hstate Htop Hgood Hfirst Hlast Hspaces Hinput.
 destruct(Protocol.formula_at logical value) as [p|] eqn:Hlookup.
 - destruct(NativeWhitespaceClassBoundary.generated_abstract native logical bs ns value p first spaces last tail observations Hmeta Htoken Hprint Hpending Herror Hroom Hvalue Hlookup Hstate Hfirst Hlast Hspaces Hinput)
   as(final & Hrun & Hstep & Hfinal & Hboundary).
   assert(Hreference:Z.of_nat value<meta_value native 1).
   { pose proof(proj1(proj2(proj1(NativeState.formula_representation _ _ Hstate)))) as Hcount. change(meta_value native 1=Z.of_nat(length(Protocol.formulas logical))) in Hcount.
     assert((value<length(Protocol.formulas logical))%nat) by (apply nth_error_Some;unfold Protocol.formula_at in Hlookup;congruence). lia. }
   pose proof(NativeWhitespaceClassAbstractInput.generated_pending native bs ns (length(Protocol.classes logical)) value first spaces last tail observations
    Hmeta Htoken Hprint Hpending Herror (proj1(NativeState.class_representation _ _ Hstate)) Hroom Hvalue Hreference Hfirst Hlast Hspaces Hinput) as Hexpected.
   assert(Hsame:final=ClassAbstractInput.result native (length(Protocol.classes logical)) value last tail) by congruence.
   exists final,(Protocol.OK(length(Protocol.classes logical))),(ClassAbstractRefinement.logical_after logical p). split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hfinal|]. split;[exact(proj1 Hboundary)|]. split.
   + rewrite Hsame. change(FormulaTopology.ordered(ClassAbstractInput.result native(length(Protocol.classes logical))value last tail)(length(Protocol.formulas logical))). now apply NativeAllocationInvariant.abstract_top.
   + rewrite Hsame. exact(NativeAllocationInvariant.abstract_good native (Protocol.formulas logical)(Protocol.classes logical) value last tail (NativeState.class_representation _ _ Hstate) Hgood Hvalue).
 - destruct(NativeWhitespaceClassBoundary.generated_abstract_rejected native logical bs ns value first spaces last tail observations Hmeta Htoken Hprint Hpending Herror Hvalue Hlookup Hstate Hfirst Hlast Hspaces Hinput)
   as(final & Hrun & Hstep & Hfinal & Hboundary).
   assert(Hreference:meta_value native 1<=Z.of_nat value).
   { pose proof(proj1(proj2(proj1(NativeState.formula_representation _ _ Hstate)))) as Hcount. change(meta_value native 1=Z.of_nat(length(Protocol.formulas logical))) in Hcount.
     unfold Protocol.formula_at in Hlookup. apply nth_error_None in Hlookup. lia. }
   pose proof(NativeWhitespaceClassAbstractInput.generated_rejected native bs ns value first spaces last tail observations Hmeta Htoken Hprint Hpending Herror Hvalue Hreference Hfirst Hlast Hspaces Hinput) as Hexpected.
   assert(Hsame:final=ClassAbstractInput.rejected native value last tail) by congruence.
   exists final,Protocol.NO,logical. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hfinal|]. split;[exact(proj1 Hboundary)|]. split.
   + rewrite Hsame. eapply FormulaTopology.same;[exact Htop|]. intros parent _. unfold HashTableInvariant.tuple_at. change(List.nth parent (memory(ClassAbstractInput.argument_state native value last tail) arraydef_0__formulas) (0,0,0)=List.nth parent (memory native arraydef_0__formulas) (0,0,0)). unfold ClassAbstractInput.argument_state. now rewrite ReadOne.argument_other by discriminate.
   + rewrite Hsame. apply(ClassLookup.transport native);[|exact Hgood]. change(memory(ClassAbstractInput.argument_state native value last tail)arraydef_0__classes=memory native arraydef_0__classes). unfold ClassAbstractInput.argument_state. now rewrite ReadOne.argument_other by discriminate.
Qed.
End NativeWhitespaceClassInvariant.
