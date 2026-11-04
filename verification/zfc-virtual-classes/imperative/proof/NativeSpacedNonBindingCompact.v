From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte NativeNameCompact NativeGeneralCommandInvariant.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSpacedNonBindingCompact.
Import IndexExecution SipHashExecution.
(** Non-binding handlers preserve compact name storage regardless of how
    their remaining fields are encoded. *)
Theorem preserves native logical request bs ns opcode ch chars separator payload observations final trace reply next :
 (1<=opcode<=26)%nat -> opcode<>9%nat -> opcode<>20%nat -> opcode<>23%nat ->
 Protocol.opcode request=opcode -> decimalBytes opcode=ch::chars ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> TokenByteExecution.separator separator ->
 stdin native=chars++separator::payload -> NativeNameCompact.compact native logical ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 Protocol.step logical request reply next -> NativeNameCompact.compact final next.
Proof.
 intros Hrange H9 H20 H23 Hop Hencoding Hmeta Htoken Hpending Herror Hsep Hinput Hcompact Hrun Hstep.
 assert(Hraw:memory final arraydef_0__names=memory native arraydef_0__names).
 { eapply NativeGeneralCommandInvariant.canonical_array with
    (opcode:=opcode)(ch:=ch)(chars:=chars)(separator:=separator)(payload:=payload)
    (bs:=bs)(ns:=ns)(observations:=observations)(trace:=trace);try eassumption;try discriminate;try lia.
   apply NativeGeneralCommandInvariant.Names.handler_ro;lia. }
 unfold NativeNameCompact.compact,NativeNameCompact.compact_bindings in *.
 rewrite Hraw. change(length(memory native arraydef_0__names)=NativeNameCompact.bytes next).
 rewrite(NativeNameCompact.step_bytes_unchanged logical request reply next ltac:(congruence) ltac:(congruence) ltac:(congruence) Hstep).
 exact Hcompact.
Qed.
End NativeSpacedNonBindingCompact.
