From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte NativeSchemaFieldBounds NativeGeneralCommandInvariant CommandSchemaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSpacedNonNodeFields.
Import IndexExecution SipHashExecution.
(** Every handler other than schema-node construction leaves the schema
    storage untouched. The payload is arbitrary, so numeric/name fields may
    contain any supported separator runs and even malformed bytes. *)
Theorem preserves native bs ns opcode ch chars separator payload observations final trace cap :
 (1<=opcode<=26)%nat -> opcode<>22%nat -> decimalBytes opcode=ch::chars ->
 (17<length(memory native arraydef_0__meta))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> TokenByteExecution.separator separator ->
 stdin native=chars++separator::payload -> NativeSchemaFieldBounds.fields native cap ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeSchemaFieldBounds.fields final cap.
Proof.
 intros Hrange Hnode Hencoding Hmeta Htoken Hpending Herror Hsep Hinput Hfields Hrun.
 eapply NativeSchemaFieldBounds.fields_frame;[|exact Hfields].
 eapply NativeGeneralCommandInvariant.canonical_array with
  (opcode:=opcode) (ch:=ch) (chars:=chars) (separator:=separator) (payload:=payload)
  (bs:=bs) (ns:=ns) (observations:=observations) (trace:=trace);try eassumption;try discriminate;try lia.
 apply CommandSchemaFrame.nodes_ro;lia.
Qed.
End NativeSpacedNonNodeFields.
