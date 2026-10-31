From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte NativeSchemaFieldBounds NativeGeneralCommandInvariant CommandSchemaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaFields.
Import IndexExecution SipHashExecution.
Theorem preserves native bs ns separator payload observations final trace cap :
 (17<length(memory native arraydef_0__meta))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=51 -> meta_value native 8=0 -> TokenByteExecution.separator separator ->
 stdin native=52::separator::payload -> NativeSchemaFieldBounds.fields native cap ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeSchemaFieldBounds.fields final cap.
Proof.
 intros Hmeta Htoken Hpending Herror Hsep Hinput Hfields Hrun.
 eapply NativeSchemaFieldBounds.fields_frame;[|exact Hfields].
 eapply NativeGeneralCommandInvariant.canonical_array with
  (opcode:=24%nat) (ch:=50) (chars:=[52]) (separator:=separator) (payload:=payload)
  (bs:=bs) (ns:=ns) (observations:=observations) (trace:=trace);try eassumption;try discriminate;try lia;try reflexivity.
 - apply CommandSchemaFrame.nodes_ro;lia.
Qed.
End NativeWhitespaceSchemaFields.
