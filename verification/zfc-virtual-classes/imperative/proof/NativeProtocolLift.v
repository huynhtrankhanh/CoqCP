From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash NativeState NativeStateFrames NativeCommandFrames
 CommandInput TokenByte Representation ClassStorage HistoryRefinement.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeProtocolLift.
Import IndexExecution SipHashExecution.
Lemma parsed_registries native ch chars payload :
 NativeStateFrames.registries native (CommandInput.parsed native ch chars payload).
Proof.
 constructor;first [apply CommandInput.parsed_meta_other;lia|apply CommandInput.parsed_other;discriminate].
Qed.
(** Strengthen an existing concrete command refinement with immutable names
    and full schema meanings. The concrete refinement supplies the actual
    command run and the three mutable components, never a helper run. *)
Theorem canonical opcode ch chars native bs ns separator payload observations final trace logical request reply next :
 (1<=opcode<=26)%nat -> opcode<>22%nat -> NativeStateFrames.nonbinding opcode -> Protocol.opcode request=opcode ->
 decimalBytes opcode=ch::chars ->
 (17<length (memory native arraydef_0__meta))%nat -> (1024<=length (memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> TokenByteExecution.separator separator ->
 stdin native=chars++separator::payload ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> Protocol.step logical request reply next ->
 NativeRepresentation.canonical_arena final (Protocol.formulas next) ->
 ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) -> HistoryRefinement.represents final next ->
 NativeState.represents final next.
Proof.
 intros Hrange HnotNode Hnonbinding Hopcode Hencoding Hmeta Htoken Hpending Herror Hseparator Hinput Hrun Hstate Hstep Harena Hclasses Hhistory.
 assert (Hword:Z.of_nat opcode<=maximum) by (unfold maximum;lia).
 eapply NativeCommandFrames.generated_preserves with (readstate:=CommandInput.parsed native ch chars payload) (opcode:=opcode);
   try eassumption.
 - exact (CommandInput.generated_pending native (fun _=>false) (fun _=>0) opcode ch chars separator payload observations
     Hmeta Htoken Hpending Herror Hword Hencoding Hseparator Hinput).
 - rewrite CommandInput.parsed_meta_length;exact Hmeta.
 - exact (CommandInput.parsed_number native opcode ch chars payload Hmeta Hword Hencoding).
 - apply CommandInput.parsed_valid;exact Hmeta.
 - rewrite CommandInput.parsed_meta_other by lia. exact Herror.
 - apply parsed_registries.
Qed.
End NativeProtocolLift.
