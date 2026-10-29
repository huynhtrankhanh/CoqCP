From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal RenameMemoControl CommandInput CommandDispatch CommandChain
 SchemaInstanceHandler SchemaInstancePrefix SchemaInstanceArguments SchemaInstanceProtocol NativeState NameRepresentation Representation ClassStorage HistoryRefinement
 ReadNat ReadToken TokenByte TokenFrame ArenaFrame FormulaProjection ClassLookup FormulaTopology HashTable SchemaRepresentation SchemaInstanceCommand FlushFrame FlushFrameReplies NativeCommandLengths NativeCommandStop NativeCommandBoundary NativeSchemaInstanceBoundary SchemaInstanceGeneralProtocol SchemaInstanceGeneralCommand SchemaInstanceCheckedResources NativeSchemaGeneralBoundary.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSchemaCheckedBoundary.
Import IndexExecution SipHashExecution ObservedLocal SchemaInstanceCommand.
Theorem generated_canonical s bs ns logical ids name tail observations :
 (31<length (memory s arraydef_0__meta))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat ->
 (0<length (memory s arraydef_0__sipState))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=51 -> meta_value s 8=0 ->
 Protocol.valid_name name -> Forall (fun id=>Z.of_nat id<=maximum) ids -> Z.of_nat (length ids)<=maximum ->
 stdin s=52::32::payload ids name tail ->
 NativeState.represents s logical -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 Guarantees.safe logical -> SchemaInstanceCheckedResources.check s logical ids name=true ->
 exists final reply next,
 execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) reply next /\
 NativeState.represents final next /\ meta_value final 8=0 /\ Guarantees.safe next /\ NativeCommandBoundary.io s final reply tail.
Proof.
 intros Hmeta Htoken Hsip Hprint Hpending Herror Hname Hwords Hlength Hinput Hstate Hgood Htop Hfalse Hsafe Hcheck.
 eapply NativeSchemaGeneralBoundary.generated_canonical;try eassumption.
 exact (SchemaInstanceCheckedResources.command_resources s logical ids name
   (NativeState.formula_representation s logical Hstate) (NativeState.schema_representation s logical Hstate) Hcheck).
Qed.
End NativeSchemaCheckedBoundary.
