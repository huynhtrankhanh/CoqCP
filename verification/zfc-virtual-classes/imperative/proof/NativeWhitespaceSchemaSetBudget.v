From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import NativeWhitespaceSchemaSetCommand NativeSetBudgetPlan NativeSchemaFlat SchemaEvaluationSetCell Index SipHash TokenByte NativeWhitespaceSchemaArguments NativeWhitespaceSchemaConcrete NativeWhitespaceSchemaFinish NativeWhitespaceSchemaSetHandler SchemaInstanceSetProtocol SchemaInstanceCommand ObservedLocal RenameMemoControl CommandInput CommandDispatch CommandChain
 SchemaInstanceHandler SchemaInstancePrefix SchemaInstanceArguments SchemaInstanceProtocol NativeState NameRepresentation Representation ClassStorage HistoryRefinement
 ReadNat ReadToken TokenByte TokenFrame ArenaFrame FormulaProjection ClassLookup FormulaTopology HashTable SchemaRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaSetBudget.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaSetCommand.
Theorem generated s bs ns logical before fields name namespaces namesep countspaces countsep firstsep tail observations :
 (31<length (memory s arraydef_0__meta))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat ->
 (0<length (memory s arraydef_0__sipState))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=51 -> meta_value s 8=0 ->
 Protocol.valid_name name -> Forall(fun item=>Forall TokenByteExecution.separator(fst item) /\ Z.of_nat(snd item)<=maximum)fields -> Z.of_nat(length fields)<=maximum ->
 Forall TokenByteExecution.separator namespaces -> TokenByteExecution.separator namesep -> Forall TokenByteExecution.separator countspaces -> TokenByteExecution.separator countsep -> TokenByteExecution.separator firstsep ->
 stdin s=52::firstsep::payload name fields namespaces namesep countspaces countsep tail ->
 NativeState.represents s logical -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 Guarantees.safe logical -> NativeSchemaFlat.flat s -> SchemaEvaluationSetCell.sets(Protocol.classes logical) -> NativeSetBudgetPlan.bounds logical before -> NativeSetBudgetPlan.conditions before (Protocol.Req 24 (map snd fields) name) ->
 exists final reply next,
 execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 (map snd fields) name) reply next /\
 NativeState.represents final next /\ meta_value final 8=0 /\ Guarantees.safe next.
Proof.
 intros Hmeta Htoken Hsip Hprint Hpending Herror Hname Hfields Hlength Hns Hnsep Hcs Hcsep Hfirstsep Hin Hstate Hgood Htop Hfalse Hsafe Hflat Hsets Hbounds Hconditions.
 eapply (NativeWhitespaceSchemaSetCommand.generated s bs ns logical fields name namespaces namesep countspaces countsep firstsep tail observations);try eassumption.
 exact(NativeSetBudgetPlan.instance_resources s logical before (map snd fields) name Hstate Hflat Hsets Hbounds Hconditions).
Qed.
End NativeWhitespaceSchemaSetBudget.
