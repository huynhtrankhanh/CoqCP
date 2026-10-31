From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ObservedLocal NameRepresentation SchemaInstanceHandler SchemaInstancePrefix CommandChain NativeWhitespaceSchemaArguments NativeWhitespaceSchemaConcrete NativeWhitespaceSchemaCommand FlushFrame FlushFrameReplies.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaIO.
Import IndexExecution SipHashExecution ObservedLocal.
Theorem handler_io (f:SchemaInstanceHandler.Frame) bindings name fields namespaces namesep countspaces countsep tail observations final reply :
 (18<length(memory(machine f)arraydef_0__meta))%nat -> (1024<=length(memory(machine f)arraydef_0__token))%nat ->
 meta_value(machine f)15=0 -> meta_value(machine f)8=0 -> NameRepresentation.represents(machine f)bindings -> Protocol.valid_name name ->
 Forall(fun item=>Forall TokenByteExecution.separator(fst item) /\ Z.of_nat(snd item)<=maximum)fields -> Z.of_nat(length fields)<=maximum ->
 Forall TokenByteExecution.separator namespaces -> TokenByteExecution.separator namesep -> Forall TokenByteExecution.separator countspaces -> TokenByteExecution.separator countsep ->
 stdin(machine f)=NativeWhitespaceSchemaCommand.payload name fields namespaces namesep countspaces countsep tail ->
 execLocalObserved(CommandChain.handler_for funcdef_0__readNat 24)(f,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout(machine f)++Protocol.reply_bytes reply;unreadInput:=tail|}])) ->
 stdin(machine final)=tail /\ stdout(machine final)=stdout(machine f)++Protocol.reply_bytes reply.
Proof.
 intros Hmeta Htoken Hpending Herror Hbindings Hname Hfields Hlength Hns Hnsep Hcs Hcsep Hin Hrun.
 destruct(NativeWhitespaceSchemaConcrete.generated_spaced f bindings name fields namespaces namesep countspaces countsep tail SchemaInstanceHandler.suffix observations
  Hmeta Htoken Hpending Herror Hbindings Hname Hfields Hlength Hns Hnsep Hcs Hcsep Hin)
 as(looked & Hframe & Hlookup & Hprefix & Hlen).
 rewrite SchemaInstancePrefix.actual_handler in Hrun.
 assert(Hsuffix:execLocalObserved SchemaInstanceHandler.suffix (NativeWhitespaceSchemaConcrete.finished_spaced f looked fields tail,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout(machine f)++Protocol.reply_bytes reply;unreadInput:=tail|}]))).
 { exact(eq_trans (eq_sym Hprefix) Hrun). }
 pose proof(FlushFrame.singleton _ _ _ _ (FlushFrameReplies.schema_suffix _ _ _ _ _ Hsuffix)) as Hfinal.
 split;[exact(f_equal unreadInput Hfinal)|exact(f_equal flushedOutput Hfinal)].
Qed.
End NativeWhitespaceSchemaIO.
