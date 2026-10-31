From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ReadToken ReadName SeedSeparator NativeArgumentWhitespace SchemaInstanceArguments SchemaInstancePrefix NativeWhitespaceSchemaConcrete NativeWhitespaceSchemaFinish NativeWhitespaceSchemaArguments NameSearch TypedNameLookup.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaTransport.
Import IndexExecution SipHashExecution SchemaInstancePrefix NativeWhitespaceSchemaConcrete.
Lemma named_memory (f:Frame) name fields countspaces countsep tail array :
 memory(named_spaced f name fields countspaces countsep tail)array = memory(SchemaInstancePrefix.named f name (map snd fields) tail)array.
Proof. unfold named_spaced,SchemaInstancePrefix.named,ReadName.result,ReadTokenExecution.read_result. cbn [memory withInput]. reflexivity. Qed.
Lemma named_output (f:Frame) name fields countspaces countsep tail :
 stdout(named_spaced f name fields countspaces countsep tail) = stdout(SchemaInstancePrefix.named f name (map snd fields) tail).
Proof. unfold named_spaced,SchemaInstancePrefix.named,ReadName.result,ReadTokenExecution.read_result. cbn [stdout withInput]. reflexivity. Qed.
Definition aligned (f:Frame) (looked:Machine) (name:list Z) (fields:list NativeWhitespaceSchemaArguments.field) (tail:list Z) := withInput looked (stdin(SchemaInstancePrefix.named f name (map snd fields) tail)).
Theorem aligned_frame (f:Frame) looked name fields countspaces countsep tail :
 NameSearchExecution.storage_frame(named_spaced f name fields countspaces countsep tail)looked ->
 NameSearchExecution.storage_frame(SchemaInstancePrefix.named f name (map snd fields) tail)(aligned f looked name fields tail).
Proof.
 intros [Harrays [Hcells [Hin Hout]]]. unfold NameSearchExecution.storage_frame,aligned. split.
 - intros array Hne. change(memory looked array=memory(SchemaInstancePrefix.named f name (map snd fields) tail)array).
   rewrite Harrays by exact Hne. apply named_memory.
 - split.
   + intros i Hne. change(meta_value looked i=meta_value(SchemaInstancePrefix.named f name (map snd fields) tail)i).
     rewrite Hcells by exact Hne. unfold meta_value. now rewrite named_memory.
   + split;[reflexivity|]. change(stdout looked=stdout(SchemaInstancePrefix.named f name (map snd fields) tail)).
     rewrite Hout. apply named_output.
Qed.
Lemma aligned_finished (f:Frame) looked name fields tail :
 SchemaInstancePrefix.finished f (aligned f looked name fields tail) (map snd fields) tail = SchemaInstancePrefix.finished f looked (map snd fields) tail.
Proof.
 unfold SchemaInstancePrefix.finished,prepared,SchemaInstancePrefix.counted,aligned.
 rewrite NativeArgumentWhitespace.encoded_result_input. reflexivity.
Qed.
End NativeWhitespaceSchemaTransport.
