From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal TypedNameLookup NameSearch SchemaInstancePrefix NativeWhitespaceSchemaConcrete NativeWhitespaceSchemaFinish NativeWhitespaceSchemaTransport.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaAligned.
Import IndexExecution SipHashExecution ObservedLocal SchemaInstancePrefix NativeWhitespaceSchemaConcrete NativeWhitespaceSchemaTransport.
Lemma aligned_outcome f looked name fields tail bindings :
 TypedNameLookup.outcome looked bindings name -> TypedNameLookup.outcome (aligned f looked name fields tail) bindings name.
Proof. unfold aligned,TypedNameLookup.outcome,meta_value. cbn [memory withInput]. destruct(Protocol.lookup name bindings);tauto. Qed.
Lemma aligned_length f looked name fields countspaces countsep tail :
 length(memory looked arraydef_0__meta)=length(memory(named_spaced f name fields countspaces countsep tail)arraydef_0__meta) ->
 length(memory(aligned f looked name fields tail)arraydef_0__meta)=length(memory(SchemaInstancePrefix.named f name (map snd fields) tail)arraydef_0__meta).
Proof. intro H. cbn [aligned memory withInput]. now rewrite H,named_memory. Qed.
Theorem aligned_execution (f:Frame) looked name fields tail work observations :
 execLocalObserved (with_suffix work) (f,observations)=execLocalObserved work(finished_spaced f looked fields tail,observations) ->
 execLocalObserved (with_suffix work) (f,observations)=execLocalObserved work(SchemaInstancePrefix.finished f (aligned f looked name fields tail) (map snd fields) tail,observations).
Proof. intro Hrun. rewrite aligned_finished,<-NativeWhitespaceSchemaFinish.finished_spaced_canonical. exact Hrun. Qed.
End NativeWhitespaceSchemaAligned.
