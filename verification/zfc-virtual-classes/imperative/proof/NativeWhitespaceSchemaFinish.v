From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ReadToken DecimalInput SeedSeparator NativeArgumentReadsTwo NativeWhitespaceSchemaArguments NativeWhitespaceSchemaConcrete SchemaInstanceArguments SchemaInstancePrefix.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaFinish.
Import IndexExecution SipHashExecution SchemaInstancePrefix NativeWhitespaceSchemaConcrete.
Lemma prepared_suffix (f:Frame) looked value n input1 input2 :
 prepared f looked (DecimalInput.encoded_result value n input1) n =
 setMachine (prepared f looked (DecimalInput.encoded_result value n input2) n)
 (withInput (machine(prepared f looked (DecimalInput.encoded_result value n input2) n)) input1).
Proof.
 unfold prepared. rewrite (NativeArgumentReadsTwo.encoded_suffix value n input1 input2),SeedSeparator.store_input.
 destruct f;reflexivity.
Qed.
Theorem finished_spaced_canonical (f:Frame) looked fields tail :
 finished_spaced f looked fields tail=SchemaInstancePrefix.finished f looked (map snd fields) tail.
Proof.
 unfold finished_spaced,counted_spaced,SchemaInstancePrefix.finished,SchemaInstancePrefix.counted.
 rewrite length_map.
 destruct fields as [|[spaces value] rest].
 - reflexivity.
 - rewrite <-!NativeWhitespaceSchemaArguments.consume_canonical.
   cbn [List.length] in *. unfold prepared.
   rewrite (NativeArgumentReadsTwo.encoded_suffix looked _ _ (SchemaInstanceArguments.wire (map snd ((spaces,value)::rest))++tail)),SeedSeparator.store_input.
   set(base:=setMachine (setNum (setNum f vardef_0__command_binding (meta_value looked 0)) vardef_0__command_a (Z.of_nat (S (length rest))))
      (store_meta (DecimalInput.encoded_result looked (S (length rest)) (SchemaInstanceArguments.wire (map snd ((spaces,value)::rest))++tail)) 18 1)).
   change (NativeWhitespaceSchemaArguments.consume_spaced (setMachine base (withInput (machine base) (NativeWhitespaceSchemaArguments.spaced_wire ((spaces,value)::rest)++tail))) 0 ((spaces,value)::rest) tail = NativeWhitespaceSchemaArguments.consume_spaced base 0 ((spaces,value)::rest) tail).
   apply NativeWhitespaceSchemaArguments.consume_spaced_input. discriminate.
Qed.
End NativeWhitespaceSchemaFinish.
