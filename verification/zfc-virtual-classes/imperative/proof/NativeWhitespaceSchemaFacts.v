From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ReadToken ReadNat ReadName DecimalInput SchemaEvaluationArguments SchemaInstanceArguments SchemaInstancePrefix NameSearch.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaFacts.
Import IndexExecution SipHashExecution SchemaInstancePrefix.
Theorem finished_facts (f:Frame) looked name args tail (observations:list FlushSnapshot) :
 (18<length(memory(machine f)arraydef_0__meta))%nat -> (1024<=length(memory(machine f)arraydef_0__token))%nat ->
 meta_value(machine f)15=0 -> meta_value(machine f)8=0 -> Forall(fun x=>Z.of_nat x<=maximum)args -> Z.of_nat(length args)<=maximum ->
 NameSearchExecution.storage_frame (named f name args tail) looked -> length(memory looked arraydef_0__meta)=length(memory(named f name args tail)arraydef_0__meta) ->
 let final:=finished f looked args tail in
 SchemaEvaluationArguments.represents(machine final)args /\ stdin(machine final)=tail /\ stdout(machine final)=stdout(machine f) /\
 meta_value(machine final)8=0 /\ meta_value(machine final)18=if forallb(fun id=>bool_decide(Z.of_nat id<meta_value(machine f)2))args then 1 else 0.
Proof.
 intros Hmeta Htoken Hpending Herror Hwords Hlength [Harrays [Hcells [Hinput Houtput]]] HlookLength final.
 assert(Hnamed:(18<length(memory(named f name args tail)arraydef_0__meta))%nat) by (unfold named,ReadName.result;rewrite ReadTokenExecution.result_meta_length;exact Hmeta).
 assert(Hlooked:(18<length(memory looked arraydef_0__meta))%nat) by (rewrite HlookLength;exact Hnamed).
 assert(HlookError:meta_value looked 8=0) by (rewrite Hcells by lia;unfold named,ReadName.result;rewrite ReadTokenExecution.result_meta_other by lia;exact Herror).
 assert(HlookPending:meta_value looked 15=0) by (rewrite Hcells by lia;unfold named,ReadName.result;rewrite ReadTokenExecution.result_meta_other by lia;exact Hpending).
 assert(HlookToken:(1024<=length(memory looked arraydef_0__token))%nat) by (rewrite Harrays by discriminate;unfold named;rewrite ReadName.token_length;exact Htoken).
 set(countState:=counted looked args tail).
 assert(Hcounted:(18<length(memory countState arraydef_0__meta))%nat) by (unfold countState,counted;rewrite DecimalInput.encoded_meta_length;exact Hlooked).
 set(start:=prepared f looked countState (length args)).
 assert(HstartMeta:(18<length(memory(machine start)arraydef_0__meta))%nat) by (unfold start,prepared;cbn [machine setMachine];rewrite store_meta_length;exact Hcounted).
 assert(HstartToken:(1024<=length(memory(machine start)arraydef_0__token))%nat) by (unfold start,prepared;cbn [machine setMachine];rewrite store_meta_other by discriminate;unfold countState,counted;rewrite DecimalInput.encoded_token_length;exact HlookToken).
 assert(HstartPending:meta_value(machine start)15=0) by (unfold start,prepared;cbn [machine setMachine];rewrite meta_store_other by lia;unfold countState,counted;rewrite DecimalInput.encoded_meta_other by (try exact Hlooked;lia);exact HlookPending).
 assert(HstartError:meta_value(machine start)8=0) by (unfold start,prepared;cbn [machine setMachine];rewrite meta_store_other by lia;unfold countState,counted;rewrite DecimalInput.encoded_meta_other by (try exact Hlooked;lia);exact HlookError).
 assert(HstartInput:stdin(machine start)=SchemaInstanceArguments.wire args++tail) by reflexivity.
 destruct(SchemaInstanceArguments.generated_arguments start args tail observations HstartMeta HstartToken HstartPending HstartError Hwords Hlength HstartInput)
 as (_ & Hvector & Hin & Hout & Hclear & Hvalid).
 unfold final,finished. fold countState start.
 split;[exact Hvector|]. split;[exact Hin|]. split.
 - rewrite Hout. unfold start,prepared,countState,counted. cbn [machine setMachine].
   change(stdout(ReadTokenExecution.read_result looked (decimalBytes(length args)) (SchemaInstanceArguments.wire args++tail))=stdout(machine f)). rewrite ReadTokenExecution.result_output. rewrite Houtput. unfold named,ReadName.result. apply ReadTokenExecution.result_output.
 - split;[exact Hclear|]. rewrite Hvalid.
   assert(HstartClass:meta_value(machine start)2=meta_value(machine f)2).
   { unfold start,prepared. cbn [machine setMachine]. rewrite meta_store_other by lia. unfold countState,counted.
     rewrite DecimalInput.encoded_meta_other by (try exact Hlooked;lia). rewrite Hcells by lia.
     unfold named,ReadName.result. rewrite ReadTokenExecution.result_meta_other by lia. reflexivity. }
   assert(HstartValid:meta_value(machine start)18=1).
   { unfold start,prepared. cbn [machine setMachine]. apply meta_store_same;exact Hcounted. }
   now rewrite HstartClass,HstartValid.
Qed.
End NativeWhitespaceSchemaFacts.
