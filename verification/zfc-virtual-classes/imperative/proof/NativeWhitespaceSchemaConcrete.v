From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl CommandChain CommandStructure
 NativeWhitespaceSchemaPrefix ReadTokenLeading NativeArgumentReadsFour NativeWhitespaceSchemaArguments SchemaInstancePrefix SchemaInstanceArguments SchemaEvaluationArguments SchemaInstanceHandler ReadName ReadToken TokenByte ReadFour DecimalInput NameSearch NameRepresentation TypedNameLookup FormulaProjection Representation ClassStorage HistoryRefinement SchemaRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaConcrete.
Import IndexExecution SipHashExecution ObservedLocal SchemaInstancePrefix NativeWhitespaceSchemaPrefix.
Definition named_spaced (f:Frame) name fields countspaces countsep tail := ReadName.result (machine f) name
 (countspaces++decimalBytes(length fields)++countsep::(NativeWhitespaceSchemaArguments.spaced_wire fields++tail)).
Definition counted_spaced looked fields tail := DecimalInput.encoded_result looked (length fields) (NativeWhitespaceSchemaArguments.spaced_wire fields++tail).
Definition finished_spaced (f:Frame) looked fields tail := SchemaInstanceArguments.consume
 (prepared f looked (counted_spaced looked fields tail) (length fields)) 0 (map snd fields) tail.
Theorem generated_spaced (f:Frame) bindings name fields namespaces namesep countspaces countsep tail (work:LocalAction unit) observations :
 (18<length(memory(machine f)arraydef_0__meta))%nat -> (1024<=length(memory(machine f)arraydef_0__token))%nat ->
 meta_value(machine f)15=0 -> meta_value(machine f)8=0 -> NameRepresentation.represents(machine f)bindings -> Protocol.valid_name name ->
 Forall(fun item=>Forall TokenByteExecution.separator(fst item) /\ Z.of_nat(snd item)<=maximum)fields -> Z.of_nat(length fields)<=maximum ->
 Forall TokenByteExecution.separator namespaces -> TokenByteExecution.separator namesep -> Forall TokenByteExecution.separator countspaces -> TokenByteExecution.separator countsep ->
 stdin(machine f)=namespaces++name++namesep::countspaces++decimalBytes(length fields)++countsep::(NativeWhitespaceSchemaArguments.spaced_wire fields++tail) ->
 exists looked, NameSearchExecution.storage_frame(named_spaced f name fields countspaces countsep tail)looked /\
 TypedNameLookup.outcome looked bindings name /\
 execLocalObserved(with_suffix work)(f,observations)=execLocalObserved work(finished_spaced f looked fields tail,observations) /\
 length(memory looked arraydef_0__meta)=length(memory(named_spaced f name fields countspaces countsep tail)arraydef_0__meta).
Proof.
 intros Hmeta Htoken Hpending Herror Hbindings Hname Hfields Hlength Hns Hnsep Hcs Hcsep Hin.
 set(rest:=countspaces++decimalBytes(length fields)++countsep::(NativeWhitespaceSchemaArguments.spaced_wire fields++tail)).
 set(nameState:=named_spaced f name fields countspaces countsep tail).
 assert(HreadName:execObserved(funcdef_0__readToken(fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(nameState,observations))).
 { apply ReadTokenExecution.generated_readToken_observed. unfold nameState,named_spaced. fold rest.
   eapply ReadTokenLeading.generated_readToken_leading with (prefix:=namespaces) (sep:=namesep);try eassumption;try lia.
   - exact(proj1 Hname).
   - now apply ReadName.name_bytes. }
 assert(Hnamed:(18<length(memory nameState arraydef_0__meta))%nat) by (unfold nameState,named_spaced,ReadName.result;rewrite ReadTokenExecution.result_meta_length;exact Hmeta).
 assert(Hnamevalid:meta_value nameState 14=1) by (apply ReadTokenExecution.result_valid;lia).
 assert(Hnameerror:meta_value nameState 8=0) by (unfold nameState,named_spaced,ReadName.result;rewrite ReadTokenExecution.result_meta_other by lia;exact Herror).
 assert(Hnamepending:meta_value nameState 15=0) by (unfold nameState,named_spaced,ReadName.result;rewrite ReadTokenExecution.result_meta_other by lia;exact Hpending).
 assert(HnameToken:(1024<=length(memory nameState arraydef_0__token))%nat) by (unfold nameState,named_spaced;rewrite ReadName.token_length;exact Htoken).
 assert(HnameRep:NameRepresentation.represents nameState bindings) by (apply ReadName.bindings;[lia|exact Hbindings]).
 assert(HnameBytes:NameRepresentation.token_rep nameState name).
 { unfold nameState,named_spaced. apply(ReadName.token_rep (machine f) name rest ltac:(lia)). destruct Hname as [[Hpositive Hsize] _]. exact (Nat.le_trans _ _ _ Hsize Htoken). }
 destruct(TypedNameLookup.generated nameState (fun _=>false)(fun _=>0) bindings name observations ltac:(lia) HnameRep HnameBytes)
 as(looked & Hlookup & HlookRep & HlookLength & Hframe & Houtcome).
 assert(Hlooked:(18<length(memory looked arraydef_0__meta))%nat) by (rewrite HlookLength;exact Hnamed).
 destruct Hframe as [Harrays [Hcells [Hinput Houtput]]].
 assert(HlookError:meta_value looked 8=0) by (rewrite Hcells by lia;exact Hnameerror).
 assert(HlookPending:meta_value looked 15=0) by (rewrite Hcells by lia;exact Hnamepending).
 assert(HlookToken:(1024<=length(memory looked arraydef_0__token))%nat) by (rewrite Harrays by discriminate;exact HnameToken).
 assert(HlookInput:stdin looked=countspaces++decimalBytes(length fields)++countsep::(NativeWhitespaceSchemaArguments.spaced_wire fields++tail)).
 { rewrite Hinput. reflexivity. }
 destruct(NativeArgumentReadsFour.read_leading looked (length fields) countspaces countsep (NativeWhitespaceSchemaArguments.spaced_wire fields++tail) observations
   ltac:(lia) HlookToken HlookPending HlookError Hlength Hcsep Hcs HlookInput)
 as(Hcount & HcountToken & HcountPending & HcountInput & HcountOutput).
 destruct Hcount as [HcountRun [HcountMeta [HcountNumber [HcountValid HcountError]]]].
 exists looked. split;[unfold NameSearchExecution.storage_frame;repeat split;assumption|]. split;[exact Houtcome|]. split.
 - unfold finished_spaced,counted_spaced.
   pose proof(generated_prefix_spaced f nameState looked (DecimalInput.encoded_result looked (length fields) (NativeWhitespaceSchemaArguments.spaced_wire fields++tail)) (map snd fields) fields tail work observations
     Hmeta Herror HreadName Hnamed Hnamevalid Hnameerror Hlookup Hlooked HlookError HcountRun
     ltac:(rewrite DecimalInput.encoded_meta_length;exact Hlooked) HcountValid HcountError
     ltac:(rewrite length_map;exact HcountNumber) HcountPending HcountToken Hfields eq_refl
     ltac:(rewrite length_map;exact Hlength) HcountInput) as Hprefix.
   now rewrite length_map in Hprefix.
 - exact HlookLength.
Qed.
End NativeWhitespaceSchemaConcrete.
