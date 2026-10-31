From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat CommandInput CommandArgs NativeMissingNumberEOF NativeReadTokenLeadingMissing NativeMalformedUnaryCommand NativeMalformedFirstArgumentCommand NativeMalformedFirstArgumentHandlers.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeMissingFirstArgument.
Import IndexExecution SipHashExecution ReadTokenExecution ReadNatExecution.
Definition argument op := store_meta(NativeReadTokenLeadingMissing.result op)11 0.
Theorem generated s bs ns opcode digit digits separator spaces observations :
 NativeMalformedFirstArgumentHandlers.supported (Z.of_nat opcode) -> Z.of_nat opcode<=maximum -> decimalBytes opcode=digit::digits ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=digit+1 -> meta_value s 8=0 -> TokenByteExecution.separator separator ->
 Forall TokenByteExecution.separator spaces -> stdin s=digits++separator::spaces ->
 exists final, execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (final, observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}])) /\
 stdin final=[] /\ stdout final=stdout s++Protocol.reply_bytes Protocol.ERR /\ meta_value final 9=1 /\
 (9<length(memory final arraydef_0__meta))%nat.
Proof.
 intros Hsupported Hword Hopencoding Hmeta Htoken Hpending Herror Hsep Hspaces Hinput.
 set(op:=CommandInput.parsed s digit digits spaces).
 assert(Hopcode:execObserved(funcdef_0__readNat(fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations))).
 { unfold op. eapply(CommandInput.generated_pending s (fun _=>false)(fun _=>0) opcode digit digits separator spaces observations);try assumption;
   assumption. }
 assert(Hopmeta:(17<length(memory op arraydef_0__meta))%nat) by (unfold op;rewrite CommandInput.parsed_meta_length;exact Hmeta).
 assert(Hoptoken:(1024<=length(memory op arraydef_0__token))%nat) by (unfold op;rewrite CommandArgs.pending_token_length;exact Htoken).
 assert(Hoppending:meta_value op 15=0) by (unfold op;apply CommandArgs.pending_cleared;exact Hmeta).
 assert(Hopvalid:meta_value op 14=1) by (unfold op;apply CommandInput.parsed_valid;exact Hmeta).
 assert(Hopnumber:meta_value op 11=Z.of_nat opcode) by (unfold op;now apply CommandInput.parsed_number).
 assert(Hoperror:meta_value op 8=0) by (unfold op;rewrite CommandInput.parsed_meta_other by lia;exact Herror).
 assert(Hopin:stdin op=spaces) by reflexivity.
 set(tok:=NativeReadTokenLeadingMissing.result op).
 assert(Htokenrun:exec(funcdef_0__readToken(fun _=>false)(fun _=>0))op=Some(tt,tok)) by (unfold tok;now apply NativeReadTokenLeadingMissing.generated_token with (prefix:=spaces)).
 assert(Htokmeta:(17<length(memory tok arraydef_0__meta))%nat).
 { unfold tok,NativeReadTokenLeadingMissing.result. rewrite store_meta_length. change(17<length(memory(reset op)arraydef_0__meta))%nat. now rewrite reset_length. }
 assert(Htokvalid:meta_value tok 14=0).
 { unfold tok,NativeReadTokenLeadingMissing.result. rewrite meta_store_other by lia. change(meta_value(reset op)14=0). rewrite reset_meta by exact Hopmeta. reflexivity. }
 assert(Harg:execObserved(funcdef_0__readNat(fun _=>false)(fun _=>0))(op,observations)=Some(tt,(argument op,observations))).
 { apply ReadNatExecution.generated_readNat_observed. unfold argument,funcdef_0__readNat. rewrite exec_eliminate,ReadNatExecution.actual_body.
   rewrite(NativeMissingNumberEOF.invalid_composition funcdef_0__readToken ReadNatExecution.digit_loop {|machine:=op;bools:=fun _=>false;nums:=fun _=>0|} tok Htokenrun ltac:(lia) Htokvalid). reflexivity. }
 assert(Hargmeta:(17<length(memory(argument op)arraydef_0__meta))%nat) by (unfold argument;rewrite store_meta_length;exact Htokmeta).
 assert(Hargnumber:meta_value(argument op)11=0) by (unfold argument;apply meta_store_same; change(11<length(memory tok arraydef_0__meta))%nat;lia).
 assert(Hargvalid:meta_value(argument op)14=0) by (unfold argument;rewrite meta_store_other by lia;exact Htokvalid).
 pose proof(NativeMalformedFirstArgumentCommand.generated s bs ns op (argument op) (Z.of_nat opcode) 0 observations Hsupported Hopcode Hopmeta Hopnumber Hopvalid Hoperror Harg Hargmeta Hargnumber Hargvalid) as Hrun.
 assert(Hout:stdout(argument op)=stdout s).
 { unfold argument,NativeReadTokenLeadingMissing.result. change(stdout(reset op)=stdout s). change(stdout op=stdout s). unfold op;apply CommandInput.parsed_output. }
 exists(NativeMalformedFirstArgumentCommand.final(argument op)). rewrite Hout in Hrun. split;[exact Hrun|].
 split;[reflexivity|]. split;[change(stdout(argument op)++Protocol.reply_bytes Protocol.ERR=stdout s++Protocol.reply_bytes Protocol.ERR);now rewrite Hout|].
 split.
 - unfold NativeMalformedFirstArgumentCommand.final. apply meta_store_same. cbn [memory withOutput]. unfold NativeMalformedFirstArgumentCommand.failed. rewrite store_meta_length. lia.
 - unfold NativeMalformedFirstArgumentCommand.final. rewrite store_meta_length. cbn [memory withOutput]. unfold NativeMalformedFirstArgumentCommand.failed. rewrite store_meta_length. lia.
Qed.
End NativeMissingFirstArgument.
