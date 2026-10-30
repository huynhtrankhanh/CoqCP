From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ReadNatInvalid ReadNatOverflow ReadTokenPendingLeading NativeByteNumber NativeByteBadDigit NativeByteOverflowEOF NativePendingSeparatorTokenInfo NativeMalformedCommand NativeTooLongSeed ObservedLocal CommandQuit.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativePendingSeparatorMalformed.
Import IndexExecution SipHashExecution ReadTokenExecution ReadNatExecution ReadTokenPendingLeading.
Definition parsed s chars tail prefix := store_meta(store_meta(pending_separator_result s chars tail)14 0)11(number_from 0 prefix).
Theorem generated s bs ns ch chars spaces sep tail prefix bad suffix observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> 0<=ch<256 -> TokenByteExecution.separator ch ->
 (0<length chars<=1024)%nat -> Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars ->
 Forall TokenByteExecution.separator spaces -> TokenByteExecution.separator sep -> stdin s=spaces++chars++sep::tail ->
 prefix++bad::suffix=chars -> Forall(fun c=>48<=c<=57)prefix -> number_from 0 prefix<=maximum ->
 ((bad<48 \/ 57<bad) \/ (48<=bad<=57 /\ maximum<10*(number_from 0 prefix)+(bad-48))) ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (NativeMalformedCommand.final(parsed s chars tail prefix),observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])).
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hsep0 Hlength Hbytes Hspaces Hsep Hinput Hencoding Hdigits Hbound Hbad.
 destruct(NativePendingSeparatorTokenInfo.generated s ch chars spaces sep tail Hmeta Htoken Hpending Herror Hch Hsep0 Hlength Hbytes Hspaces Hsep Hinput)
  as(Hreader & Htargetmeta & Hvalid & Hcount & Hcapacity & Hentries & Hclear & Htail).
 set(target:=pending_separator_result s chars tail) in *.
 assert(Hbadbyte:0<=bad<256).
 { apply Forall_forall with (x:=bad) in Hbytes;[tauto|]. rewrite <-Hencoding. apply in_or_app. right. now left. }
 assert(Hnumeric:exec(funcdef_0__readNat (fun _=>false)(fun _=>0))s=Some(tt,parsed s chars tail prefix)).
 { unfold parsed. fold target. rewrite <-Hencoding in Hcount,Hcapacity,Hentries.
   destruct Hbad as [Hbad|[Hbad Hoverflow]].
   - exact(ReadNatInvalid.generated_readNat_nondigit s (fun _=>false)(fun _=>0) target prefix bad suffix Hreader Htargetmeta Hvalid Hcount Hcapacity Hentries Hdigits Hbound Hbadbyte Hbad).
   - exact(ReadNatOverflow.generated_readNat_overflow s (fun _=>false)(fun _=>0) target prefix bad suffix Hreader Htargetmeta Hvalid Hcount Hcapacity Hentries Hdigits Hbound Hbad Hoverflow). }
 assert(Hparsedmeta:(17<length(memory(parsed s chars tail prefix)arraydef_0__meta))%nat).
 { unfold parsed. rewrite !store_meta_length,result_meta_length. exact Hmeta. }
 assert(Hnumber:meta_value(parsed s chars tail prefix)11=number_from 0 prefix).
 { unfold parsed. apply meta_store_same. rewrite store_meta_length,result_meta_length. lia. }
 assert(Hinvalid:meta_value(parsed s chars tail prefix)14=0).
 { unfold parsed. rewrite meta_store_other by lia. apply meta_store_same. rewrite result_meta_length. lia. }
 assert(Hnonempty:meta_value(parsed s chars tail prefix)6<>0).
 { unfold parsed. rewrite !meta_store_other by lia. rewrite result_count by exact Hmeta.
   intro Hz. change (Z.of_nat(length chars)=Z.of_nat 0) in Hz. apply Nat2Z.inj in Hz. lia. }
 assert(Hout:stdout(parsed s chars tail prefix)=stdout s).
 { unfold parsed,pending_separator_result. change(stdout(put_many(pending_base s)0 chars)=stdout s).
   rewrite NativeTooLongSeed.put_many_output. reflexivity. }
 assert(Hin:stdin(parsed s chars tail prefix)=tail) by reflexivity.
 set(f:={|machine:=s;bools:=bs;nums:=ns|}:CommandQuitExecution.Frame).
 unfold funcdef_0__command. rewrite ObservedLocal.eliminate_correct,CommandQuitExecution.actual_body. fold f.
 pose proof(NativeMalformedCommand.generated_body funcdef_0__readNat f (parsed s chars tail prefix) (number_from 0 prefix) observations
  ltac:(now apply generated_readNat_observed) Hparsedmeta Hnumber Hinvalid Hnonempty) as Hrun.
 unfold CommandQuitExecution.Frame in Hrun. rewrite Hrun,Hout,Hin. reflexivity.
Qed.
End NativePendingSeparatorMalformed.
