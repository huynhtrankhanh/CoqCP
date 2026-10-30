From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat NativeTokenTooLong SeedInput Startup NativeBadSeed.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeTooLongSeed.
Import IndexExecution SipHashExecution SeedInputExecution StartupExecution NativeBadSeed.
Lemma invalid_number reader digits (f:ReadNatExecution.Frame) after :
 exec(reader (fun _=>false)(fun _=>0))(machine f)=Some(tt,after) ->
 (14<length(memory after arraydef_0__meta))%nat -> meta_value after 14=0 ->
 execLocal(ReadNatExecution.body_with reader digits) f=Some(tt,setMachine (setNum f vardef_0__readNat_value 0)(store_meta after 11 0)).
Proof.
 intros Hreader Hmeta Hinvalid. destruct f as [s bs ns]. cbn [machine] in *.
 unfold ReadNatExecution.body_with.
 repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite ReadNatExecution.local_done
  |rewrite ReadNatExecution.local_get |rewrite ReadNatExecution.local_set |rewrite Hreader |rewrite Hinvalid
  |rewrite local_read_meta by (cbn [machine setMachine];lia)
  |rewrite local_put_meta by (cbn [machine setMachine];lia)
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [rewrite (bool_decide_true P) by congruence|rewrite (bool_decide_false P) by congruence] end
  |progress cbn [bind optionBind fst snd]
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]].
 unfold update. case_decide; [reflexivity|contradiction].
Qed.
Theorem generated_readNat s bs ns chars ch tail :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 -> length chars=1024%nat ->
 Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars -> 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 stdin s=chars++ch::tail ->
 exec(funcdef_0__readNat bs ns)s=Some(tt,store_meta(NativeTokenTooLong.result s chars tail)11 0).
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hch Hnosep Hinput.
 set(after:=NativeTokenTooLong.result s chars tail).
 assert(Hreader:exec(funcdef_0__readToken (fun _=>false)(fun _=>0))s=Some(tt,after)).
 { unfold after. exact(NativeTokenTooLong.generated_readToken s (fun _=>false) (fun _=>0) chars ch tail Hmeta Htoken Hpending Herror Hlength Hbytes Hch Hnosep Hinput). }
 assert(Hafter:(14<length(memory after arraydef_0__meta))%nat).
 { unfold after,NativeTokenTooLong.result. change(14<length(memory(store_meta(ReadTokenExecution.put_many(ReadTokenExecution.reset s)0 chars)8 1%Z)arraydef_0__meta))%nat.
   rewrite store_meta_length,ReadTokenExecution.put_many_meta_length,ReadTokenExecution.reset_length. lia. }
 assert(Hinvalid:meta_value after 14=0).
 { unfold after,NativeTokenTooLong.result. change(meta_value(store_meta(ReadTokenExecution.put_many(ReadTokenExecution.reset s)0 chars)8 1)14=0).
   rewrite meta_store_other by lia. rewrite ReadTokenExecution.put_many_meta_other by lia.
   rewrite ReadTokenExecution.reset_meta by exact Hmeta. reflexivity. }
 unfold funcdef_0__readNat. rewrite exec_eliminate,ReadNatExecution.actual_body.
 rewrite(invalid_number funcdef_0__readToken ReadNatExecution.digit_loop {|machine:=s;bools:=bs;nums:=ns|} after Hreader Hafter Hinvalid). reflexivity.
Qed.
Lemma put_many_output s size chars : stdout(ReadTokenExecution.put_many s size chars)=stdout s.
Proof. induction chars as [|ch rest IH] in s,size|-*;[reflexivity|]. cbn [ReadTokenExecution.put_many]. rewrite IH. reflexivity. Qed.
Theorem generated_too_long_first_seed s bs ns chars ch tail observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 -> length chars=1024%nat ->
 Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars -> 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 stdin s=chars++ch::tail ->
 exists final, execObserved(funcdef_0__main bs ns)(s,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.seed_prompt;unreadInput:=stdin s|};
 {|flushedOutput:=stdout s++Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=stdout s++Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hch Hnosep Hinput.
 set(before:=withOutput s(stdout s++Protocol.seed_prompt)).
 set(tokenstate:=NativeTokenTooLong.result before chars tail).
 set(parsed:=store_meta tokenstate 11 0).
 set(failed:=store_meta parsed 8 1).
 assert(Hread:exec(funcdef_0__readNat (fun _=>false)(fun _=>0))before=Some(tt,parsed)).
 { unfold parsed,tokenstate. exact(generated_readNat before (fun _=>false)(fun _=>0) chars ch tail Hmeta Htoken Hpending Herror Hlength Hbytes Hch Hnosep Hinput). }
 assert(Hparsedmeta:(14<length(memory parsed arraydef_0__meta))%nat).
 { unfold parsed,tokenstate,NativeTokenTooLong.result. change(14<length(memory(store_meta(store_meta(ReadTokenExecution.put_many(ReadTokenExecution.reset before)0 chars)8 1%Z)11 0%Z)arraydef_0__meta))%nat.
   rewrite !store_meta_length,ReadTokenExecution.put_many_meta_length,ReadTokenExecution.reset_length. change(14<length(memory s arraydef_0__meta))%nat. lia. }
 assert(Hparsedinvalid:meta_value parsed 14=0).
 { unfold parsed,tokenstate,NativeTokenTooLong.result. change(meta_value(store_meta(store_meta(ReadTokenExecution.put_many(ReadTokenExecution.reset before)0 chars)8 1)11 0)14=0).
   rewrite !meta_store_other by lia. rewrite ReadTokenExecution.put_many_meta_other by lia. rewrite ReadTokenExecution.reset_meta by exact Hmeta. reflexivity. }
 assert(Hseed:exec(seed_program bs ns)before=Some(tt,failed)).
 { unfold seed_program. rewrite exec_eliminate,actual_body.
   rewrite(seed_invalid funcdef_0__readNat {|machine:=before;bools:=bs;nums:=ns|} parsed Hread Hparsedmeta Hparsedinvalid). reflexivity. }
 assert(Hfailedmeta:(8<length(memory failed arraydef_0__meta))%nat).
 { unfold failed. rewrite store_meta_length. lia. }
 assert(Hfailedflag:meta_value failed 8<>0).
 { unfold failed. rewrite meta_store_same by lia. discriminate. }
 assert(Hin:stdin failed=tail) by reflexivity.
 assert(Hout:stdout failed=stdout s++Protocol.seed_prompt).
 { unfold failed,parsed,tokenstate,NativeTokenTooLong.result.
   change(stdout(ReadTokenExecution.put_many(ReadTokenExecution.reset before)0 chars)=stdout s++Protocol.seed_prompt).
   rewrite put_many_output. reflexivity. }
 rewrite observed_main_factorization,generated_prompt_observed. fold before.
 cbn [optionBind fst snd]. rewrite(observed_plain (seed_program bs ns) before (observations++[{|flushedOutput:=stdout s++Protocol.seed_prompt;unreadInput:=stdin s|}]) tt failed (seed_no_flush bs ns) Hseed).
 cbn [optionBind fst snd]. rewrite actual_finish,finish_bad by assumption. rewrite generated_err,Hin,Hout.
 exists(withOutput failed(stdout s++Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR)).
 split;[repeat rewrite <-List.app_assoc;reflexivity|]. split;[reflexivity|exact Hin].
Qed.
Theorem actual_too_long_first_seed bs ns chars ch tail :
 length chars=1024%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 exists final,execObserved(funcdef_0__main bs ns)
 ({|memory:=arrays _ environment1;stdin:=chars++ch::tail;stdout:=[]|},[])=
 Some(tt,(final,[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=chars++ch::tail|};
 {|flushedOutput:=Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hlength Hbytes Hch Hnosep.
 exact(generated_too_long_first_seed {|memory:=arrays _ environment1;stdin:=chars++ch::tail;stdout:=[]|}
  bs ns chars ch tail [] ltac:(cbn;lia) ltac:(cbn;lia) eq_refl eq_refl Hlength Hbytes Hch Hnosep eq_refl).
Qed.
End NativeTooLongSeed.
