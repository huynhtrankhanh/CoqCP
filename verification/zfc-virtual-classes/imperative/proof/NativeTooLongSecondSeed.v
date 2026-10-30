From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat DecimalInput NativeTokenTooLong NativeTooLongSeed SeedInput Startup NativeBadSeed.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeTooLongSecondSeed.
Import IndexExecution SipHashExecution SeedInputExecution StartupExecution NativeBadSeed.
Lemma second_invalid reader (f:Frame) first after :
 exec(reader (fun _=>false)(fun _=>0))(machine f)=Some(tt,first) ->
 (26<length(memory first arraydef_0__meta))%nat -> meta_value first 14<>0 ->
 exec(reader (fun _=>false)(fun _=>0))(store_meta first 26 (meta_value first 11))=Some(tt,after) ->
 (14<length(memory after arraydef_0__meta))%nat -> meta_value after 14=0 ->
 execLocal(body_with reader)f=Some(tt,setMachine f(store_meta after 8 1)).
Proof.
 intros Hfirst Hmfirst Hvalidfirst Hsecond Hmsecond Hinvalid.
 destruct f as [s bs ns]. cbn [machine] in Hfirst. unfold body_with.
 repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite local_done |rewrite Hfirst |rewrite Hsecond
  |rewrite local_read_meta by (cbn [machine setMachine];lia)
  |rewrite local_put_meta by (cbn [machine setMachine];lia)
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 26) with 26%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [rewrite (bool_decide_true P) by congruence|rewrite (bool_decide_false P) by congruence] end
  |progress cbn [bind optionBind fst snd]
  |progress cbv beta iota zeta delta [machine setMachine nums bools]].
 reflexivity.
Qed.
Theorem generated_too_long_second_seed s bs ns key0 chars ch tail observations :
 (27<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 -> Z.of_nat key0<=maximum -> length chars=1024%nat ->
 Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars -> 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 stdin s=decimalBytes key0++32::chars++ch::tail ->
 exists final, execObserved(funcdef_0__main bs ns)(s,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.seed_prompt;unreadInput:=stdin s|};
 {|flushedOutput:=stdout s++Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=stdout s++Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hmeta Htoken Hpending Herror Hkey Hlength Hbytes Hch Hnosep Hinput.
 set(before:=withOutput s(stdout s++Protocol.seed_prompt)).
 set(first:=DecimalInput.encoded_result before key0 (chars++ch::tail)).
 set(next:=store_meta first 26 (meta_value first 11)).
 set(tokenstate:=NativeTokenTooLong.result next chars tail).
 set(parsed:=store_meta tokenstate 11 0).
 set(failed:=store_meta parsed 8 1).
 assert(Hfirstmeta:(27<length(memory first arraydef_0__meta))%nat).
 { unfold first. rewrite DecimalInput.encoded_meta_length. exact Hmeta. }
 assert(Hnextmeta:(27<length(memory next arraydef_0__meta))%nat) by (unfold next;rewrite store_meta_length;exact Hfirstmeta).
 assert(Hfirst:exec(funcdef_0__readNat (fun _=>false)(fun _=>0))before=Some(tt,first)).
 { unfold first. exact(DecimalInput.generated_readNat_encoded before (fun _=>false)(fun _=>0) key0 32 (chars++ch::tail) ltac:(change (17<length(memory s arraydef_0__meta))%nat;lia) Htoken Hpending Herror Hkey ltac:(unfold TokenByteExecution.separator;tauto) Hinput). }
 assert(Hvalidfirst:meta_value first 14<>0).
 { unfold first. rewrite encoded_valid by (change (17<length(memory s arraydef_0__meta))%nat;lia). discriminate. }
 assert(Hsecond:exec(funcdef_0__readNat (fun _=>false)(fun _=>0))next=Some(tt,parsed)).
 { unfold parsed,tokenstate. apply(NativeTooLongSeed.generated_readNat next (fun _=>false)(fun _=>0) chars ch tail);try assumption.
   - lia.
   - unfold next. rewrite store_meta_other by discriminate. unfold first. rewrite DecimalInput.encoded_token_length. exact Htoken.
   - unfold next. rewrite meta_store_other by lia. unfold first. rewrite DecimalInput.encoded_meta_other by (try lia;change (17<length(memory s arraydef_0__meta))%nat;lia). exact Hpending.
   - unfold next. rewrite meta_store_other by lia. unfold first. rewrite DecimalInput.encoded_meta_other by (try lia;change (17<length(memory s arraydef_0__meta))%nat;lia). exact Herror.
   - reflexivity. }
 assert(Hparsedmeta:(14<length(memory parsed arraydef_0__meta))%nat).
 { unfold parsed,tokenstate,NativeTokenTooLong.result. change(14<length(memory(store_meta(store_meta(ReadTokenExecution.put_many(ReadTokenExecution.reset next)0 chars)8 1%Z)11 0%Z)arraydef_0__meta))%nat.
   rewrite !store_meta_length,ReadTokenExecution.put_many_meta_length,ReadTokenExecution.reset_length. lia. }
 assert(Hparsedinvalid:meta_value parsed 14=0).
 { unfold parsed,tokenstate,NativeTokenTooLong.result. change(meta_value(store_meta(store_meta(ReadTokenExecution.put_many(ReadTokenExecution.reset next)0 chars)8 1)11 0)14=0).
   rewrite !meta_store_other by lia. rewrite ReadTokenExecution.put_many_meta_other by lia. rewrite ReadTokenExecution.reset_meta by lia. reflexivity. }
 assert(Hseed:exec(seed_program bs ns)before=Some(tt,failed)).
 { unfold seed_program. rewrite exec_eliminate,actual_body.
   rewrite(second_invalid funcdef_0__readNat {|machine:=before;bools:=bs;nums:=ns|} first parsed Hfirst ltac:(lia) Hvalidfirst Hsecond Hparsedmeta Hparsedinvalid). reflexivity. }
 assert(Hfailedmeta:(8<length(memory failed arraydef_0__meta))%nat) by (unfold failed;rewrite store_meta_length;lia).
 assert(Hfailedflag:meta_value failed 8<>0) by (unfold failed;rewrite meta_store_same by lia;discriminate).
 assert(Hin:stdin failed=tail) by reflexivity.
 assert(Hout:stdout failed=stdout s++Protocol.seed_prompt).
 { unfold failed,parsed,tokenstate,NativeTokenTooLong.result.
   change(stdout(ReadTokenExecution.put_many(ReadTokenExecution.reset next)0 chars)=stdout s++Protocol.seed_prompt).
   rewrite NativeTooLongSeed.put_many_output. unfold next. change(stdout first=stdout s++Protocol.seed_prompt).
   unfold first. rewrite (proj2(proj2(DecimalInput.encoded_result_correct before key0 (chars++ch::tail) ltac:(change (17<length(memory s arraydef_0__meta))%nat;lia) Hkey))). reflexivity. }
 rewrite observed_main_factorization,generated_prompt_observed. fold before.
 cbn [optionBind fst snd]. rewrite(observed_plain (seed_program bs ns) before (observations++[{|flushedOutput:=stdout s++Protocol.seed_prompt;unreadInput:=stdin s|}]) tt failed (seed_no_flush bs ns) Hseed).
 cbn [optionBind fst snd]. rewrite actual_finish,finish_bad by assumption. rewrite generated_err,Hin,Hout.
 exists(withOutput failed(stdout s++Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR)).
 split;[repeat rewrite <-List.app_assoc;reflexivity|]. split;[reflexivity|exact Hin].
Qed.
Theorem actual_too_long_second_seed bs ns key0 chars ch tail :
 Z.of_nat key0<=maximum -> length chars=1024%nat ->
 Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars -> 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 exists final,execObserved(funcdef_0__main bs ns)
 ({|memory:=arrays _ environment1;stdin:=decimalBytes key0++32::chars++ch::tail;stdout:=[]|},[])=
 Some(tt,(final,[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=decimalBytes key0++32::chars++ch::tail|};
 {|flushedOutput:=Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hkey Hlength Hbytes Hch Hnosep.
 exact(generated_too_long_second_seed {|memory:=arrays _ environment1;stdin:=decimalBytes key0++32::chars++ch::tail;stdout:=[]|}
  bs ns key0 chars ch tail [] ltac:(cbn;lia) ltac:(cbn;lia) eq_refl eq_refl Hkey Hlength Hbytes Hch Hnosep eq_refl).
Qed.
End NativeTooLongSecondSeed.
