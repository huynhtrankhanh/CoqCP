From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ReadNatInvalid SeedInput Startup.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeBadSeed.
Import IndexExecution SipHashExecution SeedInputExecution StartupExecution.
Lemma seed_invalid reader (f:Frame) after :
 exec(reader (fun _=>false)(fun _=>0))(machine f)=Some(tt,after) ->
 (14<length(memory after arraydef_0__meta))%nat -> meta_value after 14=0 ->
 execLocal(body_with reader)f=Some(tt,setMachine f(store_meta after 8 1)).
Proof.
 intros Hreader Hmeta Hinvalid. destruct f as [s bs ns]. cbn [machine] in *.
 unfold body_with.
 repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite local_done |rewrite Hreader
  |rewrite local_read_meta by (cbn [machine setMachine];lia)
  |rewrite local_put_meta by (cbn [machine setMachine];lia)
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [rewrite (bool_decide_true P) by congruence|rewrite (bool_decide_false P) by congruence] end
  |progress cbn [bind optionBind fst snd]
  |progress cbv beta iota zeta delta [machine setMachine nums bools]].
 reflexivity.
Qed.
Lemma finish_bad error success s bs ns observations :
 (8<length(memory s arraydef_0__meta))%nat -> meta_value s 8<>0 ->
 execObserved(eliminateLocalVariables bs ns(finish_with error success))(s,observations)=
 execObserved(eliminateLocalVariables bs ns error)(s,observations).
Proof.
 intros Hmeta Hflag. unfold finish_with.
 cbn [bind eliminateLocalVariables Action_rect retrieve execObserved observedStep step optionBind fst snd].
 unfold observedStep at 1. cbn [step optionBind fst snd].
 case_decide;[|lia]. rewrite nth_lt_default with(default:=0%Z).
 replace(Z.to_nat 8)with 8%nat by reflexivity. cbn [optionBind fst snd].
 change(execObserved(eliminateLocalVariables bs ns
  ((if bool_decide(meta_value s 8<>0)then error else success)>>=fun _=>Done _ _ _ tt))(s,observations)=
  execObserved(eliminateLocalVariables bs ns error)(s,observations)).
 rewrite(bool_decide_true _) by exact Hflag.
 rewrite observed_local_bind. cbn [execObserved eliminateLocalVariables].
 destruct(execObserved(eliminateLocalVariables bs ns error)(s,observations))as[[[] after]|];reflexivity.
Qed.
Lemma generated_err s bs ns observations :
 execObserved(eliminateLocalVariables bs ns error_body)(s,observations)=
 Some(tt,(withOutput s(stdout s++Protocol.reply_bytes Protocol.ERR),
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR; unreadInput:=stdin s|}])).
Proof.
 destruct s as [values input output]. unfold error_body.
 cbv beta iota zeta delta [loopString dropWithinLoop liftToWithinLoop liftToWithLocalVariables Action_rect bind writeChar flush eliminateLocalVariables execObserved observedStep step optionBind fst snd withOutput stdout stdin memory Protocol.reply_bytes].
 repeat rewrite <-List.app_assoc. reflexivity.
Qed.
Theorem generated_bad_first_seed s bs ns prefix bad suffix sep tail observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 ->
 (length(prefix++bad::suffix)<=1024)%nat ->
 Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)(prefix++bad::suffix) ->
 TokenByteExecution.separator sep -> stdin s=(prefix++bad::suffix)++sep::tail ->
 Forall(fun ch=>48<=ch<=57)prefix -> ReadNatExecution.number_from 0 prefix<=maximum ->
 (bad<48 \/ 57<bad) ->
 exists final, execObserved(funcdef_0__main bs ns)(s,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.seed_prompt;unreadInput:=stdin s|};
 {|flushedOutput:=stdout s++Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=stdout s++Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hsep Hinput Hdigits Hbound Hbad.
 set(before:=withOutput s(stdout s++Protocol.seed_prompt)).
 set(tokenstate:=ReadTokenExecution.read_result before (prefix++bad::suffix) tail).
 set(parsed:=store_meta(store_meta tokenstate 14 0)11(ReadNatExecution.number_from 0 prefix)).
 set(failed:=store_meta parsed 8 1).
 assert(Hread:exec(funcdef_0__readNat (fun _=>false)(fun _=>0))before=Some(tt,parsed)).
 { unfold parsed,tokenstate. apply(ReadNatInvalid.generated_bad_token before (fun _=>false)(fun _=>0) prefix bad suffix sep tail);try assumption. }
 assert(Hparsedmeta:(14<length(memory parsed arraydef_0__meta))%nat).
 { unfold parsed,tokenstate. rewrite !store_meta_length,ReadTokenExecution.result_meta_length. change (14<length(memory s arraydef_0__meta))%nat. lia. }
 assert(Hparsedinvalid:meta_value parsed 14=0).
 { unfold parsed. rewrite meta_store_other by lia. apply meta_store_same. unfold tokenstate. rewrite ReadTokenExecution.result_meta_length. change (14<length(memory s arraydef_0__meta))%nat. lia. }
 assert(Hseed:exec(seed_program bs ns)before=Some(tt,failed)).
 { unfold seed_program. rewrite exec_eliminate,actual_body.
   rewrite(seed_invalid funcdef_0__readNat {|machine:=before;bools:=bs;nums:=ns|} parsed Hread Hparsedmeta Hparsedinvalid).
   reflexivity. }
 assert(Hfailedmeta:(8<length(memory failed arraydef_0__meta))%nat).
 { unfold failed. rewrite store_meta_length. lia. }
 assert(Hfailedflag:meta_value failed 8<>0).
 { unfold failed. rewrite meta_store_same by lia. discriminate. }
 assert(Hin:stdin failed=tail) by reflexivity.
 assert(Hout:stdout failed=stdout s++Protocol.seed_prompt).
 { unfold failed,parsed,tokenstate. change(stdout(ReadTokenExecution.read_result before (prefix++bad::suffix) tail)=stdout s++Protocol.seed_prompt).
   rewrite ReadTokenExecution.result_output. reflexivity. }
 rewrite observed_main_factorization,generated_prompt_observed.
 fold before.
 cbn [optionBind fst snd]. rewrite(observed_plain (seed_program bs ns) before (observations++[{|flushedOutput:=stdout s++Protocol.seed_prompt;unreadInput:=stdin s|}]) tt failed (seed_no_flush bs ns) Hseed).
 cbn [optionBind fst snd]. rewrite actual_finish,finish_bad by assumption. rewrite generated_err,Hin,Hout.
 exists(withOutput failed(stdout s++Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR)).
 split;[repeat rewrite <-List.app_assoc;reflexivity|]. split;[reflexivity|exact Hin].
Qed.
Theorem actual_bad_first_seed bs ns prefix bad suffix sep tail :
 (length(prefix++bad::suffix)<=1024)%nat ->
 Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)(prefix++bad::suffix) ->
 TokenByteExecution.separator sep -> Forall(fun ch=>48<=ch<=57)prefix ->
 ReadNatExecution.number_from 0 prefix<=maximum -> (bad<48 \/ 57<bad) ->
 exists final,execObserved(funcdef_0__main bs ns)
 ({|memory:=arrays _ environment1;stdin:=(prefix++bad::suffix)++sep::tail;stdout:=[]|},[])=
 Some(tt,(final,[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=(prefix++bad::suffix)++sep::tail|};
 {|flushedOutput:=Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.seed_prompt++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hlength Hbytes Hsep Hdigits Hbound Hbad.
 exact(generated_bad_first_seed {|memory:=arrays _ environment1;stdin:=(prefix++bad::suffix)++sep::tail;stdout:=[]|}
  bs ns prefix bad suffix sep tail [] ltac:(cbn;lia) ltac:(cbn;lia) eq_refl eq_refl Hlength Hbytes Hsep eq_refl Hdigits Hbound Hbad).
Qed.
End NativeBadSeed.
