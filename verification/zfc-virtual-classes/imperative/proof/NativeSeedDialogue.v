From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees Spec.
From NativeProof Require Import Index SipHash SeedInput SeedBootstrap SeedSeparator NativeVerifiedDomain TokenByte.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeSeedDialogue.
Import IndexExecution SipHashExecution SeedInputExecution.
Lemma observed_prepend {I T} `{EqDecision I} {R}
 (code:Action (WithArrays I T) withArraysReturnValue R) s prefix observations :
 execObserved code (s,prefix++observations) =
 option_map (fun result => (fst result,(fst (snd result),prefix++snd (snd result))))
   (execObserved code (s,observations)).
Proof.
 induction code as [value|effect next IH] in s,observations|-*;[reflexivity|].
 cbn [execObserved]. unfold observedStep. cbn [fst snd].
 destruct (step effect s) as [[value after]|];[|reflexivity]. cbn [optionBind fst snd].
 destruct effect as [basic|name index|name index assigned|name size zero];
  try (rewrite IH; destruct (execObserved (next value) (after,observations)) as [[result [final trace]]|];reflexivity).
 destruct basic; try (rewrite IH; destruct (execObserved (next value) (after,observations)) as [[result [final trace]]|];reflexivity).
 rewrite <-app_assoc,IH. destruct (execObserved (next value) (after,observations++[{|flushedOutput:=stdout s;unreadInput:=stdin s|}])) as [[result [final trace]]|];reflexivity.
Qed.
Definition alternate key0 key1 sep tail : Machine :=
 {|memory:=arrays _ environment1; stdin:=decimalBytes key0 ++ sep :: (decimalBytes key1 ++ 10 :: tail); stdout:=[]|}.
Theorem required key0 key1 sep requests bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> TokenByteExecution.separator sep ->
 Forall Protocol.shape requests -> NativeVerifiedDomain.within_capacity requests ->
 exists replies final logical remaining,
 Protocol.dialogue Protocol.initial requests replies logical remaining /\ Guarantees.safe logical /\
 execObserved (funcdef_0__main bs ns) (alternate key0 key1 sep (Protocol.wire requests),[]) =
 Some (tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=decimalBytes key0 ++ sep :: (decimalBytes key1 ++ 10 :: Protocol.wire requests)|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=Protocol.wire requests|}] ++
 Protocol.flush_schedule requests replies Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=remaining.
Proof.
 intros Hkey0 Hkey1 Hsep Hshape Hcapacity.
 destruct (NativeVerifiedDomain.required bs ns key0 key1 requests Hkey0 Hkey1 Hshape Hcapacity)
   as (replies & final & logical & remaining & Hdialogue & Hsafe & Hcanonical & Hout & Hin).
 set (wire:=Protocol.wire requests) in *.
 set (normal:=SeedBootstrapExecution.initial key0 key1 wire []).
 set (other:=alternate key0 key1 sep wire).
 set (before:=seed_result (SeedBootstrapExecution.initial key0 key1 wire Protocol.seed_prompt) key0 key1 wire).
 set (snapshot:={|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire|}).
 set (snapshot2:={|flushedOutput:=Protocol.seed_prompt;unreadInput:=decimalBytes key0 ++ sep :: (decimalBytes key1 ++ 10 :: wire)|}).
 set (ready:={|flushedOutput:=Protocol.handshake_output;unreadInput:=wire|}).
 assert (Hm:(27<length(memory normal arraydef_0__meta))%nat) by (change (27<32)%nat;lia).
 assert (Ht:(1024<=length(memory normal arraydef_0__token))%nat) by (change (1024<=1024)%nat;lia).
 assert (Hp:meta_value normal 15=0) by reflexivity.
 assert (He:meta_value normal 8=0) by reflexivity.
 pose proof (generated_main_seed_prefix normal bs ns key0 key1 wire [] Hm Ht Hp He Hkey0 Hkey1 eq_refl) as Hnorm.
 change (execObserved (funcdef_0__main bs ns) (normal,[]) =
   execObserved (eliminateLocalVariables bs ns finish_body) (before,[snapshot])) in Hnorm.
 assert (Hsame:seed_result (withOutput other (stdout other++Protocol.seed_prompt)) key0 key1 wire=before).
 { unfold before,other,alternate,SeedBootstrapExecution.initial.
   change (seed_result (withInput {|memory:=arrays _ environment1;stdin:=[];stdout:=Protocol.seed_prompt|}
      (decimalBytes key0 ++ sep :: (decimalBytes key1 ++ 10 :: wire))) key0 key1 wire =
    seed_result (withInput {|memory:=arrays _ environment1;stdin:=[];stdout:=Protocol.seed_prompt|}
      (Protocol.seed_bytes key0 key1++wire)) key0 key1 wire).
   now rewrite !SeedSeparator.seed_result_input. }
 assert (Hm2:(27<length(memory other arraydef_0__meta))%nat) by (change (27<32)%nat;lia).
 assert (Ht2:(1024<=length(memory other arraydef_0__token))%nat) by (change (1024<=1024)%nat;lia).
 assert (Hp2:meta_value other 15=0) by reflexivity.
 assert (He2:meta_value other 8=0) by reflexivity.
 pose proof (SeedSeparator.generated_main_seed_separator other bs ns key0 key1 sep wire [] Hm2 Ht2 Hp2 He2 Hkey0 Hkey1 Hsep eq_refl) as Halt.
 rewrite Hsame in Halt.
 change (execObserved (funcdef_0__main bs ns) (other,[]) =
   execObserved (eliminateLocalVariables bs ns finish_body) (before,[snapshot2])) in Halt.
 change (execObserved (funcdef_0__main bs ns) (normal,[]) =
   Some (tt,(final,[snapshot;ready]++Protocol.flush_schedule requests replies Protocol.handshake_output))) in Hcanonical.
 rewrite Hnorm in Hcanonical.
 pose proof (observed_prepend (eliminateLocalVariables bs ns finish_body) before [snapshot] []) as Hprepend.
 cbn [app] in Hprepend. rewrite Hprepend in Hcanonical.
 remember (execObserved (eliminateLocalVariables bs ns finish_body) (before,[])) as run eqn:Hbase.
 destruct run as [[value [actual trace]]|]; cbn [option_map fst snd] in Hcanonical;[|discriminate].
 injection Hcanonical as <- <- Htrace. cbn [app] in Htrace. injection Htrace as Htrace. subst trace.
 rewrite Halt. pose proof (observed_prepend (eliminateLocalVariables bs ns finish_body) before [snapshot2] []) as Hprepend2.
 cbn [app] in Hprepend2. rewrite Hprepend2,<-Hbase. cbn [option_map fst snd app].
 exists replies,final,logical,remaining. repeat first [assumption|split].
Qed.
End NativeSeedDialogue.
