From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash SeedInput SeedBootstrap SeedSeparator NativeSeedWhitespace NativeWhitespaceDialogue
 NativeVerifiedDomain NativeVerifiedSuffixSession NativeSession NativeState CommandQuit TokenByte.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeWhitespaceSuffixDialogue.
Import IndexExecution SipHashExecution SeedInputExecution.
Theorem generated_main key0 key1 prefix0 prefix1 sep1 sep2 requests suffix bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum ->
 TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
 Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 ->
 Forall Protocol.shape requests -> Forall(fun request=>Protocol.opcode request<>0%nat) requests ->
 NativeVerifiedDomain.within_capacity (requests++[NativeSession.quit]) ->
 exists replies final logical,
 length replies=length requests /\
 Protocol.dialogue Protocol.initial (requests++[NativeSession.quit]) (replies++[Protocol.BYE]) logical [] /\
 Guarantees.safe logical /\ NativeState.represents final logical /\
 execObserved(funcdef_0__main bs ns)
  (NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep1 sep2 (NativeSession.input requests suffix),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt; unreadInput:=prefix0++decimalBytes key0++sep1::(prefix1++decimalBytes key1++sep2::NativeSession.input requests suffix)|};
  {|flushedOutput:=Protocol.handshake_output; unreadInput:=NativeSession.input requests suffix|}]++
 NativeSession.schedule Protocol.handshake_output requests replies suffix)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\
 stdin final=suffix /\ meta_value final 9=1 /\ meta_value final 8=0.
Proof.
 intros Hkey0 Hkey1 Hsep1 Hsep2 Hprefix0 Hprefix1 Hshape Hpositive Hcapacity.
 destruct (NativeVerifiedSuffixSession.generated_main key0 key1 requests suffix bs ns Hkey0 Hkey1 Hshape Hpositive Hcapacity)
 as (replies & final & logical & Hlength & Hdialogue & Hsafe & Hstate & Hcanonical & Hout & Hin & Hstop & Hclear).
 set (wire:=NativeSession.input requests suffix) in *.
 set (normal:=SeedBootstrapExecution.initial key0 key1 wire []).
 set (other:=NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep1 sep2 wire).
 set (before:=seed_result (SeedBootstrapExecution.initial key0 key1 wire Protocol.seed_prompt) key0 key1 wire).
 set (snapshot:={|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire|}).
 set (snapshot2:={|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++sep1::(prefix1++decimalBytes key1++sep2::wire)|}).
 set (ready:={|flushedOutput:=Protocol.handshake_output;unreadInput:=wire|}).
 assert (Hm:(27<length(memory normal arraydef_0__meta))%nat) by (change (27<32)%nat;lia).
 assert (Ht:(1024<=length(memory normal arraydef_0__token))%nat) by (change (1024<=1024)%nat;lia).
 assert (Hp:meta_value normal 15=0) by reflexivity.
 assert (He:meta_value normal 8=0) by reflexivity.
 pose proof (generated_main_seed_prefix normal bs ns key0 key1 wire [] Hm Ht Hp He Hkey0 Hkey1 eq_refl) as Hnorm.
 change (execObserved (funcdef_0__main bs ns) (normal,[]) =
   execObserved (eliminateLocalVariables bs ns finish_body) (before,[snapshot])) in Hnorm.
 assert (Hsame:seed_result (withOutput other (stdout other++Protocol.seed_prompt)) key0 key1 wire=before).
 { unfold before,other,NativeWhitespaceDialogue.alternate,SeedBootstrapExecution.initial.
   change (seed_result (withInput {|memory:=arrays _ environment1;stdin:=[];stdout:=Protocol.seed_prompt|}
      (prefix0++decimalBytes key0++sep1::(prefix1++decimalBytes key1++sep2::wire))) key0 key1 wire =
    seed_result (withInput {|memory:=arrays _ environment1;stdin:=[];stdout:=Protocol.seed_prompt|}
      (Protocol.seed_bytes key0 key1++wire)) key0 key1 wire).
   now rewrite !SeedSeparator.seed_result_input. }
 assert (Hm2:(27<length(memory other arraydef_0__meta))%nat) by (change (27<32)%nat;lia).
 assert (Ht2:(1024<=length(memory other arraydef_0__token))%nat) by (change (1024<=1024)%nat;lia).
 assert (Hp2:meta_value other 15=0) by reflexivity.
 assert (He2:meta_value other 8=0) by reflexivity.
 pose proof (NativeSeedWhitespace.generated_main_two_separators other bs ns key0 key1 prefix0 prefix1 sep1 sep2 wire [] Hm2 Ht2 Hp2 He2 Hkey0 Hkey1 Hsep1 Hsep2 Hprefix0 Hprefix1 eq_refl) as Halt.
 rewrite Hsame in Halt.
 change (execObserved (funcdef_0__main bs ns) (other,[]) =
   execObserved (eliminateLocalVariables bs ns finish_body) (before,[snapshot2])) in Halt.
 change (execObserved (funcdef_0__main bs ns) (normal,[]) =
   Some (tt,(final,[snapshot;ready]++NativeSession.schedule Protocol.handshake_output requests replies suffix))) in Hcanonical.
 rewrite Hnorm in Hcanonical.
 assert (Hother:execObserved (eliminateLocalVariables bs ns finish_body) (before,[snapshot2]) =
   Some (tt,(final,[snapshot2;ready]++NativeSession.schedule Protocol.handshake_output requests replies suffix))).
 { eapply (NativeWhitespaceDialogue.observed_swap (eliminateLocalVariables bs ns finish_body) before [snapshot] [snapshot2]
     (ready::NativeSession.schedule Protocol.handshake_output requests replies suffix) tt final).
   exact Hcanonical. }
 exists replies,final,logical. split;[exact Hlength|]. split;[exact Hdialogue|]. split;[exact Hsafe|]. split;[exact Hstate|].
 split;[now rewrite Halt|]. repeat first[assumption|split].
Qed.
End NativeWhitespaceSuffixDialogue.
