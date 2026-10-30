From CoqCP Require Import Options Imperative Execution TapeEnd InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeMissingNumberEOF.
Import IndexExecution SipHashExecution ReadTokenExecution.
Lemma read_empty_composition tape_proc byte_proc (f:ReadTokenExecution.Frame) after :
 (17<length(memory(machine f)arraydef_0__meta))%nat ->
 meta_value(machine f)15=0 -> meta_value(machine f)8=0 ->
 execLocal tape_proc (setMachine f (reset(machine f)))=Some(tt,setMachine f after) ->
 (17<length(memory after arraydef_0__meta))%nat ->
 meta_value after 17=0 -> meta_value after 8=0 -> meta_value after 6=0 ->
 execLocal(read_with tape_proc byte_proc)f=Some(tt,setMachine f(store_meta after 7 1)).
Proof.
 intros Hlength Hpending Herror Htape Hafter Hdone Herr Hsize.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold read_with. unfold reset in Htape. cbv beta iota zeta delta [machine setMachine bools nums] in Htape.
 repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite local_done
  |rewrite local_put_meta by (cbn [machine setMachine];rewrite ?store_meta_length;lia)
  |rewrite local_read_meta by (cbn [machine setMachine];rewrite ?store_meta_length;lia)
  |rewrite Htape |rewrite meta_store_other by lia |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |rewrite Hpending |rewrite Herror |rewrite Hdone |rewrite Herr |rewrite Hsize
  |progress replace (Z.to_nat 17) with 17%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 15) with 15%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |progress replace (Z.to_nat 6) with 6%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [rewrite (bool_decide_true P) by congruence|rewrite (bool_decide_false P) by congruence] end
  |progress cbn [bind optionBind machine setMachine fst snd shortCircuitAnd]
  |progress cbv beta iota zeta delta [machine setMachine bools nums]].
 reflexivity.
Qed.
Theorem generated_token native bs ns :
 (17<length(memory native arraydef_0__meta))%nat -> meta_value native 15=0 -> meta_value native 8=0 -> stdin native=[] ->
 exec(funcdef_0__readToken bs ns)native=Some(tt,store_meta(reset native)7 1).
Proof.
 intros Hmeta Hpending Herror Hinput.
 unfold funcdef_0__readToken. rewrite exec_eliminate,actual_read_body.
 set(f:={|machine:=native;bools:=bs;nums:=ns|}:ReadTokenExecution.Frame).
 assert(Htape:execLocal(tapeEnd byte_body)(setMachine f(reset native))=Some(tt,setMachine f(reset native))).
 { apply tapeEnd_execution. apply tape_eof. change(stdin(reset native)=[]). change(stdin native=[]). exact Hinput. }
 rewrite(read_empty_composition (tapeEnd byte_body) funcdef_0__tokenByte f (reset native) Hmeta Hpending Herror Htape
  ltac:(now rewrite reset_length) ltac:(rewrite reset_meta by exact Hmeta;reflexivity)
  ltac:(rewrite reset_meta by exact Hmeta;exact Herror) ltac:(rewrite reset_meta by exact Hmeta;reflexivity)).
 reflexivity.
Qed.
Import ReadNatExecution.
Lemma invalid_composition reader digits (f:ReadNatExecution.Frame) tokenstate :
 exec(reader (fun _=>false)(fun _=>0))(machine f)=Some(tt,tokenstate) ->
 (14<length(memory tokenstate arraydef_0__meta))%nat -> meta_value tokenstate 14=0 ->
 execLocal(ReadNatExecution.body_with reader digits)f=
 Some(tt,setMachine (setNum f vardef_0__readNat_value 0)(store_meta tokenstate 11 0)).
Proof.
 intros Hreader Hmeta Hvalid. destruct f as [s bs ns]. cbn [machine] in *.
 unfold ReadNatExecution.body_with.
 repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite local_done
   |rewrite local_get |rewrite local_set |rewrite Hreader |rewrite Hvalid
   |rewrite local_read_meta by (cbn [machine setMachine];lia)
   |rewrite local_put_meta by (cbn [machine setMachine];lia)
   |progress replace (Z.to_nat 14) with 14%nat by reflexivity
   |progress replace (Z.to_nat 11) with 11%nat by reflexivity
   |match goal with |- context [bool_decide ?P] => first
      [rewrite (bool_decide_true P) by congruence|rewrite (bool_decide_false P) by congruence] end
   |progress cbn [bind optionBind fst snd]
   |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]].
 unfold update. case_decide;[reflexivity|contradiction].
Qed.
Theorem generated_number native bs ns observations :
 (17<length(memory native arraydef_0__meta))%nat -> meta_value native 15=0 -> meta_value native 8=0 -> stdin native=[] ->
 exists after, execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 meta_value after 14=0 /\ meta_value after 11=0 /\ stdin after=[].
Proof.
 intros Hmeta Hpending Herror Hinput.
 set(tokenstate:=store_meta(reset native)7 1).
 assert(Hreader:exec(funcdef_0__readToken (fun _=>false)(fun _=>0))native=Some(tt,tokenstate)).
 { unfold tokenstate. now apply generated_token. }
 assert(Hlength:(17<length(memory tokenstate arraydef_0__meta))%nat).
 { unfold tokenstate. rewrite store_meta_length,reset_length. exact Hmeta. }
 assert(Hvalid:meta_value tokenstate 14=0).
 { unfold tokenstate. rewrite meta_store_other by lia. rewrite reset_meta by exact Hmeta. reflexivity. }
 set(after:=store_meta tokenstate 11 0).
 assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
 { unfold funcdef_0__readNat. rewrite exec_eliminate,ReadNatExecution.actual_body.
   rewrite(invalid_composition funcdef_0__readToken ReadNatExecution.digit_loop {|machine:=native;bools:=bs;nums:=ns|} tokenstate Hreader ltac:(lia) Hvalid). reflexivity. }
 exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. split.
 - unfold after. rewrite meta_store_other by lia. exact Hvalid.
 - split.
   + unfold after. apply meta_store_same. lia.
   + unfold after,tokenstate,reset. change(stdin native=[]). exact Hinput.
Qed.
End NativeMissingNumberEOF.
