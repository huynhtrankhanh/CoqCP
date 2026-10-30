From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandChain CommandDispatch NativeFatalDispatch NativeMalformedArgumentHandler.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeMalformedUnaryCommand.
Import IndexExecution SipHashExecution ObservedLocal.
Definition failed arg := store_meta arg 8 1.
Definition final arg := store_meta(withOutput(failed arg)(stdout arg++Protocol.reply_bytes Protocol.ERR))9 1.
Theorem generated s bs ns op arg number observations :
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations)) ->
 (17<length(memory op arraydef_0__meta))%nat -> meta_value op 11=4 -> meta_value op 14=1 -> meta_value op 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(op,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final arg,
 observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin arg|}])).
Proof.
 intros Hop Hopmeta Hopnumber Hopvalid Hoperror Harg Hargmeta Hnumber Hvalid.
 set(initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} op 4).
 set(after:=setMachine(setNum(setMachine initial arg)vardef_0__command_a number)(failed arg)).
 pose proof(NativeFatalDispatch.generated_fatal_command s bs ns after op 4 observations observations Hop Hopmeta Hopnumber Hopvalid Hoperror ltac:(lia)
   ltac:(unfold after,initial,CommandDispatch.opcode_frame;cbn [nums setMachine setNum Imperative.update];reflexivity)
   ltac:(change(execLocalObserved(CommandChain.handler_for funcdef_0__readNat 4)(initial,observations)=Some(tt,(after,observations)));cbn [CommandChain.handler_for];unfold after,failed;apply NativeMalformedArgumentHandler.handler_4;try assumption;exact Harg)
   ltac:(unfold after,failed;cbn [machine setMachine];rewrite store_meta_length;exact Hargmeta)
   ltac:(unfold after,failed;cbn [machine setMachine];apply meta_store_same;lia)) as Hrun.
 unfold after,final,failed in *. cbn [machine setMachine] in Hrun. exact Hrun.
Qed.
End NativeMalformedUnaryCommand.
