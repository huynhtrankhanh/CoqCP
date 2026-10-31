From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandChain CommandDispatch NativeFatalDispatch NativeMalformedArgumentHandler NativeMalformedFirstArgumentHandlers.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeMalformedFirstArgumentCommand.
Import IndexExecution SipHashExecution ObservedLocal.
Definition failed arg := store_meta arg 8 1.
Definition final arg := store_meta(withOutput(failed arg)(stdout arg++Protocol.reply_bytes Protocol.ERR))9 1.
Theorem generated s bs ns op arg opcode number observations :
 NativeMalformedFirstArgumentHandlers.supported opcode ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations)) ->
 (17<length(memory op arraydef_0__meta))%nat -> meta_value op 11=opcode -> meta_value op 14=1 -> meta_value op 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(op,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final arg,
 observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin arg|}])).
Proof.
 intros Hsupported Hop Hopmeta Hopnumber Hopvalid Hoperror Harg Hargmeta Hnumber Hvalid.
 assert(Hpositive:1<=opcode<=26) by (unfold NativeMalformedFirstArgumentHandlers.supported in Hsupported;cbn [List.In] in Hsupported;repeat destruct Hsupported as [Hsupported|Hsupported];try contradiction;lia).
 set(initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} op opcode).
 set(after:=setMachine(setNum(setMachine initial arg)vardef_0__command_a number)(failed arg)).
 pose proof(NativeFatalDispatch.generated_fatal_command s bs ns after op opcode observations observations Hop Hopmeta Hopnumber Hopvalid Hoperror ltac:(lia)
   ltac:(unfold after,initial,CommandDispatch.opcode_frame;cbn [nums setMachine setNum Imperative.update];reflexivity)
   ltac:(change(execLocalObserved(CommandChain.handler_for funcdef_0__readNat opcode)(initial,observations)=Some(tt,(after,observations)));unfold after,failed;apply NativeMalformedFirstArgumentHandlers.handler;try assumption;exact Harg)
   ltac:(unfold after,failed;cbn [machine setMachine];rewrite store_meta_length;exact Hargmeta)
   ltac:(unfold after,failed;cbn [machine setMachine];apply meta_store_same;lia)) as Hrun.
 unfold after,final,failed in *. cbn [machine setMachine] in Hrun. exact Hrun.
Qed.
End NativeMalformedFirstArgumentCommand.
