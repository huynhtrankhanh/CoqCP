From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandChain CommandDispatch NativeFatalDispatch NativeMalformedTagLaterHandlers.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeMalformedTagLaterCommand.
Import IndexExecution SipHashExecution ObservedLocal.
Definition failed arg := store_meta arg 8 1.
Definition final arg := store_meta(withOutput(failed arg)(stdout arg++Protocol.reply_bytes Protocol.ERR))9 1.
Theorem generated_11_2 s bs ns op p1 v1 arg number observations :
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations)) ->
 (17<length(memory op arraydef_0__meta))%nat -> meta_value op 11=11 -> meta_value op 14=1 -> meta_value op 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(op,observations)=Some(tt,(p1,observations)) ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final arg,
 observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin arg|}])).
Proof.
 intros Hop Hopmeta Hopnumber Hopvalid Hoperror Hp1 Hp1meta Hp1number Hp1valid Hp1error Harg Hargmeta Hnumber Hvalid.
 set(initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} op 11).
 set(after:=setMachine(setNum(setMachine(setNum(setMachine(initial)p1)vardef_0__command_tag v1)arg)vardef_0__command_a number)(failed arg)).
 pose proof(NativeFatalDispatch.generated_fatal_command s bs ns after op 11 observations observations Hop Hopmeta Hopnumber Hopvalid Hoperror ltac:(lia)
   ltac:(unfold after,initial,CommandDispatch.opcode_frame;cbn [nums setMachine setNum Imperative.update];reflexivity)
   ltac:(change(execLocalObserved(CommandChain.handler_for funcdef_0__readNat 11)(initial,observations)=Some(tt,(after,observations)));cbn [CommandChain.handler_for];unfold after,failed;eapply NativeMalformedTagLaterHandlers.handler_11_2;try eassumption)
   ltac:(unfold after,failed;cbn [machine setMachine];rewrite store_meta_length;exact Hargmeta)
   ltac:(unfold after,failed;cbn [machine setMachine];apply meta_store_same;lia)) as Hrun.
 unfold after,final,failed in *. cbn [machine setMachine] in Hrun. exact Hrun.
Qed.
Theorem generated_11_3 s bs ns op p1 v1 p2 v2 arg number observations :
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations)) ->
 (17<length(memory op arraydef_0__meta))%nat -> meta_value op 11=11 -> meta_value op 14=1 -> meta_value op 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(op,observations)=Some(tt,(p1,observations)) ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(p2,observations)) ->
 (17<length(memory p2 arraydef_0__meta))%nat -> meta_value p2 11=v2 -> meta_value p2 14=1 -> meta_value p2 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p2,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final arg,
 observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin arg|}])).
Proof.
 intros Hop Hopmeta Hopnumber Hopvalid Hoperror Hp1 Hp1meta Hp1number Hp1valid Hp1error Hp2 Hp2meta Hp2number Hp2valid Hp2error Harg Hargmeta Hnumber Hvalid.
 set(initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} op 11).
 set(after:=setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(initial)p1)vardef_0__command_tag v1)p2)vardef_0__command_a v2)arg)vardef_0__command_b number)(failed arg)).
 pose proof(NativeFatalDispatch.generated_fatal_command s bs ns after op 11 observations observations Hop Hopmeta Hopnumber Hopvalid Hoperror ltac:(lia)
   ltac:(unfold after,initial,CommandDispatch.opcode_frame;cbn [nums setMachine setNum Imperative.update];reflexivity)
   ltac:(change(execLocalObserved(CommandChain.handler_for funcdef_0__readNat 11)(initial,observations)=Some(tt,(after,observations)));cbn [CommandChain.handler_for];unfold after,failed;eapply NativeMalformedTagLaterHandlers.handler_11_3;try eassumption)
   ltac:(unfold after,failed;cbn [machine setMachine];rewrite store_meta_length;exact Hargmeta)
   ltac:(unfold after,failed;cbn [machine setMachine];apply meta_store_same;lia)) as Hrun.
 unfold after,final,failed in *. cbn [machine setMachine] in Hrun. exact Hrun.
Qed.
Theorem generated_11_4 s bs ns op p1 v1 p2 v2 p3 v3 arg number observations :
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations)) ->
 (17<length(memory op arraydef_0__meta))%nat -> meta_value op 11=11 -> meta_value op 14=1 -> meta_value op 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(op,observations)=Some(tt,(p1,observations)) ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(p2,observations)) ->
 (17<length(memory p2 arraydef_0__meta))%nat -> meta_value p2 11=v2 -> meta_value p2 14=1 -> meta_value p2 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p2,observations)=Some(tt,(p3,observations)) ->
 (17<length(memory p3 arraydef_0__meta))%nat -> meta_value p3 11=v3 -> meta_value p3 14=1 -> meta_value p3 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p3,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final arg,
 observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin arg|}])).
Proof.
 intros Hop Hopmeta Hopnumber Hopvalid Hoperror Hp1 Hp1meta Hp1number Hp1valid Hp1error Hp2 Hp2meta Hp2number Hp2valid Hp2error Hp3 Hp3meta Hp3number Hp3valid Hp3error Harg Hargmeta Hnumber Hvalid.
 set(initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} op 11).
 set(after:=setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(initial)p1)vardef_0__command_tag v1)p2)vardef_0__command_a v2)p3)vardef_0__command_b v3)arg)vardef_0__command_c number)(failed arg)).
 pose proof(NativeFatalDispatch.generated_fatal_command s bs ns after op 11 observations observations Hop Hopmeta Hopnumber Hopvalid Hoperror ltac:(lia)
   ltac:(unfold after,initial,CommandDispatch.opcode_frame;cbn [nums setMachine setNum Imperative.update];reflexivity)
   ltac:(change(execLocalObserved(CommandChain.handler_for funcdef_0__readNat 11)(initial,observations)=Some(tt,(after,observations)));cbn [CommandChain.handler_for];unfold after,failed;eapply NativeMalformedTagLaterHandlers.handler_11_4;try eassumption)
   ltac:(unfold after,failed;cbn [machine setMachine];rewrite store_meta_length;exact Hargmeta)
   ltac:(unfold after,failed;cbn [machine setMachine];apply meta_store_same;lia)) as Hrun.
 unfold after,final,failed in *. cbn [machine setMachine] in Hrun. exact Hrun.
Qed.
Theorem generated_22_2 s bs ns op p1 v1 arg number observations :
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations)) ->
 (17<length(memory op arraydef_0__meta))%nat -> meta_value op 11=22 -> meta_value op 14=1 -> meta_value op 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(op,observations)=Some(tt,(p1,observations)) ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final arg,
 observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin arg|}])).
Proof.
 intros Hop Hopmeta Hopnumber Hopvalid Hoperror Hp1 Hp1meta Hp1number Hp1valid Hp1error Harg Hargmeta Hnumber Hvalid.
 set(initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} op 22).
 set(after:=setMachine(setNum(setMachine(setNum(setMachine(initial)p1)vardef_0__command_tag v1)arg)vardef_0__command_a number)(failed arg)).
 pose proof(NativeFatalDispatch.generated_fatal_command s bs ns after op 22 observations observations Hop Hopmeta Hopnumber Hopvalid Hoperror ltac:(lia)
   ltac:(unfold after,initial,CommandDispatch.opcode_frame;cbn [nums setMachine setNum Imperative.update];reflexivity)
   ltac:(change(execLocalObserved(CommandChain.handler_for funcdef_0__readNat 22)(initial,observations)=Some(tt,(after,observations)));cbn [CommandChain.handler_for];unfold after,failed;eapply NativeMalformedTagLaterHandlers.handler_22_2;try eassumption)
   ltac:(unfold after,failed;cbn [machine setMachine];rewrite store_meta_length;exact Hargmeta)
   ltac:(unfold after,failed;cbn [machine setMachine];apply meta_store_same;lia)) as Hrun.
 unfold after,final,failed in *. cbn [machine setMachine] in Hrun. exact Hrun.
Qed.
Theorem generated_22_3 s bs ns op p1 v1 p2 v2 arg number observations :
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations)) ->
 (17<length(memory op arraydef_0__meta))%nat -> meta_value op 11=22 -> meta_value op 14=1 -> meta_value op 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(op,observations)=Some(tt,(p1,observations)) ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(p2,observations)) ->
 (17<length(memory p2 arraydef_0__meta))%nat -> meta_value p2 11=v2 -> meta_value p2 14=1 -> meta_value p2 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p2,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final arg,
 observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin arg|}])).
Proof.
 intros Hop Hopmeta Hopnumber Hopvalid Hoperror Hp1 Hp1meta Hp1number Hp1valid Hp1error Hp2 Hp2meta Hp2number Hp2valid Hp2error Harg Hargmeta Hnumber Hvalid.
 set(initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} op 22).
 set(after:=setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(initial)p1)vardef_0__command_tag v1)p2)vardef_0__command_a v2)arg)vardef_0__command_b number)(failed arg)).
 pose proof(NativeFatalDispatch.generated_fatal_command s bs ns after op 22 observations observations Hop Hopmeta Hopnumber Hopvalid Hoperror ltac:(lia)
   ltac:(unfold after,initial,CommandDispatch.opcode_frame;cbn [nums setMachine setNum Imperative.update];reflexivity)
   ltac:(change(execLocalObserved(CommandChain.handler_for funcdef_0__readNat 22)(initial,observations)=Some(tt,(after,observations)));cbn [CommandChain.handler_for];unfold after,failed;eapply NativeMalformedTagLaterHandlers.handler_22_3;try eassumption)
   ltac:(unfold after,failed;cbn [machine setMachine];rewrite store_meta_length;exact Hargmeta)
   ltac:(unfold after,failed;cbn [machine setMachine];apply meta_store_same;lia)) as Hrun.
 unfold after,final,failed in *. cbn [machine setMachine] in Hrun. exact Hrun.
Qed.
Theorem generated_22_4 s bs ns op p1 v1 p2 v2 p3 v3 arg number observations :
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations)) ->
 (17<length(memory op arraydef_0__meta))%nat -> meta_value op 11=22 -> meta_value op 14=1 -> meta_value op 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(op,observations)=Some(tt,(p1,observations)) ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(p2,observations)) ->
 (17<length(memory p2 arraydef_0__meta))%nat -> meta_value p2 11=v2 -> meta_value p2 14=1 -> meta_value p2 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p2,observations)=Some(tt,(p3,observations)) ->
 (17<length(memory p3 arraydef_0__meta))%nat -> meta_value p3 11=v3 -> meta_value p3 14=1 -> meta_value p3 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p3,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final arg,
 observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin arg|}])).
Proof.
 intros Hop Hopmeta Hopnumber Hopvalid Hoperror Hp1 Hp1meta Hp1number Hp1valid Hp1error Hp2 Hp2meta Hp2number Hp2valid Hp2error Hp3 Hp3meta Hp3number Hp3valid Hp3error Harg Hargmeta Hnumber Hvalid.
 set(initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} op 22).
 set(after:=setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(initial)p1)vardef_0__command_tag v1)p2)vardef_0__command_a v2)p3)vardef_0__command_b v3)arg)vardef_0__command_c number)(failed arg)).
 pose proof(NativeFatalDispatch.generated_fatal_command s bs ns after op 22 observations observations Hop Hopmeta Hopnumber Hopvalid Hoperror ltac:(lia)
   ltac:(unfold after,initial,CommandDispatch.opcode_frame;cbn [nums setMachine setNum Imperative.update];reflexivity)
   ltac:(change(execLocalObserved(CommandChain.handler_for funcdef_0__readNat 22)(initial,observations)=Some(tt,(after,observations)));cbn [CommandChain.handler_for];unfold after,failed;eapply NativeMalformedTagLaterHandlers.handler_22_4;try eassumption)
   ltac:(unfold after,failed;cbn [machine setMachine];rewrite store_meta_length;exact Hargmeta)
   ltac:(unfold after,failed;cbn [machine setMachine];apply meta_store_same;lia)) as Hrun.
 unfold after,final,failed in *. cbn [machine setMachine] in Hrun. exact Hrun.
Qed.
Theorem generated_22_5 s bs ns op p1 v1 p2 v2 p3 v3 p4 v4 arg number observations :
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations)) ->
 (17<length(memory op arraydef_0__meta))%nat -> meta_value op 11=22 -> meta_value op 14=1 -> meta_value op 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(op,observations)=Some(tt,(p1,observations)) ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(p2,observations)) ->
 (17<length(memory p2 arraydef_0__meta))%nat -> meta_value p2 11=v2 -> meta_value p2 14=1 -> meta_value p2 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p2,observations)=Some(tt,(p3,observations)) ->
 (17<length(memory p3 arraydef_0__meta))%nat -> meta_value p3 11=v3 -> meta_value p3 14=1 -> meta_value p3 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p3,observations)=Some(tt,(p4,observations)) ->
 (17<length(memory p4 arraydef_0__meta))%nat -> meta_value p4 11=v4 -> meta_value p4 14=1 -> meta_value p4 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(p4,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final arg,
 observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin arg|}])).
Proof.
 intros Hop Hopmeta Hopnumber Hopvalid Hoperror Hp1 Hp1meta Hp1number Hp1valid Hp1error Hp2 Hp2meta Hp2number Hp2valid Hp2error Hp3 Hp3meta Hp3number Hp3valid Hp3error Hp4 Hp4meta Hp4number Hp4valid Hp4error Harg Hargmeta Hnumber Hvalid.
 set(initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} op 22).
 set(after:=setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(initial)p1)vardef_0__command_tag v1)p2)vardef_0__command_a v2)p3)vardef_0__command_b v3)p4)vardef_0__command_c v4)arg)vardef_0__command_node number)(failed arg)).
 pose proof(NativeFatalDispatch.generated_fatal_command s bs ns after op 22 observations observations Hop Hopmeta Hopnumber Hopvalid Hoperror ltac:(lia)
   ltac:(unfold after,initial,CommandDispatch.opcode_frame;cbn [nums setMachine setNum Imperative.update];reflexivity)
   ltac:(change(execLocalObserved(CommandChain.handler_for funcdef_0__readNat 22)(initial,observations)=Some(tt,(after,observations)));cbn [CommandChain.handler_for];unfold after,failed;eapply NativeMalformedTagLaterHandlers.handler_22_5;try eassumption)
   ltac:(unfold after,failed;cbn [machine setMachine];rewrite store_meta_length;exact Hargmeta)
   ltac:(unfold after,failed;cbn [machine setMachine];apply meta_store_same;lia)) as Hrun.
 unfold after,final,failed in *. cbn [machine setMachine] in Hrun. exact Hrun.
Qed.
End NativeMalformedTagLaterCommand.
