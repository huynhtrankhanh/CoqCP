From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandChain CommandDispatch NativeFatalDispatch NativeMalformedSchemaNameHandler.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeMalformedSchemaNameCommand.
Import IndexExecution SipHashExecution ObservedLocal.
Definition failed token := store_meta token 8 1.
Definition final token := store_meta (withOutput (failed token) (stdout token ++ Protocol.reply_bytes Protocol.ERR)) 9 1.
Theorem generated s bs ns op token observations :
 execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (s,observations)=Some(tt,(op,observations)) ->
 (17<length(memory op arraydef_0__meta))%nat -> meta_value op 11=24 -> meta_value op 14=1 -> meta_value op 8=0 ->
 execObserved (funcdef_0__readToken (fun _=>false) (fun _=>0)) (op,observations)=Some(tt,(token,observations)) ->
 (17<length(memory token arraydef_0__meta))%nat -> meta_value token 14=0 ->
 execObserved (funcdef_0__command bs ns) (s,observations)=Some(tt,(final token,
 observations++[{|flushedOutput:=stdout token++Protocol.reply_bytes Protocol.ERR; unreadInput:=stdin token|}])).
Proof.
 intros Hop Hopmeta Hopnumber Hopvalid Hoperror Htoken Htokenmeta Hvalid.
 set(initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} op 24).
 set(after:=setMachine initial (failed token)).
 pose proof(NativeFatalDispatch.generated_fatal_command s bs ns after op 24 observations observations Hop Hopmeta Hopnumber Hopvalid Hoperror ltac:(lia)
   ltac:(unfold after,initial,CommandDispatch.opcode_frame;cbn [nums setMachine setNum Imperative.update];reflexivity)
   ltac:(change(execLocalObserved(CommandChain.handler_for funcdef_0__readNat 24)(initial,observations)=Some(tt,(after,observations)));cbn [CommandChain.handler_for];unfold after,failed;apply NativeMalformedSchemaNameHandler.handler_24;try assumption;exact Htoken)
   ltac:(unfold after,failed;cbn [machine setMachine];rewrite store_meta_length;exact Htokenmeta)
   ltac:(unfold after,failed;cbn [machine setMachine];apply meta_store_same;lia)) as Hrun.
 unfold after,final,failed in *. cbn [machine setMachine] in Hrun. exact Hrun.
Qed.
End NativeMalformedSchemaNameCommand.
