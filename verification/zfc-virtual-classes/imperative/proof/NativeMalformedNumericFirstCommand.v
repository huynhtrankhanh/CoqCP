From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandChain CommandDispatch NativeFatalDispatch NativeMalformedArgumentHandler NativeMalformedFirstArgumentHandlers NativeMalformedTagHandlers NativeMalformedTagCommand NativeMalformedFirstArgumentCommand.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeMalformedNumericFirstCommand.
Import IndexExecution SipHashExecution ObservedLocal.
Definition failed arg := store_meta arg 8 1.
Definition final arg := store_meta(withOutput(failed arg)(stdout arg++Protocol.reply_bytes Protocol.ERR))9 1.
Theorem generated s bs ns op arg opcode number observations :
 (NativeMalformedFirstArgumentHandlers.supported opcode \/ NativeMalformedTagHandlers.supported opcode) ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(op,observations)) ->
 (17<length(memory op arraydef_0__meta))%nat -> meta_value op 11=opcode -> meta_value op 14=1 -> meta_value op 8=0 ->
 execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(op,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final arg,
 observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin arg|}])).
Proof.
 intros [Hfirst|Htag] Hop Hopmeta Hopnumber Hopvalid Hoperror Harg Hargmeta Hnumber Hvalid.
 - exact(NativeMalformedFirstArgumentCommand.generated s bs ns op arg opcode number observations Hfirst Hop Hopmeta Hopnumber Hopvalid Hoperror Harg Hargmeta Hnumber Hvalid).
 - exact(NativeMalformedTagCommand.generated s bs ns op arg opcode number observations Htag Hop Hopmeta Hopnumber Hopvalid Hoperror Harg Hargmeta Hnumber Hvalid).
Qed.
End NativeMalformedNumericFirstCommand.
