From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import ObservedLocal CommandQuit.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith.
Open Scope Z_scope.
Module NativeCommandReaderCongruence.
Definition reader := funcdef_0__readNat (fun _=>false) (fun _=>0).
Definition tail : CommandQuitExecution.LocalAction unit := ltac:(
 let body := eval unfold funcdef_0__command_body in funcdef_0__command_body in
 lazymatch body with bind _ ?next => exact (next tt) end).
Lemma body_factor : funcdef_0__command_body = liftToWithLocalVariables reader >>= fun _ => tail.
Proof. reflexivity. Qed.
Theorem command_same_reader bs ns first second parsed observations :
 execObserved reader (first,observations)=Some(tt,(parsed,observations)) ->
 execObserved reader (second,observations)=Some(tt,(parsed,observations)) ->
 execObserved (funcdef_0__command bs ns) (first,observations)=
 execObserved (funcdef_0__command bs ns) (second,observations).
Proof.
 intros Hfirst Hsecond. unfold funcdef_0__command.
 rewrite !ObservedLocal.eliminate_correct,body_factor,!ObservedLocal.local_bind,!ObservedLocal.lift_correct.
 cbn [fst snd machine]. rewrite Hfirst,Hsecond. reflexivity.
Qed.
End NativeCommandReaderCongruence.
