From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import ObservedLocal NativeCommandReaderCongruence MachinePointwise.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith.
Open Scope Z_scope.
Module NativeCommandReaderPointwise.
Import NativeCommandReaderCongruence.
Lemma command_factor bs ns before parsed observations :
 execObserved reader (before,observations)=Some(tt,(parsed,observations)) ->
 execObserved (funcdef_0__command bs ns) (before,observations)=
 execObserved (eliminateLocalVariables bs ns tail) (parsed,observations).
Proof.
 intro Hread. unfold funcdef_0__command.
 rewrite !ObservedLocal.eliminate_correct,body_factor,ObservedLocal.local_bind,ObservedLocal.lift_correct.
 cbn [fst snd machine]. rewrite Hread. reflexivity.
Qed.
Theorem command_same_reader_pointwise bs ns first second parsed1 parsed2 observations final trace :
 execObserved reader (first,observations)=Some(tt,(parsed1,observations)) ->
 execObserved reader (second,observations)=Some(tt,(parsed2,observations)) ->
 MachinePointwise.same parsed1 parsed2 ->
 execObserved (funcdef_0__command bs ns) (first,observations)=Some(tt,(final,trace)) ->
 exists target,execObserved (funcdef_0__command bs ns) (second,observations)=Some(tt,(target,trace)) /\
 MachinePointwise.same final target.
Proof.
 intros Hfirst Hsecond Hsame Hrun.
 pose proof(command_factor bs ns first parsed1 observations Hfirst) as Hfactor1.
 pose proof(command_factor bs ns second parsed2 observations Hsecond) as Hfactor2.
 pose proof(MachinePointwise.observed_same (eliminateLocalVariables bs ns tail) parsed1 parsed2 observations Hsame) as Hsimulation.
 rewrite <-Hfactor1,Hrun in Hsimulation.
 destruct(execObserved (eliminateLocalVariables bs ns tail)(parsed2,observations)) as [[result [target actual]]|] eqn:Htarget;
 cbn in Hsimulation;[|contradiction].
 destruct Hsimulation as [Hresult [Htrace Hstate]]. subst result actual.
 exists target. split;[exact Hfactor2|exact Hstate].
Qed.
End NativeCommandReaderPointwise.
