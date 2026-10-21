From CoqCP Require Import Options Imperative Execution InteractiveExecution TapeEnd.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal ObservedTape SeedInput Startup QuitLoop CommandLoop.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module DialogueExecution.
Import IndexExecution SipHashExecution.
(* A composition interface for actual command executions. This relation does not
   assert their logical correctness: each handler must separately meet Protocol. *)
Inductive run : Machine -> list FlushSnapshot -> Machine -> list FlushSnapshot -> Prop :=
| eof s observations : stdin s = [] -> run s observations s observations
| stop s observations ch tail after trace :
    0 <= ch < 256 -> stdin s = ch :: tail -> (15 < length (memory s arraydef_0__meta))%nat ->
    execObserved (funcdef_0__command (fun _ => false) (fun _ => 0))
      (CommandLoopExecution.pending_state (withInput s tail) ch,observations) = Some (tt,(after,trace)) ->
    (9 < length (memory after arraydef_0__meta))%nat -> meta_value after 9 <> 0 ->
    run s observations after trace
| next s observations ch tail after trace final final_trace :
    0 <= ch < 256 -> stdin s = ch :: tail -> (15 < length (memory s arraydef_0__meta))%nat ->
    execObserved (funcdef_0__command (fun _ => false) (fun _ => 0))
      (CommandLoopExecution.pending_state (withInput s tail) ch,observations) = Some (tt,(after,trace)) ->
    (9 < length (memory after arraydef_0__meta))%nat -> meta_value after 9 = 0 ->
    run after trace final final_trace -> run s observations final final_trace.
Theorem run_tape s observations final trace bs ns : run s observations final trace ->
  ObservedTape.tape_execution QuitLoopExecution.callback
    ({|machine := s; bools := bs; nums := ns|} : SeedInputExecution.Frame,observations)
    ({|machine := final; bools := bs; nums := ns|},trace).
Proof.
  intro Hrun. induction Hrun as [s observations Hin|
    s observations ch tail after trace Hbyte Hin Hmeta Hcommand Hafter Hstop|
    s observations ch tail after trace final final_trace Hbyte Hin Hmeta Hcommand Hafter Hnext Hrun IH].
  - apply ObservedTape.eof. exact Hin.
  - eapply ObservedTape.stop with (ch := ch) (tail := tail); [exact Hin|lia|].
    pose proof (CommandLoopExecution.generated_callback
      {|machine := withInput s tail; bools := bs; nums := ns|} ch observations after trace Hbyte Hmeta Hafter Hcommand) as Hcallback.
    unfold CommandLoopExecution.outcome in Hcallback. rewrite bool_decide_true in Hcallback by exact Hstop. exact Hcallback.
  - eapply ObservedTape.next with (ch := ch) (tail := tail)
      (after := {|machine := after; bools := bs; nums := ns|}) (trace := trace); [exact Hin|lia| |exact IH].
    pose proof (CommandLoopExecution.generated_callback
      {|machine := withInput s tail; bools := bs; nums := ns|} ch observations after trace Hbyte Hmeta Hafter Hcommand) as Hcallback.
    unfold CommandLoopExecution.outcome in Hcallback. rewrite bool_decide_false in Hcallback by congruence. exact Hcallback.
Qed.
Theorem generated_commands s observations final trace bs ns : run s observations final trace ->
  execObserved (eliminateLocalVariables bs ns StartupExecution.commands_body) (s,observations) = Some (tt,(final,trace)).
Proof.
  intro Hrun. pose proof (run_tape s observations final trace bs ns Hrun) as Htape.
  apply ObservedTape.tapeEnd_execution in Htape.
  unfold IndexExecution.Machine in *.
  rewrite QuitLoopExecution.actual_commands, SeedInputExecution.observed_local_bind, ObservedLocal.eliminate_correct.
  unfold SeedInputExecution.Frame in Htape. rewrite Htape. reflexivity.
Qed.
End DialogueExecution.
