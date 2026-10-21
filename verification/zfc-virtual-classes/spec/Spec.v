From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From stdpp Require Import numbers list.
From Trusted Require Export Protocol Guarantees.

(* Standalone specification entry point. See spec/README.md for the complete
   wire grammar, command table, ZFC calculus, virtual-class expansion rules,
   checked set certification and class-metavariable schema guarantees.

   [Protocol.dialogue] requires the mathematical transition of EVERY command,
   including exact proof-premise matching and rejection iff no acceptance rule
   applies. [Guarantees.safe] explicitly requires ZFC derivations for active and
   named theorems and for every class marked SET. It also requires named schema
   roots to denote proof templates. Schemata.infer rechecks each supplied
   substitution; Guarantees.instance_sound gives its derivation guarantee.

   The remaining clauses require actual termination, consumed input or the
   exact unread quit suffix, cumulative stdout, and each flush snapshot.
   [within_capacity] is an external resource domain, never an assumption that
   this program succeeds or implements the specified mathematics. *)
Definition required {I : Type} {T : I -> Type} `{EqDecision I}
  (program : Action (WithArrays I T) withArraysReturnValue unit)
  (initial_memory : forall name, list (T name))
  (within_capacity : list Protocol.request -> Prop) :=
  forall k0 k1 qs, Z.of_nat k0 <= Protocol.maximum -> Z.of_nat k1 <= Protocol.maximum ->
  Forall Protocol.shape qs -> within_capacity qs ->
  exists rs final logical remaining,
    Protocol.dialogue Protocol.initial qs rs logical remaining /\
    Guarantees.safe logical /\
    execObserved program
      ({| memory := initial_memory; stdin := Protocol.seed_bytes k0 k1 ++ Protocol.wire qs; stdout := [] |}, []) =
      Some (tt,(final,
        {| flushedOutput := Protocol.seed_prompt; unreadInput := Protocol.seed_bytes k0 k1 ++ Protocol.wire qs |} ::
        {| flushedOutput := Protocol.handshake_output; unreadInput := Protocol.wire qs |} ::
        Protocol.flush_schedule qs rs Protocol.handshake_output)) /\
    stdout final = Protocol.handshake_output ++ concat (map Protocol.reply_bytes rs) /\ stdin final = remaining.

(* The explicit mathematical postcondition follows from the declared rules,
   rather than from any implementation. Thus exposing it strengthens the
   readable contract without changing its accepted executions. *)
Theorem required_iff_protocol {I : Type} {T : I -> Type} `{EqDecision I}
  (program : Action (WithArrays I T) withArraysReturnValue unit) initial_memory within_capacity :
  required program initial_memory within_capacity <-> Protocol.required program initial_memory within_capacity.
Proof.
  split; intros Hprogram k0 k1 qs Hkey0 Hkey1 Hshape Hcapacity;
    destruct (Hprogram k0 k1 qs Hkey0 Hkey1 Hshape Hcapacity) as [rs [final [logical [remaining Hresult]]]];
    exists rs,final,logical,remaining.
  - destruct Hresult as [Hdialogue [_ Hresult]]. now split.
  - destruct Hresult as [Hdialogue Hresult]. split; [exact Hdialogue|].
    split; [exact (Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|exact Hresult].
Qed.
