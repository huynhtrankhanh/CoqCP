From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  AxiomStructure AxiomRefl FormulaCircuit InternLengths NativeAxiomBuilder.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeAxiomPrefix.
Import IndexExecution SipHashExecution ObservedLocal NativeAxiomBuilder.
(* Execute a native circuit fragment before a supplied continuation.  Keeping the
   frame and its numbered wires abstract lets schema builders interleave rename
   calls without expanding the complete generated handler during execution. *)
Fixpoint prefix plan start (next:AxiomStructure.LocalAction unit) : AxiomStructure.LocalAction unit := match plan with
| []=>next
| op::tail=>call op >>= fun _=>save start >>= fun _=>prefix tail (S start) next
end.
Theorem run plan s ids built result observations :
  FormulaCircuit.executes observations plan s ids built result ->
  forall (f:AxiomRefl.Frame) start,
  machine f=s -> environment f start ids -> valid plan start ->
  (13<length (memory s arraydef_0__meta))%nat ->
  exists after, machine after=built /\ environment after (start+length plan) result /\
    nums after vardef_0__axiom_tag=nums f vardef_0__axiom_tag /\
    (forall name,(forall i,(i<42)%nat -> name<>slot i) -> nums after name=nums f name) /\
    forall next,execLocalObserved (prefix plan start next) (f,observations)=execLocalObserved next (after,observations).
Proof.
  intro Htrace. induction Htrace as [s ids|op tail s ids middle id final result Hrun Hvalue Hmiddle Htail IH].
  - intros f start Hmachine Henv Hvalid Hmeta. exists f. split;[exact Hmachine|].
    split;[now rewrite Nat.add_0_r|]. split;[reflexivity|]. split;[intros;reflexivity|]. intro next;reflexivity.
  - intros f start Hmachine Henv [Hstart [Hop Hvalid]] Hmeta.
    assert (Hcall:execLocalObserved (call op) (f,observations)=Some (tt,(setMachine f middle,observations))).
    { apply (call_run f start ids op middle observations Henv Hop). now rewrite Hmachine. }
    assert (Hlen:length (memory middle arraydef_0__meta)=length (memory s arraydef_0__meta))
      by exact (proj1 (InternLengths.observed_lengths _ _ _ _ _ _ Hrun)).
    assert (Hnextmeta:(13<length (memory middle arraydef_0__meta))%nat) by lia.
    assert (Hnextenv:environment (advanced f middle start id) (S start) (ids++[id])) by (now apply advance_environment).
    destruct (IH (advanced f middle start id) (S start) eq_refl Hnextenv Hvalid Hnextmeta)
      as [after [Hmachine_after [Henv_after [Htag [Hlocals Hnext]]]]].
    exists after. split;[exact Hmachine_after|].
    split;[replace (start+length (op::tail))%nat with (S start+length tail)%nat by (cbn;lia);exact Henv_after|].
    split.
    + rewrite Htag. unfold advanced. cbn [nums setNum setMachine].
      rewrite RenameMemoControl.updated_other by (intro Heq;apply (slot_not_tag start);symmetry;exact Heq). reflexivity.
    + split.
      * intros name Hname. rewrite Hlocals by exact Hname. unfold advanced. cbn [nums setNum setMachine].
        rewrite RenameMemoControl.updated_other by (apply Hname;lia). reflexivity.
      * intro next. cbn [prefix]. rewrite local_bind,Hcall. cbn [optionBind fst snd]. rewrite local_bind.
      match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (save start) ?state] =>
        let expression:=constr:(@execLocalObserved I T EI V EV R (save start) state) in
        let Hsave:=fresh in assert (Hsave:expression=Some (tt,(setNum (setMachine f middle) (slot start) (meta_value middle 0),observations)))
          by exact (save_run (setMachine f middle) start observations Hmiddle);rewrite Hsave;clear Hsave end.
      cbn [optionBind fst snd machine setMachine]. rewrite Hvalue. apply Hnext.
Qed.
End NativeAxiomPrefix.
