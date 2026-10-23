From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  AxiomStructure AxiomDispatch AxiomRefl AxiomFixedCircuits FormulaCircuit InternLengths.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeAxiomBuilder.
Import IndexExecution SipHashExecution ObservedLocal.
Definition slots := [
vardef_0__axiom_t0;vardef_0__axiom_t1;vardef_0__axiom_t2;vardef_0__axiom_t3;vardef_0__axiom_t4;vardef_0__axiom_t5;vardef_0__axiom_t6;vardef_0__axiom_t7;vardef_0__axiom_t8;vardef_0__axiom_t9;vardef_0__axiom_t10;vardef_0__axiom_t11;vardef_0__axiom_t12;vardef_0__axiom_t13;vardef_0__axiom_t14;vardef_0__axiom_t15;vardef_0__axiom_t16;vardef_0__axiom_t17;vardef_0__axiom_t18;vardef_0__axiom_t19;vardef_0__axiom_t20;vardef_0__axiom_t21;vardef_0__axiom_t22;vardef_0__axiom_t23;vardef_0__axiom_t24;vardef_0__axiom_t25;vardef_0__axiom_t26;vardef_0__axiom_t27;vardef_0__axiom_t28;vardef_0__axiom_t29;vardef_0__axiom_t30;vardef_0__axiom_t31;vardef_0__axiom_t32;vardef_0__axiom_t33;vardef_0__axiom_t34;vardef_0__axiom_t35;vardef_0__axiom_t36;vardef_0__axiom_t37;vardef_0__axiom_t38;vardef_0__axiom_t39;vardef_0__axiom_t40;vardef_0__axiom_t41].
Definition slot i := List.nth i slots vardef_0__axiom_t0.
Definition constant (z:Z) : AxiomStructure.LocalAction Z := Done _ _ _ z.
Definition readlocal name : AxiomStructure.LocalAction Z := numberLocalGet _ _ _ name.
Definition wire i := match i with O=>constant 0 | S j=>readlocal (slot j) end.
Definition operands op : Z * AxiomStructure.LocalAction Z * AxiomStructure.LocalAction Z :=
  match op with
  | FormulaCircuit.equal i j => (1,constant (Z.of_nat i),constant (Z.of_nat j))
  | FormulaCircuit.member i j => (2,constant (Z.of_nat i),constant (Z.of_nat j))
  | FormulaCircuit.implies i j => (3,wire i,wire j)
  | FormulaCircuit.all i => (4,wire i,constant 0)
  end.
Definition call op : AxiomStructure.LocalAction unit :=
  let '(tag,a,b):=operands op in
  constant tag >>= fun preset0 => a >>= fun preset1 => b >>= fun preset2 =>
  ((((Done _ _ _ (fun _=>0%Z)) >>= fun x=>Done _ _ _ (update x vardef_0__intern_tag preset0))
    >>= fun x=>Done _ _ _ (update x vardef_0__intern_a preset1))
    >>= fun x=>Done _ _ _ (update x vardef_0__intern_b preset2)) >>= fun x=>
  (Done _ _ _ (fun _=>false)) >>= fun y=>liftToWithLocalVariables (funcdef_0__intern y x).
Definition save i : AxiomStructure.LocalAction unit :=
  ((constant 0 >>= fun x=>retrieve _ _ _ arraydef_0__meta x) >>= fun x=>numberLocalSet _ _ _ (slot i) x).
Definition finish i : AxiomStructure.LocalAction unit :=
  (constant 0 >>= fun x=>(readlocal (slot i) >>= fun v=>Done _ _ _ v) >>= fun y=>store _ _ _ arraydef_0__meta x y) >>= fun _=>
  (constant 13 >>= fun x=>(constant 1 >>= fun v=>Done _ _ _ v) >>= fun y=>store _ _ _ arraydef_0__meta x y) >>= fun _=>Done _ _ _ tt.
Fixpoint program plan start : AxiomStructure.LocalAction unit := match plan with
| []=>finish (Nat.pred start)
| op::tail=>call op >>= fun _=>save start >>= fun _=>program tail (S start)
end.
Lemma actual which :
  (match which with
  | AxiomFixedCircuits.extensionality=>AxiomStructure.handler_9
  | AxiomFixedCircuits.foundation=>AxiomStructure.handler_10
  | AxiomFixedCircuits.pairing=>AxiomStructure.handler_11
  | AxiomFixedCircuits.union=>AxiomStructure.handler_12
  | AxiomFixedCircuits.power=>AxiomStructure.handler_13
  | AxiomFixedCircuits.infinity=>AxiomStructure.handler_14
  | AxiomFixedCircuits.choice=>AxiomStructure.handler_17 end)=
  program (AxiomFixedCircuits.plan which) 0.
Proof. destruct which; reflexivity. Qed.


Local Opaque funcdef_0__intern Imperative.update.
Definition environment (f:AxiomRefl.Frame) start ids :=
  length ids=S start /\ List.nth 0 ids 0=0 /\
  (forall i,(i<start)%nat -> nums f (slot i)=List.nth (S i) ids 0).
Definition valid_op start op := match op with
| FormulaCircuit.implies i j => (i<=start /\ j<=start)%nat
| FormulaCircuit.all i => (i<=start)%nat
| _ => True end.
Fixpoint valid plan start := match plan with
| []=>True | op::tail=>(start<42)%nat /\ valid_op start op /\ valid tail (S start) end.
Lemma plans_valid which : valid (AxiomFixedCircuits.plan which) 0.
Proof. destruct which;cbn [AxiomFixedCircuits.plan AxiomFixedCircuits.extensionality_plan AxiomFixedCircuits.foundation_plan AxiomFixedCircuits.pairing_plan AxiomFixedCircuits.union_plan AxiomFixedCircuits.power_plan AxiomFixedCircuits.infinity_plan AxiomFixedCircuits.choice_plan valid valid_op];repeat split;lia. Qed.
Lemma slots_nodup : List.NoDup slots.
Proof. unfold slots. repeat (apply List.NoDup_cons;[cbn;intuition congruence|]). apply List.NoDup_nil. Qed.
Lemma slot_injective i j : (i<42)%nat -> (j<42)%nat -> slot i=slot j -> i=j.
Proof.
  intros Hi Hj Heq. apply (proj1 (List.NoDup_nth slots vardef_0__axiom_t0) slots_nodup i j);try assumption.
Qed.
Lemma slot_not_tag i : slot i<>vardef_0__axiom_tag.
Proof. unfold slot,slots. do 42 (destruct i as [|i];[discriminate|]);destruct i;discriminate. Qed.
Lemma wire_run f start ids i observations : environment f start ids -> (i<=start)%nat ->
  execLocalObserved (wire i) (f,observations)=Some (List.nth i ids 0,(f,observations)).
Proof.
  intros [Hlen [Hzero Henv]] Hi. destruct i as [|i];cbn [wire constant readlocal execLocalObserved localStepObserved fst snd].
  - now rewrite Hzero.
  - change (Some (nums f (slot i),(f,observations))=Some (List.nth (S i) ids 0,(f,observations))). rewrite Henv by lia. reflexivity.
Qed.


Lemma call_run (f:AxiomRefl.Frame) start ids op built observations :
  environment f start ids -> valid_op start op ->
  execObserved (funcdef_0__intern (fun _=>false) (FormulaCircuit.parameters ids op)) (machine f,observations)=Some (tt,(built,observations)) ->
  execLocalObserved (call op) (f,observations)=Some (tt,(setMachine f built,observations)).
Proof.
  intros Henv Hop Hrun. destruct op as [i j|i j|i j|i];unfold call,operands;
    repeat first [progress cbn [optionBind fst snd]
      |progress unfold constant at 1
      |match goal with |- context [execLocalObserved (wire ?k) (f,observations)] => rewrite (wire_run f start ids k observations Henv ltac:(cbn [valid_op] in Hop;lia)) end
      |NativePrimitives.primitive ltac:(fun frame name slot=>lia)
      |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
         let expression:=constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
         let Hsame:=fresh in assert (Hsame:expression=Some (tt,(built,observations))) by exact Hrun;rewrite Hsame;clear Hsame end];reflexivity.
Qed.
Definition advanced (f:AxiomRefl.Frame) built start id := setNum (setMachine f built) (slot start) id.
Lemma save_run (f:AxiomRefl.Frame) start observations :
  (0<length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved (save start) (f,observations)=Some (tt,(setNum f (slot start) (meta_value (machine f) 0),observations)).
Proof.
  intro Hmeta. unfold save,constant.
  repeat first [progress cbn [optionBind fst snd]|NativePrimitives.primitive ltac:(fun frame name slot=>exact Hmeta)
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity]. reflexivity.
Qed.
Lemma advance_environment f built start ids id :
  environment f start ids -> (start<42)%nat ->
  environment (advanced f built start id) (S start) (ids++[id]).
Proof.
  intros [Hlen [Hzero Henv]] Hstart. split;[rewrite length_app;cbn;lia|]. split.
  - rewrite List.app_nth1 by lia. exact Hzero.
  - intros i Hi. unfold advanced. cbn [nums setNum setMachine]. destruct (Nat.eq_dec i start) as [->|Hneq].
    + rewrite RenameMemoControl.updated_same. rewrite List.app_nth2 by lia. replace (S start-length ids)%nat with 0%nat by lia. reflexivity.
    + rewrite RenameMemoControl.updated_other by (intro Heq;apply Hneq;eapply slot_injective;[lia|lia|exact Heq]).
      rewrite List.app_nth1 by lia. apply Henv;lia.
Qed.


Lemma finish_run (f:AxiomRefl.Frame) i observations :
  (13<length (memory (machine f) arraydef_0__meta))%nat ->
  nums f (slot i)=meta_value (machine f) 0 ->
  execLocalObserved (finish i) (f,observations)=Some (tt,(setMachine f (AxiomRefl.finished (machine f)),observations)).
Proof.
  intros Hmeta Hvalue. unfold finish,constant,readlocal.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine];rewrite ?store_meta_length;lia)
    |progress rewrite Hvalue
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 13) with 13%nat by reflexivity
    |progress cbv beta iota zeta delta [machine setMachine nums bools]
  ]. reflexivity.
Qed.
Theorem run plan s ids built result observations :
  FormulaCircuit.executes observations plan s ids built result ->
  forall (f:AxiomRefl.Frame) start,
  machine f=s -> environment f start ids -> valid plan start ->
  (13<length (memory s arraydef_0__meta))%nat ->
  (start>0)%nat \/ plan<>[] ->
  (start=0)%nat \/ List.nth start ids 0=meta_value s 0 ->
  exists after,execLocalObserved (program plan start) (f,observations)=Some (tt,(after,observations)) /\
    machine after=AxiomRefl.finished built /\ nums after vardef_0__axiom_tag=nums f vardef_0__axiom_tag.
Proof.
  intro Htrace. induction Htrace as [s ids|op tail s ids middle id final result Hrun Hvalue Hmiddle Htail IH].
  - intros f start Hmachine Henv Hvalid Hmeta Hnonempty Hlast.
    assert (Hpositive:(0<start)%nat) by (destruct Hnonempty;[lia|contradiction]).
    assert (Hlocal:nums f (slot (Nat.pred start))=meta_value (machine f) 0).
    { destruct Henv as [Hlen [Hzero Henv]]. rewrite Henv by lia.
      replace (S (Nat.pred start)) with start by lia. rewrite Hmachine. destruct Hlast;[lia|assumption]. }
    exists (setMachine f (AxiomRefl.finished (machine f))). split.
    + cbn [program]. apply finish_run;[now rewrite Hmachine|exact Hlocal].
    + split;[cbn [machine setMachine];now rewrite Hmachine|reflexivity].
  - intros f start Hmachine Henv [Hstart [Hop Hvalid]] Hmeta Hnonempty Hlast.
    assert (Hcall:execLocalObserved (call op) (f,observations)=Some (tt,(setMachine f middle,observations))).
    { apply (call_run f start ids op middle observations Henv Hop). now rewrite Hmachine. }
    assert (Hlen: length (memory middle arraydef_0__meta)=length (memory s arraydef_0__meta)).
    { exact (proj1 (InternLengths.observed_lengths _ _ _ _ _ _ Hrun)). }
    assert (Hnextmeta:(13<length (memory middle arraydef_0__meta))%nat) by lia.
    assert (Hnextenv:environment (advanced f middle start id) (S start) (ids++[id])) by (now apply advance_environment).
    assert (Hnextlast:List.nth (S start) (ids++[id]) 0=meta_value middle 0).
    { rewrite List.app_nth2 by (destruct Henv as [Hlenids _];lia).
      replace (S start-length ids)%nat with 0%nat by (destruct Henv as [Hlenids _];lia). cbn. symmetry;exact Hvalue. }
    assert (Hpositive:(S start>0)%nat) by lia.
    destruct (IH (advanced f middle start id) (S start) eq_refl Hnextenv Hvalid Hnextmeta (or_introl Hpositive) (or_intror Hnextlast))
      as [after [Hafter [Hfinal Htag]]].
    exists after. split.
    + cbn [program]. rewrite local_bind,Hcall. cbn [optionBind fst snd].
      rewrite local_bind.
      match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (save start) ?state] =>
        let expression:=constr:(@execLocalObserved I T EI V EV R (save start) state) in
        let Hsave:=fresh in assert (Hsave:expression=Some (tt,(setNum (setMachine f middle) (slot start) (meta_value middle 0),observations)))
          by exact (save_run (setMachine f middle) start observations Hmiddle);rewrite Hsave;clear Hsave end.
      cbn [optionBind fst snd machine setMachine]. rewrite Hvalue. exact Hafter.
    + split;[exact Hfinal|]. rewrite Htag. unfold advanced. cbn [nums setNum setMachine].
      rewrite RenameMemoControl.updated_other by (intro Heq;apply (slot_not_tag start);symmetry;exact Heq). reflexivity.
Qed.


Lemma handler_actual which : AxiomDispatch.handler_for (AxiomFixedCircuits.selector which)=program (AxiomFixedCircuits.plan which) 0.
Proof. destruct which;reflexivity. Qed.
Theorem generated which (f:AxiomRefl.Frame) built ids observations :
  (13<length (memory (machine f) arraydef_0__meta))%nat ->
  FormulaCircuit.executes observations (AxiomFixedCircuits.plan which) (machine f) [0%Z] built ids ->
  exists after,execLocalObserved (AxiomDispatch.handler_for (AxiomFixedCircuits.selector which)) (f,observations)=Some (tt,(after,observations)) /\
    machine after=AxiomRefl.finished built /\ nums after vardef_0__axiom_tag=nums f vardef_0__axiom_tag.
Proof.
  intros Hmeta Htrace. rewrite handler_actual. eapply (run _ _ _ _ _ _ Htrace f 0);[reflexivity| |apply plans_valid|exact Hmeta| |].
  - split;[reflexivity|]. split;[reflexivity|]. intros i Hi;lia.
  - right. apply AxiomFixedCircuits.nonempty.
  - left;reflexivity.
Qed.
End NativeAxiomBuilder.
