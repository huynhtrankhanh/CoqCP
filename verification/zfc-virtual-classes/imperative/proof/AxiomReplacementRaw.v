From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  AxiomStructure AxiomDispatch AxiomRefl NativeAxiomBuilder AxiomReplacementCircuits InternLengths RenameMemoLengths.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomReplacementRaw.
Import IndexExecution SipHashExecution ObservedLocal NativeAxiomBuilder.
Module C:=AxiomReplacementCircuits.
Definition rename_call m : AxiomStructure.LocalAction unit :=
  readlocal vardef_0__axiom_p >>= fun preset0 => constant (mode_number (C.mode m)) >>= fun preset1 =>
  constant 0 >>= fun preset2 => constant 0 >>= fun preset3 =>
  (((((Done _ _ _ (fun _=>0%Z)) >>= fun x=>Done _ _ _ (update x vardef_0__rename_node preset0))
    >>= fun x=>Done _ _ _ (update x vardef_0__rename_mode preset1))
    >>= fun x=>Done _ _ _ (update x vardef_0__rename_shift preset2))
    >>= fun x=>Done _ _ _ (update x vardef_0__rename_arg preset3)) >>= fun x=>
  (Done _ _ _ (fun _=>false)) >>= fun y=>liftToWithLocalVariables (funcdef_0__rename y x).
Definition call instr := match instr with C.emit op=>NativeAxiomBuilder.call op | C.map m=>rename_call m end.
Fixpoint program instructions start : AxiomStructure.LocalAction unit := match instructions with
| []=>finish (Nat.pred start) | instr::tail=>call instr >>= fun _=>save start >>= fun _=>program tail (S start) end.
Definition valid_instr start instr := match instr with C.emit op=>valid_op start op | C.map _=>True end.
Fixpoint valid instructions start := match instructions with
| []=>True | instr::tail=>(start<42)%nat /\ valid_instr start instr /\ valid tail (S start) end.
Lemma actual : AxiomStructure.handler_16=program C.plan 0.
Proof. reflexivity. Qed.
Lemma plan_valid : valid C.plan 0.
Proof. cbn [C.plan valid valid_instr valid_op];repeat split;lia. Qed.
Lemma slot_not_p i : slot i<>vardef_0__axiom_p.
Proof. unfold slot,slots. do 42 (destruct i as [|i];[discriminate|]);destruct i;discriminate. Qed.
Local Opaque funcdef_0__intern funcdef_0__rename Imperative.update.
Lemma call_run (f:AxiomRefl.Frame) root start ids instr built observations :
  nums f vardef_0__axiom_p=root -> environment f start ids -> valid_instr start instr ->
  execObserved (C.native root ids instr) (machine f,observations)=Some (tt,(built,observations)) ->
  execLocalObserved (call instr) (f,observations)=Some (tt,(setMachine f built,observations)).
Proof.
  intros Hp Henv Hop Hrun. destruct instr as [op|m].
  - exact (NativeAxiomBuilder.call_run f start ids op built observations Henv Hop Hrun).
  - unfold call,rename_call,readlocal,constant.
    repeat first [progress cbn [optionBind fst snd]
      |progress rewrite Hp
      |NativePrimitives.primitive ltac:(fun frame name slot=>lia)
      |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__rename ?bi ?ni) ?state] =>
         let expression:=constr:(@execObserved I T EI R (funcdef_0__rename bi ni) state) in
         let Hsame:=fresh in assert (Hsame:expression=Some (tt,(built,observations))) by exact Hrun;rewrite Hsame;clear Hsame end];reflexivity.
Qed.
Lemma native_lengths root ids instr s built observations :
  execObserved (C.native root ids instr) (s,observations)=Some (tt,(built,observations)) ->
  length (memory built arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof.
  destruct instr as [op|m];intro Hrun;
    [exact (proj1 (InternLengths.observed_lengths _ _ _ _ _ _ Hrun))|
     exact (proj1 (RenameMemoLengths.observed_lengths _ _ _ _ _ _ Hrun))].
Qed.
Theorem run root plan s ids built result observations :
  C.executes observations root plan s ids built result ->
  forall (f:AxiomRefl.Frame) start,
  nums f vardef_0__axiom_p=root -> machine f=s -> environment f start ids -> valid plan start ->
  (13<length (memory s arraydef_0__meta))%nat ->
  (start>0)%nat \/ plan<>[] ->
  (start=0)%nat \/ List.nth start ids 0=meta_value s 0 ->
  exists after,execLocalObserved (program plan start) (f,observations)=Some (tt,(after,observations)) /\
    machine after=AxiomRefl.finished built /\ nums after vardef_0__axiom_tag=nums f vardef_0__axiom_tag.
Proof.
  intro Htrace. induction Htrace as [s ids|op tail s ids middle id final result Hrun Hvalue Hmiddle Htail IH].
  - intros f start Hp Hmachine Henv Hvalid Hmeta Hnonempty Hlast.
    assert (Hpositive:(0<start)%nat) by (destruct Hnonempty;[lia|contradiction]).
    assert (Hlocal:nums f (slot (Nat.pred start))=meta_value (machine f) 0).
    { destruct Henv as [Hlen [Hzero Henv]]. rewrite Henv by lia.
      replace (S (Nat.pred start)) with start by lia. rewrite Hmachine. destruct Hlast;[lia|assumption]. }
    exists (setMachine f (AxiomRefl.finished (machine f))). split.
    + cbn [program]. apply finish_run;[now rewrite Hmachine|exact Hlocal].
    + split;[cbn [machine setMachine];now rewrite Hmachine|reflexivity].
  - intros f start Hp Hmachine Henv [Hstart [Hop Hvalid]] Hmeta Hnonempty Hlast.
    assert (Hcall:execLocalObserved (call op) (f,observations)=Some (tt,(setMachine f middle,observations))).
    { apply (call_run f root start ids op middle observations Hp Henv Hop). now rewrite Hmachine. }
    assert (Hlen: length (memory middle arraydef_0__meta)=length (memory s arraydef_0__meta)).
    { exact (native_lengths _ _ _ _ _ _ Hrun). }
    assert (Hnextmeta:(13<length (memory middle arraydef_0__meta))%nat) by lia.
    assert (Hnextenv:environment (advanced f middle start id) (S start) (ids++[id])) by (now apply advance_environment).
    assert (Hnextlast:List.nth (S start) (ids++[id]) 0=meta_value middle 0).
    { rewrite List.app_nth2 by (destruct Henv as [Hlenids _];lia).
      replace (S start-length ids)%nat with 0%nat by (destruct Henv as [Hlenids _];lia). cbn. symmetry;exact Hvalue. }
    assert (Hpositive:(S start>0)%nat) by lia.
    assert (Hnextroot:nums (advanced f middle start id) vardef_0__axiom_p=root).
    { unfold advanced;cbn [nums setNum setMachine]. rewrite RenameMemoControl.updated_other by (intro Heq;apply (slot_not_p start);symmetry;exact Heq). exact Hp. }
    destruct (IH (advanced f middle start id) (S start) Hnextroot eq_refl Hnextenv Hvalid Hnextmeta (or_introl Hpositive) (or_intror Hnextlast))
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




Theorem generated_handler (f:AxiomRefl.Frame) root built ids observations :
  (13<length (memory (machine f) arraydef_0__meta))%nat -> nums f vardef_0__axiom_p=root ->
  C.executes observations root C.plan (machine f) [0] built ids ->
  exists after,execLocalObserved AxiomStructure.handler_16 (f,observations)=Some (tt,(after,observations)) /\
    machine after=AxiomRefl.finished built /\ nums after vardef_0__axiom_tag=nums f vardef_0__axiom_tag.
Proof.
  intros Hmeta Hp Htrace. rewrite actual. eapply (run _ _ _ _ _ _ _ Htrace f 0);[exact Hp|reflexivity| |apply plan_valid|exact Hmeta| |].
  - split;[reflexivity|]. split;[reflexivity|]. intros i Hi;lia.
  - right;discriminate.
  - left;reflexivity.
Qed.
Theorem generated_helper s bs ns root built ids observations :
  (13<length (memory s arraydef_0__meta))%nat -> ns vardef_0__axiom_tag=16 -> ns vardef_0__axiom_p=root ->
  root<meta_value s 1 -> C.executes observations root C.plan (AxiomRefl.cleared s) [0] built ids ->
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations)).
Proof.
  intros Hmeta Htag Hp Hroot Htrace.
  apply (AxiomDispatch.generated_projected s bs ns 16 (AxiomRefl.finished built) observations observations).
  - lia.
  - exact Htag.
  - unfold AxiomDispatch.references_valid,AxiomDispatch.reference_names. constructor;[cbn [nums machine];now rewrite Hp|constructor].
  - exact Hmeta.
  - destruct (generated_handler (AxiomDispatch.cleared_frame {|machine:=s;bools:=bs;nums:=ns|}) root built ids observations
      ltac:(cbn [AxiomDispatch.cleared_frame machine setMachine];rewrite store_meta_length;exact Hmeta) Hp Htrace)
      as [after [Hlocal [Hmachine Htagafter]]].
    change (optionBind (execLocalObserved AxiomStructure.handler_16
      (AxiomDispatch.cleared_frame {|machine:=s;bools:=bs;nums:=ns|},observations))
      (fun r=>Some (fst r,(machine (fst (snd r)),snd (snd r))))=Some (tt,(AxiomRefl.finished built,observations))).
    match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R AxiomStructure.handler_16 ?state] =>
      let expression:=constr:(@execLocalObserved I T EI V EV R AxiomStructure.handler_16 state) in
      let Hsame:=fresh in assert (Hsame:expression=Some (tt,(after,observations))) by exact Hlocal;rewrite Hsame;clear Hsame end.
    cbn [optionBind fst snd]. now rewrite Hmachine.
Qed.
End AxiomReplacementRaw.
