From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives ArenaFrame Intern InternReserve InternLengths FormulaEncoding Representation RenameMemoControl.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomRefl.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom.
Definition arguments variable : varsfuncdef_0__intern -> Z :=
  update (update (update (fun _=>0) vardef_0__intern_tag 1) vardef_0__intern_a variable) vardef_0__intern_b variable.
Definition cleared s := store_meta s 13 0.
Definition finished s := store_meta (store_meta s 0 (meta_value s 0)) 13 1.
Definition result_frame (f : Frame) built := setMachine (setNum f vardef_0__axiom_t0 (meta_value built 0)) (finished built).
Local Opaque funcdef_0__intern funcdef_0__rename Imperative.update.
Theorem generated_body (f : Frame) built variable observations :
  (13 < length (memory (machine f) arraydef_0__meta))%nat ->
  (13 < length (memory built arraydef_0__meta))%nat ->
  nums f vardef_0__axiom_tag = 5 -> nums f vardef_0__axiom_p = variable ->
  execObserved (funcdef_0__intern (fun _=>false) (arguments variable)) (cleared (machine f),observations) = Some (tt,(built,observations)) ->
  execLocalObserved funcdef_0__axiom_body (f,observations) = Some (tt,(result_frame f built,observations)).
Proof.
  intros Hmeta Hbuilt Htag Hp Hintern.
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold funcdef_0__axiom_body.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot=>first [exact Hmeta|exact Hbuilt| rewrite !store_meta_length; first [exact Hmeta|exact Hbuilt]|cbn [machine setMachine setNum]; rewrite ?store_meta_length; lia])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(built,observations))) by exact Hintern; rewrite Hrun; clear Hrun end
    |progress rewrite Htag |progress rewrite Hp
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence |progress rewrite (bool_decide_false P) by congruence] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence |progress rewrite (decide_False (P:=P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ]. reflexivity.
Qed.
Theorem generated_helper s bs ns built variable observations :
  (13 < length (memory s arraydef_0__meta))%nat -> (13 < length (memory built arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag = 5 -> ns vardef_0__axiom_p = variable ->
  execObserved (funcdef_0__intern (fun _=>false) (arguments variable)) (cleared s,observations) = Some (tt,(built,observations)) ->
  execObserved (funcdef_0__axiom bs ns) (s,observations) = Some (tt,(finished built,observations)).
Proof.
  intros Hmeta Hbuilt Htag Hp Hintern.
  pose proof (generated_body {|machine:=s;bools:=bs;nums:=ns|} built variable observations Hmeta Hbuilt Htag Hp Hintern) as Hbody.
  unfold Frame in Hbody. pose proof (eliminate_correct funcdef_0__axiom_body bs ns s observations) as Heliminate.
  rewrite Hbody in Heliminate. exact Heliminate.
Qed.
Local Transparent Imperative.update.
Definition logical_frame (s t : Machine) :=
  (forall name, name <> arraydef_0__meta -> name <> arraydef_0__sipState ->
    name <> arraydef_0__formulas -> name <> arraydef_0__formulaLinks -> name <> arraydef_0__formulaBuckets -> memory t name = memory s name) /\
  (forall i, i <> 0%nat -> i <> 1%nat -> i <> 8%nat -> i <> 13%nat -> i <> 20%nat -> i <> 21%nat -> i <> 28%nat -> meta_value t i = meta_value s i) /\
  stdin t = stdin s /\ stdout t = stdout s.
Lemma frame s built : InternExecution.logical_frame (cleared s) built -> logical_frame s (finished built).
Proof.
  intros [Ha [Hc [Hi Ho]]]. unfold logical_frame, finished, cleared in *.
  split.
  - intros name Hm Hs Hf Hl Hb. rewrite !store_meta_other by assumption. rewrite Ha by assumption. now apply store_meta_other.
  - split.
    + intros i H0 H1 H8 H13 H20 H21 H28. rewrite !meta_store_other by assumption.
      rewrite Hc by assumption. now rewrite meta_store_other by assumption.
    + split; assumption.
Qed.
Lemma finished_storage s : ArenaFrame.storage s (finished s).
Proof. unfold finished. ArenaFrame.storage_steps. Qed.
Theorem generated_refines s bs ns fs variable reserve observations :
  NativeRepresentation.canonical_arena s fs -> meta_value s 8 = 0 ->
  (13 < length (memory s arraydef_0__meta))%nat -> word (Z.of_nat variable) ->
  Z.of_nat (length fs + S reserve) <= 9223372036854775807 ->
  ns vardef_0__axiom_tag = 5 -> ns vardef_0__axiom_p = Z.of_nat variable ->
  exists final next index, execObserved (funcdef_0__axiom bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (SetTheory.equal variable variable) /\
    SetTheory.derives (SetTheory.equal variable variable) /\
    (exists extra, next = fs ++ extra) /\ meta_value final 8 = 0 /\ meta_value final 13 = 1 /\
    logical_frame s final /\ Z.of_nat (length next + reserve) <= 9223372036854775807.
Proof.
  intros Harena Herror Hmeta Hvariable Hreserve Htag Hp.
  assert (Hstorage : ArenaFrame.storage s (cleared s)).
  { unfold cleared. apply ArenaFrame.storage_meta; lia. }
  assert (Hclear : NativeRepresentation.canonical_arena (cleared s) fs).
  { exact (ArenaFrame.storage_arena s (cleared s) fs Hstorage Harena). }
  assert (Hclearerror : meta_value (cleared s) 8 = 0).
  { unfold cleared. rewrite meta_store_other by discriminate. exact Herror. }
  assert (Hnormal : FormulaEncoding.normal (arguments (Z.of_nat variable) vardef_0__intern_tag,
    arguments (Z.of_nat variable) vardef_0__intern_a,arguments (Z.of_nat variable) vardef_0__intern_b)).
  { change (FormulaEncoding.normal (1,Z.of_nat variable,Z.of_nat variable)). right. left. auto. }
  assert (Hdecode : FormulaEncoding.decode fs (arguments (Z.of_nat variable) vardef_0__intern_tag,
    arguments (Z.of_nat variable) vardef_0__intern_a,arguments (Z.of_nat variable) vardef_0__intern_b) = Some (SetTheory.equal variable variable)).
  { change (Some (SetTheory.equal (Z.to_nat (Z.of_nat variable)) (Z.to_nat (Z.of_nat variable))) = Some (SetTheory.equal variable variable)). now rewrite Nat2Z.id. }
  destruct (InternReserve.generated_refines (cleared s) (fun _=>false) (arguments (Z.of_nat variable)) fs (SetTheory.equal variable variable) reserve observations
    Hclear Hclearerror Hreserve Hnormal Hdecode)
    as [built [next [index [Hrun [Hframe [Hnext [Hflag [Hindex [Hword [Hmeaning [Hextends Hremaining]]]]]]]]]]].
  destruct (InternLengths.observed_lengths (cleared s) (fun _=>false) (arguments (Z.of_nat variable)) observations built observations Hrun) as [Hlength Hsip].
  assert (Hbuilt : (13 < length (memory built arraydef_0__meta))%nat).
  { rewrite Hlength. unfold cleared. now rewrite store_meta_length. }
  exists (finished built),next,index. split.
  - eapply generated_helper; eassumption.
  - split; [exact (ArenaFrame.storage_arena built (finished built) next (finished_storage built) Hnext)|].
    split.
    + unfold finished. rewrite meta_store_other by discriminate. rewrite meta_store_same by lia. exact Hindex.
    + split; [exact Hword|]. split; [exact Hmeaning|]. split; [apply SetTheory.d_refl|]. split; [exact Hextends|].
      split.
      * unfold finished. rewrite !meta_store_other by discriminate. exact Hflag.
      * split.
        -- unfold finished. rewrite meta_store_same; [reflexivity|rewrite store_meta_length; exact Hbuilt].
        -- split; [now apply frame|exact Hremaining].
Qed.
End AxiomRefl.

