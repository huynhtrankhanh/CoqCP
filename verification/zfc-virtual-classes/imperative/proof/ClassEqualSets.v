From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives Observation Intern InternBounded FormulaEncoding Representation ClassStorage ClassLookup RenameStorage.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ClassEqualSets.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual.
Definition arguments left right : varsfuncdef_0__intern -> Z :=
  update (update (update (fun _ => 0) vardef_0__intern_tag 1) vardef_0__intern_a left) vardef_0__intern_b right.
Local Opaque funcdef_0__intern funcdef_0__predicate.
Theorem generated_body (f : Frame) final a b left right observations :
  nums f vardef_0__classEqual_a = Z.of_nat a -> nums f vardef_0__classEqual_b = Z.of_nat b ->
  (a < length (memory (machine f) arraydef_0__classes))%nat -> (b < length (memory (machine f) arraydef_0__classes))%nat ->
  nth_error (memory (machine f) arraydef_0__classes) a = Some (0,left) ->
  nth_error (memory (machine f) arraydef_0__classes) b = Some (0,right) ->
  execObserved (funcdef_0__intern (fun _ => false) (arguments left right)) (machine f,observations) = Some (tt,(final,observations)) ->
  execLocalObserved funcdef_0__classEqual_body (f,observations) = Some (tt,(setMachine f final,observations)).
Proof.
  intros Ha Hb Habound Hbbound Hleft Hright Hintern.
  pose proof (List.nth_error_nth _ _ (0,0) Hleft) as Hleftnth.
  pose proof (List.nth_error_nth _ _ (0,0) Hright) as Hrightnth.
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold funcdef_0__classEqual_body.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id; first [exact Habound|exact Hbbound])
    |match goal with |- context [List.nth ?i (memory ?source arraydef_0__classes) ?zero] =>
       let expression := constr:(List.nth i (memory source arraydef_0__classes) zero) in
       let Hsame := fresh in first
         [assert (Hsame : expression = (0,left)) by exact Hleftnth
         |assert (Hsame : expression = (0,right)) by exact Hrightnth]; rewrite Hsame; clear Hsame end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression := constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       let Hrun := fresh in assert (Hrun : expression = Some (tt,(final,observations))) by exact Hintern; rewrite Hrun; clear Hrun end
    |progress rewrite Ha |progress rewrite Hb |progress rewrite Nat2Z.id
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence |progress rewrite (bool_decide_false P) by congruence] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence |progress rewrite (decide_False (P:=P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. reflexivity.
Qed.
Theorem generated_helper s bs ns final a b left right observations :
  ns vardef_0__classEqual_a = Z.of_nat a -> ns vardef_0__classEqual_b = Z.of_nat b ->
  (a < length (memory s arraydef_0__classes))%nat -> (b < length (memory s arraydef_0__classes))%nat ->
  nth_error (memory s arraydef_0__classes) a = Some (0,left) -> nth_error (memory s arraydef_0__classes) b = Some (0,right) ->
  execObserved (funcdef_0__intern (fun _ => false) (arguments left right)) (s,observations) = Some (tt,(final,observations)) ->
  execObserved (funcdef_0__classEqual bs ns) (s,observations) = Some (tt,(final,observations)).
Proof.
  intros Ha Hb Habound Hbbound Hleft Hright Hintern.
  pose proof (generated_body {|machine:=s;bools:=bs;nums:=ns|} final a b left right observations Ha Hb Habound Hbbound Hleft Hright Hintern) as Hbody.
  unfold Frame in Hbody. pose proof (eliminate_correct funcdef_0__classEqual_body bs ns s observations) as Heliminate.
  rewrite Hbody in Heliminate. exact Heliminate.
Qed.
Lemma set_lookup s fs classes index variable : ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes index = Some (VirtualClasses.set variable) ->
  (index < length (memory s arraydef_0__classes))%nat /\ word (Z.of_nat variable) /\
  nth_error (memory s arraydef_0__classes) index = Some (0,Z.of_nat variable).
Proof.
  intros Hclasses Hwellformed Hlookup.
  destruct (ClassLookup.lookup s fs classes index _ Hclasses Hwellformed Hlookup) as [Hbound Hraw]. split; [exact Hbound|].
  destruct Hraw as [[value [Heq [Hword Hrecord]]]|[root [p [Heq Hrest]]]]; [injection Heq as <-; auto|discriminate].
Qed.
Lemma intern_frame s t : InternExecution.logical_frame s t -> RenameStorage.logical_frame s t.
Proof.
  intros [Ha [Hc Hio]]. split.
  - intros name Hprotected. unfold RenameStorage.Arrays.persistent_array in Hprotected. apply Ha; intuition congruence.
  - split; [|exact Hio]. intros cell Hcell. unfold RenameStorage.Cells.protected in Hcell. apply Hc; tauto.
Qed.
Theorem generated_refines s bs ns fs classes a b left right observations :
  NativeRepresentation.canonical_arena s fs -> meta_value s 8 = 0 -> Z.of_nat (length fs) <= 9223372036854775807 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a = Some (VirtualClasses.set left) -> nth_error classes b = Some (VirtualClasses.set right) ->
  ns vardef_0__classEqual_a = Z.of_nat a -> ns vardef_0__classEqual_b = Z.of_nat b ->
  exists final next index, execObserved (funcdef_0__classEqual bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (VirtualClasses.erase (VirtualClasses.class_equal (VirtualClasses.set left) (VirtualClasses.set right))) /\
    (exists extra, next = fs ++ extra) /\ meta_value final 8 = 0 /\ RenameStorage.logical_frame s final /\
    ClassStorage.represents final next classes /\ ClassLookup.wellformed final.
Proof.
  intros Harena Herror Hcapacity Hclasses Hwellformed Hleft Hright Ha Hb.
  destruct (set_lookup s fs classes a left Hclasses Hwellformed Hleft) as [Habound [Hleftword Hleftrecord]].
  destruct (set_lookup s fs classes b right Hclasses Hwellformed Hright) as [Hbbound [Hrightword Hrightrecord]].
  assert (Hnormal : FormulaEncoding.normal (arguments (Z.of_nat left) (Z.of_nat right) vardef_0__intern_tag,
    arguments (Z.of_nat left) (Z.of_nat right) vardef_0__intern_a,arguments (Z.of_nat left) (Z.of_nat right) vardef_0__intern_b)).
  { change (FormulaEncoding.normal (1,Z.of_nat left,Z.of_nat right)). right. left. auto. }
  assert (Hdecode : FormulaEncoding.decode fs (arguments (Z.of_nat left) (Z.of_nat right) vardef_0__intern_tag,
    arguments (Z.of_nat left) (Z.of_nat right) vardef_0__intern_a,arguments (Z.of_nat left) (Z.of_nat right) vardef_0__intern_b) = Some (SetTheory.equal left right)).
  { change (Some (SetTheory.equal (Z.to_nat (Z.of_nat left)) (Z.to_nat (Z.of_nat right))) = Some (SetTheory.equal left right)). now rewrite !Nat2Z.id. }
  destruct (InternBounded.generated_refines s (fun _=>false) (arguments (Z.of_nat left) (Z.of_nat right)) fs (SetTheory.equal left right) Harena Herror Hcapacity Hnormal Hdecode)
    as [final [next [index [Hintern [Hlogical [Hflag [Hindex [Hindexword [Hnext [Hmeaning Hextends]]]]]]]]]].
  pose proof (intern_frame s final Hlogical) as Hframe.
  exists final,next,index. split.
  - eapply generated_helper; try eassumption. apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern].
  - split; [exact Hnext|]. split; [exact Hindex|]. split; [unfold word; lia|]. split; [exact Hmeaning|].
    split; [exact Hextends|]. split; [exact Hflag|]. split; [exact Hframe|]. split.
    + destruct Hextends as [extra ->]. exact (RenameStorage.classes_transport s final fs extra classes Hframe Hclasses).
    + now apply (ClassLookup.frame_wellformed s final).
Qed.
End ClassEqualSets.
