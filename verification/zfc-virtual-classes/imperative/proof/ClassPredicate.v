From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash Lift RenameInvariant RenameStack ClassStorage ClassLookup PredicateRefinement RenameStorage Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ClassPredicate.
Import IndexExecution SipHashExecution IndexSemantics.
Definition work cls := match cls with
  | VirtualClasses.set _ => 1%nat | VirtualClasses.abstract body => RenameStack.work (VirtualClasses.erase body) end.
Definition fits cls shift arg := match cls with
  | VirtualClasses.set variable => word (Z.of_nat variable) /\ word (Z.of_nat (variable + shift))
  | VirtualClasses.abstract body => RenameInvariant.fits (renaming predicate_mode shift arg) 0 (VirtualClasses.erase body) end.
Theorem generated_refines s bs ns fs classes cls index shift arg observations :
  NativeRepresentation.canonical_arena s fs -> nth_error fs 0 = Some SetTheory.falsity -> meta_value s 8 = 0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s -> nth_error classes index = Some cls ->
  ns vardef_0__predicate_cls = Z.of_nat index -> ns vardef_0__predicate_shift = Z.of_nat shift -> ns vardef_0__predicate_arg = Z.of_nat arg ->
  fits cls shift arg -> word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  Z.of_nat (length fs + work cls) <= RenameInvariant.resource_limit ->
  exists final next result, execObserved (funcdef_0__predicate bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat result /\ word (Z.of_nat result) /\
    nth_error next result = Some (VirtualClasses.predicate cls (fun n => (n + shift)%nat) arg) /\
    (exists extra, next = fs ++ extra) /\ meta_value final 8 = 0 /\
    (length next <= length fs + work cls)%nat /\ RenameStorage.logical_frame s final /\
    ClassStorage.represents final next classes /\ ClassLookup.wellformed final.
Proof.
  intros Harena Hfalse Herror Hclasses Hwellformed Hlookup Hindex Hshift Harg Hfits Hshiftword Hargword Hbudget.
  destruct (ClassLookup.lookup s fs classes index cls Hclasses Hwellformed Hlookup) as [Hbound Hclass].
  assert (Hresult : exists final next result,
    execObserved (funcdef_0__predicate bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat result /\ word (Z.of_nat result) /\
    nth_error next result = Some (VirtualClasses.predicate cls (fun n => (n + shift)%nat) arg) /\
    (exists extra, next = fs ++ extra) /\ meta_value final 8 = 0 /\ (length next <= length fs + work cls)%nat).
  { destruct Hclass as [[variable [-> [Hvariable Hraw]]]|[root [p [-> [Hp Hraw]]]]].
    - destruct Hfits as [Hword Hsumword].
      assert (Hcapacity : Z.of_nat (length fs) <= RenameInvariant.resource_limit).
      { cbn [work] in Hbudget. rewrite Nat2Z.inj_add in Hbudget. lia. }
      destruct (PredicateRefinement.generated_set_refines s bs ns fs index variable shift arg observations Harena Herror Hcapacity Hindex Hshift Harg Hbound Hraw Hword Hshiftword Hargword Hsumword)
        as [final [next [result [Hrun [Hnext [Hvalue [Hresultword [Hmeaning [Hextends [Hflag Hgrowth]]]]]]]]]].
      exists final,next,result. split; [exact Hrun|]. split; [exact Hnext|]. split; [exact Hvalue|]. split; [exact Hresultword|]. split; [exact Hmeaning|]. split; [exact Hextends|]. split; [exact Hflag|]. cbn [work]. lia.
    - exact (PredicateRefinement.generated_abstract_refines s bs ns fs index root p shift arg observations Harena Hfalse Herror Hindex Hshift Harg Hbound Hraw Hp Hfits Hshiftword Hargword Hbudget). }
  destruct Hresult as [final [next [result [Hrun [Hnext [Hvalue [Hresultword [Hmeaning [Hextends [Hflag Hgrowth]]]]]]]]]].
  pose proof (RenameStorage.predicate_frame s bs ns final observations observations Hrun) as Hframe.
  exists final,next,result. split; [exact Hrun|]. split; [exact Hnext|]. split; [exact Hvalue|]. split; [exact Hresultword|]. split; [exact Hmeaning|]. split; [exact Hextends|]. split; [exact Hflag|]. split; [exact Hgrowth|]. split; [exact Hframe|]. split.
  - destruct Hextends as [extra ->]. exact (RenameStorage.classes_transport s final fs extra classes Hframe Hclasses).
  - now apply (ClassLookup.frame_wellformed s final).
Qed.
End ClassPredicate.
