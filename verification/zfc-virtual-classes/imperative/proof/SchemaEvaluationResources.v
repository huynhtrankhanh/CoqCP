From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash SchemaGraph SchemaEvaluation AxiomTaggedInvariant
  RenameMemoBounds RenameMemoIndexBounds RenameMemoTransition RenameMemoClassEqual RenameMemoClassMember RenameMemoResourceBounds.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationResources.
Import IndexExecution SipHashExecution.
Definition argument (native:Machine) (classes:list VirtualClasses.class) rho a := exists id,
  nth_error (memory native arraydef_0__schemaArguments) a=Some (Z.of_nat id) /\
  word (Z.of_nat id) /\ nth_error classes id=Some (rho a).
Definition class_room (classes:list VirtualClasses.class) := Z.of_nat (length classes+1)<=maximum.
Definition formula_room (fs:list SetTheory.formula) := Z.of_nat (length fs+1)<=9223372036854775807.
Definition shifted (native:Machine) fs classes rho depth a :=
  argument native classes rho a /\
  (depth<>0%nat -> class_room classes /\
    (forall variable,rho a=VirtualClasses.set variable -> Z.of_nat variable+Z.of_nat depth<=maximum) /\
    (forall cls root p,nth_error (memory native arraydef_0__classes) cls=Some (1,Z.of_nat root) ->
      nth_error fs root=Some p ->
      exists bound,
        Z.of_nat (RenameMemoBounds.fuel root)<=maximum /\ RenameMemoIndexBounds.formula_bound bound p /\
        Z.of_nat bound+Z.of_nat depth<=maximum /\ Z.of_nat (S (RenameMemoTransition.height p))<=maximum /\
        Z.of_nat (length fs+S root*S root)<=9223372036854775807)).
Definition equal (native:Machine) fs classes := forall ia ib ca cb,
  nth_error classes ia=Some ca -> nth_error classes ib=Some cb ->
  RenameMemoClassEqual.ready native fs ia ib ca cb /\
  Z.of_nat (length fs+RenameMemoClassEqual.work native ia ib ca cb)<=RenameMemoResourceBounds.doubling_limit.
Definition member (native:Machine) fs classes := forall ia ib ca cb,
  nth_error classes ia=Some ca -> nth_error classes ib=Some cb ->
  RenameMemoClassMember.ready native fs ia ib ca cb /\
  Z.of_nat (length fs+RenameMemoClassMember.work native ia ib ca cb)<=RenameMemoResourceBounds.doubling_limit.
Definition axiom fs tag rawJ := forall idA p,
  word (Z.of_nat idA) -> (AxiomTaggedInvariant.needs_p tag=true -> nth_error fs idA=Some p) ->
  exists bound,AxiomTaggedInvariant.renaming_ready tag idA rawJ p bound /\
    Z.of_nat (length fs+AxiomTaggedInvariant.cost tag idA)<=9223372036854775807.
(** Explicit sufficient mathematical resources for a single native cell. Only
    its instruction family requests a budget; no operational run is assumed. *)
Definition ready (native:Machine) fs classes rho depth (k a b c d:nat) : Prop :=
  match k with
  | 0%nat=>shifted native fs classes rho depth a
  | 3%nat=>class_room classes
  | 4%nat=>equal native fs classes
  | 5%nat=>member native fs classes
  | 6%nat | 7%nat | 10%nat=>formula_room fs
  | 8%nat=>axiom fs a c
  | _=>True end.
End SchemaEvaluationResources.
