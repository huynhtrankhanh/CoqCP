From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash NativeState ClassStorage ClassLookup RenameMemoClassEqual RenameMemoClassMember RenameMemoCallers RenameMemoResourceBounds.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSpacedSetBinaryResources.
Import IndexExecution SipHashExecution.
Definition set_domain logical a b := forall ca cb, Protocol.class_at logical a=Some ca -> Protocol.class_at logical b=Some cb ->
 exists x y, ca=VirtualClasses.set x /\ cb=VirtualClasses.set y.
Lemma set_lookup native logical i x : NativeState.represents native logical -> ClassLookup.wellformed native -> Protocol.class_at logical i=Some(VirtualClasses.set x) ->
 word(Z.of_nat x) /\ nth_error(memory native arraydef_0__classes)i=Some(0,Z.of_nat x).
Proof.
 intros Hstate Hgood Hlookup. destruct(ClassLookup.lookup native (Protocol.formulas logical)(Protocol.classes logical) i (VirtualClasses.set x)
  (NativeState.class_representation _ _ Hstate) Hgood Hlookup) as (_ & [[y [Heq [Hword Hraw]]]|[root [p [Heq _]]]]).
 - injection Heq as <-. split;assumption.
 - discriminate.
Qed.
Theorem equal native logical a b : NativeState.represents native logical -> ClassLookup.wellformed native -> set_domain logical a b ->
 Z.of_nat(S(length(Protocol.formulas logical)))<=RenameMemoResourceBounds.doubling_limit ->
 forall ca cb, Protocol.class_at logical a=Some ca -> Protocol.class_at logical b=Some cb ->
 RenameMemoClassEqual.ready native (Protocol.formulas logical) a b ca cb /\
 Z.of_nat(length(Protocol.formulas logical)+RenameMemoClassEqual.work native a b ca cb)<=RenameMemoResourceBounds.doubling_limit.
Proof.
 intros Hstate Hgood Hsets Hbound ca cb Ha Hb. destruct(Hsets ca cb Ha Hb) as(x & y & -> & ->).
 cbn [RenameMemoClassEqual.ready RenameMemoClassEqual.work]. split;[exact I|]. now rewrite Nat.add_1_r.
Qed.
Theorem member native logical a b : NativeState.represents native logical -> ClassLookup.wellformed native -> set_domain logical a b ->
 Z.of_nat(S(length(Protocol.formulas logical)))<=RenameMemoResourceBounds.doubling_limit ->
 forall ca cb, Protocol.class_at logical a=Some ca -> Protocol.class_at logical b=Some cb ->
 RenameMemoClassMember.ready native (Protocol.formulas logical) a b ca cb /\
 Z.of_nat(length(Protocol.formulas logical)+RenameMemoClassMember.work native a b ca cb)<=RenameMemoResourceBounds.doubling_limit.
Proof.
 intros Hstate Hgood Hsets Hbound ca cb Ha Hb. destruct(Hsets ca cb Ha Hb) as(x & y & -> & ->).
 destruct(set_lookup native logical b y Hstate Hgood Hb) as(Hword & Hraw).
 cbn [RenameMemoClassMember.ready RenameMemoClassMember.work]. unfold RenameMemoCallers.predicate_ready,RenameMemoCallers.predicate_growth. rewrite Hraw.
 rewrite Nat.add_0_r. rewrite Nat2Z.id. split;[split;[lia|exact Hword]|now rewrite Nat.add_1_r].
Qed.
End NativeSpacedSetBinaryResources.
