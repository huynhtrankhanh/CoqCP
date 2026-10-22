From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift RenameStack RenameMemoState RenameMemoStep
  RenameMemoIndexBounds RenameMemoTransition RenameMemoBounds RenameMemoResourceBounds RenameMemoInit RenameMemoControl ObservedLocal.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameMemoDomain.
Import IndexExecution SipHashExecution IndexSemantics RenameMemoInit ObservedLocal.
Definition source_domain bound ceiling stack :=
  RenameMemoIndexBounds.stack_bound bound stack /\ RenameMemoTransition.depth_bounds ceiling stack.
Theorem preserved rho stack value next result bound ceiling :
  RenameMemoTransition.step rho stack value next result -> source_domain bound ceiling stack ->
  source_domain bound ceiling next.
Proof.
  intros Hstep [Hindices Hdepth]. split.
  - now apply RenameMemoTransition.source_bounds with (rho:=rho) (stack:=stack) (value:=value) (result:=result).
  - now apply RenameMemoTransition.binder_depths with (rho:=rho) (stack:=stack) (value:=value) (result:=result).
Qed.
Theorem initial source depth bound : RenameMemoIndexBounds.formula_bound bound source ->
  source_domain bound (depth+RenameMemoTransition.height source) [RenameStack.visit source depth].
Proof. intro Hbound. split; constructor; [exact Hbound|constructor|cbn [RenameMemoTransition.depth RenameMemoIndexBounds.source]; lia|constructor]. Qed.
Theorem front_indices stack m shift arg bound ceiling : source_domain bound ceiling stack ->
  Z.of_nat bound+Z.of_nat (RenameMemoIndexBounds.increment m shift arg)<=maximum ->
  Z.of_nat ceiling<=maximum ->
  match stack with RenameStack.visit source depth::_=>RenameMemoState.atomic_bounds m shift arg source depth | _=>True end.
Proof.
  intros [Hindices Hdepth] Hroom Hceiling. destruct stack as [|task tail]; [exact I|].
  destruct task as [source depth|p q depth|p q depth left_value|p depth]; try exact I.
  inversion Hindices as [|task rest Hsource Htail]; subst.
  inversion Hdepth as [|task rest Hsource_depth Htail_depth]; subst.
  cbn [RenameMemoIndexBounds.source] in Hsource.
  cbn [RenameMemoIndexBounds.source RenameMemoTransition.depth] in Hsource_depth.
  destruct source as [|i j|i j|p q|p]; try (eapply RenameMemoIndexBounds.atom_words; eauto; exact I).
  cbn [RenameMemoTransition.height] in Hsource_depth. cbn [RenameMemoState.atomic_bounds]. lia.
Qed.
(* The arithmetic hypotheses are explicit bounds, not an assumption that the
   traversal executes. Cache occupancy and stack/arena accounting discharge
   them when the native scheduler is connected to its cost model. *)
Theorem resources s fs m shift arg count stack root bound ceiling :
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  Z.of_nat (length fs)<=9223372036854775807 -> (length stack<=S root)%nat ->
  meta_value s 30<=Z.of_nat (S root*S root) ->
  word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  source_domain bound ceiling stack ->
  Z.of_nat bound+Z.of_nat (RenameMemoIndexBounds.increment m shift arg)<=maximum ->
  Z.of_nat ceiling<=maximum -> RenameMemoState.resources s fs m shift arg count stack.
Proof.
  intros Hfuel Harena Hstack Hlive Hshift Harg Hsource Hindices Hdepth. constructor; try assumption.
  - now apply RenameMemoResourceBounds.stack_room with (root:=root).
  - intro Hgrow. eapply RenameMemoResourceBounds.growth_safe; [exact Hfuel|lia|exact Hlive|exact Hgrow].
  - now apply front_indices with (bound:=bound) (ceiling:=ceiling).
Qed.
Theorem generated (f : Frame) fs m shift arg count task stack value target root bound ceiling :
  nums f vardef_0__rename_mode=mode_number m -> nums f vardef_0__rename_shift=Z.of_nat shift ->
  nums f vardef_0__rename_arg=Z.of_nat arg ->
  RenameMemoState.represents (machine f) fs (renaming m shift arg) count (task::stack) value target ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> Z.of_nat (length fs)<=9223372036854775807 ->
  (length (task::stack)<=S root)%nat -> meta_value (machine f) 30<=Z.of_nat (S root*S root) ->
  word (Z.of_nat shift) -> word (Z.of_nat arg) -> source_domain bound ceiling (task::stack) ->
  Z.of_nat bound+Z.of_nat (RenameMemoIndexBounds.increment m shift arg)<=maximum -> Z.of_nat ceiling<=maximum ->
  forall observations, exists final next next_stack next_value size,
    execLocalObserved RenameMemoControl.iteration (f,observations)=Some (KeepGoing,(final,observations)) /\
    RenameMemoStep.post f fs count (renaming m shift arg) (task::stack) value target final next next_stack next_value size /\
    source_domain bound ceiling next_stack.
Proof.
  intros Hmode Hshift Harg Hstate Hfuel Harena Hstack Hlive Hshiftword Hargword Hsource Hindices Hdepth observations.
  pose proof (resources (machine f) fs m shift arg count (task::stack) root bound ceiling
    Hfuel Harena Hstack Hlive Hshiftword Hargword Hsource Hindices Hdepth) as Hresources.
  destruct (RenameMemoStep.generated f fs m shift arg count task stack value target Hmode Hshift Harg Hstate Hresources observations)
    as (final & next & next_stack & next_value & size & Hrun & Hpost).
  exists final,next,next_stack,next_value,size. split; [exact Hrun|]. split; [exact Hpost|].
  destruct Hpost as (_ & _ & _ & _ & _ & Hstep & _). now apply preserved with (rho:=renaming m shift arg) (stack:=task::stack) (value:=value) (result:=next_value).
Qed.
End RenameMemoDomain.
