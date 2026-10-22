From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift FormulaEncoding Representation RenameStack RenameFrames
  RenameMemoInvariant RenameMemoMeaning RenameMemoContinuation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoState.
Import IndexExecution SipHashExecution IndexSemantics.
Definition result_ready s (fs : list SetTheory.formula) stack value :=
  match stack with RenameStack.visit _ _::_=>True
  | _=>word (meta_value s 0) /\ nth_error fs (Z.to_nat (meta_value s 0))=Some value end.
Record represents s fs rho count stack value target : Prop := {
  cache : RenameMemoInvariant.valid s count (RenameMemoMeaning.entry_meaning fs rho);
  arena : NativeRepresentation.canonical_arena s fs;
  frames : RenameFrames.represents s fs stack;
  current : result_ready s fs stack value;
  continuation : RenameMemoContinuation.correct rho stack value target;
  falsity_zero : nth_error fs 0=Some SetTheory.falsity
}.
Definition atomic_bounds m shift arg source depth :=
  match source with
  | SetTheory.equal i j | SetTheory.member i j =>
    word (Z.of_nat i) /\ word (Z.of_nat j) /\
    word (Z.of_nat (under_binders depth (renaming m shift arg) i)) /\
    word (Z.of_nat (under_binders depth (renaming m shift arg) j))
  | SetTheory.all _=>Z.of_nat depth<maximum
  | _=>True
  end.
Record resources s (fs : list SetTheory.formula) m shift arg count stack : Prop := {
  interner_room : Z.of_nat (length fs)<=9223372036854775807;
  stack_room : Z.of_nat (length stack)<maximum;
  shift_word : word (Z.of_nat shift);
  argument_word : word (Z.of_nat arg);
  cache_room : Z.of_nat count/2<=meta_value s 30 -> Z.of_nat count<=9223372036854775807;
  indices : match stack with RenameStack.visit source depth::_=>atomic_bounds m shift arg source depth | _=>True end
}.
Lemma ready_from_value s fs stack value : word (meta_value s 0) ->
  nth_error fs (Z.to_nat (meta_value s 0))=Some value -> result_ready s fs stack value.
Proof. intros Hword Hvalue. destruct stack as [|task stack]; [now split|]. destruct task; cbn [result_ready]; auto. Qed.
Theorem completed s fs next rho count stack value target :
  RenameMemoInvariant.valid s count (RenameMemoMeaning.entry_meaning next rho) ->
  NativeRepresentation.canonical_arena s next -> RenameFrames.represents s next stack ->
  word (meta_value s 0) -> nth_error next (Z.to_nat (meta_value s 0))=Some value ->
  RenameMemoContinuation.correct rho stack value target ->
  nth_error fs 0=Some SetTheory.falsity -> (exists extra, next=fs++extra) ->
  represents s next rho count stack value target.
Proof.
  intros Hcache Harena Hframes Hword Hvalue Hcontinuation Hzero [extra ->]. constructor; try assumption.
  - now apply ready_from_value.
  - now apply FormulaEncoding.nth_error_extend.
Qed.
Theorem scheduled s fs rho count source depth stack value target :
  RenameMemoInvariant.valid s count (RenameMemoMeaning.entry_meaning fs rho) ->
  NativeRepresentation.canonical_arena s fs -> RenameFrames.represents s fs (RenameStack.visit source depth::stack) ->
  RenameMemoContinuation.correct rho (RenameStack.visit source depth::stack) value target ->
  nth_error fs 0=Some SetTheory.falsity -> represents s fs rho count (RenameStack.visit source depth::stack) value target.
Proof. intros. constructor; try assumption. exact I. Qed.
Theorem finished s fs rho count value target : represents s fs rho count [] value target ->
  word (meta_value s 0) /\ nth_error fs (Z.to_nat (meta_value s 0))=Some target.
Proof. intros [_ _ _ [Hword Hvalue] Hcorrect _]. cbn [RenameMemoContinuation.correct] in Hcorrect. now subst value. Qed.
End RenameMemoState.
