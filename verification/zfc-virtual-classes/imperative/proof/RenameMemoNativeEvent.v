From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash FormulaEncoding RenameStack RenameMemoLookup RenameMemoAccounting.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoNativeEvent.
Import IndexExecution SipHashExecution.
Definition misses s (fs : list SetTheory.formula) count source depth := forall root, word root ->
  nth_error fs (Z.to_nat root)=Some source -> RenameMemoLookup.lookup s (root,Z.of_nat depth) count=None.
Definition completes s (fs : list SetTheory.formula) count t size source depth := forall root, word root ->
  nth_error fs (Z.to_nat root)=Some source -> RenameMemoAccounting.completed s count t size (root,Z.of_nat depth).
Definition atomic source := match source with
  | SetTheory.falsity | SetTheory.equal _ _ | SetTheory.member _ _=>True | _=>False end.
(* Every constructor records a native branch's concrete cache effects. The
   schedule may overapproximate cache hits, but a miss must be a real miss. *)
Inductive event (s : Machine) fs count (t : Machine) (next_fs : list SetTheory.formula) size : list RenameStack.frame->list RenameStack.frame->Prop :=
| cached source depth tail : RenameMemoAccounting.passive s t -> size=count ->
    (length next_fs<=length fs)%nat -> event s fs count t next_fs size (RenameStack.visit source depth::tail) tail
| leaf source depth tail : atomic source -> misses s fs count source depth ->
    completes s fs count t size source depth ->
    (length next_fs<=S (length fs))%nat -> event s fs count t next_fs size (RenameStack.visit source depth::tail) tail
| binary p q depth tail : misses s fs count (SetTheory.implies p q) depth ->
    RenameMemoAccounting.passive s t -> size=count ->
    (length next_fs<=length fs)%nat -> event s fs count t next_fs size (RenameStack.visit (SetTheory.implies p q) depth::tail)
      (RenameStack.visit p depth::RenameStack.left_done p q depth::tail)
| binder p depth tail : misses s fs count (SetTheory.all p) depth ->
    RenameMemoAccounting.passive s t -> size=count ->
    (length next_fs<=length fs)%nat -> event s fs count t next_fs size (RenameStack.visit (SetTheory.all p) depth::tail)
      (RenameStack.visit p (S depth)::RenameStack.body_done p depth::tail)
| next p q depth tail left_value : RenameMemoAccounting.passive s t -> size=count ->
    (length next_fs<=length fs)%nat -> event s fs count t next_fs size (RenameStack.left_done p q depth::tail)
      (RenameStack.visit q depth::RenameStack.right_done p q depth left_value::tail)
| joined p q depth tail left_value : completes s fs count t size (SetTheory.implies p q) depth ->
    (length next_fs<=S (length fs))%nat -> event s fs count t next_fs size (RenameStack.right_done p q depth left_value::tail) tail
| closed p depth tail : completes s fs count t size (SetTheory.all p) depth ->
    (length next_fs<=S (length fs))%nat -> event s fs count t next_fs size (RenameStack.body_done p depth::tail) tail.
Theorem misses_source s fs count source depth root : FormulaEncoding.unique fs ->
  word root -> nth_error fs (Z.to_nat root)=Some source -> RenameMemoLookup.lookup s (root,Z.of_nat depth) count=None ->
  misses s fs count source depth.
Proof.
  intros Hunique Hroot Hsource Hmiss other Hother Hsame.
  assert (Hid : root=other).
  { apply FormulaEncoding.natural_index_injective; try assumption. eapply Hunique; eassumption. }
  now rewrite <-Hid.
Qed.
End RenameMemoNativeEvent.
