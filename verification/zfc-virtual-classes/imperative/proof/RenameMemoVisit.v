From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash RenameStack RenameFrames FormulaEncoding Representation HashTable.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoVisit.
Import IndexExecution SipHashExecution.
Record view s (fs : list SetTheory.formula) source depth (stack : list RenameStack.frame) root left_id : Prop := {
  count : meta_value s 10=Z.of_nat (S (length stack));
  count_word : Z.of_nat (S (length stack))<=maximum;
  root_word : word root;
  depth_word : word (Z.of_nat depth);
  frame_capacity : (length stack<length (memory s arraydef_0__frames))%nat;
  frame_entry : List.nth (length stack) (memory s arraydef_0__frames) (0,0,0,0)=(root,Z.of_nat depth,0,left_id);
  source_entry : nth_error fs (Z.to_nat root)=Some source;
  source_capacity : (Z.to_nat root<length (memory s arraydef_0__formulas))%nat
}.
Theorem top_visit s fs source depth stack : NativeRepresentation.canonical_arena s fs ->
  RenameFrames.represents s fs (RenameStack.visit source depth::stack) -> exists root left_id, view s fs source depth stack root left_id.
Proof.
  intros Harena Hstack.
  destruct (RenameFrames.top_entry s fs _ stack Hstack) as [raw [Hraw [Hentry Hcapacity]]].
  destruct raw as [[[root raw_depth] phase] left_id]. cbn [RenameFrames.entry] in Hentry.
  destruct Hentry as [Hroot [Hdepth [Hdepth_eq [Hphase Hlookup]]]]. subst raw_depth phase.
  pose proof Hstack as [Hcount [Hword Hentries]]. cbn [length] in Hcount,Hword.
  exists root,left_id. constructor; try assumption.
  - exact (List.nth_error_nth _ _ (0,0,0,0) Hraw).
  - assert (Hbound : (Z.to_nat root<length fs)%nat) by (apply nth_error_Some; congruence).
    pose proof (proj1 (proj1 Harena)) as [_ [_ [_ [_ [Hformulas _]]]]]. lia.
Qed.
Theorem falsity_record s fs root : NativeRepresentation.canonical_arena s fs ->
  nth_error fs (Z.to_nat root)=Some SetTheory.falsity ->
  List.nth (Z.to_nat root) (memory s arraydef_0__formulas) (0,0,0)=(0,0,0).
Proof.
  intros [Htable [Hrep [Hunique Hnormal]]] Hlookup.
  assert (Hbound : (Z.to_nat root<length fs)%nat) by (apply nth_error_Some; congruence).
  pose proof (NativeRepresentation.represented_lookup s fs (Z.to_nat root) SetTheory.falsity Hrep Hlookup) as Hdecode.
  exact (FormulaEncoding.decode_injective fs (HashTableInvariant.tuple_at s (Z.to_nat root)) (0,0,0) SetTheory.falsity
    Hunique (Hnormal (Z.to_nat root) Hbound) ltac:(left; auto) Hdecode eq_refl).
Qed.
End RenameMemoVisit.
