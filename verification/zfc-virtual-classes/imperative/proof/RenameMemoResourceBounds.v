From CoqCP Require Import Options.
From NativeProof Require Import RenameMemoBounds.
From Stdlib Require Import ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoResourceBounds.
Definition maximum : Z := 18446744073709551615.
Definition doubling_limit : Z := 9223372036854775807.
Theorem grid_word root : Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  0<Z.of_nat (S root) /\ Z.of_nat (S root)<maximum /\
  0<=Z.of_nat (S root*S root) /\ 5*Z.of_nat (S root*S root)+1<=maximum.
Proof.
  intros Hfuel. unfold RenameMemoBounds.fuel in Hfuel. rewrite Nat2Z.inj_add,!Nat2Z.inj_mul in Hfuel.
  rewrite Nat2Z.inj_mul. cbn in Hfuel. unfold maximum in *. repeat split; nia.
Qed.
Theorem growth_safe root capacity live : Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  0<=capacity -> live<=Z.of_nat (S root*S root) -> capacity/2<=live -> capacity<=doubling_limit.
Proof.
  intros Hfuel Hcapacity Hlive Hgrow. destruct (grid_word root Hfuel) as [_ [_ [_ Hgrid]]].
  pose proof (Z.div_mod capacity 2 ltac:(lia)). pose proof (Z.mod_pos_bound capacity 2 ltac:(lia)).
  unfold maximum,doubling_limit in *. lia.
Qed.
Theorem arena_room initial_length visited waiting current root :
  (current+waiting<=initial_length+visited)%nat -> (visited<=S root*S root)%nat ->
  Z.of_nat initial_length+Z.of_nat (S root*S root)<=doubling_limit -> Z.of_nat current<=doubling_limit.
Proof. intros Hcurrent Hvisited Hroom. lia. Qed.
Theorem stack_room root stack_length : Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  (stack_length<=S root)%nat -> Z.of_nat stack_length<maximum.
Proof. intros Hfuel Hlength. destruct (grid_word root Hfuel) as [_ [Hwidth _]]. lia. Qed.
Theorem binder_room root base depth : (depth<base+S root)%nat ->
  Z.of_nat base+Z.of_nat root<maximum -> Z.of_nat depth<maximum.
Proof. intros. lia. Qed.
End RenameMemoResourceBounds.
