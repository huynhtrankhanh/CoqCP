From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift RenameStack RenameFrames RenameStructure RenameConfiguration FormulaEncoding Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameInvariant.
Import IndexExecution SipHashExecution IndexSemantics RenameStructure.
Record ghost := Snapshot { formulas : list SetTheory.formula; tasks : list RenameStack.frame; answer : SetTheory.formula }.
Fixpoint fits rho depth p : Prop := word (Z.of_nat depth) /\ match p with
| SetTheory.falsity => True
| SetTheory.equal i j | SetTheory.member i j => word (Z.of_nat i) /\ word (Z.of_nat j) /\
    word (Z.of_nat (under_binders depth rho i)) /\ word (Z.of_nat (under_binders depth rho j))
| SetTheory.implies p q => fits rho depth p /\ fits rho depth q
| SetTheory.all p => Z.of_nat depth < maximum /\ fits rho (S depth) p end.
Definition task_fits rho task := match task with
| RenameStack.visit p depth => fits rho depth p
| RenameStack.left_done p q depth | RenameStack.right_done p q depth _ => fits rho depth (SetTheory.implies p q)
| RenameStack.body_done p depth => fits rho depth (SetTheory.all p) end.
Definition current (fs : list SetTheory.formula) stack value (f : Frame) := match stack with
| RenameStack.visit _ _ :: _ => True
| _ => word (meta_value (machine f) 0) /\ nth_error fs (Z.to_nat (meta_value (machine f) 0)) = Some value end.
Definition parameters m shift arg (f : Frame) := nums f vardef_0__rename_mode = mode_number m /\
  nums f vardef_0__rename_shift = Z.of_nat shift /\ nums f vardef_0__rename_arg = Z.of_nat arg.
Definition resource_limit : Z := 9223372036854775807.
Lemma parameters_preserved m shift arg f final : parameters m shift arg f -> RenameConfiguration.preserved f final -> parameters m shift arg final.
Proof. intros [Hm [Hs Ha]] [Hmode [Hshift Harg]]. unfold parameters. now rewrite Hmode,Hshift,Harg. Qed.
Lemma pending_length stack : (length stack <= RenameStack.pending stack)%nat.
Proof.
  induction stack as [|task stack IH]; [reflexivity|].
  pose proof (RenameStack.pending_positive task []) as Hpositive.
  cbn [RenameStack.pending length] in *. lia.
Qed.
Lemma pending_zero stack : RenameStack.pending stack = 0%nat <-> stack = [].
Proof. destruct stack as [|task stack]; [tauto|]. pose proof (RenameStack.pending_positive task stack). split; intros; [lia|discriminate]. Qed.
Lemma tick_fits rho stack value : Forall (task_fits rho) stack ->
  Forall (task_fits rho) (fst (RenameStack.tick rho (stack,value))).
Proof.
  intros Hfits. destruct stack as [|task stack]; [exact Hfits|]. inversion Hfits as [|head tail Hhead Htail]; subst head tail.
  destruct task as [p depth|p q depth|p q depth left_value|p depth].
  - destruct p; cbn [RenameStack.tick fst]; try exact Htail.
    + constructor; [exact (proj1 (proj2 Hhead))|]. constructor; assumption.
    + constructor; [exact (proj2 (proj2 Hhead))|]. constructor; assumption.
  - cbn [RenameStack.tick fst]. constructor; [exact (proj2 (proj2 Hhead))|]. constructor; assumption.
  - exact Htail.
  - exact Htail.
Qed.
Lemma word_id native fs index p : NativeRepresentation.canonical_arena native fs -> nth_error fs index = Some p -> word (Z.of_nat index).
Proof.
  intros [Htable Hrest] Hlookup. pose proof (proj1 Htable) as [_ [_ [_ [_ [_ [_ Hlimit]]]]]].
  assert (Hbound : (index < length fs)%nat) by (apply nth_error_Some; congruence). unfold word. lia.
Qed.
Lemma current_with_id native fs stack value index : NativeRepresentation.canonical_arena (machine native) fs ->
  meta_value (machine native) 0 = Z.of_nat index -> nth_error fs index = Some value -> current fs stack value native.
Proof.
  intros Harena Hindex Hvalue. unfold current. destruct stack as [|task stack]; [|destruct task; [exact I| | | ]].
  all: rewrite Hindex; split; [eapply word_id; eassumption|now rewrite Nat2Z.id].
Qed.
Section FixedInput.
Context (base : list SetTheory.formula) (target : SetTheory.formula) (m : mode) (shift arg : nat).
Definition rho := renaming m shift arg.
Record holds (f : Frame) (g : ghost) : Prop := {
  arena_valid : NativeRepresentation.canonical_arena (machine f) (formulas g);
  falsity_valid : nth_error (formulas g) 0 = Some SetTheory.falsity;
  frames_valid : RenameFrames.represents (machine f) (formulas g) (tasks g);
  current_valid : current (formulas g) (tasks g) (answer g) f;
  fits_valid : Forall (task_fits rho) (tasks g);
  meaning_valid : RenameStack.meaning rho (tasks g) (answer g) = target;
  prefix_valid : exists extra, formulas g = base ++ extra;
  budget_valid : Z.of_nat (length (formulas g) + RenameStack.pending (tasks g)) <= resource_limit;
  allocation_mass : (length (formulas g) + RenameStack.pending (tasks g) <= length base + RenameStack.work target)%nat;
  parameters_valid : parameters m shift arg f;
  error_clear : meta_value (machine f) 8 = 0
}.
Lemma ready f g : holds f g ->
  (10 < length (memory (machine f) arraydef_0__meta))%nat /\
  (meta_value (machine f) 10 = 0 <-> RenameStack.pending (tasks g) = 0%nat) /\ meta_value (machine f) 8 = 0.
Proof.
  intros Hgood. pose proof (proj1 (proj1 (arena_valid f g Hgood))) as [Hmeta Hrest].
  split; [eapply Nat.le_lt_trans; [|exact Hmeta]; cbn; lia|]. split; [|exact (error_clear f g Hgood)].
  pose proof (proj1 (frames_valid f g Hgood)) as Hcount.
  destruct (tasks g) as [|task stack] eqn:Htasks.
  - cbn [length RenameStack.pending] in Hcount |- *. rewrite Hcount. tauto.
  - cbn [length] in Hcount. pose proof (RenameStack.pending_positive task stack). split; intro; lia.
Qed.
Lemma capacity f g : holds f g -> Z.of_nat (length (formulas g)) <= resource_limit.
Proof. intros Hgood. pose proof (budget_valid f g Hgood) as Hbudget. rewrite Nat2Z.inj_add in Hbudget. lia. Qed.
Lemma stack_room f g : holds f g -> Z.of_nat (length (tasks g)) < maximum.
Proof.
  intros Hgood. pose proof (budget_valid f g Hgood) as Hbudget. pose proof (pending_length (tasks g)) as Hlength.
  unfold resource_limit,maximum in *. rewrite Nat2Z.inj_add in Hbudget. lia.
Qed.
Theorem adopt f g final next stack value : holds f g -> tasks g <> [] ->
  RenameStack.tick rho (tasks g,answer g) = (stack,value) ->
  NativeRepresentation.canonical_arena (machine final) next -> RenameFrames.represents (machine final) next stack ->
  current next stack value final -> (exists extra, next = formulas g ++ extra) ->
  (length next <= S (length (formulas g)))%nat -> meta_value (machine final) 8 = 0 -> RenameConfiguration.preserved f final ->
  holds final (Snapshot next stack value).
Proof.
  intros Hgood Hnonempty Htick Harena Hframes Hcurrent [extra Hextends] Hgrowth Herror Hconfiguration.
  assert (Hpending : RenameStack.pending (tasks g) = S (RenameStack.pending stack)).
  { destruct (tasks g) as [|head tail] eqn:Htasks; [contradiction|].
    pose proof (RenameStack.tick_decreases rho head tail (answer g)) as Hdecrease. rewrite Htick in Hdecrease. exact Hdecrease. }
  constructor; cbn [formulas tasks answer].
  - exact Harena.
  - rewrite Hextends. apply FormulaEncoding.nth_error_extend. exact (falsity_valid f g Hgood).
  - exact Hframes.
  - exact Hcurrent.
  - pose proof (tick_fits rho (tasks g) (answer g) (fits_valid f g Hgood)) as Hfits. now rewrite Htick in Hfits.
  - pose proof (RenameStack.tick_preserves rho (tasks g) (answer g)) as Hmeaning. rewrite Htick in Hmeaning.
    cbn [fst snd] in Hmeaning. rewrite Hmeaning. exact (meaning_valid f g Hgood).
  - destruct (prefix_valid f g Hgood) as [old Hold]. exists (old ++ extra). rewrite Hextends,Hold,app_assoc. reflexivity.
  - assert (Hsize : (length next + RenameStack.pending stack <= length (formulas g) + RenameStack.pending (tasks g))%nat) by lia.
    apply Nat2Z.inj_le in Hsize. pose proof (budget_valid f g Hgood). lia.
  - pose proof (allocation_mass f g Hgood) as Hmass. lia.
  - exact (parameters_preserved m shift arg f final (parameters_valid f g Hgood) Hconfiguration).
  - exact Herror.
Qed.
End FixedInput.
End RenameInvariant.
