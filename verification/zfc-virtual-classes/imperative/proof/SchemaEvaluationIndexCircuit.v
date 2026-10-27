From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Intern InternGrowth InternLengths InternReserve FormulaEncoding
  FormulaTopology Representation FormulaCircuit RenameMemoTopology SchemaEvaluationIndexBounds RenameMemoInput RenameMemoControl.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaEvaluationIndexCircuit.
Import IndexExecution SipHashExecution.
Definition operation_bound bound op := match op with
| FormulaCircuit.equal i j | FormulaCircuit.member i j => (i<=bound /\ j<=bound)%nat
| _ => True end.
Lemma parameters_bound ids op bound : operation_bound bound op ->
 RenameMemoInput.raw_bound bound (FormulaCircuit.parameters ids op vardef_0__intern_tag,
 FormulaCircuit.parameters ids op vardef_0__intern_a,FormulaCircuit.parameters ids op vardef_0__intern_b).
Proof.
 destruct op as [i j|i j|i j|i].
 - change ((i<=bound /\ j<=bound)%nat -> RenameMemoInput.raw_bound bound (1,Z.of_nat i,Z.of_nat j)).
   unfold RenameMemoInput.raw_bound. rewrite !Nat2Z.id. tauto.
 - change ((i<=bound /\ j<=bound)%nat -> RenameMemoInput.raw_bound bound (2,Z.of_nat i,Z.of_nat j)).
   unfold RenameMemoInput.raw_bound. rewrite !Nat2Z.id. tauto.
 - change (True -> RenameMemoInput.raw_bound bound (3,List.nth i ids 0,List.nth j ids 0)).
   unfold RenameMemoInput.raw_bound. intros _ [H|H];discriminate.
 - change (True -> RenameMemoInput.raw_bound bound (4,List.nth i ids 0,0)).
   unfold RenameMemoInput.raw_bound. intros _ [H|H];discriminate.
Qed.
Theorem complete plan s fs ids values result reserve bound observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  FormulaCircuit.represents fs ids values -> Forall FormulaCircuit.fits plan -> FormulaCircuit.infer plan values=Some result ->
  Z.of_nat (length fs+length plan+reserve)<=9223372036854775807 ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound -> Forall (operation_bound bound) plan ->
  exists final next result_ids, SchemaEvaluationIndexBounds.raw_arena final (length next) bound /\
    FormulaCircuit.executes observations plan s ids final result_ids /\
    InternExecution.logical_frame s final /\ NativeRepresentation.canonical_arena final next /\ meta_value final 8=0 /\
    FormulaCircuit.represents next result_ids result /\ (exists extra,next=fs++extra) /\
    Z.of_nat (length next+reserve)<=9223372036854775807 /\ FormulaTopology.ordered final (length next) /\
    (length next<=length fs+length plan)%nat.
Proof.
  induction plan as [|op tail IH] in s,fs,ids,values |- *.
  - intros Harena Hordered Herror Hrep Hfits Hinfer Hbudget Hraw Hops. injection Hinfer as <-.
    exists s,fs,ids. split;[exact Hraw|]. split; [constructor|]. split; [apply InternExecution.logical_refl|]. split; [exact Harena|].
    split; [exact Herror|]. split; [exact Hrep|]. split; [exists []; now rewrite app_nil_r|].
    split; [cbn [length] in Hbudget; lia|]. split; [exact Hordered|cbn [length]; lia].
  - intros Harena Hordered Herror Hrep Hfits Hinfer Hbudget Hraw Hops.
    inversion Hops as [|head rest HopBound HtailBound];subst head rest.
    inversion Hfits as [|head rest Hop Htail]; subst head rest. cbn [FormulaCircuit.infer] in Hinfer.
    destruct (FormulaCircuit.meaning values op) as [p|] eqn:Hp; [|discriminate].
    assert (Hstepbudget : Z.of_nat (length fs+S (length tail+reserve))<=9223372036854775807)
      by (replace (length fs+S (length tail+reserve))%nat with (length fs+length (op::tail)+reserve)%nat by (cbn; lia); exact Hbudget).
    destruct (FormulaCircuit.step s fs ids values op p (length tail+reserve) observations Harena Herror Hrep Hop Hp Hstepbudget)
      as (middle & middle_fs & index & Hrun & Hframe & Hmiddle & Hflag & Hindex & Hmiddle_rep & Hprefix & Hremaining).
    assert (Hplain : exec (funcdef_0__intern (fun _=>false) (FormulaCircuit.parameters ids op)) s=Some (tt,middle)).
    { pose proof (execObserved_erases (funcdef_0__intern (fun _=>false) (FormulaCircuit.parameters ids op)) (s,observations)) as Herased.
      rewrite Hrun in Herased. exact (eq_sym Herased). }
    assert (Hcapacity : Z.of_nat (length fs)<=9223372036854775807).
    { rewrite Nat2Z.inj_add in Hbudget. lia. }
    pose proof (InternGrowth.at_most_one s middle _ _ fs middle_fs Harena Herror Hcapacity Hplain Hmiddle) as Hgrowth.
    assert (HmiddleRaw:SchemaEvaluationIndexBounds.raw_arena middle (length middle_fs) bound).
    { exact (SchemaEvaluationIndexBounds.observed_intern s middle (fun _=>false) (FormulaCircuit.parameters ids op)
      fs middle_fs bound observations observations Harena Herror Hcapacity Hraw
      (parameters_bound ids op bound HopBound) Hrun Hmiddle). }
    pose proof (RenameMemoTopology.preserves s middle fs middle_fs Harena Hmiddle Hprefix Hgrowth Hordered) as Hordered_middle.
    replace (length middle_fs+(length tail+reserve))%nat with (length middle_fs+length tail+reserve)%nat in Hremaining by lia.
    destruct (IH middle middle_fs (ids++[Z.of_nat index]) (values++[p]) Hmiddle Hordered_middle Hflag Hmiddle_rep Htail Hinfer Hremaining HmiddleRaw HtailBound)
      as (final & next & result_ids & HfinalRaw & Htrace & Hlast_frame & Hlast & Hlast_flag & Hlast_rep & Hlast_prefix & Hlast_reserve & Hlast_order & Hlast_growth).
    exists final,next,result_ids. split;[exact HfinalRaw|]. split.
    + econstructor; [exact Hrun|exact Hindex| |exact Htrace]. pose proof (proj1 (proj1 Hmiddle)) as [Hmeta Hrest]. lia.
    + split; [exact (InternExecution.logical_trans s middle final Hframe Hlast_frame)|]. split; [exact Hlast|].
      split; [exact Hlast_flag|]. split; [exact Hlast_rep|]. split; [eapply InternReserve.extends_trans; eassumption|].
      split; [exact Hlast_reserve|]. split; [exact Hlast_order|cbn [length]; lia].
Qed.
End SchemaEvaluationIndexCircuit.
