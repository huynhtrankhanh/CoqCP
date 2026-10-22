From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Intern InternGrowth InternLengths InternReserve FormulaEncoding
  FormulaTopology Representation FormulaCircuit RenameMemoTopology.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module FormulaCircuitProperties.
Import IndexExecution SipHashExecution.
Theorem lengths observations plan s ids final result : FormulaCircuit.executes observations plan s ids final result ->
  length (memory final arraydef_0__meta)=length (memory s arraydef_0__meta) /\
  length (memory final arraydef_0__sipState)=length (memory s arraydef_0__sipState).
Proof.
  intro Htrace. induction Htrace as [s ids|op tail s ids middle id final result Hrun Hvalue Hmeta Htail IH]; [now split|].
  destruct (InternLengths.observed_lengths _ _ _ _ _ _ Hrun) as [Hm Hs]. destruct IH as [Hm' Hs']. split; congruence.
Qed.
Theorem deterministic observations plan s ids first first_ids second second_ids :
  FormulaCircuit.executes observations plan s ids first first_ids ->
  FormulaCircuit.executes observations plan s ids second second_ids -> first=second /\ first_ids=second_ids.
Proof.
  intro Htrace. induction Htrace as [s ids|op tail s ids middle id final result Hrun Hvalue Hmeta Htail IH] in second,second_ids |- *.
  - intro Hother. inversion Hother; subst. now split.
  - intro Hother. inversion Hother as [|other_op other_tail before before_ids other_middle other_id after after_ids Hrun' Hvalue' Hmeta' Htail']; subst.
    rewrite Hrun in Hrun'. injection Hrun' as <-. now apply IH.
Qed.
(* Strengthen the circuit evaluator with topology and a node-count bound. Each
   emitted operation executes the existing proved native interner. *)
Theorem complete plan s fs ids values result reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  FormulaCircuit.represents fs ids values -> Forall FormulaCircuit.fits plan -> FormulaCircuit.infer plan values=Some result ->
  Z.of_nat (length fs+length plan+reserve)<=9223372036854775807 ->
  exists final next result_ids, FormulaCircuit.executes observations plan s ids final result_ids /\
    InternExecution.logical_frame s final /\ NativeRepresentation.canonical_arena final next /\ meta_value final 8=0 /\
    FormulaCircuit.represents next result_ids result /\ (exists extra,next=fs++extra) /\
    Z.of_nat (length next+reserve)<=9223372036854775807 /\ FormulaTopology.ordered final (length next) /\
    (length next<=length fs+length plan)%nat.
Proof.
  induction plan as [|op tail IH] in s,fs,ids,values |- *.
  - intros Harena Hordered Herror Hrep Hfits Hinfer Hbudget. injection Hinfer as <-.
    exists s,fs,ids. split; [constructor|]. split; [apply InternExecution.logical_refl|]. split; [exact Harena|].
    split; [exact Herror|]. split; [exact Hrep|]. split; [exists []; now rewrite app_nil_r|].
    split; [cbn [length] in Hbudget; lia|]. split; [exact Hordered|cbn [length]; lia].
  - intros Harena Hordered Herror Hrep Hfits Hinfer Hbudget.
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
    pose proof (RenameMemoTopology.preserves s middle fs middle_fs Harena Hmiddle Hprefix Hgrowth Hordered) as Hordered_middle.
    replace (length middle_fs+(length tail+reserve))%nat with (length middle_fs+length tail+reserve)%nat in Hremaining by lia.
    destruct (IH middle middle_fs (ids++[Z.of_nat index]) (values++[p]) Hmiddle Hordered_middle Hflag Hmiddle_rep Htail Hinfer Hremaining)
      as (final & next & result_ids & Htrace & Hlast_frame & Hlast & Hlast_flag & Hlast_rep & Hlast_prefix & Hlast_reserve & Hlast_order & Hlast_growth).
    exists final,next,result_ids. split.
    + econstructor; [exact Hrun|exact Hindex| |exact Htrace]. pose proof (proj1 (proj1 Hmiddle)) as [Hmeta Hrest]. lia.
    + split; [exact (InternExecution.logical_trans s middle final Hframe Hlast_frame)|]. split; [exact Hlast|].
      split; [exact Hlast_flag|]. split; [exact Hlast_rep|]. split; [eapply InternReserve.extends_trans; eassumption|].
      split; [exact Hlast_reserve|]. split; [exact Hlast_order|cbn [length]; lia].
Qed.
End FormulaCircuitProperties.
