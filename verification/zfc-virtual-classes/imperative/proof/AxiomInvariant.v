From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal ArenaFrame Intern FormulaTopology FormulaCircuit
  FormulaCircuitProperties FormulaCircuitResult Representation AxiomCommand AxiomRefl AxiomK AxiomSRefinement
  AxiomDNERefinement AxiomEqualityCircuits AxiomEqualityRefinement AxiomFixedCircuits AxiomFixedRefinement
  AxiomInstRefinement AxiomDistRefinement AxiomSeparationRefinement AxiomReplacementRefinement
  AxiomLogicalProtocol AxiomRenamingProtocol AxiomStorage AxiomLengths RenameMemoLengths
  RenameMemoBounds RenameMemoIndexBounds RenameMemoTransition.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomInvariant.
Import IndexExecution SipHashExecution ObservedLocal.
Local Opaque funcdef_0__axiom funcdef_0__intern funcdef_0__rename.

Definition constructed s bs ns observations fs wanted reserve allowance :=
  exists final next index,
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some wanted /\ SetTheory.derives wanted /\ (exists extra,next=fs++extra) /\
    meta_value final 8=0 /\ meta_value final 13=1 /\ FormulaTopology.ordered final (length next) /\
    Z.of_nat (length next+reserve)<=9223372036854775807 /\ (length next<=length fs+allowance)%nat /\
    AxiomStorage.logical_frame s final /\
    (forall watched,RenameMemoLengths.protected watched -> length (memory final watched)=length (memory s watched)).

Lemma normalize s bs ns observations fs wanted reserve allowance final next :
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) ->
  NativeRepresentation.canonical_arena final next -> meta_value final 13=1 -> meta_value final 8=0 ->
  word (meta_value final 0) -> nth_error next (Z.to_nat (meta_value final 0))=Some wanted -> SetTheory.derives wanted ->
  (exists extra,next=fs++extra) -> FormulaTopology.ordered final (length next) ->
  Z.of_nat (length next+reserve)<=9223372036854775807 -> (length next<=length fs+allowance)%nat ->
  constructed s bs ns observations fs wanted reserve allowance.
Proof.
  intros Hrun Hnext Hsuccess Herror Hword Hmeaning Hderives Hprefix Htopology Hreserve Hgrowth.
  exists final,next,(Z.to_nat (meta_value final 0)). rewrite Z2Nat.id by exact (proj1 Hword).
  split;[exact Hrun|]. split;[exact Hnext|]. split;[reflexivity|]. split;[exact Hword|].
  split;[exact Hmeaning|]. split;[exact Hderives|]. split;[exact Hprefix|]. split;[exact Herror|].
  split;[exact Hsuccess|]. split;[exact Htopology|]. split;[exact Hreserve|]. split;[exact Hgrowth|].
  split;[exact (AxiomStorage.generated_frame s bs ns final observations observations Hrun)|].
  intros watched Hprotected. exact (AxiomLengths.observed_length s bs ns observations final observations watched Hprotected Hrun).
Qed.

Lemma reflexivity s bs ns fs variable reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat -> word (Z.of_nat variable) ->
  Z.of_nat (length fs+1+reserve)<=9223372036854775807 ->
  ns vardef_0__axiom_tag=5 -> ns vardef_0__axiom_p=Z.of_nat variable ->
  constructed s bs ns observations fs (SetTheory.equal variable variable) reserve 1.
Proof.
  intros Harena Htopology Herror Hmeta Hvariable Hbudget Htag Hp.
  pose proof (AxiomK.clearing_storage s) as Hclear.
  pose proof (ArenaFrame.storage_arena s (AxiomRefl.cleared s) fs Hclear Harena) as Hclear_arena.
  pose proof (AxiomK.storage_topology s (AxiomRefl.cleared s) (length fs) Hclear Htopology) as Hclear_topology.
  assert (Hclear_error:meta_value (AxiomRefl.cleared s) 8=0)
    by (unfold AxiomRefl.cleared;rewrite meta_store_other by lia;exact Herror).
  assert (Hrep:FormulaCircuit.represents fs [] []) by constructor.
  assert (Hfits:Forall FormulaCircuit.fits [FormulaCircuit.equal variable variable]).
  { constructor;[split;exact Hvariable|constructor]. }
  destruct (FormulaCircuitProperties.complete [FormulaCircuit.equal variable variable] (AxiomRefl.cleared s) fs [] []
    [SetTheory.equal variable variable] reserve observations Hclear_arena Hclear_topology Hclear_error Hrep Hfits eq_refl Hbudget)
    as (built & next & ids & Htrace & Hframe & Hnext & Hflag & Hnextrep & Hprefix & Hreserve & Hordered & Hgrowth).
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hlength.
  assert (Hbuiltmeta:(13<length (memory built arraydef_0__meta))%nat)
    by (rewrite Hlength;unfold AxiomRefl.cleared;rewrite store_meta_length;exact Hmeta).
  assert (Hlookup:nth_error [SetTheory.equal variable variable]
    (length ([]:list Z)+length [FormulaCircuit.equal variable variable]-1)=Some (SetTheory.equal variable variable)) by reflexivity.
  destruct (FormulaCircuitResult.meaning observations _ _ _ _ _ next _ _ Htrace ltac:(discriminate) Hnextrep Hlookup)
    as [Hword Hmeaning].
  assert (Hintern:execObserved (funcdef_0__intern (fun _=>false) (AxiomRefl.arguments (Z.of_nat variable)))
    (AxiomRefl.cleared s,observations)=Some (tt,(built,observations))).
  { inversion Htrace;subst. match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H;subst end. assumption. }
  pose proof (AxiomRefl.generated_helper s bs ns built (Z.of_nat variable) observations
    Hmeta Hbuiltmeta Htag Hp Hintern) as Hrun.
  destruct (AxiomK.finishing_result built Hbuiltmeta) as [Hsuccess [Hfinalerror Hfinalid]].
  change (meta_value (AxiomRefl.finished built) 0=meta_value built 0) in Hfinalid.
  apply (normalize s bs ns observations fs _ reserve 1 (AxiomRefl.finished built) next Hrun).
  - eapply ArenaFrame.storage_arena;[apply AxiomRefl.finished_storage|exact Hnext].
  - exact Hsuccess.
  - unfold AxiomRefl.finished. rewrite !meta_store_other by lia. exact Hflag.
  - now rewrite Hfinalid.
  - now rewrite Hfinalid.
  - apply SetTheory.d_refl.
  - exact Hprefix.
  - eapply AxiomK.storage_topology;[apply AxiomRefl.finished_storage|exact Hordered].
  - exact Hreserve.
  - exact Hgrowth.
Qed.

Lemma logical which s fs a b c p q r reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat -> nth_error fs 0=Some SetTheory.falsity ->
  word (Z.of_nat a) -> word (Z.of_nat b) -> word (Z.of_nat c) ->
  AxiomLogicalProtocol.bindings which fs a b c p q r ->
  Z.of_nat (length fs+AxiomLogicalProtocol.cost which+reserve)<=9223372036854775807 ->
  constructed s (fun _=>false) (AxiomCommand.arguments (Z.of_nat (AxiomLogicalProtocol.tag which)) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
    observations fs (AxiomLogicalProtocol.expected which p q r a b c) reserve (AxiomLogicalProtocol.cost which).
Proof.
  intros Harena Htopology Herror Hmeta Hfalse Ha Hb Hc Hbindings Hbudget.
  destruct which as [ | | |which].
  - destruct Hbindings as [Hp Hq].
    destruct (AxiomK.generated_refines s (fun _=>false) (AxiomCommand.arguments 0 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)) fs
      (Z.of_nat a) (Z.of_nat b) p q reserve observations Harena Htopology Herror Hmeta eq_refl eq_refl eq_refl Ha Hb
      ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) Hbudget)
      as (built & next & Hrun & Hnext & Hsuccess & Hflag & Hword & Hmeaning & Hderives & Hprefix & Hreserve & Hordered & Hgrowth & Hframe).
    eapply normalize;eassumption.
  - destruct Hbindings as [Hp [Hq Hr]].
    destruct (AxiomSRefinement.generated_refines s (fun _=>false) (AxiomCommand.arguments 1 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)) fs
      (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) p q r reserve observations Harena Htopology Herror Hmeta eq_refl eq_refl eq_refl eq_refl Ha Hb Hc
      ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) Hbudget)
      as (built & next & Hrun & Hnext & Hsuccess & Hflag & Hword & Hmeaning & Hderives & Hprefix & Hreserve & Hordered & Hgrowth & Hframe).
    eapply normalize;eassumption.
  - destruct (AxiomDNERefinement.generated_refines s (fun _=>false) (AxiomCommand.arguments 2 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)) fs
      (Z.of_nat a) p reserve observations Harena Htopology Herror Hmeta Hfalse Ha ltac:(now rewrite Nat2Z.id)
      Hbudget eq_refl eq_refl)
      as (final & next & index & Hrun & Hnext & Hindex & Hword & Hmeaning & Hderives & Hprefix & Hflag & Hsuccess & Hframe & Hreserve & Hordered & Hgrowth).
    assert (Hlookup:nth_error next (Z.to_nat (meta_value final 0))=Some (SetTheory.axiom_formula (SetTheory.DNE p)))
      by (rewrite Hindex,Nat2Z.id;exact Hmeaning).
    eapply normalize;try eassumption. now rewrite Hindex.
  - destruct (AxiomEqualityRefinement.generated_refines which s (fun _=>false)
      (AxiomCommand.arguments (AxiomEqualityCircuits.selector which) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)) fs a b c reserve observations
      Harena Htopology Herror Hmeta eq_refl eq_refl eq_refl eq_refl Ha Hb Hc Hbudget)
      as (built & next & Hrun & Hnext & Hsuccess & Hflag & Hword & Hmeaning & Hderives & Hprefix & Hreserve & Hordered & Hgrowth & Hframe).
    destruct which;eapply normalize;eassumption.
Qed.

Lemma fixed which s fs a b c reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat -> nth_error fs 0=Some SetTheory.falsity ->
  Z.of_nat (length fs+length (AxiomFixedCircuits.plan which)+reserve)<=9223372036854775807 ->
  constructed s (fun _=>false) (AxiomCommand.arguments (AxiomFixedCircuits.selector which) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
    observations fs (SetTheory.axiom_formula (AxiomFixedCircuits.witness which)) reserve (length (AxiomFixedCircuits.plan which)).
Proof.
  intros Harena Htopology Herror Hmeta Hfalse Hbudget.
  destruct (AxiomFixedRefinement.generated_refines which s (fun _=>false)
    (AxiomCommand.arguments (AxiomFixedCircuits.selector which) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)) fs reserve observations
    Harena Htopology Herror Hmeta Hfalse Hbudget eq_refl)
    as (final & next & index & Hrun & Hnext & Hindex & Hword & Hmeaning & Hderives & Hprefix & Hflag & Hsuccess & Hframe & Hstorage & Hreserve & Hordered & Hgrowth).
  assert (Hlookup:nth_error next (Z.to_nat (meta_value final 0))=Some (SetTheory.axiom_formula (AxiomFixedCircuits.witness which)))
    by (rewrite Hindex,Nat2Z.id;exact Hmeaning).
  eapply normalize;try eassumption. now rewrite Hindex.
Qed.

Lemma renaming which s fs a b c p q bound reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs 0=Some SetTheory.falsity -> AxiomRenamingProtocol.bindings which fs a b p q ->
  Z.of_nat (RenameMemoBounds.fuel a)<=maximum -> RenameMemoIndexBounds.formula_bound bound p ->
  Z.of_nat bound+Z.of_nat (AxiomRenamingProtocol.increment which b)<=maximum ->
  Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  Z.of_nat (length fs+AxiomRenamingProtocol.cost which a+reserve)<=9223372036854775807 ->
  constructed s (fun _=>false) (AxiomCommand.arguments (Z.of_nat (AxiomRenamingProtocol.tag which)) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
    observations fs (AxiomRenamingProtocol.expected which p q b) reserve (AxiomRenamingProtocol.cost which a).
Proof.
  intros Hmeta Hsip Harena Htopology Herror Hfalse [Hp Hq] Hfuel Hbound Hindices Hheight Hbudget.
  destruct which.
  - destruct (AxiomInstRefinement.generated_refines s (fun _=>false) (AxiomCommand.arguments 3 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
      fs p a b bound reserve observations Hmeta Hsip Harena Htopology Herror Hp Hfalse eq_refl eq_refl eq_refl Hfuel Hbound Hindices Hheight ltac:(cbn [AxiomRenamingProtocol.cost] in Hbudget;lia))
      as (final & next & index & Hrun & Hnext & Hindex & Hword & Hmeaning & Hderives & Hprefix & Hflag & Hsuccess & Hframe & Hreserve & Hordered & Hgrowth).
    assert (Hlookup:nth_error next (Z.to_nat (meta_value final 0))=Some (SetTheory.axiom_formula (SetTheory.Inst p b)))
      by (rewrite Hindex,Nat2Z.id;exact Hmeaning).
    eapply normalize;try eassumption. all: first [now rewrite Hindex|cbn [AxiomRenamingProtocol.cost];lia].
  - destruct (AxiomDistRefinement.generated_refines s (fun _=>false) (AxiomCommand.arguments 4 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
      fs p q a b bound reserve observations Hmeta Hsip Harena Htopology Herror Hp Hq Hfalse eq_refl eq_refl eq_refl Hfuel Hbound Hindices Hheight ltac:(cbn [AxiomRenamingProtocol.cost] in Hbudget;lia))
      as (built & next & Hrun & Hnext & Hsuccess & Hflag & Hword & Hmeaning & Hderives & Hprefix & Hreserve & Hordered & Hgrowth & Hframe).
    eapply normalize;try eassumption;cbn [AxiomRenamingProtocol.cost];lia.
  - destruct (AxiomSeparationRefinement.generated_refines s (fun _=>false) (AxiomCommand.arguments 15 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
      fs p a bound reserve observations Hmeta Hsip Harena Htopology Herror Hp Hfalse eq_refl eq_refl Hfuel Hbound Hindices Hheight ltac:(cbn [AxiomRenamingProtocol.cost] in Hbudget;lia))
      as (built & next & Hrun & Hnext & Hsuccess & Hflag & Hword & Hmeaning & Hderives & Hprefix & Hreserve & Hordered & Hgrowth & Hframe).
    eapply normalize;try eassumption;cbn [AxiomRenamingProtocol.cost];lia.
  - destruct (AxiomReplacementRefinement.generated_refines s (fun _=>false) (AxiomCommand.arguments 16 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
      fs p a bound reserve observations Hmeta Hsip Harena Htopology Herror Hp Hfalse eq_refl eq_refl Hfuel Hbound Hindices Hheight ltac:(cbn [AxiomRenamingProtocol.cost] in Hbudget;lia))
      as (built & next & Hrun & Hnext & Hsuccess & Hflag & Hword & Hmeaning & Hderives & Hprefix & Hreserve & Hordered & Hgrowth & Hframe).
    eapply normalize;try eassumption;cbn [AxiomRenamingProtocol.cost];lia.
Qed.
End AxiomInvariant.
