From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Schemata VirtualClasses.
From NativeProof Require Import Index SipHash AxiomCommand AxiomInvariant AxiomLogicalProtocol AxiomRenamingProtocol
  AxiomEqualityCircuits AxiomFixedCircuits Representation FormulaTopology RenameMemoBounds
  RenameMemoIndexBounds RenameMemoTransition.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomTaggedInvariant.
Import IndexExecution SipHashExecution.
Definition needs_p tag := existsb (Nat.eqb tag) [0;1;2;3;4;15;16]%nat.
Definition needs_q tag := existsb (Nat.eqb tag) [0;1;4]%nat.
Definition ready (fs:list SetTheory.formula) tag idA idB idC rawI rawJ rawK p q r :=
  (if needs_p tag then nth_error fs idA=Some p else idA=rawI) /\
  (if needs_q tag then nth_error fs idB=Some q else idB=rawJ) /\
  (if Nat.eqb tag 1 then nth_error fs idC=Some r else idC=rawK).
Definition cost (tag root:nat) : nat := (match tag with
| 0=>2 | 1=>6 | 2=>3 | 3=>S root*S root+2 | 4=>S root*S root+5
| 5=>1 | 6 | 7 | 8=>5 | 9=>10 | 10=>15 | 11=>8 | 12=>10 | 13=>9 | 14=>33
| 15=>S root*S root+14 | 16=>3*(S root*S root)+21 | 17=>42 | _=>0 end)%nat.
Definition uses_rename tag := existsb (Nat.eqb tag) [3;4;15;16]%nat.
Definition increment (tag rawJ:nat) : nat := (match tag with 3=>rawJ | 4=>1 | _=>2 end)%nat.
Definition renaming_ready tag root rawJ p bound :=
  if uses_rename tag then
    Z.of_nat (RenameMemoBounds.fuel root)<=maximum /\ RenameMemoIndexBounds.formula_bound bound p /\
    Z.of_nat bound+Z.of_nat (increment tag rawJ)<=maximum /\ Z.of_nat (RenameMemoTransition.height p)<=maximum
  else True.
Definition literal_axiom tag p q r rawI rawJ rawK :=
  Schemata.instantiate_axiom (fun _=>VirtualClasses.set 0) 0
    (Schemata.template_axiom tag (Schemata.literal_formula p) (Schemata.literal_formula q) (Schemata.literal_formula r) rawI rawJ rawK).

Lemma literal_instantiated rho depth tag tp tq tr rawI rawJ rawK :
  literal_axiom tag (Schemata.instantiate_formula rho depth tp) (Schemata.instantiate_formula rho depth tq)
    (Schemata.instantiate_formula rho depth tr) rawI rawJ rawK=
  Schemata.instantiate_axiom rho depth (Schemata.template_axiom tag tp tq tr rawI rawJ rawK).
Proof. reflexivity. Qed.

Theorem construct s fs tag idA idB idC rawI rawJ rawK p q r bound reserve observations :
  (tag<=17)%nat ->
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs 0=Some SetTheory.falsity ->
  word (Z.of_nat idA) -> word (Z.of_nat idB) -> word (Z.of_nat idC) ->
  ready fs tag idA idB idC rawI rawJ rawK p q r -> renaming_ready tag idA rawJ p bound ->
  Z.of_nat (length fs+cost tag idA+reserve)<=9223372036854775807 ->
  exists witness,literal_axiom tag p q r rawI rawJ rawK=Some witness /\
    AxiomInvariant.constructed s (fun _=>false)
      (AxiomCommand.arguments (Z.of_nat tag) (Z.of_nat idA) (Z.of_nat idB) (Z.of_nat idC))
      observations fs (SetTheory.axiom_formula witness) reserve (cost tag idA).
Proof.
  intros Htag Hmeta Hsip Harena Hordered Herror Hfalse HAword HBword HCword Hready Hrename Hbudget.
  let rec cases count index := lazymatch count with
    O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 18%nat tag.
  19: lia.
  all: destruct Hready as [HA [HB HC]];
    cbn [needs_p needs_q existsb Nat.eqb orb] in HA,HB,HC;
    eexists;split;[reflexivity|].
  - eapply (AxiomInvariant.logical AxiomLogicalProtocol.k s fs idA idB idC p q r reserve observations);try eassumption;[lia|split;assumption].
  - eapply (AxiomInvariant.logical AxiomLogicalProtocol.srule s fs idA idB idC p q r reserve observations);try eassumption;[lia|repeat split;assumption].
  - eapply (AxiomInvariant.logical AxiomLogicalProtocol.dne s fs idA idB idC p q r reserve observations);try eassumption;lia.
  - subst idB. destruct Hrename as [Hfuel [Hbound [Hindices Hheight]]].
    eapply (AxiomInvariant.renaming AxiomRenamingProtocol.inst s fs idA rawJ idC p q bound reserve observations);try eassumption. split;[exact HA|exact I].
  - destruct Hrename as [Hfuel [Hbound [Hindices Hheight]]].
    eapply (AxiomInvariant.renaming AxiomRenamingProtocol.dist s fs idA idB idC p q bound reserve observations);try eassumption. split;assumption.
  - subst idA. eapply (AxiomInvariant.reflexivity s (fun _=>false) (AxiomCommand.arguments 5 (Z.of_nat rawI) (Z.of_nat idB) (Z.of_nat idC)) fs rawI reserve observations);try eassumption;[lia|reflexivity|reflexivity].
  - subst idA idB idC. eapply (AxiomInvariant.logical (AxiomLogicalProtocol.equality AxiomEqualityCircuits.member_left) s fs rawI rawJ rawK p q r reserve observations);try eassumption;first [lia|exact I].
  - subst idA idB idC. eapply (AxiomInvariant.logical (AxiomLogicalProtocol.equality AxiomEqualityCircuits.member_right) s fs rawI rawJ rawK p q r reserve observations);try eassumption;first [lia|exact I].
  - subst idA idB idC. eapply (AxiomInvariant.logical (AxiomLogicalProtocol.equality AxiomEqualityCircuits.equal_trans) s fs rawI rawJ rawK p q r reserve observations);try eassumption;first [lia|exact I].
  - eapply (AxiomInvariant.fixed AxiomFixedCircuits.extensionality s fs idA idB idC reserve observations);try eassumption;lia.
  - eapply (AxiomInvariant.fixed AxiomFixedCircuits.foundation s fs idA idB idC reserve observations);try eassumption;lia.
  - eapply (AxiomInvariant.fixed AxiomFixedCircuits.pairing s fs idA idB idC reserve observations);try eassumption;lia.
  - eapply (AxiomInvariant.fixed AxiomFixedCircuits.union s fs idA idB idC reserve observations);try eassumption;lia.
  - eapply (AxiomInvariant.fixed AxiomFixedCircuits.power s fs idA idB idC reserve observations);try eassumption;lia.
  - eapply (AxiomInvariant.fixed AxiomFixedCircuits.infinity s fs idA idB idC reserve observations);try eassumption;lia.
  - destruct Hrename as [Hfuel [Hbound [Hindices Hheight]]].
    eapply (AxiomInvariant.renaming AxiomRenamingProtocol.separation s fs idA idB idC p q bound reserve observations);try eassumption. split;[exact HA|exact I].
  - destruct Hrename as [Hfuel [Hbound [Hindices Hheight]]].
    eapply (AxiomInvariant.renaming AxiomRenamingProtocol.replacement s fs idA idB idC p q bound reserve observations);try eassumption. split;[exact HA|exact I].
  - eapply (AxiomInvariant.fixed AxiomFixedCircuits.choice s fs idA idB idC reserve observations);try eassumption;lia.
Qed.
End AxiomTaggedInvariant.
