From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Schemata.
From NativeProof Require Import Index SipHash NameRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaMetadata.
Import IndexExecution SipHashExecution.
Definition kind expression : Z := match expression with Protocol.CE _ => 0 | Protocol.FE _ => 1 | Protocol.PE _ => 2 end.
Definition arity expression : nat := match expression with Protocol.CE c => Schemata.class_arity c | Protocol.FE p => Schemata.formula_arity p | Protocol.PE p => Schemata.proof_arity p end.
Definition entry (raw : Z*Z*Z*Z*Z*Z*Z) expression :=
  let '(_,_,_,_,_,type,width) := raw in type = kind expression /\ width = Z.of_nat (arity expression) /\ word width.
Definition represents native expressions := meta_value native 16 = Z.of_nat (length expressions) /\
  Z.of_nat (length expressions) <= maximum /\ Forall2 entry (memory native arraydef_0__schemaNodes) expressions.
Lemma empty native : meta_value native 16 = 0 -> memory native arraydef_0__schemaNodes = [] -> represents native [].
Proof. intros Hcount Hnodes. split; [exact Hcount|]. split; [unfold maximum; cbn; lia|rewrite Hnodes; constructor]. Qed.
Lemma represents_length native expressions : represents native expressions -> length (memory native arraydef_0__schemaNodes) = length expressions.
Proof. intros [_ [_ Hentries]]. now apply Forall2_length in Hentries. Qed.
Lemma transport s t expressions : meta_value t 16 = meta_value s 16 -> memory t arraydef_0__schemaNodes = memory s arraydef_0__schemaNodes ->
  represents s expressions -> represents t expressions.
Proof. intros Hcount Hnodes. unfold represents. now rewrite Hcount,Hnodes. Qed.
Lemma represented_lookup native expressions index expression : represents native expressions -> nth_error expressions index = Some expression ->
  exists raw, nth_error (memory native arraydef_0__schemaNodes) index = Some raw /\ entry raw expression.
Proof.
  intros [_ [_ Hentries]] Hentry. exact (NameRepresentation.related_lookup _ _ _ index expression Hentries Hentry).
Qed.
Definition node_at (native : Machine) index := List.nth index (memory native arraydef_0__schemaNodes) (0,0,0,0,0,0,0).
Lemma fields native expressions index expression : represents native expressions -> nth_error expressions index = Some expression ->
  (index < length (memory native arraydef_0__schemaNodes))%nat /\
  snd (fst (node_at native index)) = kind expression /\ snd (node_at native index) = Z.of_nat (arity expression) /\
  Z.of_nat (arity expression) <= maximum.
Proof.
  intros Hrep Hentry. destruct (represented_lookup native expressions index expression Hrep Hentry) as [raw [Hraw Hfields]].
  split; [apply nth_error_Some; congruence|]. unfold node_at.
  match goal with |- context [@List.nth ?A index ?xs ?zero] =>
    let expression := constr:(@List.nth A index xs zero) in
    assert (Hnth : expression = raw) by exact (List.nth_error_nth _ _ zero Hraw); rewrite Hnth
  end.
  destruct raw as [[[[[[k a] b] c] d] type] width]. cbn [entry] in Hfields. destruct Hfields as [Htype [Hwidth Hword]].
  cbn [fst snd]. rewrite Htype,Hwidth. split; [reflexivity|]. split; [reflexivity|]. rewrite <-Hwidth. exact (proj2 Hword).
Qed.
Lemma proof_fields native logical index cert : represents native (Protocol.expressions logical) -> Protocol.pf logical index = Some cert ->
  (index < length (memory native arraydef_0__schemaNodes))%nat /\
  snd (fst (node_at native index)) = 2 /\ snd (node_at native index) = Z.of_nat (Schemata.proof_arity cert) /\
  Z.of_nat (Schemata.proof_arity cert) <= maximum.
Proof.
  intros Hrep Hproof. unfold Protocol.pf in Hproof.
  destruct (nth_error (Protocol.expressions logical) index) as [expr|] eqn:Hentry; [destruct expr|]; try discriminate.
  injection Hproof as <-. exact (fields native _ index _ Hrep Hentry).
Qed.
End SchemaMetadata.
