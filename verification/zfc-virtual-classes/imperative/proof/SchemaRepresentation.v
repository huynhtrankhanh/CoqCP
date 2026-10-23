From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Schemata.
From NativeProof Require Import Index SipHash SchemaMetadata.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaRepresentation.
Import IndexExecution SipHashExecution.

Definition context fs classes prior := Protocol.State fs classes [] [] prior.

(* Children are interpreted in the strict prefix of this node. Saved theorems
   store their formula ID: schemaNode has already resolved the history ID. *)
Definition denotes fs classes prior k a b c d expression :=
  (k<>11%nat /\ Protocol.builds_node (context fs classes prior) [k;a;b;c;d] expression) \/
  (exists p (checked : SetTheory.derives p), k=11%nat /\ nth_error fs a=Some p /\
    expression=Protocol.PE (Schemata.saved_theorem p checked)).

Definition encode k a b c d expression : Z*Z*Z*Z*Z*Z*Z :=
  (Z.of_nat k,Z.of_nat a,Z.of_nat b,Z.of_nat c,Z.of_nat d,
    SchemaMetadata.kind expression,Z.of_nat (SchemaMetadata.arity expression)).
Definition fields_fit k a b c d expression :=
  Forall (fun n=>word (Z.of_nat n)) [k;a;b;c;d;SchemaMetadata.arity expression].
Definition entry fs classes prior raw expression :=
  exists k a b c d,
    raw=encode k a b c d expression /\ fields_fit k a b c d expression /\
    denotes fs classes prior k a b c d expression.

Lemma entry_metadata fs classes prior raw expression :
  entry fs classes prior raw expression -> SchemaMetadata.entry raw expression.
Proof.
  intros [k [a [b [c [d [-> [Hfit Hmeaning]]]]]]].
  unfold SchemaMetadata.entry,encode. cbn. split;[reflexivity|]. split;[reflexivity|].
  unfold fields_fit in Hfit.
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H;clear H;subst end. assumption.
Qed.

Lemma entry_builds fs classes prior k a b c d expression :
  k<>11%nat -> fields_fit k a b c d expression ->
  Protocol.builds_node (context fs classes prior) [k;a;b;c;d] expression ->
  entry fs classes prior (encode k a b c d expression) expression.
Proof. intros Hkind Hfit Hbuild. exists k,a,b,c,d. split;[reflexivity|]. split;[exact Hfit|]. left. split;assumption. Qed.

Lemma entry_saved fs classes prior a b c d p checked :
  fields_fit 11 a b c d (Protocol.PE (Schemata.saved_theorem p checked)) ->
  nth_error fs a=Some p ->
  entry fs classes prior (encode 11 a b c d (Protocol.PE (Schemata.saved_theorem p checked)))
    (Protocol.PE (Schemata.saved_theorem p checked)).
Proof.
  intros Hfit Hformula. exists 11%nat,a,b,c,d. split;[reflexivity|]. split;[exact Hfit|].
  right. exists p,checked. auto.
Qed.

Lemma builds_transport fs classes next_fs next_classes prior fields expression :
  (forall i p, nth_error fs i=Some p -> nth_error next_fs i=Some p) ->
  (forall i cls, nth_error classes i=Some cls -> nth_error next_classes i=Some cls) ->
  Protocol.builds_node (context fs classes prior) fields expression ->
  Protocol.builds_node (context next_fs next_classes prior) fields expression.
Proof.
  intros Hfs Hclasses Hbuild. inversion Hbuild;subst.
  - apply Protocol.node_meta. assumption.
  - apply Protocol.node_class. apply Hclasses. assumption.
  - apply Protocol.node_formula. apply Hfs. assumption.
  - apply Protocol.node_abstract. assumption.
  - apply Protocol.node_equal;assumption.
  - apply Protocol.node_member;assumption.
  - apply Protocol.node_imp;assumption.
  - apply Protocol.node_all. assumption.
  - apply Protocol.node_ax. assumption.
  - apply Protocol.node_mp;assumption.
  - apply Protocol.node_gen. assumption.
  - match goal with H : Protocol.theorem_at _ ?i=Some _ |- _ =>
      unfold Protocol.theorem_at,context in H;cbn [Protocol.history] in H;
      destruct i;discriminate end.
Qed.

Lemma entry_extend fs classes next_fs next_classes prior raw expression :
  (forall i p, nth_error fs i=Some p -> nth_error next_fs i=Some p) ->
  (forall i cls, nth_error classes i=Some cls -> nth_error next_classes i=Some cls) ->
  entry fs classes prior raw expression -> entry next_fs next_classes prior raw expression.
Proof.
  intros Hfs Hclasses [k [a [b [c [d [Hraw [Hfit Hdenotes]]]]]]].
  exists k,a,b,c,d. split;[exact Hraw|]. split;[exact Hfit|].
  destruct Hdenotes as [[Hkind Hbuild]|[p [checked [Hkind [Hformula Hsaved]]]]].
  - left. split;[exact Hkind|]. eapply builds_transport;eassumption.
  - right. exists p,checked. split;[exact Hkind|]. split;[now apply Hfs|exact Hsaved].
Qed.

Definition represents native logical :=
  SchemaMetadata.represents native (Protocol.expressions logical) /\
  forall index raw expression,
    nth_error (memory native arraydef_0__schemaNodes) index=Some raw ->
    nth_error (Protocol.expressions logical) index=Some expression ->
    entry (Protocol.formulas logical) (Protocol.classes logical)
      (firstn index (Protocol.expressions logical)) raw expression.

Lemma metadata native logical : represents native logical -> SchemaMetadata.represents native (Protocol.expressions logical).
Proof. exact (@proj1 _ _). Qed.

Lemma lookup native logical index expression :
  represents native logical -> nth_error (Protocol.expressions logical) index=Some expression ->
  exists raw, nth_error (memory native arraydef_0__schemaNodes) index=Some raw /\
    entry (Protocol.formulas logical) (Protocol.classes logical)
      (firstn index (Protocol.expressions logical)) raw expression.
Proof.
  intros [Hmeta Hmeaning] Hexpression.
  destruct (SchemaMetadata.represented_lookup native _ index expression Hmeta Hexpression) as [raw [Hraw Hentry]].
  exists raw. split;[exact Hraw|]. eapply Hmeaning;eassumption.
Qed.

Lemma empty native logical : Protocol.expressions logical=[] ->
  meta_value native 16=0 -> memory native arraydef_0__schemaNodes=[] -> represents native logical.
Proof.
  intros Hexpressions Hcount Hnodes. split.
  - rewrite Hexpressions. now apply SchemaMetadata.empty.
  - intros index raw expression Hraw Hexpression. rewrite Hexpressions in Hexpression.
    destruct index;discriminate.
Qed.

Lemma transport s t logical next :
  represents s logical ->
  meta_value t 16=meta_value s 16 -> memory t arraydef_0__schemaNodes=memory s arraydef_0__schemaNodes ->
  Protocol.formulas next=Protocol.formulas logical -> Protocol.classes next=Protocol.classes logical ->
  Protocol.expressions next=Protocol.expressions logical -> represents t next.
Proof.
  intros [Hmeta Hmeaning] Hcount Hnodes Hfs Hclasses Hexpressions. split.
  - rewrite Hexpressions. eapply SchemaMetadata.transport;eassumption.
  - rewrite Hnodes,Hfs,Hclasses,Hexpressions. exact Hmeaning.
Qed.

Theorem extend s t logical next :
  represents s logical ->
  meta_value t 16=meta_value s 16 -> memory t arraydef_0__schemaNodes=memory s arraydef_0__schemaNodes ->
  (forall i p, nth_error (Protocol.formulas logical) i=Some p -> nth_error (Protocol.formulas next) i=Some p) ->
  (forall i cls, nth_error (Protocol.classes logical) i=Some cls -> nth_error (Protocol.classes next) i=Some cls) ->
  Protocol.expressions next=Protocol.expressions logical -> represents t next.
Proof.
  intros [Hmetadata Hmeaning] Hcount Hnodes Hfs Hclasses Hexpressions. split.
  - rewrite Hexpressions. eapply SchemaMetadata.transport;eassumption.
  - intros index raw expression Hraw Hexpression. rewrite Hexpressions in Hexpression|-*.
    rewrite Hnodes in Hraw. eapply entry_extend;[exact Hfs|exact Hclasses|]. eapply Hmeaning;eassumption.
Qed.

Definition with_expression logical expression :=
  Protocol.State (Protocol.formulas logical) (Protocol.classes logical) (Protocol.history logical)
    (Protocol.bindings logical) (Protocol.expressions logical++[expression]).

Lemma prefix_before {A} (xs:list A) n tail : (n<=length xs)%nat -> firstn n (xs++tail)=firstn n xs.
Proof. intro Hbound. rewrite firstn_app. replace (n-length xs)%nat with 0%nat by lia. cbn. apply app_nil_r. Qed.

Theorem append s t logical raw expression :
  represents s logical ->
  entry (Protocol.formulas logical) (Protocol.classes logical) (Protocol.expressions logical) raw expression ->
  memory t arraydef_0__schemaNodes=memory s arraydef_0__schemaNodes++[raw] ->
  meta_value t 16=Z.of_nat (length (Protocol.expressions logical)+1) ->
  Z.of_nat (length (Protocol.expressions logical)+1)<=maximum ->
  represents t (with_expression logical expression).
Proof.
  intros [Hmetadata Hmeaning] Hentry Hnodes Hcount Hlimit.
  pose proof (SchemaMetadata.represents_length s _ Hmetadata) as Hlength.
  split.
  - unfold SchemaMetadata.represents,with_expression. cbn [Protocol.expressions].
    rewrite length_app. cbn [length]. split;[exact Hcount|]. split;[exact Hlimit|].
    rewrite Hnodes. apply Forall2_app;[exact (proj2 (proj2 Hmetadata))|].
    constructor;[now apply entry_metadata in Hentry|constructor].
  - unfold with_expression. cbn [Protocol.formulas Protocol.classes Protocol.expressions].
    intros index found item Hraw Hitem. rewrite Hnodes in Hraw.
    destruct (lt_dec index (length (Protocol.expressions logical))) as [Hbefore|Hafter].
    + rewrite nth_error_app1 in Hraw by lia. rewrite nth_error_app1 in Hitem by exact Hbefore.
      rewrite prefix_before by lia. eapply Hmeaning;eassumption.
    + rewrite nth_error_app2 in Hitem by lia.
      assert (Hindex:index=length (Protocol.expressions logical)).
      { destruct (index-length (Protocol.expressions logical))%nat as [|difference] eqn:Hdifference;[lia|].
        destruct difference;discriminate. }
      subst index. rewrite nth_error_app2 in Hraw by lia.
      rewrite Hlength,Nat.sub_diag in Hraw. injection Hraw as <-.
      rewrite Nat.sub_diag in Hitem. injection Hitem as <-.
      rewrite prefix_before by lia. now rewrite firstn_all.
Qed.
End SchemaRepresentation.
