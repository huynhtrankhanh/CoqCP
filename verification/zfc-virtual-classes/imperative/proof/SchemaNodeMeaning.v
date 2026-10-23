From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Schemata.
From NativeProof Require Import Index SipHash SchemaMetadata SchemaNode.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaNodeMeaning.
Import IndexExecution SipHashExecution.
Lemma class_lookup logical index cls : Protocol.cf logical index=Some cls ->
  nth_error (Protocol.expressions logical) index=Some (Protocol.CE cls).
Proof.
  unfold Protocol.cf. destruct (nth_error (Protocol.expressions logical) index) as [expression|] eqn:Hentry;
    [destruct expression|];try discriminate. intro Hsome. injection Hsome as <-. reflexivity.
Qed.
Lemma formula_lookup logical index formula : Protocol.ff logical index=Some formula ->
  nth_error (Protocol.expressions logical) index=Some (Protocol.FE formula).
Proof.
  unfold Protocol.ff. destruct (nth_error (Protocol.expressions logical) index) as [expression|] eqn:Hentry;
    [destruct expression|];try discriminate. intro Hsome. injection Hsome as <-. reflexivity.
Qed.
Lemma proof_lookup logical index cert : Protocol.pf logical index=Some cert ->
  nth_error (Protocol.expressions logical) index=Some (Protocol.PE cert).
Proof.
  unfold Protocol.pf. destruct (nth_error (Protocol.expressions logical) index) as [expression|] eqn:Hentry;
    [destruct expression|];try discriminate. intro Hsome. injection Hsome as <-. reflexivity.
Qed.
Lemma valid_lookup expressions index expected expression : nth_error expressions index=Some expression ->
  SchemaMetadata.kind expression=expected -> SchemaNode.valid_reference expressions (index,expected).
Proof. intros Hentry Hkind. exists expression. split;assumption. Qed.
Ltac collect_lookups := repeat match goal with
| H:Protocol.cf ?logical ?index=Some ?cls |- _ =>
  let Hentry:=fresh "Hentry" in pose proof (class_lookup logical index cls H) as Hentry; clear H
| H:Protocol.ff ?logical ?index=Some ?formula |- _ =>
  let Hentry:=fresh "Hentry" in pose proof (formula_lookup logical index formula H) as Hentry; clear H
| H:Protocol.pf ?logical ?index=Some ?cert |- _ =>
  let Hentry:=fresh "Hentry" in pose proof (proof_lookup logical index cert H) as Hentry; clear H
end.
Ltac valid_requests := lazymatch goal with
| |- Forall _ [] => constructor
| |- Forall _ (_::_) => constructor; [
    match goal with H:nth_error ?expressions ?index=Some ?expression |- SchemaNode.valid_reference ?expressions (?index,?expected) =>
      exact (valid_lookup expressions index expected expression H ltac:(reflexivity)) end
  |valid_requests]
end.
Ltac widths :=
  unfold SchemaNode.reference_width; cbn [fst snd];
  repeat match goal with H:nth_error ?expressions ?index=Some ?expression |- context[nth_error ?expressions ?index] => rewrite H end;
  cbn [SchemaMetadata.arity Schemata.class_arity Schemata.formula_arity Schemata.proof_arity Schemata.axiom_arity];
  repeat rewrite Nat2Z.inj_max;
  repeat match goal with |- context[Z.max 0 (Z.of_nat ?width)] => rewrite (Z.max_r 0 (Z.of_nat width)) by lia end;
  rewrite ?Z.max_assoc; reflexivity.
Definition plan logical kind a b c d expression :=
  Forall (SchemaNode.valid_reference (Protocol.expressions logical)) (SchemaNode.reference_requests kind a b c d) /\
  (kind=8%nat -> (a<=17)%nat) /\
  fold_left (fun width request=>Z.max width (SchemaNode.reference_width (Protocol.expressions logical) request))
    (SchemaNode.reference_requests kind a b c d) 0=Z.of_nat (SchemaMetadata.arity expression) /\
  SchemaNode.reference_type kind=SchemaMetadata.kind expression.
Lemma axiom_plan logical tag a b c cert : Protocol.axiom_expression logical tag a b c=Some cert ->
  plan logical 8 tag a b c (Protocol.PE cert).
Proof.
  intro Haxiom.
  let rec cases depth tag := lazymatch depth with O=>idtac | S ?rest=>
    let next:=fresh "tag" in destruct tag as [|next];[idtac|cases rest next] end in cases 18%nat tag.
  all: cbn [Protocol.axiom_expression Protocol.formula_argument existsb Nat.eqb Nat.leb] in Haxiom.
  all: repeat match goal with Haxiom:context[Protocol.ff ?logical ?index] |- _ =>
    let formula:=fresh "formula" in let Hlookup:=fresh "Hlookup" in
    destruct (Protocol.ff logical index) as [formula|] eqn:Hlookup; [|discriminate Haxiom] end.
  all: try discriminate Haxiom.
  all: injection Haxiom as <-; collect_lookups;
    unfold plan,SchemaNode.reference_requests,SchemaNode.reference_type;
    cbn [bool_decide app fold_left fst snd]; split;[valid_requests|];
    split;[lia|];split;[widths|reflexivity].
Qed.
Theorem builds_plan logical kind a b c d expression :
  Protocol.builds_node logical [kind;a;b;c;d] expression -> (3<=kind<=10)%nat ->
  plan logical kind a b c d expression.
Proof.
  intros Hbuild Hrange. inversion Hbuild;subst;try lia.
  all: try match goal with H:Protocol.axiom_expression _ _ _ _ _=Some _ |- _ => exact (axiom_plan _ _ _ _ _ _ H) end.
  all: collect_lookups; unfold plan,SchemaNode.reference_requests,SchemaNode.reference_type;
    cbn [bool_decide fold_left fst snd]; split;[valid_requests|];
    split;[lia|];split;[widths|reflexivity].
Qed.
Theorem reference_metadata s logical kind a b c d expression :
  (19<length (memory s arraydef_0__meta))%nat ->
  Protocol.builds_node logical [kind;a;b;c;d] expression -> (3<=kind<=10)%nat ->
  meta_value (SchemaNode.reference_state s (Protocol.expressions logical) kind a b c d) 18=1 /\
  meta_value (SchemaNode.reference_state s (Protocol.expressions logical) kind a b c d) 19=Z.of_nat (SchemaMetadata.arity expression) /\
  SchemaNode.reference_type kind=SchemaMetadata.kind expression.
Proof.
  intros Hmeta Hbuild Hrange.
  destruct (builds_plan logical kind a b c d expression Hbuild Hrange) as [Hvalid [Htag [Hwidth Htype]]].
  assert (Hinitial:SchemaNode.reference_initial s kind a=SchemaNode.initialized s).
  { unfold SchemaNode.reference_initial. rewrite bool_decide_false by (intros [Hkind Hlarge];specialize (Htag Hkind);lia). reflexivity. }
  unfold SchemaNode.reference_state. rewrite Hinitial.
  assert (Hlength:(19<length (memory (SchemaNode.initialized s) arraydef_0__meta))%nat).
  { rewrite SchemaNode.initialized_length. exact Hmeta. }
  assert (Hflag:meta_value (SchemaNode.initialized s) 18=1).
  { unfold SchemaNode.initialized. rewrite meta_store_other by lia. apply meta_store_same. lia. }
  pose proof (SchemaNode.check_many_valid (Protocol.expressions logical) (SchemaNode.reference_requests kind a b c d)
    (SchemaNode.initialized s) Hlength Hvalid Hflag) as [Hdone Hresult].
  split;[exact Hdone|]. split;[|exact Htype]. rewrite Hresult.
  assert (Hzero:meta_value (SchemaNode.initialized s) 19=0).
  { unfold SchemaNode.initialized. apply meta_store_same. rewrite store_meta_length. lia. }
  rewrite Hzero. exact Hwidth.
Qed.
End SchemaNodeMeaning.
