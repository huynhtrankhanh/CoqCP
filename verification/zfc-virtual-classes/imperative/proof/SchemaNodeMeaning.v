From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Schemata.
From NativeProof Require Import Index SipHash SchemaMetadata SchemaRepresentation SchemaCheck SchemaNode.
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
  all: unfold Protocol.axiom_expression,Protocol.formula_argument in Haxiom; cbn [existsb Nat.eqb Nat.leb] in Haxiom.
  all: repeat match type of Haxiom with context[Protocol.ff ?logical ?index] =>
    let formula:=fresh "formula" in let Hlookup:=fresh "Hlookup" in
    destruct (Protocol.ff logical index) as [formula|] eqn:Hlookup; [|discriminate Haxiom] end.
  all: try discriminate Haxiom.
  all: injection Haxiom as <-; collect_lookups;
    unfold plan,SchemaNode.reference_requests,SchemaNode.reference_type;
    repeat first [rewrite bool_decide_true by lia|rewrite bool_decide_false by lia];
    cbn [app fold_left fst snd]; split;[valid_requests|];
    split;[lia|];split;[widths|reflexivity].
Qed.
Theorem builds_plan logical kind a b c d expression :
  Protocol.builds_node logical [kind;a;b;c;d] expression -> (3<=kind<=10)%nat ->
  plan logical kind a b c d expression.
Proof.
  intros Hbuild Hrange. inversion Hbuild;subst;try lia.
  all: try match goal with H:Protocol.axiom_expression _ _ _ _ _=Some _ |- _ => exact (axiom_plan _ _ _ _ _ _ H) end.
  all: collect_lookups; unfold plan,SchemaNode.reference_requests,SchemaNode.reference_type;
    repeat first [rewrite bool_decide_true by lia|rewrite bool_decide_false by lia];
    cbn [fold_left fst snd]; split;[valid_requests|];
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
Lemma builds_context logical kind a b c d expression :
  Protocol.builds_node logical [kind;a;b;c;d] expression -> (3<=kind<=10)%nat ->
  Protocol.builds_node (SchemaRepresentation.context (Protocol.formulas logical) (Protocol.classes logical) (Protocol.expressions logical))
    [kind;a;b;c;d] expression.
Proof. intros Hbuild Hrange. inversion Hbuild;subst;try lia;constructor;assumption. Qed.
Theorem entry_bridge logical kind a b c d expression :
  Protocol.builds_node logical [kind;a;b;c;d] expression -> (3<=kind<=10)%nat ->
  Forall (fun index=>word (Z.of_nat index)) [kind;a;b;c;d] ->
  word (Z.of_nat (SchemaMetadata.arity expression)) ->
  SchemaRepresentation.entry (Protocol.formulas logical) (Protocol.classes logical) (Protocol.expressions logical)
    (Z.of_nat kind,Z.of_nat a,Z.of_nat b,Z.of_nat c,Z.of_nat d,SchemaNode.reference_type kind,Z.of_nat (SchemaMetadata.arity expression)) expression.
Proof.
  intros Hbuild Hrange Hfields Hwidth.
  destruct (builds_plan logical kind a b c d expression Hbuild Hrange) as [_ [_ [_ Htype]]].
  rewrite Htype. change (SchemaRepresentation.entry (Protocol.formulas logical) (Protocol.classes logical) (Protocol.expressions logical) (SchemaRepresentation.encode kind a b c d expression) expression).
  apply SchemaRepresentation.entry_builds;[lia| |exact (builds_context logical kind a b c d expression Hbuild Hrange)].
  unfold SchemaRepresentation.fields_fit.
  inversion Hfields as [|k ks Hk Htail];subst k ks.
  inversion Htail as [|x xs Ha Htail2];subst x xs.
  inversion Htail2 as [|x xs Hb Htail3];subst x xs.
  inversion Htail3 as [|x xs Hc Htail4];subst x xs.
  inversion Htail4 as [|x xs Hd Hnil];subst x xs.
  constructor 2;[exact Hk|]. constructor 2;[exact Ha|]. constructor 2;[exact Hb|].
  constructor 2;[exact Hc|]. constructor 2;[exact Hd|]. constructor 2;[exact Hwidth|constructor 1].
Qed.
Lemma represented_arity_word s expressions index expression : SchemaMetadata.represents s expressions ->
  nth_error expressions index=Some expression -> word (Z.of_nat (SchemaMetadata.arity expression)).
Proof.
  intros Hrep Hlookup. destruct (SchemaMetadata.fields s expressions index expression Hrep Hlookup) as [_ [_ [_ Hbound]]].
  unfold word. split;lia.
Qed.
Lemma width_fold_word expressions requests initial :
  Forall (fun request=>word (SchemaNode.reference_width expressions request)) requests -> word initial ->
  word (fold_left (fun width request=>Z.max width (SchemaNode.reference_width expressions request)) requests initial).
Proof.
  intros Hrequests. induction Hrequests as [|request tail Hwidth Htail IH] in initial|-*;[exact (fun H=>H)|].
  intros Hinitial. cbn [fold_left]. apply IH. unfold word in *. destruct Hwidth as [Hw0 Hwmax]. destruct Hinitial as [Hi0 Himax].
  split;[eapply Z.le_trans;[exact Hi0|apply Z.le_max_l]|apply Z.max_lub;assumption].
Qed.
Theorem builds_arity_word s logical kind a b c d expression :
  SchemaMetadata.represents s (Protocol.expressions logical) ->
  Protocol.builds_node logical [kind;a;b;c;d] expression -> (3<=kind<=10)%nat ->
  word (Z.of_nat (SchemaMetadata.arity expression)).
Proof.
  intros Hrep Hbuild Hrange.
  destruct (builds_plan logical kind a b c d expression Hbuild Hrange) as [Hvalid [_ [Hwidth _]]].
  rewrite <-Hwidth. apply width_fold_word;[|unfold word,maximum;lia].
  clear Hwidth. induction Hvalid as [|request tail Hrequest Htail IH];[constructor|]. constructor;[|exact IH].
  destruct Hrequest as [found [Hlookup Hkind]]. unfold SchemaNode.reference_width. rewrite Hlookup.
  exact (represented_arity_word s (Protocol.expressions logical) (fst request) found Hrep Hlookup).
Qed.
Lemma check_many_nonzero expressions requests s :
  (19<length (memory s arraydef_0__meta))%nat ->
  meta_value (SchemaNode.check_many expressions requests s) 18<>0 ->
  meta_value s 18<>0 /\ Forall (SchemaNode.valid_reference expressions) requests.
Proof.
  induction requests as [|[index expected] tail IH] in s|-*.
  - intros Hmeta Hflag. split;[exact Hflag|constructor].
  - intros Hmeta Hflag. unfold SchemaNode.check_many in Hflag. cbn [fold_left fst snd] in Hflag.
    destruct (IH (SchemaCheck.semantic_result s expressions index expected)
      ltac:(rewrite SchemaNode.semantic_length;exact Hmeta) Hflag) as [Hhead Htail].
    rewrite SchemaCheck.semantic_flag in Hhead by exact Hmeta.
    destruct (nth_error expressions index) as [expression|] eqn:Hlookup;[|contradiction].
    destruct (bool_decide (SchemaMetadata.kind expression<>expected)) eqn:Hkind;[contradiction|].
    apply bool_decide_eq_false in Hkind.
    split;[exact Hhead|]. constructor;[|exact Htail].
    exists expression. cbn [fst snd]. split;[exact Hlookup|]. lia.
Qed.
Lemma valid_class logical index :
  SchemaNode.valid_reference (Protocol.expressions logical) (index,0) ->
  exists cls, Protocol.cf logical index=Some cls.
Proof.
  intros [expression [Hlookup Hkind]]. destruct expression;cbn [SchemaMetadata.kind] in Hkind;try discriminate.
  unfold Protocol.cf. cbn [fst] in Hlookup. rewrite Hlookup. eexists;reflexivity.
Qed.
Lemma valid_formula logical index :
  SchemaNode.valid_reference (Protocol.expressions logical) (index,1) ->
  exists formula, Protocol.ff logical index=Some formula.
Proof.
  intros [expression [Hlookup Hkind]]. destruct expression;cbn [SchemaMetadata.kind] in Hkind;try discriminate.
  unfold Protocol.ff. cbn [fst] in Hlookup. rewrite Hlookup. eexists;reflexivity.
Qed.
Lemma valid_proof logical index :
  SchemaNode.valid_reference (Protocol.expressions logical) (index,2) ->
  exists cert, Protocol.pf logical index=Some cert.
Proof.
  intros [expression [Hlookup Hkind]]. destruct expression;cbn [SchemaMetadata.kind] in Hkind;try discriminate.
  unfold Protocol.pf. cbn [fst] in Hlookup. rewrite Hlookup. eexists;reflexivity.
Qed.
Ltac unpack_requests H := repeat match type of H with
| Forall _ (_::_) => let Hhead:=fresh "Hhead" in let Htail:=fresh "Htail" in
  inversion H as [|request requests Hhead Htail];subst request requests;clear H;rename Htail into H
end.
Ltac resolve_valid := repeat match goal with
| H:SchemaNode.valid_reference (Protocol.expressions ?logical) (?index,0) |- _ =>
  let cls:=fresh "cls" in let Hlookup:=fresh "Hlookup" in destruct (valid_class logical index H) as [cls Hlookup];clear H
| H:SchemaNode.valid_reference (Protocol.expressions ?logical) (?index,1) |- _ =>
  let formula:=fresh "formula" in let Hlookup:=fresh "Hlookup" in destruct (valid_formula logical index H) as [formula Hlookup];clear H
| H:SchemaNode.valid_reference (Protocol.expressions ?logical) (?index,2) |- _ =>
  let cert:=fresh "cert" in let Hlookup:=fresh "Hlookup" in destruct (valid_proof logical index H) as [cert Hlookup];clear H
end.
Lemma valid_axiom_builds logical tag a b c : (tag<=17)%nat ->
  Forall (SchemaNode.valid_reference (Protocol.expressions logical)) (SchemaNode.reference_requests 8 tag a b c) ->
  exists cert, Protocol.axiom_expression logical tag a b c=Some cert.
Proof.
  intros Htag Hvalid.
  let rec cases depth tag := lazymatch depth with O=>idtac | S ?rest=>
    let next:=fresh "tag" in destruct tag as [|next];[idtac|cases rest next] end in cases 18%nat tag.
  all: try lia.
  all: unfold SchemaNode.reference_requests in Hvalid;
    repeat first [rewrite bool_decide_true in Hvalid by lia|rewrite bool_decide_false in Hvalid by lia];
    cbn [app] in Hvalid;unpack_requests Hvalid;resolve_valid;
    unfold Protocol.axiom_expression,Protocol.formula_argument;
    cbn [existsb Nat.eqb Nat.leb];
    repeat match goal with H:Protocol.ff ?logical ?index=Some ?formula |- context[Protocol.ff ?logical ?index] => rewrite H end;
    eexists;reflexivity.
Qed.
Lemma valid_requests_builds logical kind a b c d :
  (3<=kind<=10)%nat -> (kind=8%nat -> (a<=17)%nat) ->
  Forall (SchemaNode.valid_reference (Protocol.expressions logical)) (SchemaNode.reference_requests kind a b c d) ->
  exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression.
Proof.
  intros Hrange Htag Hvalid.
  assert (Hcases:kind=3%nat \/ kind=4%nat \/ kind=5%nat \/ kind=6%nat \/ kind=7%nat \/ kind=8%nat \/ kind=9%nat \/ kind=10%nat) by lia.
  destruct Hcases as [Hcase|[Hcase|[Hcase|[Hcase|[Hcase|[Hcase|[Hcase|Hcase]]]]]]];subst kind.
  all: try match goal with H:Forall _ (SchemaNode.reference_requests 8 _ _ _ _) |- _ =>
    destruct (valid_axiom_builds logical a b c d ltac:(apply Htag;reflexivity) H) as [cert Haxiom];
    exists (Protocol.PE cert);constructor;exact Haxiom end.
  all: unfold SchemaNode.reference_requests in Hvalid;unpack_requests Hvalid;resolve_valid;
    eexists;constructor;eassumption.
Qed.
Theorem reference_builds s logical kind a b c d :
  (19<length (memory s arraydef_0__meta))%nat -> (3<=kind<=10)%nat ->
  meta_value (SchemaNode.reference_state s (Protocol.expressions logical) kind a b c d) 18<>0 ->
  exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression.
Proof.
  intros Hmeta Hrange Hflag. unfold SchemaNode.reference_state in Hflag.
  assert (Hlength:(19<length (memory (SchemaNode.reference_initial s kind a) arraydef_0__meta))%nat).
  { unfold SchemaNode.reference_initial,SchemaCheck.rejected.
    destruct (bool_decide (kind=8%nat /\ (17<a)%nat));rewrite ?store_meta_length,SchemaNode.initialized_length;exact Hmeta. }
  destruct (check_many_nonzero _ _ _ Hlength Hflag) as [Hinitial Hvalid].
  apply valid_requests_builds;[exact Hrange| |exact Hvalid].
  intro Hkind. unfold SchemaNode.reference_initial in Hinitial.
  destruct (bool_decide (kind=8%nat /\ (17<a)%nat)) eqn:Hbad.
  - unfold SchemaCheck.rejected in Hinitial. rewrite meta_store_same in Hinitial by (rewrite SchemaNode.initialized_length;lia). contradiction.
  - apply bool_decide_eq_false in Hbad. lia.
Qed.
Theorem reference_rejected s logical kind a b c d :
  (19<length (memory s arraydef_0__meta))%nat -> (3<=kind<=10)%nat ->
  (~exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression) ->
  meta_value (SchemaNode.reference_state s (Protocol.expressions logical) kind a b c d) 18=0.
Proof.
  intros Hmeta Hrange Hnone.
  destruct (Z.eq_dec (meta_value (SchemaNode.reference_state s (Protocol.expressions logical) kind a b c d) 18) 0) as [Hzero|Hnonzero];[exact Hzero|].
  exfalso. apply Hnone. exact (reference_builds s logical kind a b c d Hmeta Hrange Hnonzero).
Qed.
End SchemaNodeMeaning.
