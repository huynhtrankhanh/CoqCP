From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Schemata.
From NativeProof Require Import Index SipHash SchemaMetadata SchemaRepresentation ObservedLocal NativePrimitives InternTail.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaGraph.
Import IndexExecution SipHashExecution ObservedLocal.
Definition need_p tag := existsb (Nat.eqb tag) [0;1;2;3;4;15;16]%nat.
Definition need_q tag := existsb (Nat.eqb tag) [0;1;4]%nat.
Definition need_r tag := Nat.eqb tag 1.
(* Pairs contain a dependency ID and its extra binder depth. These are exactly
   the schemaMark calls made for a marked schemaInstance node. *)
Definition children_fields (k a b c d:nat) : list (nat*nat) := match k with
| 3%nat | 7%nat | 10%nat => [(a,1%nat)]
| 4%nat | 5%nat | 6%nat | 9%nat => [(a,0%nat);(b,0%nat)]
| 8%nat => (if need_p a then [(b,0%nat)] else [])++
       (if need_q a then [(c,0%nat)] else [])++
       (if need_r a then [(d,0%nat)] else [])
| _=>[] end.
Definition children (raw:Z*Z*Z*Z*Z*Z*Z) :=
  let '(k,a,b,c,d,_,_):=raw in children_fields (Z.to_nat k) (Z.to_nat a) (Z.to_nat b) (Z.to_nat c) (Z.to_nat d).
Lemma children_encode k a b c d expression :
  children (SchemaRepresentation.encode k a b c d expression)=children_fields k a b c d.
Proof. unfold children,SchemaRepresentation.encode. now rewrite !Nat2Z.id. Qed.
Lemma cf_bound s index value : Protocol.cf s index=Some value -> (index<length (Protocol.expressions s))%nat.
Proof.
  unfold Protocol.cf. destruct (nth_error (Protocol.expressions s) index) as [expression|] eqn:Hlookup;[|discriminate].
  intro Hvalue. apply nth_error_Some;congruence.
Qed.
Lemma ff_bound s index value : Protocol.ff s index=Some value -> (index<length (Protocol.expressions s))%nat.
Proof.
  unfold Protocol.ff. destruct (nth_error (Protocol.expressions s) index) as [expression|] eqn:Hlookup;[|discriminate].
  intro Hvalue. apply nth_error_Some;congruence.
Qed.
Lemma pf_bound s index value : Protocol.pf s index=Some value -> (index<length (Protocol.expressions s))%nat.
Proof.
  unfold Protocol.pf. destruct (nth_error (Protocol.expressions s) index) as [expression|] eqn:Hlookup;[|discriminate].
  intro Hvalue. apply nth_error_Some;congruence.
Qed.
Lemma axiom_dependencies s tag a b c cert :
  Protocol.axiom_expression s tag a b c=Some cert ->
  (need_p tag=true -> (a<length (Protocol.expressions s))%nat) /\
  (need_q tag=true -> (b<length (Protocol.expressions s))%nat) /\
  (need_r tag=true -> (c<length (Protocol.expressions s))%nat).
Proof.
  unfold Protocol.axiom_expression. fold (need_p tag) (need_q tag) (need_r tag).
  destruct (Protocol.formula_argument s (need_p tag) a) as [p|] eqn:Hp;[|discriminate].
  destruct (Protocol.formula_argument s (need_q tag) b) as [q|] eqn:Hq;[|discriminate].
  destruct (Protocol.formula_argument s (need_r tag) c) as [r|] eqn:Hr;[|discriminate].
  intro Hcert. repeat split;intro Hneeded;unfold Protocol.formula_argument in *;
    first [rewrite Hneeded in Hp;eapply ff_bound;exact Hp
          |rewrite Hneeded in Hq;eapply ff_bound;exact Hq
          |rewrite Hneeded in Hr;eapply ff_bound;exact Hr].
Qed.
Lemma builds_children s k a b c d expression child extra :
  Protocol.builds_node s [k;a;b;c;d]%nat expression ->
  In (child,extra) (children_fields k a b c d) ->
  (child<length (Protocol.expressions s) /\ extra<=1)%nat.
Proof.
  intro Hbuild. inversion Hbuild;subst;cbn [children_fields];try contradiction.
  all: try solve [intro Hin;cbn in Hin;destruct Hin as [Heq|Hnone];[injection Heq as <- <-;split;[eauto using cf_bound,ff_bound,pf_bound|lia]|contradiction]].
  all: try solve [intro Hin;cbn in Hin;destruct Hin as [Heq|[Heq|Hnone]];try contradiction;
    injection Heq as <- <-;(split;[eauto using cf_bound,ff_bound,pf_bound|lia])].
  match goal with Hax:Protocol.axiom_expression _ _ _ _ _=Some _ |- _ =>
    destruct (axiom_dependencies _ _ _ _ _ _ Hax) as [Hp [Hq Hr]] end.
  intro Hin. repeat rewrite in_app_iff in Hin.
  destruct Hin as [Hin|[Hin|Hin]].
  - destruct (need_p _) eqn:Hneed;[|contradiction]. cbn in Hin. destruct Hin as [Heq|Hnone];[|contradiction]. injection Heq as <- <-. split;[now apply Hp|lia].
  - destruct (need_q _) eqn:Hneed;[|contradiction]. cbn in Hin. destruct Hin as [Heq|Hnone];[|contradiction]. injection Heq as <- <-. split;[now apply Hq|lia].
  - destruct (need_r _) eqn:Hneed;[|contradiction]. cbn in Hin. destruct Hin as [Heq|Hnone];[|contradiction]. injection Heq as <- <-. split;[now apply Hr|lia].
Qed.
Lemma entry_children fs classes prior raw expression child extra :
  SchemaRepresentation.entry fs classes prior raw expression -> In (child,extra) (children raw) ->
  (child<length prior /\ extra<=1)%nat.
Proof.
  intros (k & a & b & c & d & -> & Hfit & Hmeaning). rewrite children_encode.
  destruct Hmeaning as [[Hkind Hbuild]|(p & checked & -> & Hformula & Hexpression)].
  - apply (builds_children _ _ _ _ _ _ _ child extra Hbuild).
  - cbn [children_fields]. contradiction.
Qed.
Definition ordered native := forall node child extra,
  (node<length (memory native arraydef_0__schemaNodes))%nat ->
  In (child,extra) (children (SchemaMetadata.node_at native node)) -> (child<node /\ extra<=1)%nat.
Theorem represented_ordered native logical : SchemaRepresentation.represents native logical -> ordered native.
Proof.
  intros Hrep node child extra Hnode Hin.
  pose proof (SchemaMetadata.represents_length native _ (SchemaRepresentation.metadata _ _ Hrep)) as Hlength.
  assert (Hlogical:(node<length (Protocol.expressions logical))%nat) by lia.
  destruct (nth_error (Protocol.expressions logical) node) as [expression|] eqn:Hexpression;
    [|apply nth_error_None in Hexpression;lia].
  destruct (SchemaRepresentation.lookup native logical node expression Hrep Hexpression) as (raw & Hraw & Hentry).
  unfold SchemaMetadata.node_at in Hin.
  match type of Hin with context [@List.nth ?A node ?xs ?zero] =>
    let expression:=constr:(@List.nth A node xs zero) in
    let Hnth:=fresh in assert (Hnth:expression=raw) by exact (List.nth_error_nth _ _ zero Hraw);rewrite Hnth in Hin end.
  destruct (entry_children _ _ _ _ _ _ _ Hentry Hin) as [Hchild Hextra].
  rewrite length_firstn in Hchild. pose proof (Nat.le_min_l node (length (Protocol.expressions logical))). split;lia.
Qed.
Inductive reachable native root : nat -> nat -> Prop :=
| root_reachable : reachable native root root 0
| child_reachable node depth child extra : reachable native root node depth ->
    In (child,extra) (children (SchemaMetadata.node_at native node)) -> reachable native root child (depth+extra).
Theorem reachable_bound native root node depth : ordered native ->
  (root<length (memory native arraydef_0__schemaNodes))%nat -> reachable native root node depth ->
  (node<length (memory native arraydef_0__schemaNodes) /\ node+depth<=root)%nat.
Proof.
  intros Hordered Hroot Hreachable. induction Hreachable as [|parent depth child extra Hparent [Hparentbound Hsum] Hchild].
  - split;lia.
  - destruct (Hordered parent child extra Hparentbound Hchild) as [Hlower Hextra]. split;lia.
Qed.
Definition width root := S root.
Definition key root node depth := (node*width root+depth)%nat.
Lemma grid_bound root node depth : (node<width root)%nat -> (depth<width root)%nat ->
  (key root node depth<width root*width root)%nat.
Proof. unfold key,width. intros;nia. Qed.
Theorem reachable_grid native root node depth : ordered native ->
  (root<length (memory native arraydef_0__schemaNodes))%nat -> reachable native root node depth ->
  (node<width root /\ depth<width root /\ key root node depth<width root*width root)%nat.
Proof.
  intros Hordered Hroot Hreachable. destruct (reachable_bound _ _ _ _ Hordered Hroot Hreachable) as [_ Hsum].
  assert (Hnode:(node<width root)%nat) by (unfold width;lia).
  assert (Hdepth:(depth<width root)%nat) by (unfold width;lia).
  split;[exact Hnode|]. split;[exact Hdepth|]. now apply grid_bound.
Qed.
Theorem child_grid native root node depth child extra : ordered native ->
  (root<length (memory native arraydef_0__schemaNodes))%nat -> reachable native root node depth ->
  In (child,extra) (children (SchemaMetadata.node_at native node)) ->
  (child<node /\ depth+extra<width root /\ key root child (depth+extra)<width root*width root)%nat.
Proof.
  intros Hordered Hroot Hreachable Hin.
  pose proof (reachable_bound _ _ _ _ Hordered Hroot Hreachable) as [Hnode Hsum].
  destruct (Hordered _ _ _ Hnode Hin) as [Hlower Hextra].
  destruct (reachable_grid _ _ _ _ Hordered Hroot (child_reachable _ _ _ _ _ _ Hreachable Hin)) as [Hchild [Hdepth Hkey]].
  repeat split;assumption.
Qed.
Lemma key_injective root left ld right rd : (ld<width root)%nat -> (rd<width root)%nat ->
  key root left ld=key root right rd -> left=right /\ ld=rd.
Proof. unfold key,width. intros Hld Hrd Heq. assert (left=right) by nia. subst right. split;[reflexivity|nia]. Qed.
Lemma grid_words root node depth :
  (node<width root)%nat -> (depth<width root)%nat ->
  Z.of_nat (width root*width root)<=maximum ->
  word (Z.of_nat (width root)) /\ word (Z.of_nat node*Z.of_nat (width root)) /\ word (Z.of_nat (key root node depth)).
Proof.
  intros Hnode Hdepth Hroom.
  pose proof (grid_bound root node depth Hnode Hdepth) as Hkey.
  assert (Hwidth:(width root<=width root*width root)%nat) by (unfold width;nia).
  assert (Hproduct:(node*width root<=key root node depth)%nat) by (unfold key;lia).
  apply Nat2Z.inj_le in Hwidth. apply Nat2Z.inj_le in Hproduct. apply Nat2Z.inj_lt in Hkey.
  unfold word. rewrite <-Nat2Z.inj_mul. repeat split;lia.
Qed.
Definition marked (s:Machine) index := withMemory s (modifyArray (memory s) arraydef_0__schemaMarks index 1).
Lemma marked_other s index name : name<>arraydef_0__schemaMarks -> memory (marked s index) name=memory s name.
Proof. intro Hname. unfold marked. cbn [memory withMemory]. now apply InternTailExecution.modify_other. Qed.
Lemma marked_meta s index slot : meta_value (marked s index) slot=meta_value s slot.
Proof. unfold meta_value. now rewrite marked_other by discriminate. Qed.
Lemma marked_represents s index logical : SchemaRepresentation.represents s logical -> SchemaRepresentation.represents (marked s index) logical.
Proof.
  intro Hrep. eapply SchemaRepresentation.transport;[exact Hrep|apply marked_meta|apply marked_other;discriminate|reflexivity|reflexivity|reflexivity].
Qed.
Theorem generated_mark s bs ns node depth stride observations :
  ns vardef_0__schemaMark_node=Z.of_nat node -> ns vardef_0__schemaMark_depth=Z.of_nat depth ->
  ns vardef_0__schemaMark_width=Z.of_nat stride ->
  Z.of_nat (node*stride+depth)<=maximum ->
  (node*stride+depth<length (memory s arraydef_0__schemaMarks))%nat ->
  execObserved (funcdef_0__schemaMark bs ns) (s,observations)=
    Some (tt,(marked s (node*stride+depth),observations)).
Proof.
  intros Hnode Hdepth Hwidth Hroom Hindex.
  assert (Hproduct:coerceInt (Z.of_nat node*Z.of_nat stride) 64=Z.of_nat (node*stride)).
  { rewrite <-Nat2Z.inj_mul. apply coerce_word. unfold word. rewrite Nat2Z.inj_add in Hroom. lia. }
  assert (Hsum:coerceInt (Z.of_nat (node*stride)+Z.of_nat depth) 64=Z.of_nat (node*stride+depth)).
  { rewrite <-Nat2Z.inj_add. apply coerce_word. unfold word;lia. }
  unfold funcdef_0__schemaMark. rewrite eliminate_correct. unfold funcdef_0__schemaMark_body.
  repeat first [progress cbn [optionBind fst snd]
    |progress unfold addInt at 1|progress unfold multInt at 1
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];rewrite Nat2Z.id;exact Hindex)
    |progress rewrite Hnode|progress rewrite Hdepth|progress rewrite Hwidth
    |progress rewrite Hproduct|progress rewrite Hsum|progress rewrite Nat2Z.id
    |progress replace (coerceInt 1 8) with 1 by reflexivity
    |progress cbv beta iota zeta delta [machine setMachine nums bools]
  ]. reflexivity.
Qed.
Theorem generated_reachable_mark s bs ns root node depth observations :
  ordered s -> (root<length (memory s arraydef_0__schemaNodes))%nat -> reachable s root node depth ->
  Z.of_nat (width root*width root)<=maximum ->
  (width root*width root<=length (memory s arraydef_0__schemaMarks))%nat ->
  ns vardef_0__schemaMark_node=Z.of_nat node -> ns vardef_0__schemaMark_depth=Z.of_nat depth ->
  ns vardef_0__schemaMark_width=Z.of_nat (width root) ->
  execObserved (funcdef_0__schemaMark bs ns) (s,observations)=Some (tt,(marked s (key root node depth),observations)).
Proof.
  intros Hordered Hroot Hreachable Hroom Hallocated Hnode Hdepth Hwidth.
  destruct (reachable_grid _ _ _ _ Hordered Hroot Hreachable) as [Hn [Hd Hkey]].
  unfold key. apply generated_mark;try assumption.
  - change (Z.of_nat (key root node depth)<=maximum). apply Nat2Z.inj_lt in Hkey. lia.
  - change (key root node depth<length (memory s arraydef_0__schemaMarks))%nat. lia.
Qed.
End SchemaGraph.
