From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash SchemaMetadata SchemaRepresentation SchemaNodeMeaning
  SchemaGraph SchemaEvaluation SchemaEvaluationInvariant SchemaEvaluationAxiom AxiomTaggedInvariant InternReserve.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationDependencies.
Import IndexExecution SipHashExecution.

(** Typed semantic views of the twelve native descriptor families. Child
    references are ordinary expression lookups, with no protocol evaluator left
    in the interface. A saved theorem retains its checked object proof. *)
Inductive view fs classes expressions : nat -> nat -> nat -> nat -> nat -> Protocol.expression -> Prop :=
| view_meta a b c d : Z.of_nat a<maximum ->
    view fs classes expressions 0 a b c d (Protocol.CE (Schemata.metavariable a))
| view_class a b c d cls : nth_error classes a=Some cls ->
    view fs classes expressions 1 a b c d (Protocol.CE (Schemata.literal_class cls))
| view_formula a b c d p : nth_error fs a=Some p ->
    view fs classes expressions 2 a b c d (Protocol.FE (Schemata.literal_formula p))
| view_abstract a b c d p : nth_error expressions a=Some (Protocol.FE p) ->
    view fs classes expressions 3 a b c d (Protocol.CE (Schemata.template_abstract p))
| view_equal a b c d x y : nth_error expressions a=Some (Protocol.CE x) -> nth_error expressions b=Some (Protocol.CE y) ->
    view fs classes expressions 4 a b c d (Protocol.FE (Schemata.template_equal x y))
| view_member a b c d x y : nth_error expressions a=Some (Protocol.CE x) -> nth_error expressions b=Some (Protocol.CE y) ->
    view fs classes expressions 5 a b c d (Protocol.FE (Schemata.template_member x y))
| view_imp a b c d p q : nth_error expressions a=Some (Protocol.FE p) -> nth_error expressions b=Some (Protocol.FE q) ->
    view fs classes expressions 6 a b c d (Protocol.FE (Schemata.template_imp p q))
| view_all a b c d p : nth_error expressions a=Some (Protocol.FE p) ->
    view fs classes expressions 7 a b c d (Protocol.FE (Schemata.template_all p))
| view_axiom tag a b c p q r : (tag<=17)%nat ->
    (SchemaGraph.need_p tag=true -> nth_error expressions a=Some (Protocol.FE p)) ->
    (SchemaGraph.need_q tag=true -> nth_error expressions b=Some (Protocol.FE q)) ->
    (SchemaGraph.need_r tag=true -> nth_error expressions c=Some (Protocol.FE r)) ->
    view fs classes expressions 8 tag a b c
      (Protocol.PE (Schemata.template_ax (Schemata.template_axiom tag p q r a b c)))
| view_mp a b c d p q : nth_error expressions a=Some (Protocol.PE p) -> nth_error expressions b=Some (Protocol.PE q) ->
    view fs classes expressions 9 a b c d (Protocol.PE (Schemata.template_mp p q))
| view_gen a b c d p : nth_error expressions a=Some (Protocol.PE p) ->
    view fs classes expressions 10 a b c d (Protocol.PE (Schemata.template_gen p))
| view_saved a b c d p (checked:SetTheory.derives p) : nth_error fs a=Some p ->
    view fs classes expressions 11 a b c d (Protocol.PE (Schemata.saved_theorem p checked)).

Lemma prefix_lookup {A} (expressions:list A) node child expression :
  nth_error (firstn node expressions) child=Some expression ->
  nth_error expressions child=Some expression.
Proof.
  intro Hlookup. rewrite List.nth_error_firstn in Hlookup.
  destruct (Nat.ltb child node);[exact Hlookup|discriminate].
Qed.
Lemma class_prefix fs classes expressions node child cls :
  Protocol.cf (SchemaRepresentation.context fs classes (firstn node expressions)) child=Some cls ->
  nth_error expressions child=Some (Protocol.CE cls).
Proof. intro Hlookup. apply prefix_lookup with node. exact (SchemaNodeMeaning.class_lookup _ _ _ Hlookup). Qed.
Lemma formula_prefix fs classes expressions node child p :
  Protocol.ff (SchemaRepresentation.context fs classes (firstn node expressions)) child=Some p ->
  nth_error expressions child=Some (Protocol.FE p).
Proof. intro Hlookup. apply prefix_lookup with node. exact (SchemaNodeMeaning.formula_lookup _ _ _ Hlookup). Qed.
Lemma proof_prefix fs classes expressions node child cert :
  Protocol.pf (SchemaRepresentation.context fs classes (firstn node expressions)) child=Some cert ->
  nth_error expressions child=Some (Protocol.PE cert).
Proof. intro Hlookup. apply prefix_lookup with node. exact (SchemaNodeMeaning.proof_lookup _ _ _ Hlookup). Qed.
Lemma argument_prefix fs classes expressions node needed child p :
  Protocol.formula_argument (SchemaRepresentation.context fs classes (firstn node expressions)) needed child=Some p ->
  needed=true -> nth_error expressions child=Some (Protocol.FE p).
Proof. unfold Protocol.formula_argument. intros Hlookup ->. now apply (formula_prefix fs classes expressions node child p). Qed.
Lemma axiom_view fs classes expressions node tag a b c cert :
  Protocol.axiom_expression (SchemaRepresentation.context fs classes (firstn node expressions)) tag a b c=Some cert ->
  view fs classes expressions 8 tag a b c (Protocol.PE cert).
Proof.
  unfold Protocol.axiom_expression. fold (SchemaGraph.need_p tag) (SchemaGraph.need_q tag) (SchemaGraph.need_r tag).
  destruct (Protocol.formula_argument _ (SchemaGraph.need_p tag) a) as [p|] eqn:Hp;[|discriminate].
  destruct (Protocol.formula_argument _ (SchemaGraph.need_q tag) b) as [q|] eqn:Hq;[|discriminate].
  destruct (Protocol.formula_argument _ (SchemaGraph.need_r tag) c) as [r|] eqn:Hr;[|discriminate].
  destruct (Nat.leb tag 17) eqn:Htag;[|discriminate].
  intro Hcert. injection Hcert as <-. apply view_axiom;[now apply Nat.leb_le| | |].
  - exact (argument_prefix fs classes expressions node _ a p Hp).
  - exact (argument_prefix fs classes expressions node _ b q Hq).
  - exact (argument_prefix fs classes expressions node _ c r Hr).
Qed.

Theorem entry_view fs classes expressions node raw expression :
  SchemaRepresentation.entry fs classes (firstn node expressions) raw expression ->
  exists k a b c d,raw=SchemaRepresentation.encode k a b c d expression /\
    SchemaRepresentation.fields_fit k a b c d expression /\ view fs classes expressions k a b c d expression.
Proof.
  intros (k & a & b & c & d & Hraw & Hfit & Hdenotes).
  exists k,a,b,c,d. split;[exact Hraw|]. split;[exact Hfit|].
  destruct Hdenotes as [[HnotSaved Hbuild]|(p & checked & -> & Hformula & ->)].
  - inversion Hbuild;subst.
    + constructor. assumption.
    + constructor. assumption.
    + constructor. assumption.
    + constructor. eapply formula_prefix;eassumption.
    + constructor;eapply class_prefix;eassumption.
    + constructor;eapply class_prefix;eassumption.
    + constructor;eapply formula_prefix;eassumption.
    + constructor. eapply formula_prefix;eassumption.
    + eapply axiom_view;eassumption.
    + constructor;eapply proof_prefix;eassumption.
    + constructor. eapply proof_prefix;eassumption.
    + contradiction.
  - constructor. exact Hformula.
Qed.

Theorem represented_view source logical node expression :
  SchemaRepresentation.represents source logical -> nth_error (Protocol.expressions logical) node=Some expression ->
  exists k a b c d,
    nth_error (memory source arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode k a b c d expression) /\
    SchemaRepresentation.fields_fit k a b c d expression /\
    view (Protocol.formulas logical) (Protocol.classes logical) (Protocol.expressions logical) k a b c d expression.
Proof.
  intros Hrepresentation Hlookup.
  destruct (SchemaRepresentation.lookup source logical node expression Hrepresentation Hlookup) as (raw & Hraw & Hentry).
  destruct (entry_view _ _ _ _ _ _ Hentry) as (k & a & b & c & d & -> & Hfit & Hview).
  exists k,a,b,c,d. repeat first [assumption|split].
Qed.

(** A reachable dependency is already completed in the native forward grid.
    This supplies the exact array read, word bound, strict earlier position and
    typed instantiated meaning required by the instruction handlers. *)
Theorem completed_child source native root expressions rho fs classes node depth raw child extra expression :
  SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
  SchemaGraph.reachable source root node depth ->
  nth_error (memory source arraydef_0__schemaNodes) node=Some raw ->
  In (child,extra) (SchemaGraph.children raw) ->
  SchemaEvaluationInvariant.completed source root expressions rho fs classes native (SchemaGraph.key root node depth) ->
  nth_error expressions child=Some expression ->
  Z.of_nat (SchemaGraph.width root*SchemaGraph.width root)<=maximum ->
  (SchemaGraph.width root*SchemaGraph.width root<=length (memory native arraydef_0__schemaValues))%nat ->
  (child<node /\ depth+extra<SchemaGraph.width root /\
    SchemaGraph.key root child (depth+extra)<SchemaGraph.key root node depth)%nat /\
  Z.of_nat (SchemaGraph.key root child (depth+extra))<=maximum /\
  nth_error (memory native arraydef_0__schemaValues) (SchemaGraph.key root child (depth+extra))=
    Some (SchemaEvaluation.value native (SchemaGraph.key root child (depth+extra))) /\
  SchemaEvaluation.meaning fs classes rho (depth+extra) expression
    (SchemaEvaluation.value native (SchemaGraph.key root child (depth+extra))).
Proof.
  intros Hordered Hroot Hreachable Hraw Hin Hcompleted Hlookup Hword Hallocated.
  assert (Hat:SchemaMetadata.node_at source node=raw).
  { unfold SchemaMetadata.node_at. exact (List.nth_error_nth _ _ _ Hraw). }
  rewrite <-Hat in Hin.
  destruct (SchemaGraph.child_grid source root node depth child extra Hordered Hroot Hreachable Hin) as [Hchild [Hdepth Hgrid]].
  assert (Hprevious:(SchemaGraph.key root child (depth+extra)<SchemaGraph.key root node depth)%nat).
  { unfold SchemaGraph.key,SchemaGraph.width in *. nia. }
  split;[repeat split;assumption|]. split.
  - apply Nat2Z.inj_lt in Hgrid. lia.
  - split.
    + unfold SchemaEvaluation.value. apply List.nth_error_nth'. lia.
    + eapply Hcompleted;[eapply SchemaGraph.child_reachable;eassumption|exact Hprevious|exact Hlookup].
Qed.
Lemma view_extend fs classes next_fs next_classes expressions k a b c d expression :
  (exists extra,next_fs=fs++extra) -> (exists extra,next_classes=classes++extra) ->
  view fs classes expressions k a b c d expression -> view next_fs next_classes expressions k a b c d expression.
Proof.
  intros Hfs Hclasses Hview. inversion Hview;subst;constructor;try assumption;
    eapply InternReserve.lookup_preserved;eassumption.
Qed.

Lemma fields_words k a b c d expression : SchemaRepresentation.fields_fit k a b c d expression ->
  word (Z.of_nat k) /\ word (Z.of_nat a) /\ word (Z.of_nat b) /\ word (Z.of_nat c) /\ word (Z.of_nat d).
Proof.
  unfold SchemaRepresentation.fields_fit. intro Hfit.
  repeat match goal with H:Forall _ (_::_) |- _ => inversion H;subst;clear H end.
  repeat first [assumption|split].
Qed.

Theorem axiom_argument source native root expressions rho fs classes node depth raw needed child template :
  SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
  SchemaGraph.reachable source root node depth ->
  nth_error (memory source arraydef_0__schemaNodes) node=Some raw ->
  (needed=true -> In (child,0%nat) (SchemaGraph.children raw)) ->
  (needed=true -> nth_error expressions child=Some (Protocol.FE template)) ->
  SchemaEvaluationInvariant.completed source root expressions rho fs classes native (SchemaGraph.key root node depth) ->
  Z.of_nat (SchemaGraph.width root*SchemaGraph.width root)<=maximum ->
  (SchemaGraph.width root*SchemaGraph.width root<=length (memory native arraydef_0__schemaValues))%nat ->
  word (Z.of_nat child) ->
  exists id,
    SchemaEvaluationAxiom.readable native (SchemaGraph.width root) depth needed child /\
    SchemaEvaluationAxiom.selected_id native (SchemaGraph.width root) depth needed child=Z.of_nat id /\
    word (Z.of_nat id) /\
    (if needed then nth_error fs id=Some (Schemata.instantiate_formula rho depth template) else id=child).
Proof.
  intros Hordered Hroot Hreachable Hraw Hin Hlookup Hcompleted Hword Hallocated Hchildword.
  destruct needed.
  - destruct (completed_child source native root expressions rho fs classes node depth raw child 0
      (Protocol.FE template) Hordered Hroot Hreachable Hraw (Hin eq_refl) Hcompleted (Hlookup eq_refl) Hword Hallocated)
      as [[Hchild [Hdepth Hprevious]] [Hkeyword [Hread Hmeaning]]].
    rewrite Nat.add_0_r in *. change (SchemaEvaluation.formula_value fs
      (SchemaEvaluation.value native (SchemaGraph.key root child depth)) (Schemata.instantiate_formula rho depth template)) in Hmeaning.
    destruct Hmeaning as [Hvalueword Hvalue].
    exists (Z.to_nat (SchemaEvaluation.value native (SchemaGraph.key root child depth))).
    assert (Hnatural:SchemaEvaluation.value native (SchemaGraph.key root child depth)=
      Z.of_nat (Z.to_nat (SchemaEvaluation.value native (SchemaGraph.key root child depth)))).
    { symmetry. apply Z2Nat.id. exact (proj1 Hvalueword). }
    split.
    + intros _. split;[exact Hkeyword|]. apply nth_error_Some. change (nth_error (memory native arraydef_0__schemaValues) (SchemaGraph.key root child depth)<>None). rewrite Hread. discriminate.
    + split;[exact Hnatural|]. split;[now rewrite <-Hnatural|exact Hvalue].
  - exists child. split;[intros H;discriminate|]. split;[reflexivity|]. split;[exact Hchildword|reflexivity].
Qed.

Theorem axiom_ready source native root expressions rho fs classes node depth tag a b c tp tq tr expression :
  SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
  SchemaGraph.reachable source root node depth ->
  nth_error (memory source arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode 8 tag a b c expression) ->
  (SchemaGraph.need_p tag=true -> nth_error expressions a=Some (Protocol.FE tp)) ->
  (SchemaGraph.need_q tag=true -> nth_error expressions b=Some (Protocol.FE tq)) ->
  (SchemaGraph.need_r tag=true -> nth_error expressions c=Some (Protocol.FE tr)) ->
  SchemaEvaluationInvariant.completed source root expressions rho fs classes native (SchemaGraph.key root node depth) ->
  Z.of_nat (SchemaGraph.width root*SchemaGraph.width root)<=maximum ->
  (SchemaGraph.width root*SchemaGraph.width root<=length (memory native arraydef_0__schemaValues))%nat ->
  word (Z.of_nat a) -> word (Z.of_nat b) -> word (Z.of_nat c) ->
  exists idA idB idC,
    SchemaEvaluationAxiom.readable native (SchemaGraph.width root) depth (AxiomTaggedInvariant.needs_p tag) a /\
    SchemaEvaluationAxiom.readable native (SchemaGraph.width root) depth (AxiomTaggedInvariant.needs_q tag) b /\
    SchemaEvaluationAxiom.readable native (SchemaGraph.width root) depth (Nat.eqb tag 1) c /\
    SchemaEvaluationAxiom.selected_id native (SchemaGraph.width root) depth (AxiomTaggedInvariant.needs_p tag) a=Z.of_nat idA /\
    SchemaEvaluationAxiom.selected_id native (SchemaGraph.width root) depth (AxiomTaggedInvariant.needs_q tag) b=Z.of_nat idB /\
    SchemaEvaluationAxiom.selected_id native (SchemaGraph.width root) depth (Nat.eqb tag 1) c=Z.of_nat idC /\
    word (Z.of_nat idA) /\ word (Z.of_nat idB) /\ word (Z.of_nat idC) /\
    AxiomTaggedInvariant.ready fs tag idA idB idC a b c
      (Schemata.instantiate_formula rho depth tp) (Schemata.instantiate_formula rho depth tq) (Schemata.instantiate_formula rho depth tr).
Proof.
  intros Hordered Hroot Hreachable Hraw Hp Hq Hr Hcompleted Hword Hallocated Ha Hb Hc.
  assert (Hpa:SchemaGraph.need_p tag=true -> In (a,0%nat)
    (SchemaGraph.children (SchemaRepresentation.encode 8 tag a b c expression))).
  { intro Hneed. rewrite SchemaGraph.children_encode. unfold SchemaGraph.children_fields.
    apply in_or_app. left. rewrite Hneed. now left. }
  assert (Hqb:SchemaGraph.need_q tag=true -> In (b,0%nat)
    (SchemaGraph.children (SchemaRepresentation.encode 8 tag a b c expression))).
  { intro Hneed. rewrite SchemaGraph.children_encode. unfold SchemaGraph.children_fields.
    apply in_or_app. right. apply in_or_app. left. rewrite Hneed. now left. }
  assert (Hrc:SchemaGraph.need_r tag=true -> In (c,0%nat)
    (SchemaGraph.children (SchemaRepresentation.encode 8 tag a b c expression))).
  { intro Hneed. rewrite SchemaGraph.children_encode. unfold SchemaGraph.children_fields.
    apply in_or_app. right. apply in_or_app. right. rewrite Hneed. now left. }
  destruct (axiom_argument source native root expressions rho fs classes node depth _ (SchemaGraph.need_p tag) a tp
    Hordered Hroot Hreachable Hraw Hpa Hp Hcompleted Hword Hallocated Ha)
    as (idA & HreadA & HselectedA & HwordA & HlookupA).
  destruct (axiom_argument source native root expressions rho fs classes node depth _ (SchemaGraph.need_q tag) b tq
    Hordered Hroot Hreachable Hraw Hqb Hq Hcompleted Hword Hallocated Hb)
    as (idB & HreadB & HselectedB & HwordB & HlookupB).
  destruct (axiom_argument source native root expressions rho fs classes node depth _ (SchemaGraph.need_r tag) c tr
    Hordered Hroot Hreachable Hraw Hrc Hr Hcompleted Hword Hallocated Hc)
    as (idC & HreadC & HselectedC & HwordC & HlookupC).
  exists idA,idB,idC. repeat first [assumption|split].
Qed.
End SchemaEvaluationDependencies.
